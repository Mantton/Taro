use compiler::{
    constants::{LOCK_FILE, MANIFEST_FILE, SOURCE_DIRECTORY},
    diagnostics::{DiagnosticLevel, DiagnosticRecord, DiagnosticStage},
    ide::{
        AnalysisMode, AnalysisOwner, AnalysisRequest, AnalysisSnapshot, CompletionInfo,
        CompletionKind as TaroCompletionKind, DocumentSymbolInfo,
        DocumentSymbolKind as TaroDocumentSymbolKind, InlayHintKind as TaroInlayHintKind,
        SemanticTokenInfo, SemanticTokenKind as TaroSemanticTokenKind, SourceOverlay,
        analyze_owner_for_ide, completion_at, document_highlights_at, document_symbols_for_file,
        inlay_hints_in_range, reference_span_at, references_at, resolve_analysis_owner,
        semantic_tokens_for_file, signature_help_at,
    },
    ide_completion::{
        CompletionContext, build_completion_probe_overlay, completion_context_at,
        filter_completion_items_by_prefix,
    },
    span::{FileID, Position as SpanPosition, Span},
};
use std::{
    collections::{HashMap, HashSet},
    path::{Path, PathBuf},
    sync::Arc,
    time::{Duration, Instant},
};
use tokio::{
    sync::{Mutex, Semaphore},
    task::JoinHandle,
    time::sleep,
};
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};
use url::Url;

#[derive(Default)]
struct DocumentData {
    text: String,
    version: i32,
    owner: Option<AnalysisOwner>,
}

#[derive(Default)]
struct AnalysisData {
    snapshot: Option<AnalysisSnapshot>,
    pending_mode: Option<AnalysisMode>,
    published_diagnostic_uris: HashSet<Url>,
}

#[derive(Default)]
struct BackendState {
    documents: HashMap<Url, DocumentData>,
    analyses: HashMap<AnalysisOwner, AnalysisData>,
    tasks: HashMap<AnalysisOwner, JoinHandle<()>>,
    supports_dynamic_file_watching: bool,
}

struct Backend {
    client: Client,
    state: Arc<Mutex<BackendState>>,
    analysis_gate: Arc<Semaphore>,
}

impl Backend {
    fn new(client: Client) -> Self {
        Self {
            client,
            state: Arc::new(Mutex::new(BackendState::default())),
            analysis_gate: Arc::new(Semaphore::new(1)),
        }
    }

    async fn schedule_analysis(&self, uri: Url, mode: AnalysisMode) {
        let _ = self.refresh_analysis_owners(vec![uri], mode).await;
    }

    async fn refresh_analysis_owners(
        &self,
        uris: Vec<Url>,
        mode: AnalysisMode,
    ) -> HashSet<AnalysisOwner> {
        let mut assignments = Vec::new();
        for uri in uris {
            let path = match uri.to_file_path() {
                Ok(path) => path,
                Err(_) => {
                    self.client
                        .log_message(MessageType::ERROR, "failed to resolve file path from URI")
                        .await;
                    continue;
                }
            };
            match resolve_analysis_owner(path, None) {
                Ok(owner) => assignments.push((uri, owner)),
                Err(error) => {
                    self.client
                        .log_message(
                            MessageType::ERROR,
                            format!("failed to resolve analysis owner for {}: {error}", uri),
                        )
                        .await;
                    self.client
                        .publish_diagnostics(
                            uri,
                            vec![general_diagnostic(format!(
                                "failed to resolve analysis owner: {error}"
                            ))],
                            None,
                        )
                        .await;
                }
            }
        }
        if assignments.is_empty() {
            return HashSet::new();
        }

        let (owners_to_schedule, stale_diagnostic_uris) = {
            let mut state = self.state.lock().await;
            let mut previous_owners = HashSet::new();
            let mut owners_to_schedule = HashSet::new();

            for (uri, owner) in assignments {
                let Some(document) = state.documents.get_mut(&uri) else {
                    continue;
                };
                if let Some(previous_owner) = document.owner.replace(owner.clone())
                    && previous_owner != owner
                {
                    previous_owners.insert(previous_owner);
                }
                owners_to_schedule.insert(owner);
            }

            let mut stale_diagnostic_uris = HashSet::new();
            for previous_owner in previous_owners {
                if has_documents_for_owner(&state.documents, &previous_owner) {
                    owners_to_schedule.insert(previous_owner);
                } else {
                    if let Some(handle) = state.tasks.remove(&previous_owner) {
                        handle.abort();
                    }
                    if let Some(analysis) = state.analyses.remove(&previous_owner) {
                        stale_diagnostic_uris.extend(analysis.published_diagnostic_uris);
                    }
                }
            }

            (owners_to_schedule, stale_diagnostic_uris)
        };

        self.clear_diagnostics(stale_diagnostic_uris).await;
        for owner in &owners_to_schedule {
            self.schedule_owner_analysis(owner.clone(), mode).await;
        }
        owners_to_schedule
    }

    async fn schedule_owner_analysis(&self, owner: AnalysisOwner, mode: AnalysisMode) {
        let mut state = self.state.lock().await;
        if !has_documents_for_owner(&state.documents, &owner) {
            return;
        }

        let entry = state.analyses.entry(owner.clone()).or_default();
        entry.pending_mode = Some(match (entry.pending_mode, mode) {
            (Some(existing), next) => merge_analysis_mode(existing, next),
            (None, next) => next,
        });

        if state.tasks.contains_key(&owner) {
            return;
        };
        let task_owner = owner.clone();
        let state_ref = self.state.clone();
        let client = self.client.clone();
        let analysis_gate = self.analysis_gate.clone();
        let handle = tokio::spawn(async move {
            loop {
                let mut mode = {
                    let mut state = state_ref.lock().await;
                    let Some(entry) = state.analyses.get_mut(&task_owner) else {
                        state.tasks.remove(&task_owner);
                        return;
                    };
                    let Some(mode) = entry.pending_mode.take() else {
                        state.tasks.remove(&task_owner);
                        return;
                    };
                    mode
                };

                let debounce = match mode {
                    AnalysisMode::OnType => Duration::from_millis(175),
                    AnalysisMode::OnSave => Duration::from_millis(0),
                };
                if !debounce.is_zero() {
                    sleep(debounce).await;
                }

                let (text, version) = {
                    let mut state = state_ref.lock().await;
                    let Some(entry) = state.analyses.get_mut(&task_owner) else {
                        state.tasks.remove(&task_owner);
                        return;
                    };
                    if let Some(extra_mode) = entry.pending_mode.take() {
                        mode = merge_analysis_mode(mode, extra_mode);
                    }
                    let documents = owner_documents(&state.documents, &task_owner);
                    if documents.is_empty() {
                        state.analyses.remove(&task_owner);
                        state.tasks.remove(&task_owner);
                        return;
                    }

                    let request = AnalysisRequest {
                        mode,
                        overlays: documents
                            .iter()
                            .map(|document| SourceOverlay {
                                path: document.path.clone(),
                                content: document.text.clone(),
                            })
                            .collect(),
                    };
                    (request, documents)
                };
                let started_at = Instant::now();

                let analysis_owner = task_owner.clone();
                let Ok(_permit) = analysis_gate.clone().acquire_owned().await else {
                    client
                        .log_message(MessageType::ERROR, "analysis gate closed")
                        .await;
                    break;
                };
                let snapshot = match tokio::task::spawn_blocking(move || {
                    analyze_owner_for_ide(analysis_owner, text, None)
                })
                .await
                {
                    Ok(Ok(snapshot)) => snapshot,
                    Ok(Err(error)) => {
                        client
                            .log_message(
                                MessageType::ERROR,
                                format!(
                                    "analysis failed for {}: {error}",
                                    analysis_owner_label(&task_owner)
                                ),
                            )
                            .await;
                        AnalysisSnapshot::default()
                    }
                    Err(error) => {
                        client
                            .log_message(
                                MessageType::ERROR,
                                format!(
                                    "analysis task failed for {}: {error}",
                                    analysis_owner_label(&task_owner)
                                ),
                            )
                            .await;
                        AnalysisSnapshot::default()
                    }
                };
                let elapsed_ms = started_at.elapsed().as_millis();
                client
                    .log_message(
                        MessageType::LOG,
                        format!(
                            "analysis owner={} mode={:?} docs={} elapsed_ms={} diagnostics={} hir_available={} typed_available={}",
                            analysis_owner_label(&task_owner),
                            mode,
                            version.len(),
                            elapsed_ms,
                            snapshot.diagnostics.len(),
                            snapshot.status.hir_available,
                            snapshot.status.typed_available,
                        ),
                    )
                    .await;

                {
                    let state = state_ref.lock().await;
                    if owner_analysis_superseded(&state, &task_owner, &version) {
                        continue;
                    }
                }

                let previous_diagnostic_uris = {
                    let state = state_ref.lock().await;
                    state
                        .analyses
                        .get(&task_owner)
                        .map(|analysis| analysis.published_diagnostic_uris.clone())
                        .unwrap_or_default()
                };
                let (publications, published_diagnostic_uris) = diagnostic_publications(
                    &snapshot,
                    &task_owner,
                    &version,
                    &previous_diagnostic_uris,
                );
                let mut possibly_published_diagnostic_uris = previous_diagnostic_uris;
                possibly_published_diagnostic_uris
                    .extend(published_diagnostic_uris.iter().cloned());
                {
                    let mut state = state_ref.lock().await;
                    if owner_analysis_superseded(&state, &task_owner, &version) {
                        continue;
                    }
                    let Some(entry) = state.analyses.get_mut(&task_owner) else {
                        continue;
                    };
                    // Record every URI that could carry diagnostics before sending. If an
                    // overlay changes during publication, the next pass will clear any stale URI.
                    entry.published_diagnostic_uris = possibly_published_diagnostic_uris;
                }
                for publication in publications {
                    client
                        .publish_diagnostics(
                            publication.uri,
                            publication.diagnostics,
                            publication.version,
                        )
                        .await;
                }

                let mut state = state_ref.lock().await;
                if owner_analysis_superseded(&state, &task_owner, &version) {
                    continue;
                }
                if let Some(entry) = state.analyses.get_mut(&task_owner) {
                    entry.snapshot = Some(snapshot);
                    entry.published_diagnostic_uris = published_diagnostic_uris;
                }
            }

            let mut state = state_ref.lock().await;
            state.tasks.remove(&task_owner);
            if !has_documents_for_owner(&state.documents, &task_owner) {
                state.analyses.remove(&task_owner);
            }
        });

        state.tasks.insert(owner, handle);
    }

    async fn clear_diagnostics(&self, uris: impl IntoIterator<Item = Url>) {
        for uri in uris {
            self.client.publish_diagnostics(uri, Vec::new(), None).await;
        }
    }

    async fn snapshot_for_uri(&self, uri: &Url) -> Option<(String, i32, AnalysisSnapshot)> {
        let state = self.state.lock().await;
        let doc = state.documents.get(uri)?;
        let owner = doc.owner.as_ref()?;
        let snapshot = state.analyses.get(owner)?.snapshot.clone()?;
        Some((doc.text.clone(), doc.version, snapshot))
    }

    async fn snapshot_context_for_uri(
        &self,
        uri: &Url,
    ) -> Option<(String, i32, AnalysisOwner, AnalysisSnapshot)> {
        let state = self.state.lock().await;
        let doc = state.documents.get(uri)?;
        let owner = doc.owner.as_ref()?.clone();
        let snapshot = state.analyses.get(&owner)?.snapshot.clone()?;
        Some((doc.text.clone(), doc.version, owner, snapshot))
    }

    async fn completion_for_uri_position(
        &self,
        uri: &Url,
        position: Position,
    ) -> Option<Vec<CompletionInfo>> {
        let (text, _version, owner, snapshot) = self.snapshot_context_for_uri(uri).await?;
        let line_text = line_at(&text, position.line as usize)?;
        let file_id = file_id_for_uri(&snapshot, uri)?;
        let span_position = SpanPosition {
            line: position.line as usize,
            offset: utf16_to_char_offset(line_text, position.character),
        };
        let context = completion_context_at(&text, span_position);
        let fallback_prefix = completion_prefix(&context);
        let fallback = || {
            filter_completion_items_by_prefix(
                completion_at(&snapshot, &text, file_id, span_position),
                fallback_prefix,
            )
        };

        match &context {
            CompletionContext::Member { .. } | CompletionContext::StaticMember { .. } => {
                let Some(overlay) = build_completion_probe_overlay(&text, span_position, &context)
                else {
                    return Some(fallback());
                };
                let Some(probe_snapshot) = self
                    .completion_probe_snapshot(&owner, uri, overlay.source_text.clone())
                    .await
                else {
                    return Some(fallback());
                };
                let Some(probe_file_id) = file_id_for_uri(&probe_snapshot, uri) else {
                    return Some(fallback());
                };

                let items = filter_completion_items_by_prefix(
                    completion_at(
                        &probe_snapshot,
                        &overlay.source_text,
                        probe_file_id,
                        overlay.position,
                    ),
                    &overlay.prefix,
                );
                if items.is_empty() {
                    Some(fallback())
                } else {
                    Some(items)
                }
            }
            CompletionContext::Lexical { .. } => Some(fallback()),
            CompletionContext::Unknown => {
                Some(completion_at(&snapshot, &text, file_id, span_position))
            }
        }
    }

    async fn completion_probe_snapshot(
        &self,
        owner: &AnalysisOwner,
        uri: &Url,
        active_document_text: String,
    ) -> Option<AnalysisSnapshot> {
        let request = {
            let state = self.state.lock().await;
            let documents = owner_documents(&state.documents, owner);
            if documents.is_empty() {
                return None;
            }
            AnalysisRequest {
                mode: AnalysisMode::OnType,
                overlays: documents
                    .into_iter()
                    .map(|document| SourceOverlay {
                        path: document.path,
                        content: if document.uri == *uri {
                            active_document_text.clone()
                        } else {
                            document.text
                        },
                    })
                    .collect(),
            }
        };

        let owner = owner.clone();
        let _permit = self.analysis_gate.clone().acquire_owned().await.ok()?;
        tokio::task::spawn_blocking(move || analyze_owner_for_ide(owner, request, None))
            .await
            .ok()?
            .ok()
    }

    async fn text_for_path(&self, path: &Path) -> Option<String> {
        let state = self.state.lock().await;
        state.documents.iter().find_map(|(uri, document)| {
            let candidate = uri.to_file_path().ok()?;
            if paths_match(candidate.as_path(), path) {
                Some(document.text.clone())
            } else {
                None
            }
        })
    }

    async fn text_for_snapshot_path(&self, path: &Path) -> String {
        if let Some(text) = self.text_for_path(path).await {
            return text;
        }
        std::fs::read_to_string(path).unwrap_or_default()
    }

    async fn location_for_span(&self, snapshot: &AnalysisSnapshot, span: Span) -> Option<Location> {
        let path = path_for_file_id(snapshot, span.file)?;
        let uri = Url::from_file_path(path).ok()?;
        let text = self.text_for_snapshot_path(path).await;
        Some(Location {
            uri,
            range: range_from_span(span, &text),
        })
    }

    async fn text_for_span(&self, snapshot: &AnalysisSnapshot, span: Span) -> Option<String> {
        let path = path_for_file_id(snapshot, span.file)?;
        let text = self.text_for_snapshot_path(path).await;
        extract_span_text(&text, span).map(ToOwned::to_owned)
    }
}

#[tower_lsp::async_trait]
impl LanguageServer for Backend {
    async fn initialize(&self, params: InitializeParams) -> Result<InitializeResult> {
        let supports_dynamic_file_watching =
            client_supports_dynamic_file_watching(&params.capabilities);
        self.state.lock().await.supports_dynamic_file_watching = supports_dynamic_file_watching;

        Ok(InitializeResult {
            server_info: Some(ServerInfo {
                name: "taro-lsp".to_string(),
                version: Some(env!("CARGO_PKG_VERSION").to_string()),
            }),
            capabilities: server_capabilities(),
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        self.client
            .log_message(
                MessageType::INFO,
                format!("taro-lsp initialized pid={}", std::process::id()),
            )
            .await;

        let supports_dynamic_file_watching = self.state.lock().await.supports_dynamic_file_watching;
        if supports_dynamic_file_watching
            && let Err(error) = self
                .client
                .register_capability(vec![watched_files_registration()])
                .await
        {
            self.client
                .log_message(
                    MessageType::WARNING,
                    format!("failed to register file watchers: {error}"),
                )
                .await;
        }
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        let uri = params.text_document.uri;
        let mut state = self.state.lock().await;
        state.documents.insert(
            uri.clone(),
            DocumentData {
                text: params.text_document.text,
                version: params.text_document.version,
                owner: None,
            },
        );
        drop(state);
        self.schedule_analysis(uri, AnalysisMode::OnType).await;
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        let uri = params.text_document.uri;
        if let Some(change) = params.content_changes.into_iter().next() {
            let mut state = self.state.lock().await;
            if let Some(doc) = state.documents.get_mut(&uri) {
                doc.text = change.text;
                doc.version = params.text_document.version;
            }
            drop(state);
            self.schedule_analysis(uri, AnalysisMode::OnType).await;
        }
    }

    async fn did_save(&self, params: DidSaveTextDocumentParams) {
        self.schedule_analysis(params.text_document.uri, AnalysisMode::OnSave)
            .await;
    }

    async fn did_change_watched_files(&self, params: DidChangeWatchedFilesParams) {
        let changed_paths = params
            .changes
            .into_iter()
            .filter_map(|change| change.uri.to_file_path().ok())
            .collect::<Vec<_>>();
        if changed_paths.is_empty() {
            return;
        }

        let (documents_to_reassign, owners_to_schedule) = {
            let state = self.state.lock().await;
            watched_analysis_targets(&state, &changed_paths)
        };

        let refreshed_owners = if documents_to_reassign.is_empty() {
            HashSet::new()
        } else {
            self.refresh_analysis_owners(documents_to_reassign, AnalysisMode::OnSave)
                .await
        };
        for owner in owners_to_schedule {
            if !refreshed_owners.contains(&owner) {
                self.schedule_owner_analysis(owner, AnalysisMode::OnSave)
                    .await;
            }
        }
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        let uri = params.text_document.uri;
        let mut follow_up_uri = None;
        let mut stale_diagnostic_uris = HashSet::new();
        let mut state = self.state.lock().await;
        let owner = state.documents.remove(&uri).and_then(|doc| doc.owner);
        if let Some(owner) = owner {
            if has_documents_for_owner(&state.documents, &owner) {
                follow_up_uri = first_uri_for_owner(&state.documents, &owner);
            } else {
                if let Some(handle) = state.tasks.remove(&owner) {
                    handle.abort();
                }
                if let Some(analysis) = state.analyses.remove(&owner) {
                    stale_diagnostic_uris.extend(analysis.published_diagnostic_uris);
                }
                if stale_diagnostic_uris.is_empty() {
                    stale_diagnostic_uris.insert(uri.clone());
                }
            }
        } else {
            stale_diagnostic_uris.insert(uri);
        }
        drop(state);

        self.clear_diagnostics(stale_diagnostic_uris).await;
        if let Some(uri) = follow_up_uri {
            self.schedule_analysis(uri, AnalysisMode::OnSave).await;
        }
    }

    async fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
        let uri = params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;

        let Some((text, _version, snapshot)) = self.snapshot_for_uri(&uri).await else {
            return Ok(None);
        };

        let Some(line_text) = line_at(&text, position.line as usize) else {
            return Ok(None);
        };
        let Some(file_id) = file_id_for_uri(&snapshot, &uri) else {
            return Ok(None);
        };
        let char_offset = utf16_to_char_offset(line_text, position.character);
        let position = (position.line as usize, char_offset);

        let hover = find_navigation_index(
            snapshot.navigation.hovers.as_slice(),
            snapshot.navigation.hover_parents.as_slice(),
            file_id,
            position,
            |hover| hover.span,
        )
        .map(|index| {
            let hover = &snapshot.navigation.hovers[index];
            Hover {
                contents: HoverContents::Markup(MarkupContent {
                    kind: MarkupKind::Markdown,
                    value: format!("```taro\n{}\n```", hover.contents),
                }),
                range: Some(range_from_span(hover.span, &text)),
            }
        });

        Ok(hover)
    }

    async fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        let uri = params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;

        let Some((text, _version, snapshot)) = self.snapshot_for_uri(&uri).await else {
            return Ok(None);
        };

        let Some(line_text) = line_at(&text, position.line as usize) else {
            return Ok(None);
        };
        let Some(file_id) = file_id_for_uri(&snapshot, &uri) else {
            return Ok(None);
        };
        let char_offset = utf16_to_char_offset(line_text, position.character);
        let position = (position.line as usize, char_offset);

        let Some(definition_index) = find_navigation_index(
            snapshot.navigation.definitions.as_slice(),
            snapshot.navigation.definition_parents.as_slice(),
            file_id,
            position,
            |item| item.source,
        ) else {
            return Ok(None);
        };
        let definition = &snapshot.navigation.definitions[definition_index];

        let target_path = snapshot
            .file_mappings
            .iter()
            .find(|mapping| mapping.file == definition.target.file)
            .map(|mapping| mapping.path.clone());

        let Some(target_path) = target_path else {
            return Ok(None);
        };

        let target_uri = Url::from_file_path(&target_path).ok();
        let Some(target_uri) = target_uri else {
            return Ok(None);
        };

        let target_text = if let Some(target_text) = self.text_for_path(&target_path).await {
            target_text
        } else {
            std::fs::read_to_string(&target_path).unwrap_or_default()
        };

        let location = Location {
            uri: target_uri,
            range: range_from_span(definition.target, &target_text),
        };

        Ok(Some(GotoDefinitionResponse::Scalar(location)))
    }

    async fn references(&self, params: ReferenceParams) -> Result<Option<Vec<Location>>> {
        let uri = params.text_document_position.text_document.uri;
        let position = params.text_document_position.position;

        let Some((text, _version, snapshot)) = self.snapshot_for_uri(&uri).await else {
            return Ok(None);
        };
        let Some(line_text) = line_at(&text, position.line as usize) else {
            return Ok(None);
        };
        let Some(file_id) = file_id_for_uri(&snapshot, &uri) else {
            return Ok(None);
        };

        let span_position = SpanPosition {
            line: position.line as usize,
            offset: utf16_to_char_offset(line_text, position.character),
        };
        let mut locations = Vec::new();
        for reference in references_at(
            &snapshot,
            file_id,
            span_position,
            params.context.include_declaration,
        ) {
            if let Some(location) = self.location_for_span(&snapshot, reference.span).await {
                locations.push(location);
            }
        }

        Ok(Some(locations))
    }

    async fn document_highlight(
        &self,
        params: DocumentHighlightParams,
    ) -> Result<Option<Vec<DocumentHighlight>>> {
        let uri = params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;
        let Some((text, _version, snapshot)) = self.snapshot_for_uri(&uri).await else {
            return Ok(None);
        };
        let Some(file_id) = file_id_for_uri(&snapshot, &uri) else {
            return Ok(None);
        };
        let Some(position) = span_position_from_lsp(&text, position) else {
            return Ok(None);
        };
        let highlights = document_highlights_at(&snapshot, file_id, position)
            .into_iter()
            .map(|reference| DocumentHighlight {
                range: range_from_span(reference.span, &text),
                kind: Some(DocumentHighlightKind::TEXT),
            })
            .collect();
        Ok(Some(highlights))
    }

    async fn document_symbol(
        &self,
        params: DocumentSymbolParams,
    ) -> Result<Option<DocumentSymbolResponse>> {
        let uri = params.text_document.uri;
        let Some((text, _version, snapshot)) = self.snapshot_for_uri(&uri).await else {
            return Ok(None);
        };
        let Some(file_id) = file_id_for_uri(&snapshot, &uri) else {
            return Ok(None);
        };
        let symbols = document_symbols_for_file(&snapshot, file_id)
            .into_iter()
            .map(|symbol| lsp_document_symbol(symbol, &text))
            .collect();
        Ok(Some(DocumentSymbolResponse::Nested(symbols)))
    }

    async fn semantic_tokens_full(
        &self,
        params: SemanticTokensParams,
    ) -> Result<Option<SemanticTokensResult>> {
        let uri = params.text_document.uri;
        let Some((text, _version, snapshot)) = self.snapshot_for_uri(&uri).await else {
            return Ok(None);
        };
        let Some(file_id) = file_id_for_uri(&snapshot, &uri) else {
            return Ok(None);
        };
        let data = encode_semantic_tokens(semantic_tokens_for_file(&snapshot, file_id), &text);
        Ok(Some(SemanticTokensResult::Tokens(SemanticTokens {
            result_id: None,
            data,
        })))
    }

    async fn inlay_hint(&self, params: InlayHintParams) -> Result<Option<Vec<InlayHint>>> {
        let uri = params.text_document.uri;
        let Some((text, _version, snapshot)) = self.snapshot_for_uri(&uri).await else {
            return Ok(None);
        };
        let Some(file_id) = file_id_for_uri(&snapshot, &uri) else {
            return Ok(None);
        };
        let Some(start) = span_position_from_lsp(&text, params.range.start) else {
            return Ok(Some(Vec::new()));
        };
        let Some(end) = span_position_from_lsp(&text, params.range.end) else {
            return Ok(Some(Vec::new()));
        };
        let hints = inlay_hints_in_range(&snapshot, file_id, start, end)
            .into_iter()
            .map(|hint| InlayHint {
                position: position_from_span_location(
                    &text,
                    hint.position.line,
                    hint.position.offset,
                ),
                label: InlayHintLabel::String(hint.label),
                kind: Some(match hint.kind {
                    TaroInlayHintKind::Type => InlayHintKind::TYPE,
                    TaroInlayHintKind::Parameter => InlayHintKind::PARAMETER,
                }),
                text_edits: None,
                tooltip: None,
                padding_left: Some(true),
                padding_right: None,
                data: None,
            })
            .collect();
        Ok(Some(hints))
    }

    async fn signature_help(&self, params: SignatureHelpParams) -> Result<Option<SignatureHelp>> {
        let uri = params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;

        let Some((text, _version, snapshot)) = self.snapshot_for_uri(&uri).await else {
            return Ok(None);
        };
        let Some(line_text) = line_at(&text, position.line as usize) else {
            return Ok(None);
        };
        let Some(file_id) = file_id_for_uri(&snapshot, &uri) else {
            return Ok(None);
        };

        let char_offset = utf16_to_char_offset(line_text, position.character);
        let Some(help) = signature_help_at(
            &snapshot,
            &text,
            file_id,
            SpanPosition {
                line: position.line as usize,
                offset: char_offset,
            },
        ) else {
            return Ok(None);
        };

        Ok(Some(SignatureHelp {
            signatures: help
                .signatures
                .into_iter()
                .map(|signature| SignatureInformation {
                    label: signature.label,
                    documentation: None,
                    parameters: Some(
                        signature
                            .parameters
                            .into_iter()
                            .map(|label| ParameterInformation {
                                label: ParameterLabel::Simple(label),
                                documentation: None,
                            })
                            .collect(),
                    ),
                    active_parameter: Some(help.active_parameter as u32),
                })
                .collect(),
            active_signature: Some(help.active_signature as u32),
            active_parameter: Some(help.active_parameter as u32),
        }))
    }

    async fn completion(&self, params: CompletionParams) -> Result<Option<CompletionResponse>> {
        let uri = params.text_document_position.text_document.uri;
        let position = params.text_document_position.position;

        let Some(items) = self.completion_for_uri_position(&uri, position).await else {
            return Ok(None);
        };
        let items = items
            .into_iter()
            .map(lsp_completion_item)
            .collect::<Vec<_>>();

        Ok(Some(CompletionResponse::Array(items)))
    }

    async fn prepare_rename(
        &self,
        params: TextDocumentPositionParams,
    ) -> Result<Option<PrepareRenameResponse>> {
        let uri = params.text_document.uri;
        let position = params.position;

        let Some((text, _version, snapshot)) = self.snapshot_for_uri(&uri).await else {
            return Ok(None);
        };
        let Some(line_text) = line_at(&text, position.line as usize) else {
            return Ok(None);
        };
        let Some(file_id) = file_id_for_uri(&snapshot, &uri) else {
            return Ok(None);
        };
        let span_position = SpanPosition {
            line: position.line as usize,
            offset: utf16_to_char_offset(line_text, position.character),
        };
        let Some(span) = reference_span_at(&snapshot, file_id, span_position) else {
            return Ok(None);
        };

        Ok(Some(PrepareRenameResponse::Range(range_from_span(
            span, &text,
        ))))
    }

    async fn rename(&self, params: RenameParams) -> Result<Option<WorkspaceEdit>> {
        if !is_valid_rename_identifier(&params.new_name) {
            return Ok(None);
        }

        let uri = params.text_document_position.text_document.uri;
        let position = params.text_document_position.position;
        let Some((text, _version, owner, snapshot)) = self.snapshot_context_for_uri(&uri).await
        else {
            return Ok(None);
        };
        let Some(line_text) = line_at(&text, position.line as usize) else {
            return Ok(None);
        };
        let Some(file_id) = file_id_for_uri(&snapshot, &uri) else {
            return Ok(None);
        };
        let span_position = SpanPosition {
            line: position.line as usize,
            offset: utf16_to_char_offset(line_text, position.character),
        };
        let Some(active_span) = reference_span_at(&snapshot, file_id, span_position) else {
            return Ok(None);
        };
        let Some(original_text) = self.text_for_span(&snapshot, active_span).await else {
            return Ok(None);
        };

        let references = references_at(&snapshot, file_id, span_position, true);
        if references.is_empty() {
            return Ok(None);
        }

        let mut changes: HashMap<Url, Vec<TextEdit>> = HashMap::new();
        for reference in references {
            let Some(path) = path_for_file_id(&snapshot, reference.span.file) else {
                return Ok(None);
            };
            if !owner_contains_path(&owner, path) {
                return Ok(None);
            }
            let Some(existing_text) = self.text_for_span(&snapshot, reference.span).await else {
                return Ok(None);
            };
            if existing_text != original_text {
                return Ok(None);
            }
            let Some(uri) = Url::from_file_path(path).ok() else {
                return Ok(None);
            };
            let source_text = self.text_for_snapshot_path(path).await;
            changes.entry(uri).or_default().push(TextEdit {
                range: range_from_span(reference.span, &source_text),
                new_text: params.new_name.clone(),
            });
        }

        Ok(Some(WorkspaceEdit {
            changes: Some(changes),
            ..WorkspaceEdit::default()
        }))
    }
}

#[derive(Clone)]
struct OwnerDocument {
    uri: Url,
    path: PathBuf,
    text: String,
    version: i32,
}

struct DiagnosticPublication {
    uri: Url,
    diagnostics: Vec<Diagnostic>,
    version: Option<i32>,
}

struct DiagnosticTarget {
    uri: Url,
    path: PathBuf,
    text: String,
    version: Option<i32>,
}

fn diagnostic_publications(
    snapshot: &AnalysisSnapshot,
    owner: &AnalysisOwner,
    documents: &[OwnerDocument],
    previous_uris: &HashSet<Url>,
) -> (Vec<DiagnosticPublication>, HashSet<Url>) {
    let mut targets = HashMap::<Url, DiagnosticTarget>::new();
    let mut current_uris = HashSet::new();

    for document in documents {
        current_uris.insert(document.uri.clone());
        targets.insert(
            document.uri.clone(),
            DiagnosticTarget {
                uri: document.uri.clone(),
                path: document.path.clone(),
                text: document.text.clone(),
                version: Some(document.version),
            },
        );
    }

    for diagnostic in &snapshot.diagnostics {
        let Some(span) = diagnostic.span else {
            continue;
        };
        let Some(path) = path_for_file_id(snapshot, span.file) else {
            continue;
        };
        if !owner_contains_source_path(owner, path) {
            continue;
        }
        if let Some(document) = documents
            .iter()
            .find(|document| paths_match(&document.path, path))
        {
            current_uris.insert(document.uri.clone());
            continue;
        }
        let Some(uri) = Url::from_file_path(path).ok() else {
            continue;
        };

        current_uris.insert(uri.clone());
        targets
            .entry(uri.clone())
            .or_insert_with(|| DiagnosticTarget {
                uri,
                path: path.to_path_buf(),
                text: std::fs::read_to_string(path).unwrap_or_default(),
                version: None,
            });
    }

    for uri in previous_uris {
        let Some(path) = uri.to_file_path().ok() else {
            continue;
        };
        targets
            .entry(uri.clone())
            .or_insert_with(|| DiagnosticTarget {
                uri: uri.clone(),
                text: std::fs::read_to_string(&path).unwrap_or_default(),
                path,
                version: None,
            });
    }

    let general_diagnostic_uri = documents.first().map(|document| &document.uri);
    let mut publications = targets
        .into_values()
        .map(|target| {
            let diagnostics = if current_uris.contains(&target.uri) {
                diagnostics_for_uri(
                    snapshot,
                    &target.path,
                    &target.text,
                    general_diagnostic_uri == Some(&target.uri),
                )
            } else {
                Vec::new()
            };
            DiagnosticPublication {
                diagnostics,
                uri: target.uri,
                version: target.version,
            }
        })
        .collect::<Vec<_>>();
    publications.sort_by(|lhs, rhs| lhs.uri.as_str().cmp(rhs.uri.as_str()));

    (publications, current_uris)
}

fn owner_documents(
    documents: &HashMap<Url, DocumentData>,
    owner: &AnalysisOwner,
) -> Vec<OwnerDocument> {
    let mut matching = documents
        .iter()
        .filter_map(|(uri, document)| {
            if document.owner.as_ref() != Some(owner) {
                return None;
            }

            let path = uri.to_file_path().ok()?;
            Some(OwnerDocument {
                uri: uri.clone(),
                path,
                text: document.text.clone(),
                version: document.version,
            })
        })
        .collect::<Vec<_>>();
    matching.sort_by(|lhs, rhs| lhs.path.cmp(&rhs.path));
    matching
}

fn owner_documents_changed(
    documents: &HashMap<Url, DocumentData>,
    owner: &AnalysisOwner,
    tracked: &[OwnerDocument],
) -> bool {
    if documents
        .values()
        .filter(|document| document.owner.as_ref() == Some(owner))
        .count()
        != tracked.len()
    {
        return true;
    }

    tracked.iter().any(|document| {
        documents
            .get(&document.uri)
            .map(|current| {
                current.version != document.version || current.owner.as_ref() != Some(owner)
            })
            .unwrap_or(true)
    })
}

fn owner_analysis_superseded(
    state: &BackendState,
    owner: &AnalysisOwner,
    tracked: &[OwnerDocument],
) -> bool {
    owner_documents_changed(&state.documents, owner, tracked)
        || state
            .analyses
            .get(owner)
            .and_then(|analysis| analysis.pending_mode)
            .is_some()
}

fn watched_analysis_targets(
    state: &BackendState,
    changed_paths: &[PathBuf],
) -> (Vec<Url>, Vec<AnalysisOwner>) {
    let mut documents_to_reassign = HashSet::new();
    let mut owners_to_schedule = HashSet::new();

    for changed_path in changed_paths {
        if changed_path.file_name().and_then(|name| name.to_str()) == Some(MANIFEST_FILE)
            && let Some(package_root) = changed_path.parent()
        {
            let source_root = package_root.join(SOURCE_DIRECTORY);
            for uri in state.documents.keys() {
                let Some(document_path) = uri.to_file_path().ok() else {
                    continue;
                };
                if path_is_within(&document_path, &source_root) {
                    documents_to_reassign.insert(uri.clone());
                }
            }
        }

        // Text sync owns open buffers. Reanalyzing their disk events would duplicate didSave
        // and, for dirty buffers, would still analyze the in-memory overlay rather than the disk.
        let changed_document_is_open = state.documents.keys().any(|uri| {
            uri.to_file_path()
                .ok()
                .is_some_and(|path| paths_match(&path, changed_path))
        });
        if !changed_document_is_open {
            for owner in state
                .documents
                .values()
                .filter_map(|document| document.owner.as_ref())
            {
                if watched_path_affects_owner(owner, changed_path) {
                    owners_to_schedule.insert(owner.clone());
                }
            }
        }
    }

    let mut documents_to_reassign = documents_to_reassign.into_iter().collect::<Vec<_>>();
    documents_to_reassign.sort_by(|lhs, rhs| lhs.as_str().cmp(rhs.as_str()));
    let mut owners_to_schedule = owners_to_schedule.into_iter().collect::<Vec<_>>();
    owners_to_schedule.sort_by(|lhs, rhs| lhs.path().cmp(rhs.path()));
    (documents_to_reassign, owners_to_schedule)
}

fn watched_path_affects_owner(owner: &AnalysisOwner, changed_path: &Path) -> bool {
    match owner {
        AnalysisOwner::Package(root) => {
            paths_match(changed_path, &root.join(MANIFEST_FILE))
                || paths_match(changed_path, &root.join(LOCK_FILE))
                || path_is_within(changed_path, &root.join(SOURCE_DIRECTORY))
        }
        AnalysisOwner::Script(script) => paths_match(changed_path, script),
    }
}

fn path_is_within(path: &Path, root: &Path) -> bool {
    if path.starts_with(root) {
        return true;
    }

    match (normalize_watch_path(path), normalize_watch_path(root)) {
        (Some(path), Some(root)) => path.starts_with(root),
        _ => false,
    }
}

fn normalize_watch_path(path: &Path) -> Option<PathBuf> {
    path.canonicalize().ok().or_else(|| {
        let parent = path.parent()?.canonicalize().ok()?;
        Some(parent.join(path.file_name()?))
    })
}

fn has_documents_for_owner(documents: &HashMap<Url, DocumentData>, owner: &AnalysisOwner) -> bool {
    documents
        .values()
        .any(|document| document.owner.as_ref() == Some(owner))
}

fn first_uri_for_owner(
    documents: &HashMap<Url, DocumentData>,
    owner: &AnalysisOwner,
) -> Option<Url> {
    documents.iter().find_map(|(uri, document)| {
        if document.owner.as_ref() == Some(owner) {
            Some(uri.clone())
        } else {
            None
        }
    })
}

fn analysis_owner_label(owner: &AnalysisOwner) -> String {
    match owner {
        AnalysisOwner::Package(path) => format!("package:{}", path.display()),
        AnalysisOwner::Script(path) => format!("script:{}", path.display()),
    }
}

fn merge_analysis_mode(current: AnalysisMode, next: AnalysisMode) -> AnalysisMode {
    match (current, next) {
        (AnalysisMode::OnSave, _) | (_, AnalysisMode::OnSave) => AnalysisMode::OnSave,
        _ => AnalysisMode::OnType,
    }
}

fn completion_prefix(context: &CompletionContext) -> &str {
    match context {
        CompletionContext::Lexical { prefix }
        | CompletionContext::Member { prefix, .. }
        | CompletionContext::StaticMember { prefix, .. } => prefix,
        CompletionContext::Unknown => "",
    }
}

fn completion_trigger_characters() -> Vec<String> {
    let mut characters = vec![".".to_string()];
    characters.extend(('a'..='z').map(|ch| ch.to_string()));
    characters.extend(('A'..='Z').map(|ch| ch.to_string()));
    characters.push("_".to_string());
    characters
}

fn watched_files_registration() -> Registration {
    let options = DidChangeWatchedFilesRegistrationOptions {
        watchers: ["**/*.tr", "**/package.toml", "**/package.lock"]
            .into_iter()
            .map(|pattern| FileSystemWatcher {
                glob_pattern: GlobPattern::String(pattern.to_string()),
                kind: None,
            })
            .collect(),
    };

    Registration {
        id: "taro-watch-files".to_string(),
        method: "workspace/didChangeWatchedFiles".to_string(),
        register_options: Some(
            serde_json::to_value(options).expect("watched-file registration must serialize"),
        ),
    }
}

fn client_supports_dynamic_file_watching(capabilities: &ClientCapabilities) -> bool {
    capabilities
        .workspace
        .as_ref()
        .and_then(|workspace| workspace.did_change_watched_files.as_ref())
        .and_then(|watching| watching.dynamic_registration)
        .unwrap_or(false)
}

fn server_capabilities() -> ServerCapabilities {
    ServerCapabilities {
        text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::FULL)),
        hover_provider: Some(HoverProviderCapability::Simple(true)),
        definition_provider: Some(OneOf::Left(true)),
        references_provider: Some(OneOf::Left(true)),
        document_highlight_provider: Some(OneOf::Left(true)),
        document_symbol_provider: Some(OneOf::Left(true)),
        semantic_tokens_provider: Some(
            SemanticTokensOptions {
                work_done_progress_options: WorkDoneProgressOptions::default(),
                legend: semantic_tokens_legend(),
                range: None,
                full: Some(SemanticTokensFullOptions::Bool(true)),
            }
            .into(),
        ),
        inlay_hint_provider: Some(OneOf::Right(InlayHintServerCapabilities::Options(
            InlayHintOptions {
                work_done_progress_options: WorkDoneProgressOptions::default(),
                resolve_provider: Some(false),
            },
        ))),
        rename_provider: Some(OneOf::Right(RenameOptions {
            prepare_provider: Some(true),
            work_done_progress_options: WorkDoneProgressOptions::default(),
        })),
        signature_help_provider: Some(SignatureHelpOptions {
            trigger_characters: Some(signature_help_trigger_characters()),
            retrigger_characters: Some(signature_help_trigger_characters()),
            work_done_progress_options: WorkDoneProgressOptions::default(),
        }),
        completion_provider: Some(CompletionOptions {
            resolve_provider: Some(false),
            trigger_characters: Some(completion_trigger_characters()),
            all_commit_characters: None,
            work_done_progress_options: WorkDoneProgressOptions::default(),
            completion_item: None,
        }),
        ..ServerCapabilities::default()
    }
}

fn semantic_tokens_legend() -> SemanticTokensLegend {
    SemanticTokensLegend {
        token_types: vec![
            SemanticTokenType::NAMESPACE,
            SemanticTokenType::TYPE,
            SemanticTokenType::STRUCT,
            SemanticTokenType::ENUM,
            SemanticTokenType::INTERFACE,
            SemanticTokenType::TYPE_PARAMETER,
            SemanticTokenType::FUNCTION,
            SemanticTokenType::METHOD,
            SemanticTokenType::PROPERTY,
            SemanticTokenType::VARIABLE,
            SemanticTokenType::PARAMETER,
            SemanticTokenType::ENUM_MEMBER,
        ],
        token_modifiers: vec![
            SemanticTokenModifier::DECLARATION,
            SemanticTokenModifier::READONLY,
            SemanticTokenModifier::STATIC,
            SemanticTokenModifier::ASYNC,
            SemanticTokenModifier::DEFAULT_LIBRARY,
        ],
    }
}

#[allow(deprecated)]
fn lsp_document_symbol(symbol: DocumentSymbolInfo, source_text: &str) -> DocumentSymbol {
    DocumentSymbol {
        name: symbol.name,
        detail: symbol.detail,
        kind: match symbol.kind {
            TaroDocumentSymbolKind::Namespace => SymbolKind::NAMESPACE,
            TaroDocumentSymbolKind::Struct => SymbolKind::STRUCT,
            TaroDocumentSymbolKind::Enum => SymbolKind::ENUM,
            TaroDocumentSymbolKind::Interface => SymbolKind::INTERFACE,
            TaroDocumentSymbolKind::Function => SymbolKind::FUNCTION,
            TaroDocumentSymbolKind::Method => SymbolKind::METHOD,
            TaroDocumentSymbolKind::Field => SymbolKind::FIELD,
            TaroDocumentSymbolKind::Property => SymbolKind::PROPERTY,
            TaroDocumentSymbolKind::EnumMember => SymbolKind::ENUM_MEMBER,
            TaroDocumentSymbolKind::TypeAlias => SymbolKind::TYPE_PARAMETER,
            TaroDocumentSymbolKind::Constant => SymbolKind::CONSTANT,
            TaroDocumentSymbolKind::Variable => SymbolKind::VARIABLE,
            TaroDocumentSymbolKind::Type => SymbolKind::CLASS,
        },
        tags: None,
        deprecated: None,
        range: range_from_span(symbol.span, source_text),
        selection_range: range_from_span(symbol.selection_span, source_text),
        children: if symbol.children.is_empty() {
            None
        } else {
            Some(
                symbol
                    .children
                    .into_iter()
                    .map(|child| lsp_document_symbol(child, source_text))
                    .collect(),
            )
        },
    }
}

fn encode_semantic_tokens(items: Vec<SemanticTokenInfo>, source_text: &str) -> Vec<SemanticToken> {
    let mut encoded = Vec::new();
    let mut previous_line = 0;
    let mut previous_start = 0;
    let mut previous_end: Option<(u32, u32)> = None;

    for item in items {
        if item.span.start.line != item.span.end.line {
            continue;
        }
        let range = range_from_span(item.span, source_text);
        if range.start == range.end {
            continue;
        }
        if previous_end
            .is_some_and(|(line, end)| line == range.start.line && range.start.character < end)
        {
            continue;
        }
        let delta_line = range.start.line - previous_line;
        let delta_start = if delta_line == 0 {
            range.start.character - previous_start
        } else {
            range.start.character
        };
        let mut modifiers = 0;
        modifiers |= u32::from(item.modifiers.declaration);
        modifiers |= u32::from(item.modifiers.readonly) << 1;
        modifiers |= u32::from(item.modifiers.static_member) << 2;
        modifiers |= u32::from(item.modifiers.async_member) << 3;
        modifiers |= u32::from(item.modifiers.default_library) << 4;
        encoded.push(SemanticToken {
            delta_line,
            delta_start,
            length: range.end.character - range.start.character,
            token_type: semantic_token_type_index(item.kind),
            token_modifiers_bitset: modifiers,
        });
        previous_line = range.start.line;
        previous_start = range.start.character;
        previous_end = Some((range.end.line, range.end.character));
    }
    encoded
}

fn semantic_token_type_index(kind: TaroSemanticTokenKind) -> u32 {
    match kind {
        TaroSemanticTokenKind::Namespace => 0,
        TaroSemanticTokenKind::Type => 1,
        TaroSemanticTokenKind::Struct => 2,
        TaroSemanticTokenKind::Enum => 3,
        TaroSemanticTokenKind::Interface => 4,
        TaroSemanticTokenKind::TypeParameter => 5,
        TaroSemanticTokenKind::Function => 6,
        TaroSemanticTokenKind::Method => 7,
        TaroSemanticTokenKind::Property => 8,
        TaroSemanticTokenKind::Variable => 9,
        TaroSemanticTokenKind::Parameter => 10,
        TaroSemanticTokenKind::EnumMember => 11,
    }
}

fn lsp_completion_item(item: CompletionInfo) -> CompletionItem {
    CompletionItem {
        label: item.label.clone(),
        kind: Some(lsp_completion_kind(item.kind)),
        detail: item.detail,
        insert_text: Some(item.label),
        insert_text_format: Some(InsertTextFormat::PLAIN_TEXT),
        ..CompletionItem::default()
    }
}

fn lsp_completion_kind(kind: TaroCompletionKind) -> CompletionItemKind {
    match kind {
        TaroCompletionKind::Function => CompletionItemKind::FUNCTION,
        TaroCompletionKind::Method => CompletionItemKind::METHOD,
        TaroCompletionKind::Struct => CompletionItemKind::STRUCT,
        TaroCompletionKind::Enum => CompletionItemKind::ENUM,
        TaroCompletionKind::Interface => CompletionItemKind::INTERFACE,
        TaroCompletionKind::Module
        | TaroCompletionKind::Namespace
        | TaroCompletionKind::Package => CompletionItemKind::MODULE,
        TaroCompletionKind::Field => CompletionItemKind::FIELD,
        TaroCompletionKind::Variant => CompletionItemKind::ENUM_MEMBER,
        TaroCompletionKind::Variable => CompletionItemKind::VARIABLE,
        TaroCompletionKind::Constant => CompletionItemKind::CONSTANT,
        TaroCompletionKind::Property => CompletionItemKind::PROPERTY,
        TaroCompletionKind::TypeAlias
        | TaroCompletionKind::TypeParameter
        | TaroCompletionKind::Type => CompletionItemKind::TYPE_PARAMETER,
        TaroCompletionKind::Keyword => CompletionItemKind::KEYWORD,
        TaroCompletionKind::Unknown => CompletionItemKind::TEXT,
    }
}

fn diagnostics_for_uri(
    snapshot: &AnalysisSnapshot,
    current_path: &Path,
    source_text: &str,
    include_general: bool,
) -> Vec<Diagnostic> {
    let mut file_map: HashMap<FileID, PathBuf> = HashMap::new();
    for mapping in &snapshot.file_mappings {
        file_map.insert(mapping.file, mapping.path.clone());
    }

    snapshot
        .diagnostics
        .iter()
        .filter(|diagnostic| include_general || diagnostic.span.is_some())
        .filter_map(|diagnostic| lsp_diagnostic(diagnostic, current_path, source_text, &file_map))
        .collect()
}

fn lsp_diagnostic(
    diagnostic: &DiagnosticRecord,
    current_path: &Path,
    source_text: &str,
    file_map: &HashMap<FileID, PathBuf>,
) -> Option<Diagnostic> {
    let span = diagnostic.span;
    if let Some(span) = span {
        let file_path = file_map.get(&span.file)?;
        if !paths_match(file_path, current_path) {
            return None;
        }
    }

    let severity = match diagnostic.level {
        DiagnosticLevel::Error => Some(DiagnosticSeverity::ERROR),
        DiagnosticLevel::Warn => Some(DiagnosticSeverity::WARNING),
        DiagnosticLevel::Info => Some(DiagnosticSeverity::INFORMATION),
    };

    let code = diagnostic
        .code
        .map(|value| NumberOrString::Number(value as i32))
        .or_else(|| {
            Some(NumberOrString::String(
                stage_name(diagnostic.stage).to_string(),
            ))
        });

    let mut related_information = Vec::new();
    for related in &diagnostic.related_info {
        if let Some(span) = related.span {
            let related_path = file_map.get(&span.file)?;
            let related_text = if paths_match(related_path, current_path) {
                source_text.to_string()
            } else {
                std::fs::read_to_string(related_path).unwrap_or_default()
            };
            let location = Location {
                uri: Url::from_file_path(related_path).ok()?,
                range: range_from_span(span, &related_text),
            };
            related_information.push(DiagnosticRelatedInformation {
                location,
                message: related.message.clone(),
            });
        }
    }

    Some(Diagnostic {
        range: span
            .map(|span| range_from_span(span, source_text))
            .unwrap_or_else(zero_range),
        severity,
        code,
        code_description: None,
        source: Some("taro".to_string()),
        message: diagnostic.message.clone(),
        related_information: if related_information.is_empty() {
            None
        } else {
            Some(related_information)
        },
        tags: None,
        data: None,
    })
}

fn general_diagnostic(message: String) -> Diagnostic {
    Diagnostic {
        range: zero_range(),
        severity: Some(DiagnosticSeverity::ERROR),
        code: Some(NumberOrString::String("general".into())),
        code_description: None,
        source: Some("taro".to_string()),
        message,
        related_information: None,
        tags: None,
        data: None,
    }
}

fn zero_range() -> Range {
    Range {
        start: Position {
            line: 0,
            character: 0,
        },
        end: Position {
            line: 0,
            character: 0,
        },
    }
}

fn stage_name(stage: DiagnosticStage) -> &'static str {
    match stage {
        DiagnosticStage::Parse => "parse",
        DiagnosticStage::Resolve => "resolve",
        DiagnosticStage::Typecheck => "typecheck",
        DiagnosticStage::PostTypecheck => "post_typecheck",
        DiagnosticStage::Thir => "thir",
        DiagnosticStage::Mir => "mir",
        DiagnosticStage::Entry => "entry",
        DiagnosticStage::General => "general",
    }
}

fn file_id_for_uri(snapshot: &AnalysisSnapshot, uri: &Url) -> Option<FileID> {
    let path = uri.to_file_path().ok()?;
    snapshot.file_lookup.get(&path).copied().or_else(|| {
        path.canonicalize()
            .ok()
            .and_then(|path| snapshot.file_lookup.get(&path).copied())
    })
}

fn path_for_file_id(snapshot: &AnalysisSnapshot, file_id: FileID) -> Option<&Path> {
    snapshot
        .file_mappings
        .iter()
        .find(|mapping| mapping.file == file_id)
        .map(|mapping| mapping.path.as_path())
}

fn find_navigation_index<T>(
    items: &[T],
    parents: &[Option<usize>],
    file: FileID,
    position: (usize, usize),
    span_of: impl Fn(&T) -> Span,
) -> Option<usize> {
    if items.is_empty() || items.len() != parents.len() {
        return None;
    }

    let insertion =
        items.partition_point(|item| span_start_at_or_before(span_of(item), file, position));
    let mut current = insertion.checked_sub(1)?;

    loop {
        let span = span_of(&items[current]);
        if span.file != file {
            return None;
        }
        if span_contains(span, position.0, position.1) {
            return Some(current);
        }
        current = parents[current]?;
    }
}

fn span_start_at_or_before(span: Span, file: FileID, position: (usize, usize)) -> bool {
    if span.file < file {
        return true;
    }
    if span.file > file {
        return false;
    }

    span.start.line < position.0
        || (span.start.line == position.0 && span.start.offset <= position.1)
}

fn span_contains(span: Span, line: usize, char_offset: usize) -> bool {
    if line < span.start.line || line > span.end.line {
        return false;
    }
    if line == span.start.line && char_offset < span.start.offset {
        return false;
    }
    if line == span.end.line && char_offset > span.end.offset {
        return false;
    }
    true
}

fn range_from_span(span: Span, source_text: &str) -> Range {
    let start = position_from_span_location(source_text, span.start.line, span.start.offset);
    let end = position_from_span_location(source_text, span.end.line, span.end.offset);
    Range { start, end }
}

fn span_position_from_lsp(source_text: &str, position: Position) -> Option<SpanPosition> {
    let line = line_at(source_text, position.line as usize)?;
    Some(SpanPosition {
        line: position.line as usize,
        offset: utf16_to_char_offset(line, position.character),
    })
}

fn extract_span_text(source_text: &str, span: Span) -> Option<&str> {
    if span.start.line != span.end.line {
        return None;
    }
    let line = line_at(source_text, span.start.line)?;
    let start = byte_index_for_char_offset(line, span.start.offset)?;
    let end = byte_index_for_char_offset(line, span.end.offset)?;
    line.get(start..end)
}

fn byte_index_for_char_offset(line_text: &str, char_offset: usize) -> Option<usize> {
    if char_offset == line_text.chars().count() {
        return Some(line_text.len());
    }
    line_text
        .char_indices()
        .nth(char_offset)
        .map(|(index, _)| index)
}

fn position_from_span_location(source_text: &str, line: usize, char_offset: usize) -> Position {
    let utf16_col = line_at(source_text, line)
        .map(|line_text| {
            line_text
                .chars()
                .take(char_offset)
                .map(|ch| ch.len_utf16() as u32)
                .sum()
        })
        .unwrap_or(char_offset as u32);

    Position {
        line: line as u32,
        character: utf16_col,
    }
}

fn utf16_to_char_offset(line_text: &str, utf16_col: u32) -> usize {
    let mut consumed_utf16 = 0u32;
    let mut char_offset = 0usize;

    for ch in line_text.chars() {
        if consumed_utf16 >= utf16_col {
            break;
        }
        consumed_utf16 += ch.len_utf16() as u32;
        char_offset += 1;
    }

    char_offset
}

fn line_at(source_text: &str, line: usize) -> Option<&str> {
    source_text.lines().nth(line)
}

fn signature_help_trigger_characters() -> Vec<String> {
    vec!["(".into(), ",".into()]
}

fn paths_match(lhs: &Path, rhs: &Path) -> bool {
    if lhs == rhs {
        return true;
    }

    match (lhs.canonicalize(), rhs.canonicalize()) {
        (Ok(lhs), Ok(rhs)) => lhs == rhs,
        _ => match (normalize_watch_path(lhs), normalize_watch_path(rhs)) {
            (Some(lhs), Some(rhs)) => lhs == rhs,
            _ => false,
        },
    }
}

fn owner_contains_path(owner: &AnalysisOwner, path: &Path) -> bool {
    match owner {
        AnalysisOwner::Package(root) => path.starts_with(root),
        AnalysisOwner::Script(script) => paths_match(script, path),
    }
}

fn owner_contains_source_path(owner: &AnalysisOwner, path: &Path) -> bool {
    match owner {
        AnalysisOwner::Package(root) => path_is_within(path, &root.join(SOURCE_DIRECTORY)),
        AnalysisOwner::Script(script) => paths_match(script, path),
    }
}

fn is_valid_rename_identifier(value: &str) -> bool {
    let mut chars = value.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    if !(first == '_' || first.is_alphabetic()) {
        return false;
    }
    if !chars.all(|ch| ch == '_' || ch.is_alphanumeric()) {
        return false;
    }
    !is_taro_keyword(value)
}

fn is_taro_keyword(value: &str) -> bool {
    matches!(
        value,
        "any"
            | "as"
            | "is"
            | "break"
            | "case"
            | "const"
            | "continue"
            | "defer"
            | "else"
            | "enum"
            | "export"
            | "extern"
            | "false"
            | "for"
            | "func"
            | "guard"
            | "if"
            | "impl"
            | "import"
            | "in"
            | "interface"
            | "let"
            | "loop"
            | "match"
            | "mod"
            | "mut"
            | "namespace"
            | "nil"
            | "operator"
            | "private"
            | "public"
            | "return"
            | "readonly"
            | "static"
            | "struct"
            | "true"
            | "type"
            | "unsafe"
            | "var"
            | "where"
            | "while"
            | "class"
            | "final"
            | "override"
            | "fileprivate"
            | "protected"
            | "async"
            | "await"
            | "ref"
            | "init"
    )
}

#[tokio::main]
async fn main() {
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (service, socket) = LspService::new(Backend::new);
    Server::new(stdin, stdout, socket).serve(service).await;
}

#[cfg(test)]
mod tests {
    use super::{
        AnalysisData, AnalysisMode, AnalysisOwner, BackendState, CompletionInfo, DocumentData,
        OneOf, OwnerDocument, TaroCompletionKind, client_supports_dynamic_file_watching,
        completion_prefix, completion_trigger_characters, diagnostic_publications,
        encode_semantic_tokens, find_navigation_index, general_diagnostic,
        is_valid_rename_identifier, lsp_completion_item, owner_analysis_superseded,
        owner_documents, owner_documents_changed, server_capabilities,
        signature_help_trigger_characters, utf16_to_char_offset, watched_analysis_targets,
        watched_files_registration, watched_path_affects_owner,
    };
    use compiler::span::{FileID, Position, Span};
    use compiler::{
        diagnostics::{DiagnosticLevel, DiagnosticRecord, DiagnosticStage},
        ide::{
            AnalysisSnapshot, FileMapping, SemanticTokenInfo, SemanticTokenKind,
            SemanticTokenModifiers,
        },
        ide_completion::CompletionContext,
    };
    use std::collections::{HashMap, HashSet};
    use std::path::PathBuf;
    use tower_lsp::lsp_types::{
        ClientCapabilities, CompletionItemKind, DidChangeWatchedFilesClientCapabilities,
        DidChangeWatchedFilesRegistrationOptions, GlobPattern, SemanticTokensFullOptions,
        SemanticTokensServerCapabilities, Url, WorkspaceClientCapabilities,
    };

    #[test]
    fn owner_documents_collects_matching_documents() {
        let owner = AnalysisOwner::Package(PathBuf::from("/tmp/pkg"));
        let other_owner = AnalysisOwner::Script(PathBuf::from("/tmp/other.tr"));
        let uri_a = Url::from_file_path("/tmp/pkg/src/a.tr").expect("uri a");
        let uri_b = Url::from_file_path("/tmp/pkg/src/b.tr").expect("uri b");
        let uri_c = Url::from_file_path("/tmp/other.tr").expect("uri c");

        let mut documents = HashMap::new();
        documents.insert(
            uri_a.clone(),
            DocumentData {
                text: "a".into(),
                version: 1,
                owner: Some(owner.clone()),
            },
        );
        documents.insert(
            uri_b.clone(),
            DocumentData {
                text: "b".into(),
                version: 2,
                owner: Some(owner.clone()),
            },
        );
        documents.insert(
            uri_c,
            DocumentData {
                text: "c".into(),
                version: 3,
                owner: Some(other_owner),
            },
        );

        let collected = owner_documents(&documents, &owner);
        assert_eq!(collected.len(), 2);
        assert!(collected.iter().any(|document| document.uri == uri_a));
        assert!(collected.iter().any(|document| document.uri == uri_b));
    }

    #[test]
    fn owner_documents_changed_detects_new_document() {
        let owner = AnalysisOwner::Package(PathBuf::from("/tmp/pkg"));
        let uri_a = Url::from_file_path("/tmp/pkg/src/a.tr").expect("uri a");
        let uri_b = Url::from_file_path("/tmp/pkg/src/b.tr").expect("uri b");

        let mut documents = HashMap::new();
        documents.insert(
            uri_a.clone(),
            DocumentData {
                text: "a".into(),
                version: 1,
                owner: Some(owner.clone()),
            },
        );

        let tracked = vec![OwnerDocument {
            uri: uri_a,
            path: PathBuf::from("/tmp/pkg/src/a.tr"),
            text: "a".into(),
            version: 1,
        }];

        documents.insert(
            uri_b,
            DocumentData {
                text: "b".into(),
                version: 1,
                owner: Some(owner.clone()),
            },
        );

        assert!(owner_documents_changed(&documents, &owner, &tracked));
    }

    #[test]
    fn pending_filesystem_analysis_supersedes_matching_open_versions() {
        let owner = AnalysisOwner::Package(PathBuf::from("/tmp/pkg"));
        let uri = Url::from_file_path("/tmp/pkg/src/a.tr").expect("uri");
        let document = DocumentData {
            text: "a".into(),
            version: 1,
            owner: Some(owner.clone()),
        };
        let tracked = vec![OwnerDocument {
            uri: uri.clone(),
            path: PathBuf::from("/tmp/pkg/src/a.tr"),
            text: "a".into(),
            version: 1,
        }];
        let mut state = BackendState::default();
        state.documents.insert(uri, document);
        state.analyses.insert(
            owner.clone(),
            AnalysisData {
                pending_mode: Some(AnalysisMode::OnSave),
                ..AnalysisData::default()
            },
        );

        assert!(owner_analysis_superseded(&state, &owner, &tracked));
    }

    #[test]
    fn watched_file_registration_covers_sources_and_package_metadata() {
        let registration = watched_files_registration();
        assert_eq!(registration.method, "workspace/didChangeWatchedFiles");
        let options: DidChangeWatchedFilesRegistrationOptions =
            serde_json::from_value(registration.register_options.expect("registration options"))
                .expect("deserialize registration options");
        let patterns = options
            .watchers
            .into_iter()
            .map(|watcher| match watcher.glob_pattern {
                GlobPattern::String(pattern) => pattern,
                GlobPattern::Relative(_) => panic!("expected workspace-wide pattern"),
            })
            .collect::<HashSet<_>>();

        assert_eq!(
            patterns,
            HashSet::from([
                "**/*.tr".to_string(),
                "**/package.toml".to_string(),
                "**/package.lock".to_string(),
            ])
        );
    }

    #[test]
    fn dynamic_file_watching_requires_client_registration_support() {
        assert!(!client_supports_dynamic_file_watching(
            &ClientCapabilities::default()
        ));

        let capabilities = ClientCapabilities {
            workspace: Some(WorkspaceClientCapabilities {
                did_change_watched_files: Some(DidChangeWatchedFilesClientCapabilities {
                    dynamic_registration: Some(true),
                    relative_pattern_support: None,
                }),
                ..WorkspaceClientCapabilities::default()
            }),
            ..ClientCapabilities::default()
        };
        assert!(client_supports_dynamic_file_watching(&capabilities));
    }

    #[test]
    fn deleted_package_source_path_schedules_known_owner_without_io() {
        let owner = AnalysisOwner::Package(PathBuf::from("/tmp/taro-lsp-deleted-source"));
        let deleted = PathBuf::from("/tmp/taro-lsp-deleted-source/src/removed.tr");
        assert!(watched_path_affects_owner(&owner, &deleted));
    }

    #[test]
    fn watched_change_for_open_source_relies_on_text_document_sync() {
        let root = PathBuf::from("/tmp/taro-lsp-open-source");
        let source = root.join("src/main.tr");
        let uri = Url::from_file_path(&source).expect("source uri");
        let mut state = BackendState::default();
        state.documents.insert(
            uri,
            DocumentData {
                text: String::new(),
                version: 1,
                owner: Some(AnalysisOwner::Package(root)),
            },
        );

        let (documents, owners) = watched_analysis_targets(&state, &[source]);
        assert!(documents.is_empty());
        assert!(owners.is_empty());
    }

    #[test]
    fn manifest_change_reassigns_open_package_documents() {
        let root = PathBuf::from("/tmp/taro-lsp-manifest-change");
        let owner = AnalysisOwner::Package(root.clone());
        let uri = Url::from_file_path(root.join("src/main.tr")).expect("source uri");
        let mut state = BackendState::default();
        state.documents.insert(
            uri.clone(),
            DocumentData {
                text: "func main() {}".into(),
                version: 1,
                owner: Some(owner.clone()),
            },
        );

        let (documents, owners) = watched_analysis_targets(&state, &[root.join("package.toml")]);
        assert_eq!(documents, vec![uri]);
        assert_eq!(owners, vec![owner]);
    }

    #[test]
    fn nested_manifest_change_still_schedules_outer_owner() {
        let root = PathBuf::from("/tmp/taro-lsp-nested-manifest");
        let owner = AnalysisOwner::Package(root.clone());
        let outer_uri = Url::from_file_path(root.join("src/main.tr")).expect("outer uri");
        let nested_root = root.join("src/nested");
        let nested_uri = Url::from_file_path(nested_root.join("src/lib.tr")).expect("nested uri");
        let mut state = BackendState::default();
        for uri in [outer_uri, nested_uri.clone()] {
            state.documents.insert(
                uri,
                DocumentData {
                    text: String::new(),
                    version: 1,
                    owner: Some(owner.clone()),
                },
            );
        }

        let (documents, owners) =
            watched_analysis_targets(&state, &[nested_root.join("package.toml")]);
        assert_eq!(documents, vec![nested_uri]);
        assert_eq!(owners, vec![owner]);
    }

    #[test]
    fn diagnostic_publications_include_unopened_and_clear_stale_files() {
        let root = PathBuf::from("/tmp/taro-lsp-diagnostic-publications");
        let open_path = root.join("src/open.tr");
        let unopened_path = root.join("src/unopened.tr");
        let stale_path = root.join("src/stale.tr");
        let dependency_path = root.join("vendor/dependency.tr");
        let open_uri = Url::from_file_path(&open_path).expect("open uri");
        let unopened_uri = Url::from_file_path(&unopened_path).expect("unopened uri");
        let stale_uri = Url::from_file_path(&stale_path).expect("stale uri");
        let dependency_uri = Url::from_file_path(&dependency_path).expect("dependency uri");
        let open_file = FileID::new(0);
        let unopened_file = FileID::new(1);
        let dependency_file = FileID::new(2);
        let snapshot = AnalysisSnapshot {
            diagnostics: vec![
                DiagnosticRecord {
                    message: "unopened error".into(),
                    span: Some(Span {
                        file: unopened_file,
                        start: Position { line: 0, offset: 0 },
                        end: Position { line: 0, offset: 1 },
                    }),
                    level: DiagnosticLevel::Error,
                    code: None,
                    stage: DiagnosticStage::Typecheck,
                    related_info: Vec::new(),
                },
                DiagnosticRecord {
                    message: "package error".into(),
                    span: None,
                    level: DiagnosticLevel::Error,
                    code: None,
                    stage: DiagnosticStage::General,
                    related_info: Vec::new(),
                },
                DiagnosticRecord {
                    message: "dependency error".into(),
                    span: Some(Span {
                        file: dependency_file,
                        start: Position { line: 0, offset: 0 },
                        end: Position { line: 0, offset: 1 },
                    }),
                    level: DiagnosticLevel::Error,
                    code: None,
                    stage: DiagnosticStage::Typecheck,
                    related_info: Vec::new(),
                },
            ],
            file_mappings: vec![
                FileMapping {
                    file: open_file,
                    path: open_path.clone(),
                },
                FileMapping {
                    file: unopened_file,
                    path: unopened_path,
                },
                FileMapping {
                    file: dependency_file,
                    path: dependency_path,
                },
            ],
            ..AnalysisSnapshot::default()
        };
        let documents = vec![OwnerDocument {
            uri: open_uri.clone(),
            path: open_path,
            text: "func main() {}".into(),
            version: 7,
        }];

        let (publications, current) = diagnostic_publications(
            &snapshot,
            &AnalysisOwner::Package(root),
            &documents,
            &HashSet::from([stale_uri.clone()]),
        );
        let publication = |uri: &Url| {
            publications
                .iter()
                .find(|publication| publication.uri == *uri)
                .expect("publication")
        };

        assert_eq!(publication(&open_uri).diagnostics.len(), 1);
        assert_eq!(publication(&open_uri).version, Some(7));
        assert_eq!(publication(&unopened_uri).diagnostics.len(), 1);
        assert_eq!(publication(&unopened_uri).version, None);
        assert!(publication(&stale_uri).diagnostics.is_empty());
        assert!(
            publications
                .iter()
                .all(|publication| publication.uri != dependency_uri)
        );
        assert_eq!(current, HashSet::from([open_uri, unopened_uri]));
    }

    #[test]
    fn find_navigation_index_selects_deepest_nested_span() {
        let file = FileID::new(0);
        let outer = Span {
            file,
            start: Position { line: 0, offset: 0 },
            end: Position {
                line: 0,
                offset: 10,
            },
        };
        let inner = Span {
            file,
            start: Position { line: 0, offset: 2 },
            end: Position { line: 0, offset: 4 },
        };

        let items = [outer, inner];
        let parents = [None, Some(0)];
        let index = find_navigation_index(&items, &parents, file, (0, 3), |span| *span);
        assert_eq!(index, Some(1));
    }

    #[test]
    fn signature_help_trigger_characters_match_supported_contexts() {
        assert_eq!(signature_help_trigger_characters(), vec!["(", ","]);
    }

    #[test]
    fn server_capabilities_advertise_completion() {
        let capabilities = server_capabilities();
        let completion = capabilities
            .completion_provider
            .expect("completion provider");
        assert_eq!(
            completion.trigger_characters,
            Some(completion_trigger_characters())
        );
    }

    #[test]
    fn server_capabilities_advertise_references_and_rename_prepare() {
        let capabilities = server_capabilities();
        assert!(matches!(
            capabilities.references_provider,
            Some(OneOf::Left(true))
        ));
        let Some(OneOf::Right(rename)) = capabilities.rename_provider else {
            panic!("expected rename options");
        };
        assert_eq!(rename.prepare_provider, Some(true));
    }

    #[test]
    fn server_capabilities_advertise_remaining_lsp_stories() {
        let capabilities = server_capabilities();
        assert!(matches!(
            capabilities.document_highlight_provider,
            Some(OneOf::Left(true))
        ));
        assert!(matches!(
            capabilities.document_symbol_provider,
            Some(OneOf::Left(true))
        ));
        let Some(SemanticTokensServerCapabilities::SemanticTokensOptions(tokens)) =
            capabilities.semantic_tokens_provider
        else {
            panic!("expected semantic token options");
        };
        assert_eq!(tokens.range, None);
        assert!(matches!(
            tokens.full,
            Some(SemanticTokensFullOptions::Bool(true))
        ));
        assert_eq!(tokens.legend.token_types.len(), 12);
        assert_eq!(tokens.legend.token_modifiers.len(), 5);
        assert!(capabilities.inlay_hint_provider.is_some());
    }

    #[test]
    fn semantic_token_encoding_uses_utf16_and_modifier_bits() {
        let file = FileID::new(0);
        let tokens = encode_semantic_tokens(
            vec![SemanticTokenInfo {
                span: Span {
                    file,
                    start: Position { line: 0, offset: 2 },
                    end: Position { line: 0, offset: 5 },
                },
                kind: SemanticTokenKind::Function,
                modifiers: SemanticTokenModifiers {
                    declaration: true,
                    async_member: true,
                    ..SemanticTokenModifiers::default()
                },
            }],
            "😀 foo",
        );

        assert_eq!(tokens.len(), 1);
        assert_eq!(tokens[0].delta_start, 3);
        assert_eq!(tokens[0].length, 3);
        assert_eq!(tokens[0].token_type, 6);
        assert_eq!(tokens[0].token_modifiers_bitset, 0b01001);
    }

    #[test]
    fn rename_identifier_validation_rejects_keywords_and_invalid_names() {
        assert!(is_valid_rename_identifier("renamedValue"));
        assert!(is_valid_rename_identifier("_value2"));
        for invalid in ["", "2value", "with-dash", "struct", "async"] {
            assert!(!is_valid_rename_identifier(invalid), "{invalid}");
        }
    }

    #[test]
    fn completion_trigger_characters_include_dot_and_identifier_starts() {
        let characters = completion_trigger_characters();
        let unique = characters.iter().collect::<HashSet<_>>();

        assert_eq!(characters.len(), unique.len(), "{characters:?}");
        for expected in [".", "a", "z", "A", "Z", "_"] {
            assert!(characters.iter().any(|item| item == expected));
        }
        for excluded in ["0", "9"] {
            assert!(!characters.iter().any(|item| item == excluded));
        }
    }

    #[test]
    fn completion_item_conversion_is_stable() {
        let item = lsp_completion_item(CompletionInfo {
            label: "format".into(),
            kind: TaroCompletionKind::Function,
            detail: Some("func format()".into()),
        });

        assert_eq!(item.label, "format");
        assert_eq!(item.kind, Some(CompletionItemKind::FUNCTION));
        assert_eq!(item.insert_text.as_deref(), Some("format"));
        assert_eq!(item.detail.as_deref(), Some("func format()"));
    }

    #[test]
    fn completion_prefix_tracks_all_contexts() {
        assert_eq!(
            completion_prefix(&CompletionContext::Lexical {
                prefix: "loc".into()
            }),
            "loc"
        );
        assert_eq!(
            completion_prefix(&CompletionContext::Member {
                receiver: "point".into(),
                prefix: "m".into()
            }),
            "m"
        );
        assert_eq!(
            completion_prefix(&CompletionContext::StaticMember {
                base: "Heading".into(),
                prefix: "n".into()
            }),
            "n"
        );
        assert_eq!(completion_prefix(&CompletionContext::Unknown), "");
    }

    #[test]
    fn utf16_offsets_count_wide_characters_for_completion_positions() {
        assert_eq!(utf16_to_char_offset("a😀b", 0), 0);
        assert_eq!(utf16_to_char_offset("a😀b", 1), 1);
        assert_eq!(utf16_to_char_offset("a😀b", 3), 2);
        assert_eq!(utf16_to_char_offset("a😀b", 4), 3);
    }

    #[test]
    fn general_diagnostic_uses_zero_range() {
        let diagnostic = general_diagnostic("missing TARO_HOME".into());
        assert_eq!(diagnostic.range.start.line, 0);
        assert_eq!(diagnostic.range.start.character, 0);
        assert_eq!(diagnostic.message, "missing TARO_HOME");
    }
}
