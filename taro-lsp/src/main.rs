use compiler::{
    diagnostics::{DiagnosticLevel, DiagnosticRecord, DiagnosticStage},
    ide::{
        AnalysisMode, AnalysisOwner, AnalysisRequest, AnalysisSnapshot, CompletionInfo,
        CompletionKind as TaroCompletionKind, SourceOverlay, analyze_owner_for_ide, completion_at,
        resolve_analysis_owner, signature_help_at,
    },
    ide_completion::{
        CompletionContext, build_completion_probe_overlay, completion_context_at,
        filter_completion_items_by_prefix,
    },
    span::{FileID, Position as SpanPosition, Span},
};
use std::{
    collections::HashMap,
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
}

#[derive(Default)]
struct BackendState {
    documents: HashMap<Url, DocumentData>,
    analyses: HashMap<AnalysisOwner, AnalysisData>,
    tasks: HashMap<AnalysisOwner, JoinHandle<()>>,
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
        let path = match uri.to_file_path() {
            Ok(path) => path,
            Err(_) => {
                self.client
                    .log_message(MessageType::ERROR, "failed to resolve file path from URI")
                    .await;
                return;
            }
        };
        let owner = match resolve_analysis_owner(path, None) {
            Ok(owner) => owner,
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
                return;
            }
        };

        let mut state = self.state.lock().await;
        let previous_owner = {
            let Some(document) = state.documents.get_mut(&uri) else {
                return;
            };
            document.owner.replace(owner.clone())
        };

        if let Some(previous_owner) = previous_owner
            && previous_owner != owner
            && !has_documents_for_owner(&state.documents, &previous_owner)
        {
            if let Some(handle) = state.tasks.remove(&previous_owner) {
                handle.abort();
            }
            state.analyses.remove(&previous_owner);
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
                        break;
                    };
                    let Some(mode) = entry.pending_mode.take() else {
                        break;
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
                        break;
                    };
                    if let Some(extra_mode) = entry.pending_mode.take() {
                        mode = merge_analysis_mode(mode, extra_mode);
                    }
                    let documents = owner_documents(&state.documents, &task_owner);
                    if documents.is_empty() {
                        state.analyses.remove(&task_owner);
                        break;
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
                    if owner_documents_changed(&state.documents, &task_owner, &version) {
                        continue;
                    }
                }

                for document in &version {
                    let diagnostics =
                        diagnostics_for_uri(&snapshot, &document.path, &document.text);
                    client
                        .publish_diagnostics(
                            document.uri.clone(),
                            diagnostics,
                            Some(document.version),
                        )
                        .await;
                }

                let mut state = state_ref.lock().await;
                if owner_documents_changed(&state.documents, &task_owner, &version) {
                    continue;
                }
                if let Some(entry) = state.analyses.get_mut(&task_owner) {
                    entry.snapshot = Some(snapshot);
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
}

#[tower_lsp::async_trait]
impl LanguageServer for Backend {
    async fn initialize(&self, _: InitializeParams) -> Result<InitializeResult> {
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

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        let uri = params.text_document.uri;
        let mut follow_up_uri = None;
        let mut state = self.state.lock().await;
        let owner = state.documents.remove(&uri).and_then(|doc| doc.owner);
        if let Some(owner) = owner {
            if has_documents_for_owner(&state.documents, &owner) {
                follow_up_uri = first_uri_for_owner(&state.documents, &owner);
            } else {
                if let Some(handle) = state.tasks.remove(&owner) {
                    handle.abort();
                }
                state.analyses.remove(&owner);
            }
        }
        drop(state);

        self.client.publish_diagnostics(uri, Vec::new(), None).await;
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
}

#[derive(Clone)]
struct OwnerDocument {
    uri: Url,
    path: PathBuf,
    text: String,
    version: i32,
}

fn owner_documents(
    documents: &HashMap<Url, DocumentData>,
    owner: &AnalysisOwner,
) -> Vec<OwnerDocument> {
    documents
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
        .collect()
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

fn server_capabilities() -> ServerCapabilities {
    ServerCapabilities {
        text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::FULL)),
        hover_provider: Some(HoverProviderCapability::Simple(true)),
        definition_provider: Some(OneOf::Left(true)),
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
) -> Vec<Diagnostic> {
    let mut file_map: HashMap<FileID, PathBuf> = HashMap::new();
    for mapping in &snapshot.file_mappings {
        file_map.insert(mapping.file, mapping.path.clone());
    }

    snapshot
        .diagnostics
        .iter()
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
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::{
        AnalysisOwner, CompletionInfo, DocumentData, OwnerDocument, TaroCompletionKind,
        completion_prefix, completion_trigger_characters, find_navigation_index,
        general_diagnostic, lsp_completion_item, owner_documents, owner_documents_changed,
        server_capabilities, signature_help_trigger_characters, utf16_to_char_offset,
    };
    use compiler::ide_completion::CompletionContext;
    use compiler::span::{FileID, Position, Span};
    use std::collections::{HashMap, HashSet};
    use std::path::PathBuf;
    use tower_lsp::lsp_types::{CompletionItemKind, Url};

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

#[tokio::main]
async fn main() {
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (service, socket) = LspService::new(Backend::new);
    Server::new(stdin, stdout, socket).serve(service).await;
}
