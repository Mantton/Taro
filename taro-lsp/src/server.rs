//! LSP transport and synchronization of current editor text.

use std::{
    collections::BTreeMap,
    error::Error,
    fs,
    path::{Path, PathBuf},
    time::{Duration, Instant},
};

use compiler::compile::source::canonical_source_path;
use crossbeam_channel::RecvTimeoutError;
use lsp_server::{Connection, ErrorCode, Message, Notification, Request, RequestId, Response};
use lsp_types::{
    CompletionOptions, CompletionParams, DidChangeTextDocumentParams, DidChangeWatchedFilesParams,
    DidChangeWatchedFilesRegistrationOptions, DidChangeWorkspaceFoldersParams,
    DidCloseTextDocumentParams, DidOpenTextDocumentParams, FileSystemWatcher, GotoDefinitionParams,
    HoverParams, HoverProviderCapability, InitializeParams, MessageType, OneOf,
    PublishDiagnosticsParams, Registration, RegistrationParams, ServerCapabilities,
    TextDocumentPositionParams, TextDocumentSyncCapability, TextDocumentSyncKind,
    TextDocumentSyncOptions, Uri, WorkspaceFoldersServerCapabilities, WorkspaceServerCapabilities,
    notification::{self, Notification as _},
    request::{self, Request as _},
};
use serde_json::Value;
use url::Url;

use crate::{
    features,
    protocol::AnalysisMode,
    supervisor::{Launch, Notice, Policy, Supervisor},
};

type Result<T> = std::result::Result<T, Box<dyn Error + Send + Sync>>;
const REQUEST_TIMEOUT: Duration = Duration::from_secs(2);
const STD_IDLE_TIMEOUT: Duration = Duration::from_secs(5);
const MAX_WAITING_REQUESTS: usize = 32;
const FILE_WATCH_REGISTRATION: &str = "taro-file-watchers";

pub fn run(launch: Launch, installed_std: Option<PathBuf>) -> Result<()> {
    let (connection, io) = Connection::stdio();
    let (initialize_id, params) = connection.initialize_start()?;
    let init: InitializeParams = serde_json::from_value(params)?;
    let caps = ServerCapabilities {
        text_document_sync: Some(TextDocumentSyncCapability::Options(
            TextDocumentSyncOptions {
                open_close: Some(true),
                change: Some(TextDocumentSyncKind::FULL),
                ..TextDocumentSyncOptions::default()
            },
        )),
        hover_provider: Some(HoverProviderCapability::Simple(true)),
        definition_provider: Some(OneOf::Left(true)),
        completion_provider: Some(CompletionOptions {
            trigger_characters: Some(vec![".".into()]),
            ..CompletionOptions::default()
        }),
        workspace: Some(WorkspaceServerCapabilities {
            workspace_folders: Some(WorkspaceFoldersServerCapabilities {
                supported: Some(true),
                change_notifications: Some(lsp_types::OneOf::Left(true)),
            }),
            file_operations: None,
        }),
        ..ServerCapabilities::default()
    };
    connection.initialize_finish(
        initialize_id,
        serde_json::json!({
            "capabilities": caps,
            "serverInfo": { "name": "taro-lsp", "version": env!("CARGO_PKG_VERSION") },
        }),
    )?;
    if init
        .capabilities
        .workspace
        .as_ref()
        .and_then(|workspace| workspace.did_change_watched_files)
        .is_some_and(|files| files.dynamic_registration == Some(true))
    {
        register_watchers(&connection)?;
    }
    let mut server = Server {
        launch,
        installed_std,
        watching_files: false,
        workspaces: BTreeMap::new(),
        std_workspace: None,
        waiting: Vec::new(),
        trace_analysis: std::env::var_os("TARO_LSP_TRACE_ANALYSIS").is_some(),
    };
    if let Some(folders) = init.workspace_folders {
        for folder in folders {
            server.add_workspace(&folder.uri);
        }
    } else {
        #[allow(deprecated)]
        if let Some(uri) = init.root_uri {
            server.add_workspace(&uri);
        }
    }
    let result = server.event_loop(&connection);
    drop(server);
    drop(connection);
    io.join()?;
    result
}

struct Server {
    launch: Launch,
    installed_std: Option<PathBuf>,
    watching_files: bool,
    workspaces: BTreeMap<PathBuf, Supervisor>,
    std_workspace: Option<StdWorkspace>,
    waiting: Vec<EditorQuery>,
    trace_analysis: bool,
}

struct StdWorkspace {
    supervisor: Supervisor,
    disk_digest: Option<String>,
    idle_until: Option<Instant>,
}

impl StdWorkspace {
    fn refresh_disk_view(&mut self, root: &Path) {
        let digest = crate::bundle::std_digest(root).ok();
        if digest.is_none() || self.disk_digest != digest {
            self.supervisor.filesystem_changed();
            self.disk_digest = digest;
        }
    }
}

enum QueryKind {
    Hover,
    Definition,
    Completion,
}

struct EditorQuery {
    kind: QueryKind,
    id: RequestId,
    path: PathBuf,
    position: lsp_types::Position,
    workspace_instance: u64,
    workspace_revision: u64,
    deadline: Instant,
}

impl Server {
    fn is_installed_std(&self, path: &Path) -> bool {
        self.installed_std
            .as_ref()
            .is_some_and(|root| path.starts_with(root))
    }

    fn add_workspace(&mut self, uri: &Uri) {
        let Some(path) = file_path(uri).filter(|path| !self.is_installed_std(path)) else {
            return;
        };
        self.workspaces
            .entry(path.clone())
            .or_insert_with(|| Supervisor::new(path, self.launch.clone(), Policy::default()));
    }

    fn lookup(&mut self, path: &Path) -> Option<&mut Supervisor> {
        if self.is_installed_std(path) {
            return self
                .std_workspace
                .as_mut()
                .filter(|workspace| workspace.idle_until.is_none())
                .map(|workspace| &mut workspace.supervisor);
        }
        let root = self
            .workspaces
            .keys()
            .filter(|root| path.starts_with(root))
            .max_by_key(|root| root.components().count())?;
        let root = root.clone();
        self.workspaces.get_mut(&root)
    }

    fn event_loop(&mut self, connection: &Connection) -> Result<()> {
        loop {
            match connection.receiver.recv_timeout(Duration::from_millis(10)) {
                Ok(Message::Request(request)) => {
                    if connection.handle_shutdown(&request)? {
                        return Ok(());
                    }
                    self.request(connection, request)?;
                }
                Ok(Message::Notification(note)) => {
                    if note.method == notification::Exit::METHOD {
                        return Err("client exited before shutdown".into());
                    }
                    if note.method == "$/cancelRequest" {
                        self.cancel_request(connection, note)?;
                    } else if let Err(error) = self.notification(connection, note) {
                        log_warning(connection, error.to_string())?;
                    }
                }
                Ok(Message::Response(response)) => {
                    if response.id == RequestId::from(FILE_WATCH_REGISTRATION.to_owned()) {
                        match response.response_result {
                            Ok(_) => self.watching_files = true,
                            Err(error) => log_warning(
                                connection,
                                format!("could not register file watchers: {}", error.message),
                            )?,
                        }
                    }
                }
                Err(RecvTimeoutError::Timeout) => {}
                Err(RecvTimeoutError::Disconnected) => return Ok(()),
            }
            let now = Instant::now();
            if self
                .std_workspace
                .as_ref()
                .and_then(|workspace| workspace.idle_until)
                .is_some_and(|deadline| now >= deadline)
            {
                self.std_workspace = None;
            }
            let active_std = self
                .std_workspace
                .iter_mut()
                .filter(|workspace| workspace.idle_until.is_none())
                .map(|workspace| &mut workspace.supervisor);
            for supervisor in self.workspaces.values_mut().chain(active_std) {
                match supervisor.drive(now) {
                    Some(Notice::Current(mode, product)) => {
                        let diagnostics = features::diagnostics(supervisor, &product);
                        publish(
                            connection,
                            supervisor,
                            diagnostics,
                            self.trace_analysis.then_some(mode),
                        )?;
                        for diagnostic in product
                            .diagnostics
                            .iter()
                            .filter(|diagnostic| diagnostic.source.is_none())
                        {
                            log_warning(connection, diagnostic.message.clone())?;
                        }
                        supervisor.install(product);
                    }
                    Some(Notice::Unavailable(error)) => {
                        publish(connection, supervisor, BTreeMap::new(), None)?;
                        log_warning(connection, error)?;
                    }
                    None => {}
                }
            }
            for query in std::mem::take(&mut self.waiting) {
                if !self.answer(connection, &query, now)? {
                    self.waiting.push(query);
                }
            }
        }
    }

    fn request(&mut self, connection: &Connection, request: Request) -> Result<()> {
        let decoded = match request.method.as_str() {
            request::HoverRequest::METHOD => serde_json::from_value::<HoverParams>(request.params)
                .map(|params| (QueryKind::Hover, params.text_document_position_params)),
            request::GotoDefinition::METHOD => {
                serde_json::from_value::<GotoDefinitionParams>(request.params)
                    .map(|params| (QueryKind::Definition, params.text_document_position_params))
            }
            request::Completion::METHOD => {
                serde_json::from_value::<CompletionParams>(request.params)
                    .map(|params| (QueryKind::Completion, params.text_document_position))
            }
            _ => {
                return send_error(
                    connection,
                    request.id,
                    ErrorCode::MethodNotFound,
                    "unsupported request",
                );
            }
        };
        let (
            kind,
            TextDocumentPositionParams {
                text_document,
                position,
            },
        ) = match decoded {
            Ok(decoded) => decoded,
            Err(error) => {
                return send_error(
                    connection,
                    request.id,
                    ErrorCode::InvalidParams,
                    &error.to_string(),
                );
            }
        };
        let Some(path) = file_path(&text_document.uri) else {
            return send_value(connection, request.id, Value::Null);
        };
        let Some((workspace_instance, workspace_revision)) = self
            .lookup(&path)
            .map(|workspace| (workspace.instance(), workspace.revision()))
        else {
            return send_value(connection, request.id, Value::Null);
        };
        let now = Instant::now();
        // The first request from an SDK file may wait for a full source check.
        let timeout = if self.is_installed_std(&path) {
            Policy::default().timeout
        } else {
            REQUEST_TIMEOUT
        };
        let query = EditorQuery {
            kind,
            id: request.id,
            path,
            position,
            workspace_instance,
            workspace_revision,
            deadline: now + timeout,
        };
        if !self.answer(connection, &query, now)? {
            if self.waiting.len() == MAX_WAITING_REQUESTS {
                return send_error(
                    connection,
                    query.id,
                    ErrorCode::ServerCancelled,
                    "too many pending analysis requests",
                );
            }
            self.waiting.push(query);
        }
        Ok(())
    }

    fn answer(
        &mut self,
        connection: &Connection,
        query: &EditorQuery,
        now: Instant,
    ) -> Result<bool> {
        let Some(workspace) = self.lookup(&query.path) else {
            send_value(connection, query.id.clone(), Value::Null)?;
            return Ok(true);
        };
        if workspace.instance() != query.workspace_instance
            || workspace.revision() != query.workspace_revision
        {
            send_error(
                connection,
                query.id.clone(),
                ErrorCode::ContentModified,
                "source changed during analysis",
            )?;
            return Ok(true);
        }
        if workspace.current().is_none() {
            if now < query.deadline {
                return Ok(false);
            }
            send_error(
                connection,
                query.id.clone(),
                ErrorCode::ServerCancelled,
                "current analysis is unavailable",
            )?;
            return Ok(true);
        }
        let value = match query.kind {
            QueryKind::Hover => {
                serde_json::to_value(features::hover(workspace, &query.path, query.position))?
            }
            QueryKind::Definition => {
                serde_json::to_value(features::definition(workspace, &query.path, query.position))?
            }
            QueryKind::Completion => serde_json::to_value(features::completions(
                workspace,
                &query.path,
                query.position,
            ))?,
        };
        send_value(connection, query.id.clone(), value)?;
        Ok(true)
    }

    fn cancel_request(&mut self, connection: &Connection, note: Notification) -> Result<()> {
        if let Some(id) = note.params.get("id")
            && let Ok(id) = serde_json::from_value::<RequestId>(id.clone())
            && let Some(index) = self.waiting.iter().position(|query| query.id == id)
        {
            self.waiting.swap_remove(index);
            send_error(
                connection,
                id,
                ErrorCode::RequestCanceled,
                "request cancelled",
            )?;
        }
        Ok(())
    }

    fn notification(&mut self, connection: &Connection, note: Notification) -> Result<()> {
        match note.method.as_str() {
            notification::DidOpenTextDocument::METHOD => {
                let params: DidOpenTextDocumentParams = serde_json::from_value(note.params)?;
                let doc = params.text_document;
                if let Some(path) = file_path(&doc.uri).filter(|path| is_taro_source(path)) {
                    if let Some(root) = self
                        .installed_std
                        .as_ref()
                        .filter(|root| path.starts_with(root))
                    {
                        let workspace = self.std_workspace.get_or_insert_with(|| StdWorkspace {
                            supervisor: Supervisor::new(
                                root.clone(),
                                self.launch.clone(),
                                Policy::default(),
                            ),
                            disk_digest: None,
                            idle_until: None,
                        });
                        workspace.idle_until = None;
                        workspace.refresh_disk_view(root);
                        let supervisor = &mut workspace.supervisor;
                        if workspace.disk_digest.is_some()
                            && fs::read_to_string(&path).is_ok_and(|disk| disk == doc.text)
                        {
                            supervisor.open_disk_document(path.clone(), doc.version, doc.text);
                        } else {
                            supervisor.set_document(path.clone(), doc.version, doc.text);
                        }
                        supervisor.set_document_uri(&path, doc.uri);
                        if let Some(product) = supervisor.current() {
                            let diagnostics = features::diagnostics(supervisor, product);
                            publish(connection, supervisor, diagnostics, None)?;
                        }
                    } else {
                        if self.lookup(&path).is_none() {
                            self.workspaces.insert(
                                path.clone(),
                                Supervisor::new(
                                    path.clone(),
                                    self.launch.clone(),
                                    Policy::default(),
                                ),
                            );
                        }
                        if let Some(supervisor) = self.lookup(&path) {
                            supervisor.set_document(path.clone(), doc.version, doc.text);
                            supervisor.set_document_uri(&path, doc.uri);
                        }
                    }
                }
            }
            notification::DidChangeTextDocument::METHOD => {
                let params: DidChangeTextDocumentParams = serde_json::from_value(note.params)?;
                let doc = params.text_document;
                let refresh_disk = !self.watching_files;
                if params
                    .content_changes
                    .iter()
                    .any(|change| change.range.is_some())
                {
                    return Err("client sent a ranged edit in full-text sync mode".into());
                }
                if let Some(path) = file_path(&doc.uri)
                    && let Some(supervisor) = self.lookup(&path)
                    && let Some(change) = params.content_changes.into_iter().last()
                    && supervisor.set_document(path, doc.version, change.text)
                    && refresh_disk
                {
                    supervisor.discard_disk_view();
                }
            }
            notification::DidCloseTextDocument::METHOD => {
                let params: DidCloseTextDocumentParams = serde_json::from_value(note.params)?;
                if let Some(path) = file_path(&params.text_document.uri) {
                    if let Some(root) = self
                        .installed_std
                        .as_ref()
                        .filter(|root| path.starts_with(root))
                    {
                        if let Some(workspace) = &mut self.std_workspace
                            && workspace.supervisor.close_document(&path)
                        {
                            workspace.refresh_disk_view(root);
                            let supervisor = &mut workspace.supervisor;
                            if supervisor.open_document_uris().next().is_none() {
                                // A preview tab can close just before the next one opens.
                                workspace.idle_until = Some(Instant::now() + STD_IDLE_TIMEOUT);
                                publish(connection, supervisor, BTreeMap::new(), None)?;
                            } else if let Some(product) = supervisor.current() {
                                let diagnostics = features::diagnostics(supervisor, product);
                                publish(connection, supervisor, diagnostics, None)?;
                            }
                        }
                    } else if self.workspaces.remove(&path).is_none()
                        && let Some(supervisor) = self.lookup(&path)
                    {
                        supervisor.close_document(&path);
                    }
                }
            }
            notification::DidChangeWatchedFiles::METHOD => {
                let params: DidChangeWatchedFilesParams = serde_json::from_value(note.params)?;
                for change in params.changes {
                    let Some(path) = file_path(&change.uri) else {
                        continue;
                    };
                    let supervisor = if self.is_installed_std(&path) {
                        self.std_workspace
                            .as_mut()
                            .map(|workspace| &mut workspace.supervisor)
                    } else {
                        self.lookup(&path)
                    };
                    if let Some(supervisor) = supervisor {
                        supervisor.filesystem_changed();
                    }
                }
            }
            notification::DidChangeWorkspaceFolders::METHOD => {
                let params: DidChangeWorkspaceFoldersParams = serde_json::from_value(note.params)?;
                for folder in params.event.removed {
                    if let Some(path) = file_path(&folder.uri) {
                        self.workspaces.remove(&path);
                    }
                }
                for folder in params.event.added {
                    self.add_workspace(&folder.uri);
                }
            }
            _ => {}
        }
        Ok(())
    }
}

fn register_watchers(connection: &Connection) -> Result<()> {
    let watchers =
        ["**/*.tr", "**/package.toml", "**/package.lock"].map(|glob| FileSystemWatcher {
            glob_pattern: glob.to_owned().into(),
            kind: None,
        });
    let options = DidChangeWatchedFilesRegistrationOptions {
        watchers: watchers.into(),
    };
    let params = RegistrationParams {
        registrations: vec![Registration {
            id: FILE_WATCH_REGISTRATION.into(),
            method: notification::DidChangeWatchedFiles::METHOD.into(),
            register_options: Some(serde_json::to_value(options)?),
        }],
    };
    connection.sender.send(
        Request::new(
            FILE_WATCH_REGISTRATION.to_owned().into(),
            request::RegisterCapability::METHOD.into(),
            params,
        )
        .into(),
    )?;
    Ok(())
}

fn is_taro_source(path: &Path) -> bool {
    path.extension().is_some_and(|extension| extension == "tr")
}

fn file_path(uri: &Uri) -> Option<PathBuf> {
    let path = Url::parse(uri.as_str()).ok()?.to_file_path().ok()?;
    canonical_source_path(&path).ok()
}

fn publish(
    connection: &Connection,
    workspace: &mut Supervisor,
    mut diagnostics: BTreeMap<Uri, Vec<lsp_types::Diagnostic>>,
    trace: Option<AnalysisMode>,
) -> Result<()> {
    for uri in workspace.open_document_uris() {
        diagnostics.entry(uri).or_default();
    }
    // Only a document that had diagnostics needs a clearing notification.
    let previous = workspace.swap_published(
        diagnostics
            .iter()
            .filter(|(_, items)| !items.is_empty())
            .map(|(uri, _)| uri.clone())
            .collect(),
    );
    for uri in previous {
        diagnostics.entry(uri).or_default();
    }
    for (uri, diagnostics) in diagnostics {
        let version = file_path(&uri).and_then(|path| workspace.document_version(&path));
        if let (Some(version), Some(mode)) = (version, &trace) {
            eprintln!("taro-lsp analysis {version} {mode:?} {}", uri.as_str());
        }
        let payload = PublishDiagnosticsParams::new(uri, diagnostics, version);
        connection.sender.send(
            Notification::new(notification::PublishDiagnostics::METHOD.into(), payload).into(),
        )?;
    }
    Ok(())
}

fn send_value(connection: &Connection, id: RequestId, value: Value) -> Result<()> {
    connection.sender.send(Response::new_ok(id, value).into())?;
    Ok(())
}

fn send_error(
    connection: &Connection,
    id: RequestId,
    code: ErrorCode,
    message: &str,
) -> Result<()> {
    connection
        .sender
        .send(Response::new_err(id, code as i32, message.into()).into())?;
    Ok(())
}

fn log_warning(connection: &Connection, message: String) -> Result<()> {
    let params = lsp_types::LogMessageParams {
        typ: MessageType::WARNING,
        message,
    };
    connection
        .sender
        .send(Notification::new(notification::LogMessage::METHOD.into(), params).into())?;
    Ok(())
}
