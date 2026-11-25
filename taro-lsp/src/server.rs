//! LSP transport and synchronization of current editor text.

use std::{
    collections::BTreeMap,
    error::Error,
    path::{Path, PathBuf},
    time::{Duration, Instant},
};

use crossbeam_channel::RecvTimeoutError;
use lsp_server::{Connection, Message, Notification, Response};
use lsp_types::{
    DidChangeTextDocumentParams, DidChangeWatchedFilesParams, DidChangeWorkspaceFoldersParams,
    DidCloseTextDocumentParams, DidOpenTextDocumentParams, InitializeParams, MessageType,
    ServerCapabilities, TextDocumentSyncCapability, TextDocumentSyncKind, TextDocumentSyncOptions,
    Uri, WorkspaceFoldersServerCapabilities, WorkspaceServerCapabilities,
    notification::{self, Notification as _},
};
use url::Url;

use crate::supervisor::{Launch, Notice, Policy, Supervisor};

type Result<T> = std::result::Result<T, Box<dyn Error + Send + Sync>>;

pub fn run(launch: Launch) -> Result<()> {
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
    let mut server = Server {
        launch,
        workspaces: BTreeMap::new(),
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
    workspaces: BTreeMap<PathBuf, Supervisor>,
}

impl Server {
    fn add_workspace(&mut self, uri: &Uri) {
        let Some(path) = file_path(uri) else { return };
        self.workspaces
            .entry(path.clone())
            .or_insert_with(|| Supervisor::new(path, self.launch.clone(), Policy::default()));
    }

    fn lookup(&mut self, path: &Path) -> Option<&mut Supervisor> {
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
                    connection.sender.send(
                        Response::new_err(
                            request.id,
                            lsp_server::ErrorCode::MethodNotFound as i32,
                            format!("unknown method {}", request.method),
                        )
                        .into(),
                    )?;
                }
                Ok(Message::Notification(note)) => {
                    if note.method == notification::Exit::METHOD {
                        return Err("client exited before shutdown".into());
                    }
                    if let Err(error) = self.notification(note) {
                        log_warning(connection, error.to_string())?;
                    }
                }
                Ok(Message::Response(_)) | Err(RecvTimeoutError::Timeout) => {}
                Err(RecvTimeoutError::Disconnected) => return Ok(()),
            }
            let now = Instant::now();
            for supervisor in self.workspaces.values_mut() {
                match supervisor.drive(now) {
                    Some(Notice::Current(product)) => {
                        debug_assert_eq!(product.revision, supervisor.revision());
                    }
                    Some(Notice::Unavailable(error)) => log_warning(connection, error)?,
                    None => {}
                }
            }
        }
    }

    fn notification(&mut self, note: Notification) -> Result<()> {
        match note.method.as_str() {
            notification::DidOpenTextDocument::METHOD => {
                let params: DidOpenTextDocumentParams = serde_json::from_value(note.params)?;
                let doc = params.text_document;
                if let Some(path) = file_path(&doc.uri).filter(|path| is_taro_source(path)) {
                    if self.lookup(&path).is_none() {
                        self.workspaces.insert(
                            path.clone(),
                            Supervisor::new(path.clone(), self.launch.clone(), Policy::default()),
                        );
                    }
                    if let Some(supervisor) = self.lookup(&path) {
                        supervisor.set_document(path, doc.version, doc.text);
                    }
                }
            }
            notification::DidChangeTextDocument::METHOD => {
                let params: DidChangeTextDocumentParams = serde_json::from_value(note.params)?;
                let doc = params.text_document;
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
                {
                    supervisor.set_document(path, doc.version, change.text);
                }
            }
            notification::DidCloseTextDocument::METHOD => {
                let params: DidCloseTextDocumentParams = serde_json::from_value(note.params)?;
                if let Some(path) = file_path(&params.text_document.uri) {
                    if self.workspaces.remove(&path).is_none()
                        && let Some(supervisor) = self.lookup(&path)
                    {
                        supervisor.close_document(&path);
                    }
                }
            }
            notification::DidChangeWatchedFiles::METHOD => {
                let params: DidChangeWatchedFilesParams = serde_json::from_value(note.params)?;
                for change in params.changes {
                    if let Some(path) = file_path(&change.uri)
                        && let Some(supervisor) = self.lookup(&path)
                    {
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

fn is_taro_source(path: &Path) -> bool {
    path.extension().is_some_and(|extension| extension == "tr")
}

fn file_path(uri: &Uri) -> Option<PathBuf> {
    Url::parse(uri.as_str()).ok()?.to_file_path().ok()
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
