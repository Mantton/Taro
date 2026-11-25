//! Disposable compiler sessions used by the private worker process.

use std::{
    collections::BTreeMap,
    io::{self, BufReader, BufWriter},
    path::{Path, PathBuf},
    rc::Rc,
    sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    },
    thread,
};

use compiler::{
    PackageIndex,
    compile::{
        Compiler,
        analysis_products::AnalysisProduct,
        config::{Config, PackageKind, StdMode},
        context::{CompilerArenas, CompilerContext, CompilerStore},
        source::{FileContents, FileOverlay, SourceText, WorkspaceSources},
        target_facts::TargetFacts,
    },
    diagnostics::{DiagCtx, run_cancellable},
};
use crossbeam_channel::bounded;

use crate::protocol::{self, AnalysisRequest, FromWorker, Inputs, Stamp, ToWorker};

pub fn run(target: TargetFacts) -> io::Result<()> {
    let (requests, incoming) = bounded(1);
    let cancelled = Arc::new(AtomicU64::new(0));
    let reader_cancellation = Arc::clone(&cancelled);
    thread::spawn(move || {
        let mut input = BufReader::new(io::stdin().lock());
        loop {
            match protocol::read(&mut input) {
                Ok(Some(ToWorker::Analyze(request))) => {
                    if requests.send(Ok(request)).is_err() {
                        break;
                    }
                }
                Ok(Some(ToWorker::Cancel { revision })) => {
                    reader_cancellation.fetch_max(revision, Ordering::Release);
                }
                Ok(None) => break,
                Err(error) => {
                    let _ = requests.send(Err(error));
                    break;
                }
            }
        }
        reader_cancellation.store(u64::MAX, Ordering::Release);
    });
    let mut output = BufWriter::new(io::stdout().lock());
    let mut workspace = Workspace::default();
    for request in incoming {
        let AnalysisRequest { stamp, inputs } = request?;
        let result = workspace.update(stamp, inputs).and_then(|()| {
            if is_cancelled(&cancelled, stamp.revision) {
                return Ok(None);
            }
            workspace.analyze(stamp.revision, &target, Arc::clone(&cancelled))
        });
        let reply = if is_cancelled(&cancelled, stamp.revision) {
            FromWorker::Cancelled(stamp)
        } else {
            match result {
                Ok(Some(result)) => FromWorker::Finished {
                    stamp,
                    result: Ok(Box::new(result)),
                },
                Ok(None) => FromWorker::Cancelled(stamp),
                Err(error) => FromWorker::Finished {
                    stamp,
                    result: Err(error.to_string()),
                },
            }
        };
        protocol::write(&mut output, &reply)?;
    }
    Ok(())
}

fn is_cancelled(cancelled: &AtomicU64, revision: u64) -> bool {
    cancelled.load(Ordering::Acquire) >= revision
}

#[derive(Default)]
struct Workspace {
    stamp: Option<Stamp>,
    root: PathBuf,
    documents: BTreeMap<PathBuf, Arc<SourceText>>,
    sources: Option<Rc<WorkspaceSources>>,
}

impl Workspace {
    fn update(&mut self, stamp: Stamp, inputs: Inputs) -> io::Result<()> {
        if self.stamp.is_some_and(|previous| {
            previous.generation != stamp.generation || previous.revision >= stamp.revision
        }) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "stale worker request",
            ));
        }
        match inputs {
            Inputs::Reset { root, documents } => {
                for path in documents.keys() {
                    validate_path(&root, path)?;
                }
                self.root = root;
                self.documents = documents
                    .into_iter()
                    .map(|(path, text)| (path, Arc::new(SourceText::new(text))))
                    .collect();
                self.sources = None;
            }
            Inputs::Delta(edits) => {
                if self.stamp.is_none() || edits.is_empty() {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "worker delta without a base",
                    ));
                }
                for path in edits.keys() {
                    validate_path(&self.root, path)?;
                }
                let single_file = edits.len() == 1;
                for (path, contents) in edits {
                    let reusable =
                        match contents {
                            Some(text) => {
                                let source = Arc::new(SourceText::new(text));
                                let was_open = self
                                    .documents
                                    .insert(path.clone(), Arc::clone(&source))
                                    .is_some();
                                single_file
                                    && was_open
                                    && self.sources.as_mut().and_then(Rc::get_mut).is_some_and(
                                        |view| {
                                            view.replace_open_text(stamp.revision, &path, source)
                                                .is_ok()
                                        },
                                    )
                            }
                            None => {
                                self.documents.remove(&path);
                                false
                            }
                        };
                    if !reusable {
                        self.sources = None;
                    }
                }
            }
        }
        self.stamp = Some(stamp);
        Ok(())
    }

    fn analyze(
        &mut self,
        revision: u64,
        target: &TargetFacts,
        cancelled: Arc<AtomicU64>,
    ) -> io::Result<Option<AnalysisProduct>> {
        if self.sources.is_none() {
            let buffers = self.documents.iter().map(|(path, text)| {
                (
                    path.clone(),
                    FileOverlay::Contents(FileContents::Text(Arc::clone(text))),
                )
            });
            self.sources = Some(Rc::new(WorkspaceSources::new(revision, buffers)?));
        }
        let sources = self.sources.as_ref().unwrap().clone();
        Ok(run_cancellable(|| {
            let arenas = CompilerArenas::new();
            let dcx = Rc::new(
                DiagCtx::with_sources(self.root.clone(), sources)
                    .with_cancellation(move || is_cancelled(&cancelled, revision)),
            );
            let store =
                CompilerStore::new_for_analysis(&arenas, self.root.join("target"), target.clone());
            let context = CompilerContext::new(dcx, store);
            let config = package_config(&self.root);
            Compiler::new(&context, &config).analyze_partial_owned(revision)
        }))
    }
}

fn validate_path(root: &Path, path: &Path) -> io::Result<()> {
    if root.is_absolute()
        && path.is_absolute()
        && path.starts_with(root)
        && path.extension().is_some_and(|extension| extension == "tr")
        && !path
            .components()
            .any(|part| part == std::path::Component::ParentDir)
    {
        Ok(())
    } else {
        Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "source is outside its workspace",
        ))
    }
}

fn package_config(root: &Path) -> Config {
    let name = root
        .file_stem()
        .and_then(|name| name.to_str())
        .unwrap_or("workspace");
    Config {
        name: name.into(),
        identifier: name.into(),
        src: root.to_path_buf(),
        dependencies: Default::default(),
        index: PackageIndex::new(1),
        kind: PackageKind::Library,
        executable_out: None,
        no_std_prelude: true,
        is_script: root.extension().is_some_and(|extension| extension == "tr"),
        profile: Default::default(),
        codegen: Default::default(),
        overflow_checks: true,
        debug: Default::default(),
        harness_mode: Default::default(),
        std_mode: StdMode::BootstrapStd,
        is_std_provider: false,
        lint_warnings: true,
    }
}
