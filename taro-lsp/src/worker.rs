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
    compile::{
        Compiler,
        analysis_products::AnalysisProduct,
        context::{CompilerArenas, CompilerContext, CompilerStore},
        source::{FileContents, FileOverlay, SourceText, WorkspaceSources},
        target_facts::TargetFacts,
    },
    diagnostics::{DiagCtx, run_cancellable},
};
use crossbeam_channel::bounded;

use crate::{
    bundle::Bundle,
    project::Project,
    protocol::{self, AnalysisRequest, FromWorker, Inputs, Stamp, ToWorker},
    standard_library::StdCache,
};

pub enum Environment {
    Bootstrap(TargetFacts),
    Installed(Bundle),
}

pub fn run(environment: Environment) -> io::Result<()> {
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
            workspace.analyze(stamp.revision, &environment, Arc::clone(&cancelled))
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
    std_cache: StdCache,
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
                self.std_cache = StdCache::default();
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
        environment: &Environment,
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
        let project = Project::read(
            &self.root,
            sources.as_ref(),
            matches!(environment, Environment::Installed(_)),
        )?;
        run_cancellable(|| {
            let (target, prepared_std) = match environment {
                Environment::Bootstrap(target) => {
                    if project
                        .prefs
                        .target
                        .as_deref()
                        .is_some_and(|requested| requested != target.triple())
                    {
                        return Err(io::Error::other(
                            "the project requests an unavailable analysis target",
                        ));
                    }
                    (target.clone(), None)
                }
                Environment::Installed(bundle) => {
                    let target = bundle.target(project.prefs.target.as_deref())?;
                    let cancel_std = Arc::clone(&cancelled);
                    let prepared = self.std_cache.prepare(
                        bundle,
                        &target,
                        project.prefs.std_digest.as_deref(),
                        Rc::clone(&sources),
                        move || is_cancelled(&cancel_std, revision),
                    )?;
                    (target, Some(prepared))
                }
            };
            let arenas = CompilerArenas::new();
            let dcx = Rc::new(
                DiagCtx::with_sources(self.root.clone(), sources)
                    .with_cancellation(move || is_cancelled(&cancelled, revision)),
            );
            let store = CompilerStore::new_for_analysis(&arenas, self.root.join("target"), target);
            let context = CompilerContext::new(dcx, store);
            if let Some(std) = prepared_std {
                std.hydrate(&context)?;
            }
            Ok(Compiler::new(&context, &project.config).analyze_partial_owned(revision))
        })
        .transpose()
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
