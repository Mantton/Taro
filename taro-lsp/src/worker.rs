//! Disposable compiler sessions used by the private worker process.

use std::{
    collections::BTreeMap,
    io::{self, BufReader, BufWriter},
    panic::{self, AssertUnwindSafe},
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
        analysis_products::{AnalysisProduct, SourceRange, SyntaxUncertainty},
        body_check::BodyProduct,
        config::Config,
        context::{CompilerArenas, CompilerContext, CompilerStore},
        source::{FileContents, FileOverlay, SourceText, WorkspaceSources},
        target_facts::TargetFacts,
    },
    diagnostics::{DiagCtx, is_cancellation, run_cancellable},
};
use crossbeam_channel::bounded;

use crate::{
    project::Project,
    protocol::{self, AnalysisMode, AnalysisRequest, FromWorker, Inputs, Stamp, ToWorker},
    standard_library::{Installation, Prepared, StdCache, std_config},
};

pub enum Environment {
    Bootstrap(TargetFacts),
    Installed(Installation),
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
        let edit = match workspace.update(stamp, inputs) {
            Ok(edit) => edit,
            Err(error) => {
                protocol::write(
                    &mut output,
                    &FromWorker::Rejected {
                        stamp,
                        error: error.to_string(),
                    },
                )?;
                continue;
            }
        };
        let result = if is_cancelled(&cancelled, stamp.revision) {
            Ok(None)
        } else {
            workspace.analyze(stamp.revision, edit, &environment, Arc::clone(&cancelled))
        };
        let reply = if is_cancelled(&cancelled, stamp.revision) {
            FromWorker::Cancelled(stamp)
        } else {
            match result {
                Ok(Some(CheckedRevision {
                    mode,
                    product,
                    fingerprint,
                })) => {
                    let result = Arc::new(product);
                    if let Some(fingerprint) = fingerprint
                        && reusable(&result)
                    {
                        workspace.previous = Some((Arc::clone(&result), fingerprint));
                    }
                    FromWorker::Finished {
                        stamp,
                        mode,
                        result: Ok(result),
                    }
                }
                Ok(None) => FromWorker::Cancelled(stamp),
                Err(error) => FromWorker::Finished {
                    stamp,
                    mode: AnalysisMode::Package,
                    result: Err(error.to_string()),
                },
            }
        };
        protocol::write_frame(
            &mut output,
            &protocol::reply_frame(&reply, protocol::MAX_FRAME)?,
        )?;
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
    previous: Option<(Arc<AnalysisProduct>, blake3::Hash)>,
}

struct CheckedRevision {
    mode: AnalysisMode,
    product: AnalysisProduct,
    fingerprint: Option<blake3::Hash>,
}

struct Edit {
    path: PathBuf,
    before: Arc<SourceText>,
    after: Arc<SourceText>,
}

impl Workspace {
    fn update(&mut self, stamp: Stamp, inputs: Inputs) -> io::Result<Option<Edit>> {
        if self.stamp.is_some_and(|previous| {
            previous.generation != stamp.generation || previous.revision >= stamp.revision
        }) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "stale worker request",
            ));
        }
        if self.previous.as_ref().map(|(product, _)| product.revision)
            != self.stamp.map(|previous| previous.revision)
        {
            self.previous = None;
        }
        let mut edit = None;
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
                self.std_cache.invalidate_sources();
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
                    if let Some(text) = contents {
                        let after = Arc::new(SourceText::new(text));
                        let before = self.documents.insert(path.clone(), Arc::clone(&after));
                        if let Some(before) = before
                            && single_file
                            && let Some(view) = self.sources.as_mut().and_then(Rc::get_mut)
                            && view
                                .replace_open_text(stamp.revision, &path, Arc::clone(&after))
                                .is_ok()
                        {
                            edit = Some(Edit {
                                path,
                                before,
                                after,
                            });
                            continue;
                        }
                    } else {
                        self.documents.remove(&path);
                    }
                    self.sources = None;
                }
            }
        }
        self.stamp = Some(stamp);
        if edit.is_none() {
            self.previous = None;
        }
        Ok(edit)
    }

    fn analyze(
        &mut self,
        revision: u64,
        edit: Option<Edit>,
        environment: &Environment,
        cancelled: Arc<AtomicU64>,
    ) -> io::Result<Option<CheckedRevision>> {
        let previous = self.previous.take();
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
        let browsing_std = match environment {
            Environment::Installed(installation) => installation.is_std_root(&self.root)?,
            Environment::Bootstrap(_) => false,
        };
        let project = if browsing_std {
            Project {
                config: std_config(self.root.clone()),
                prefs: Default::default(),
            }
        } else {
            Project::read(
                &self.root,
                sources.as_ref(),
                matches!(environment, Environment::Installed(_)),
            )?
        };
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
                // Open SDK sources are the source package of this worker.
                // The project worker loads the installed metadata separately.
                Environment::Installed(installation) if browsing_std => {
                    installation.verify_browsing_sources()?;
                    (installation.target(None)?, None)
                }
                Environment::Installed(installation) => {
                    let target = installation.target(project.prefs.target.as_deref())?;
                    // The frozen std is independent of the editor revision.
                    // Finish a source rebuild even if the user keeps typing.
                    let shutdown = Arc::clone(&cancelled);
                    let prepared = self.std_cache.prepare(
                        installation,
                        &target,
                        project.prefs.std_digest.as_deref(),
                        move || shutdown.load(Ordering::Acquire) == u64::MAX,
                    )?;
                    (target, Some(prepared))
                }
            };
            let with_compiler = AnalysisSession {
                config: &project.config,
                std: prepared_std,
                target,
                sources,
                cancelled,
                revision,
            };
            if let (Some(edit), Some((previous, fingerprint))) = (edit, previous)
                && let Ok(mut product) = Arc::try_unwrap(previous)
                && let Some(index) = edit.unchanged_body_bounds(&product)
            {
                let source = &product.bodies[index].source;
                let checked = with_compiler.run(|compiler| {
                    compiler.recheck_clean_body_owned(&source.path, source.start, fingerprint)
                })?;
                if let Ok(body) = checked
                    && replace_body(&mut product, index, body)
                {
                    product.revision = revision;
                    return Ok(CheckedRevision {
                        mode: AnalysisMode::Body,
                        product,
                        fingerprint: Some(fingerprint),
                    });
                }
            }
            let (product, fingerprint) = with_compiler.analyze_package(revision)?;
            Ok(CheckedRevision {
                mode: AnalysisMode::Package,
                product,
                fingerprint,
            })
        })
        .transpose()
    }
}

struct AnalysisSession<'a> {
    config: &'a Config,
    std: Option<&'a Prepared>,
    target: TargetFacts,
    sources: Rc<WorkspaceSources>,
    cancelled: Arc<AtomicU64>,
    revision: u64,
}

impl AnalysisSession<'_> {
    /// Check the whole package, continuing past errors so the parts that do
    /// check still answer editor queries. A compiler failure in that mode
    /// falls back to the strict check instead of taking the worker down.
    fn analyze_package(
        &self,
        revision: u64,
    ) -> io::Result<(AnalysisProduct, Option<blake3::Hash>)> {
        let full = |recover| {
            self.session(recover, |compiler| {
                compiler.analyze_partial_owned_with_fingerprint(revision)
            })
        };
        match panic::catch_unwind(AssertUnwindSafe(|| full(true))) {
            Ok(result) => result,
            Err(payload) if is_cancellation(payload.as_ref()) => panic::resume_unwind(payload),
            Err(_) => full(false),
        }
    }

    fn run<R>(&self, analyze: impl FnOnce(&mut Compiler<'_>) -> R) -> io::Result<R> {
        self.session(false, analyze)
    }

    fn session<R>(
        &self,
        recover_errors: bool,
        analyze: impl FnOnce(&mut Compiler<'_>) -> R,
    ) -> io::Result<R> {
        let arenas = CompilerArenas::new();
        let cancelled = Arc::clone(&self.cancelled);
        let revision = self.revision;
        let dcx = DiagCtx::with_sources(self.config.src.clone(), self.sources.clone())
            .with_cancellation(move || is_cancelled(&cancelled, revision));
        let dcx = Rc::new(if recover_errors {
            dcx.with_error_recovery()
        } else {
            dcx
        });
        let store = CompilerStore::new_for_analysis(
            &arenas,
            self.config.src.join("target"),
            self.target.clone(),
        );
        let context = CompilerContext::new(dcx, store);
        if let Some(std) = self.std {
            std.hydrate(&context)?;
        }
        Ok(analyze(&mut Compiler::new(&context, self.config)))
    }
}

fn reusable(product: &AnalysisProduct) -> bool {
    let AnalysisProduct {
        revision: _,
        complete,
        syntax_uncertainty,
        declarations: _,
        bodies: _,
        occurrences: _,
        missing_members,
        diagnostics,
    } = product;
    *complete
        && *syntax_uncertainty == SyntaxUncertainty::None
        && diagnostics.is_empty()
        && missing_members.is_empty()
}

impl Edit {
    fn unchanged_body_bounds(&self, analysis: &AnalysisProduct) -> Option<usize> {
        let before = self.before.text();
        let after = self.after.text();
        let difference = before
            .bytes()
            .zip(after.bytes())
            .take_while(|(a, b)| a == b)
            .count();
        if difference == before.len() && difference == after.len() {
            return None;
        }
        analysis
            .bodies
            .iter()
            .enumerate()
            .find_map(|(index, body)| {
                let range = &body.source;
                if range.path != self.path {
                    return None;
                }
                let start = self.before.byte_offset(range.start)?;
                let old_end = self.before.byte_offset(range.end)?;
                if !(start..old_end).contains(&difference) {
                    return None;
                }
                // The suffix must still begin at the same scalar position. That
                // keeps references and nested type ranges in other bodies valid.
                let new_end = self.after.byte_offset(range.end)?;
                (before[old_end..] == after[new_end..]).then_some(index)
            })
    }
}

fn replace_body(analysis: &mut AnalysisProduct, index: usize, checked: BodyProduct) -> bool {
    let BodyProduct {
        package_fingerprint: _,
        declaration,
        body,
        scope,
        occurrences,
        diagnostics,
    } = checked;
    let previous = &analysis.bodies[index];
    let inside = |range: &SourceRange| {
        range.path == scope.path && scope.start <= range.start && range.end <= scope.end
    };
    if previous.source != body.source
        || previous.declaration != declaration.location
        || previous.identity.owner != declaration.anchor
        || !analysis.declarations.contains(&declaration)
        || !diagnostics.is_empty()
        || analysis
            .declarations
            .iter()
            .any(|entry| entry != &declaration && inside(&entry.location.source))
    {
        return false;
    }
    if analysis
        .bodies
        .iter()
        .enumerate()
        .any(|(other, body)| other != index && inside(&body.source))
    {
        return false;
    }
    // A HIR declaration is traversed in one pass. Guard this assumption so a
    // future collector that interleaves facts cannot silently drop neighbors.
    let Some(start) = analysis
        .occurrences
        .iter()
        .position(|fact| inside(&fact.source))
    else {
        return false;
    };
    let end = analysis
        .occurrences
        .iter()
        .rposition(|fact| inside(&fact.source))
        .unwrap()
        + 1;
    if analysis.occurrences[start..end]
        .iter()
        .any(|fact| !inside(&fact.source))
        || occurrences.iter().any(|fact| !inside(&fact.source))
    {
        return false;
    }
    analysis.occurrences.splice(start..end, occurrences);
    analysis.bodies[index] = body;
    true
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
