//! Compare the full package path with the compiler's closed-body projection.

#[allow(dead_code)]
#[path = "../src/bundle.rs"]
mod bundle;
#[path = "../src/project.rs"]
mod project;
#[allow(dead_code)]
#[path = "../src/sdk.rs"]
mod sdk;
#[path = "../src/standard_library.rs"]
mod standard_library;

use std::{
    fs, io,
    path::Path,
    rc::Rc,
    sync::Arc,
    time::{Duration, Instant},
};

use bundle::Bundle;
use compiler::{
    compile::{
        Compiler,
        context::{CompilerArenas, CompilerContext, CompilerStore},
        source::{FileContents, FileOverlay, SourceText, WorkspaceSources},
        target_facts::TargetFacts,
    },
    diagnostics::DiagCtx,
    span::Position,
};
use project::Project;
use serde_json::json;
use standard_library::{Installation, Prepared, StdCache};

fn with_compiler<R>(
    root: &Path,
    rev_sources: Rc<WorkspaceSources>,
    target: &TargetFacts,
    prepared: Option<&Prepared>,
    f: impl for<'ctx> FnOnce(&mut Compiler<'ctx>) -> R,
) -> io::Result<(R, Duration, Duration)> {
    let started = Instant::now();
    let project = Project::read(root, &*rev_sources, prepared.is_some())?;
    let arenas = CompilerArenas::new();
    let dcx = Rc::new(DiagCtx::with_sources(root.into(), rev_sources));
    let store = CompilerStore::new_for_analysis(&arenas, root.join("target"), target.clone());
    let context = CompilerContext::new(dcx, store);
    let setup = started.elapsed();
    let now = Instant::now();
    if let Some(prepared) = prepared {
        prepared.hydrate(&context)?;
    }
    let hydrate = now.elapsed();
    Ok((
        f(&mut Compiler::new(&context, &project.config)),
        setup,
        hydrate,
    ))
}

fn overlay(text: String) -> FileOverlay {
    FileOverlay::Contents(FileContents::Text(Arc::new(SourceText::new(text))))
}

fn millis(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1_000.0
}

fn p95(samples: &mut [f64]) -> f64 {
    samples.sort_by(f64::total_cmp);
    samples[(samples.len() * 95).div_ceil(100) - 1]
}

fn series(root: &Path, target: &TargetFacts, unrelated: usize) -> io::Result<serde_json::Value> {
    let edit_path = root.join("src/focus.tr");
    let text = |revision| {
        format!(
            "private func focus(_ seed: int32) -> int32 {{\n    value{revision} := seed\n    value{revision}\n}}"
        )
    };
    let overlays =
        std::iter::once((edit_path.clone(), overlay(text(1)))).chain((0..unrelated).map(|index| {
            (
                root.join(format!("src/sibling{index:04}.tr")),
                overlay(format!("private func other{index}() -> int32 {{ 1 }}")),
            )
        }));
    let mut sources = Rc::new(WorkspaceSources::new(1, overlays)?);
    let (eager, _, _) = with_compiler(root, sources.clone(), target, None, |compiler| {
        compiler.analyze_owned(1)
    })?;
    let (prepared, _, _) = with_compiler(root, sources.clone(), target, None, |compiler| {
        compiler.prepare_closed_body_edit(&edit_path, Position::default(), &eager)
    })?;
    let mut prepared = prepared.expect("projected body eligibility");
    let mut eager_ms = Vec::new();
    let mut current_ms = Vec::new();
    for revision in 2..=33 {
        Rc::get_mut(&mut sources).unwrap().replace_open_text(
            revision,
            &edit_path,
            Arc::new(SourceText::new(text(revision))),
        )?;
        let now = Instant::now();
        let (body, _, _) = with_compiler(root, sources.clone(), target, None, |compiler| {
            compiler.check_closed_body_edit(&mut prepared)
        })?;
        let body = body.expect("warm projected check");
        current_ms.push(millis(now.elapsed()));
        let now = Instant::now();
        let (eager, _, _) = with_compiler(root, sources.clone(), target, None, |compiler| {
            compiler.analyze_owned(revision)
        })?;
        eager_ms.push(millis(now.elapsed()));
        assert!(eager.complete);
        let expected = eager
            .occurrences
            .into_iter()
            .filter(|fact| fact.source.path == body.scope.path)
            .collect::<Vec<_>>();
        assert_eq!(expected, body.occurrences);
    }
    Ok(json!({
        "unrelated_functions": unrelated,
        "samples": current_ms.len(),
        "full_p95_ms": p95(&mut eager_ms),
        "closed_body_p95_ms": p95(&mut current_ms),
    }))
}

fn iris(root: &Path, installation: &Installation) -> io::Result<serde_json::Value> {
    let path = root.join("src/main.tr");
    let source = fs::read_to_string(&path)?;
    let line = source
        .lines()
        .position(|line| line.starts_with("func encodeDouble"))
        .unwrap();
    let revision = 1;
    let sources = Rc::new(WorkspaceSources::new(
        revision,
        [(path.clone(), overlay(source))],
    )?);
    let project = Project::read(root, &*sources, true)?;
    let target = installation.target(project.prefs.target.as_deref())?;
    let mut cache = StdCache::default();
    let prepared = cache.prepare(
        installation,
        &target,
        project.prefs.std_digest.as_deref(),
        || false,
    )?;
    let mut hydrate_ms = Vec::new();
    let mut analysis_ms = Vec::new();
    let mut semantic_ms = Vec::new();
    let mut selected_body_ms = Vec::new();
    let mut selected_body_fallback = None;
    let mut setup_ms = Vec::new();
    let mut result = None;
    let position = Position { line, offset: 0 };
    for _ in 0..16 {
        let ((product, measured), setup, hydrate) =
            with_compiler(root, sources.clone(), &target, Some(prepared), |compiler| {
                let now = Instant::now();
                (compiler.analyze_owned(revision), now.elapsed())
            })?;
        assert!(product.complete, "{:?}", product.diagnostics);
        result = Some(product);
        hydrate_ms.push(millis(hydrate));
        setup_ms.push(millis(setup));
        analysis_ms.push(millis(measured));
        let (semantic, _, _) =
            with_compiler(root, sources.clone(), &target, Some(prepared), |compiler| {
                let now = Instant::now();
                assert!(compiler.analyze().is_ok());
                now.elapsed()
            })?;
        semantic_ms.push(millis(semantic));
        let ((selected, duration), _, _) =
            with_compiler(root, sources.clone(), &target, Some(prepared), |compiler| {
                let now = Instant::now();
                let result = compiler.check_body_owned(&path, position, None);
                (result, now.elapsed())
            })?;
        match selected {
            Ok(_) => selected_body_ms.push(millis(duration)),
            Err(reason) => selected_body_fallback = Some(format!("{reason:?}")),
        }
    }
    let result = result.unwrap();
    let (candidate, _, _) = with_compiler(root, sources, &target, Some(prepared), |compiler| {
        compiler.prepare_closed_body_edit(&path, position, &result)
    })?;
    Ok(json!({
        "target": target.triple(),
        "samples": analysis_ms.len(),
        "setup_p95_ms": p95(&mut setup_ms),
        "hydrate_std_p95_ms": p95(&mut hydrate_ms),
        "semantic_check_p95_ms": p95(&mut semantic_ms),
        "package_analysis_p95_ms": p95(&mut analysis_ms),
        "selected_body_samples": selected_body_ms.len(),
        "selected_body_p95_ms": (!selected_body_ms.is_empty()).then(|| p95(&mut selected_body_ms)),
        "selected_body_fallback": selected_body_fallback,
        "projection": candidate.err().map_or_else(|| "eligible".into(), |fallback| format!("{fallback:?}")),
    }))
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let [target, scratch, iris_root, bundle_root] = std::env::args_os()
        .skip(1)
        .collect::<Vec<_>>()
        .try_into()
        .map_err(
            |_| "pass a target descriptor, empty scratch directory, Iris root and bundle directory",
        )?;
    let facts: TargetFacts = toml::from_str(&fs::read_to_string(target)?)?;
    let scratch = Path::new(&scratch).canonicalize()?;
    let iris_root = Path::new(&iris_root).canonicalize()?;
    let bundle = Installation::Portable(Bundle::load(Path::new(&bundle_root))?);
    let generated = [10, 100, 1_000]
        .into_iter()
        .map(|size| series(&scratch, &facts, size))
        .collect::<io::Result<Vec<_>>>()?;
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "generated": generated,
            "iris": iris(&iris_root, &bundle)?,
        }))?
    );
    Ok(())
}
