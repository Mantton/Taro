use crate::{
    PackageIndex,
    compile::{
        Compiler,
        config::{BuildProfile, Config, HarnessMode, PackageKind, StdMode},
        context::{CompilerArenas, CompilerContext, CompilerStore, Gcx},
    },
    diagnostics::{DiagCtx, DiagnosticRecord},
    hir,
};
use std::{cell::Cell, fs, path::Path, rc::Rc};

#[path = "../../test_support.rs"]
mod files;
pub(crate) use files::TempDir;

thread_local! {
    static LINT_WARNINGS: Cell<bool> = const { Cell::new(false) };
}

/// Runs `f` with advisory lint warnings enabled for the packages it compiles.
/// Other tests compile without them, so an unused local in a test program
/// does not add a diagnostic.
pub(crate) fn with_lint_warnings<R>(f: impl FnOnce() -> R) -> R {
    let previous = LINT_WARNINGS.with(|lints| lints.replace(true));
    let result = f();
    LINT_WARNINGS.with(|lints| lints.set(previous));
    result
}

fn test_config(root: &Path) -> Config {
    Config {
        name: "test".into(),
        identifier: "test".into(),
        src: root.to_path_buf(),
        dependencies: Default::default(),
        index: PackageIndex::new(1),
        kind: PackageKind::Library,
        executable_out: None,
        no_std_prelude: true,
        is_script: true,
        profile: BuildProfile::Debug,
        codegen: Default::default(),
        overflow_checks: true,
        debug: Default::default(),
        harness_mode: Default::default(),
        std_mode: StdMode::BootstrapStd,
        is_std_provider: true,
        lint_warnings: LINT_WARNINGS.with(Cell::get),
    }
}

fn with_context<R>(
    root: &Path,
    config: Config,
    f: impl for<'ctx> FnOnce(&'ctx CompilerContext<'ctx>, &'ctx Config) -> R,
) -> R {
    let dcx = Rc::new(DiagCtx::new(root.to_path_buf()));
    dcx.enable_recording();
    let arenas = CompilerArenas::new();
    let store = CompilerStore::new(&arenas, root.join("target"), &dcx, None, config.profile)
        .unwrap_or_else(|_| panic!("test compiler store"));
    let context = CompilerContext::new(dcx, store);
    let config = context.store.arenas.configs.alloc(config);
    f(&context, config)
}

pub(crate) fn with_test_gcx<R>(f: impl for<'ctx> FnOnce(Gcx<'ctx>) -> R) -> R {
    with_test_gcx_config(|_| {}, f)
}

pub(crate) fn with_test_gcx_config<R>(
    configure: impl FnOnce(&mut Config),
    f: impl for<'ctx> FnOnce(Gcx<'ctx>) -> R,
) -> R {
    let root = TempDir::new("context");
    let mut config = test_config(&root);
    configure(&mut config);
    with_context(&root, config, |context, config| {
        f(Gcx::new(context, config))
    })
}

fn with_source_compiler<R>(
    files: &[(&str, &str)],
    is_script: bool,
    harness_mode: HarnessMode,
    f: impl for<'ctx> FnOnce(&mut Compiler<'ctx>) -> R,
) -> R {
    let root = TempDir::new("analysis");
    let mut config = test_config(&root);
    config.name = if is_script { "script" } else { "package" }.into();
    config.identifier = config.name.clone();
    config.is_script = is_script;
    config.kind = if is_script {
        PackageKind::Executable
    } else {
        PackageKind::Library
    };
    config.src = if is_script {
        root.join("main.tr")
    } else {
        root.to_path_buf()
    };
    config.overflow_checks = false;
    config.harness_mode = harness_mode;
    config.is_std_provider = false;
    let source_root = if is_script {
        root.to_path_buf()
    } else {
        root.join("src")
    };
    for (name, source) in files {
        let path = source_root.join(name);
        fs::create_dir_all(path.parent().unwrap()).expect("source directory");
        fs::write(&path, source).expect("test source");
    }
    with_context(&root, config, |context, config| {
        f(&mut Compiler::new(context, config))
    })
}

pub(crate) fn analyze_script<R>(
    source: &str,
    f: impl for<'ctx> FnOnce(hir::Package, Gcx<'ctx>) -> R,
) -> R {
    with_source_compiler(
        &[("main.tr", source)],
        true,
        HarnessMode::None,
        |compiler| {
            let (package, _) = compiler.analyze().unwrap_or_else(|_| {
                panic!(
                    "test analysis failed: {:#?}",
                    compiler.context.dcx().take_recorded_diagnostics()
                )
            });
            f(package, compiler.context)
        },
    )
}

pub(crate) fn analyze_script_diagnostics(source: &str) -> Vec<DiagnosticRecord> {
    analyze_diagnostics(&[("main.tr", source)], true, false, HarnessMode::Test)
}

pub(crate) fn analyze_language_item_script(
    source: &str,
    build_mir: bool,
    items: &[(hir::StdItem, &str)],
) -> Vec<DiagnosticRecord> {
    with_source_compiler(
        &[("main.tr", source)],
        true,
        HarnessMode::None,
        |compiler| {
            let result = compiler.analyze_for_diagnostics_with_items(build_mir, items);
            let dcx = compiler.context.dcx();
            assert!(result.is_ok() || dcx.has_error());
            dcx.take_recorded_diagnostics()
        },
    )
}

/// Inspect canonical MIR after the real source checking/lowering pipeline.
/// The context also retains pre-inline MIR for evaluation-order regressions.
pub(crate) fn check_script<R>(
    source: &str,
    f: impl for<'ctx> FnOnce(hir::Package, Gcx<'ctx>) -> R,
) -> R {
    with_source_compiler(
        &[("main.tr", source)],
        true,
        HarnessMode::None,
        |compiler| {
            let package = compiler.check().unwrap_or_else(|_| {
                panic!(
                    "test checking failed: {:#?}",
                    compiler.context.dcx().take_recorded_diagnostics()
                )
            });
            f(package, compiler.context)
        },
    )
}

/// Inspect source-form MIR before ownership checking/lowering removes its
/// access operations. This helper does not publish unchecked canonical MIR.
pub(crate) fn analyze_script_built_mir<R>(
    source: &str,
    f: impl for<'ctx> FnOnce(Vec<crate::mir::Body<'ctx>>, Gcx<'ctx>) -> R,
) -> R {
    analyze_script_built_mir_with_items(source, &[], f)
}

/// Install only the allocation-family identities needed by a lowering fixture.
/// Source semantics are checked normally before registering these test items;
/// this does not bypass production standard-library validation.
pub(crate) fn analyze_script_built_mir_with_items<R>(
    source: &str,
    items: &[(hir::StdItem, &str)],
    f: impl for<'ctx> FnOnce(Vec<crate::mir::Body<'ctx>>, Gcx<'ctx>) -> R,
) -> R {
    with_source_compiler(
        &[("main.tr", source)],
        true,
        HarnessMode::None,
        |compiler| {
            let (package, results) = compiler.analyze().unwrap_or_else(|_| {
                panic!(
                    "source analysis: {:#?}",
                    compiler.context.dcx().take_recorded_diagnostics()
                )
            });
            if !items.is_empty() {
                let gcx = compiler.context;
                gcx.store.std_provider_index.set(Some(gcx.package_index()));
                let registry = crate::sema::std_items::StdItemRegistry::from_entries(
                    items.iter().map(|(item, name)| {
                        let declaration = package
                            .root
                            .declarations
                            .iter()
                            .find(|declaration| declaration.identifier.symbol.as_str() == *name)
                            .expect("fixture allocation-family declaration");
                        (
                            *item,
                            crate::sema::std_items::StdItemEntry {
                                def_id: declaration.id,
                                def_kind: gcx.definition_kind(declaration.id),
                                span: declaration.identifier.span,
                            },
                        )
                    }),
                );
                gcx.store
                    .std_items
                    .borrow_mut()
                    .replace((gcx.package_index(), registry));
            }
            let package = crate::thir::package::build_package(&package, compiler.context, results)
                .unwrap_or_else(|_| {
                    panic!(
                        "source THIR: {:#?}",
                        compiler.context.dcx().take_recorded_diagnostics()
                    )
                });
            let bodies = package
                .functions
                .values()
                .filter(|function| function.body.is_some())
                .map(|function| {
                    crate::mir::builder::MirBuilder::build_function(compiler.context, function)
                })
                .collect();
            f(bodies, compiler.context)
        },
    )
}

pub(crate) fn analyze_script_mir_diagnostics(source: &str) -> Vec<DiagnosticRecord> {
    analyze_diagnostics(&[("main.tr", source)], true, true, HarnessMode::Test)
}

pub(crate) fn analyze_package_diagnostics(files: &[(&str, &str)]) -> Vec<DiagnosticRecord> {
    analyze_diagnostics(files, false, false, HarnessMode::Test)
}

/// Like `analyze_package_diagnostics`, but compiled as `check` or `build`
/// would: `@test` declarations are dropped before type checking.
pub(crate) fn analyze_package_diagnostics_outside_tests(
    files: &[(&str, &str)],
) -> Vec<DiagnosticRecord> {
    analyze_diagnostics(files, false, false, HarnessMode::None)
}

fn analyze_diagnostics(
    files: &[(&str, &str)],
    is_script: bool,
    build_mir: bool,
    harness: HarnessMode,
) -> Vec<DiagnosticRecord> {
    with_source_compiler(files, is_script, harness, |compiler| {
        let result = compiler.analyze_for_diagnostics(build_mir);
        let dcx = compiler.context.dcx();
        // Diagnostic collection continues after semantic errors, but any early
        // failure must still have emitted a diagnostic for the test to inspect.
        assert!(
            result.is_ok() || dcx.has_error(),
            "analysis failed without diagnostics"
        );
        dcx.take_recorded_diagnostics()
    })
}

/// Real class semantics with a minimal allocator provider, without making
/// unfinished class interoperability available to normal source programs.
pub(crate) fn analyze_native_class_fixture<R>(
    source: &str,
    classes: &[&str],
    items: &[(hir::StdItem, &str)],
    f: impl for<'ctx> FnOnce(hir::Package, Vec<crate::mir::Body<'ctx>>, Gcx<'ctx>) -> R,
) -> R {
    analyze_native_fixture(&[("main.tr", source)], true, classes, items, f)
}

fn analyze_native_fixture<R>(
    files: &[(&str, &str)],
    is_script: bool,
    classes: &[&str],
    items: &[(hir::StdItem, &str)],
    f: impl for<'ctx> FnOnce(hir::Package, Vec<crate::mir::Body<'ctx>>, Gcx<'ctx>) -> R,
) -> R {
    with_source_compiler(files, is_script, HarnessMode::None, |compiler| {
        let (package, bodies) = compiler
            .native_class_fixture(classes, items)
            .unwrap_or_else(|_| {
                panic!(
                    "class fixture: {:#?}",
                    compiler.context.dcx().take_recorded_diagnostics()
                )
            });
        f(package, bodies, compiler.context)
    })
}
