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
use std::{fs, path::Path, rc::Rc};

#[path = "../../test_support.rs"]
mod files;
pub(crate) use files::TempDir;

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
            let (package, _) = compiler
                .analyze()
                .unwrap_or_else(|_| panic!("test analysis"));
            f(package, compiler.context)
        },
    )
}

pub(crate) fn analyze_script_diagnostics(source: &str) -> Vec<DiagnosticRecord> {
    analyze_diagnostics(&[("main.tr", source)], true, false)
}

pub(crate) fn analyze_script_mir_diagnostics(source: &str) -> Vec<DiagnosticRecord> {
    analyze_diagnostics(&[("main.tr", source)], true, true)
}

pub(crate) fn analyze_package_diagnostics(files: &[(&str, &str)]) -> Vec<DiagnosticRecord> {
    analyze_diagnostics(files, false, false)
}

fn analyze_diagnostics(
    files: &[(&str, &str)],
    is_script: bool,
    build_mir: bool,
) -> Vec<DiagnosticRecord> {
    with_source_compiler(files, is_script, HarnessMode::Test, |compiler| {
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
