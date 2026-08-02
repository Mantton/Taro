use crate::{
    PackageIndex,
    compile::{
        Compiler,
        config::{BuildProfile, Config, DebugOptions, HarnessMode, PackageKind, StdMode},
        context::{CompilerArenas, CompilerContext, CompilerStore},
    },
    diagnostics::{DiagCtx, DiagnosticRecord},
    interner,
};
use rustc_hash::FxHashMap;
use std::{
    fs::{create_dir_all, write},
    path::{Path, PathBuf},
    rc::Rc,
    sync::Mutex,
};

static ANALYSIS_LOCK: Mutex<()> = Mutex::new(());

pub(crate) fn temp_dir(name: &str) -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "taro-tycheck-{name}-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("time")
            .as_nanos()
    ));
    create_dir_all(&path).expect("temp dir");
    path
}

pub(crate) fn write_file(path: &Path, contents: &str) {
    if let Some(parent) = path.parent() {
        create_dir_all(parent).expect("parent dir");
    }
    write(path, contents).expect("write file");
}

pub(crate) fn make_script_config<'a>(
    icx: &'a CompilerContext<'a>,
    src: PathBuf,
    identifier: &str,
) -> &'a Config {
    icx.store.arenas.configs.alloc(Config {
        name: "script".into(),
        identifier: identifier.into(),
        src,
        dependencies: FxHashMap::default(),
        index: PackageIndex::new(1),
        kind: PackageKind::Executable,
        executable_out: None,
        no_std_prelude: true,
        is_script: true,
        profile: BuildProfile::Debug,
        codegen: Default::default(),
        overflow_checks: false,
        debug: DebugOptions {
            dump_mir: false,
            dump_llvm: false,
            timings: false,
            debug_info: Default::default(),
        },
        harness_mode: HarnessMode::Test,
        std_mode: StdMode::BootstrapStd,
        is_std_provider: false,
    })
}

pub(crate) fn make_package_config<'a>(
    icx: &'a CompilerContext<'a>,
    src: PathBuf,
    identifier: &str,
) -> &'a Config {
    icx.store.arenas.configs.alloc(Config {
        name: "package".into(),
        identifier: identifier.into(),
        src,
        dependencies: FxHashMap::default(),
        index: PackageIndex::new(1),
        kind: PackageKind::Library,
        executable_out: None,
        no_std_prelude: true,
        is_script: false,
        profile: BuildProfile::Debug,
        codegen: Default::default(),
        overflow_checks: false,
        debug: DebugOptions {
            dump_mir: false,
            dump_llvm: false,
            timings: false,
            debug_info: Default::default(),
        },
        harness_mode: HarnessMode::Test,
        std_mode: StdMode::BootstrapStd,
        is_std_provider: false,
    })
}

pub(crate) fn analyze_script_diagnostics(source: &str) -> Vec<DiagnosticRecord> {
    analyze_script_diagnostics_with_mir(source, false)
}

pub(crate) fn analyze_script_mir_diagnostics(source: &str) -> Vec<DiagnosticRecord> {
    analyze_script_diagnostics_with_mir(source, true)
}

fn analyze_script_diagnostics_with_mir(source: &str, build_mir: bool) -> Vec<DiagnosticRecord> {
    let _guard = ANALYSIS_LOCK
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    interner::reset_session();

    let root = temp_dir("diagnostics");
    let output_root = root.join("target");
    create_dir_all(&output_root).expect("output root");
    let file = root.join("main.tr");
    write_file(&file, source);

    let dcx = Rc::new(DiagCtx::new(PathBuf::from(".")));
    dcx.enable_recording();
    let arenas = CompilerArenas::new();
    let store = CompilerStore::new(&arenas, output_root, &dcx, None, BuildProfile::Debug)
        .unwrap_or_else(|_| panic!("store"));
    let icx = CompilerContext::new(dcx.clone(), store);
    let config = make_script_config(&icx, file, "script-diagnostics");

    let mut compiler = Compiler::new(&icx, config);
    let _ = compiler.analyze_for_diagnostics(build_mir);
    dcx.take_recorded_diagnostics()
}

pub(crate) fn analyze_package_diagnostics(files: &[(&str, &str)]) -> Vec<DiagnosticRecord> {
    let _guard = ANALYSIS_LOCK
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    interner::reset_session();

    let root = temp_dir("package-diagnostics");
    let output_root = root.join("target");
    create_dir_all(&output_root).expect("output root");
    for (relative_path, contents) in files {
        write_file(&root.join("src").join(relative_path), contents);
    }

    let dcx = Rc::new(DiagCtx::new(PathBuf::from(".")));
    dcx.enable_recording();
    let arenas = CompilerArenas::new();
    let store = CompilerStore::new(&arenas, output_root, &dcx, None, BuildProfile::Debug)
        .unwrap_or_else(|_| panic!("store"));
    let icx = CompilerContext::new(dcx.clone(), store);
    let config = make_package_config(&icx, root, "package-diagnostics");

    let mut compiler = Compiler::new(&icx, config);
    let _ = compiler.analyze_for_diagnostics(false);
    dcx.take_recorded_diagnostics()
}
