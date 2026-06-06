use crate::{
    PackageIndex,
    compile::{
        Compiler, IdeAnalysisMode,
        config::{BuildProfile, Config, DebugOptions, PackageKind, StdMode},
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
};

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
        overflow_checks: false,
        debug: DebugOptions {
            dump_mir: false,
            dump_llvm: false,
            timings: false,
        },
        test_mode: true,
        std_mode: StdMode::BootstrapStd,
        is_std_provider: false,
    })
}

pub(crate) fn analyze_script_diagnostics(source: &str) -> Vec<DiagnosticRecord> {
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
    let _ = compiler.analyze_for_ide(IdeAnalysisMode::OnType);
    dcx.take_recorded_diagnostics()
}
