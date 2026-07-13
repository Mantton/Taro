use crate::{
    PackageIndex,
    compile::{
        config::{BuildProfile, Config, DebugOptions, PackageKind, StdMode},
        context::{CompilerArenas, CompilerContext, CompilerStore, Gcx},
    },
    diagnostics::DiagCtx,
    hir::DefinitionID,
    mir::{
        BasicBlockData, Body, LocalDecl, LocalId, LocalKind, MirPhase, Terminator, TerminatorKind,
        pretty::PrettyPrintMir,
    },
    sema::resolve::models::DefinitionIndex,
    span::{FileID, Span},
};
use index_vec::IndexVec;
use rustc_hash::FxHashMap;
use std::{path::PathBuf, rc::Rc};

pub(crate) fn with_test_gcx<R>(f: impl for<'ctx> FnOnce(Gcx<'ctx>) -> R) -> R {
    let root = std::env::temp_dir().join(format!(
        "taro-mir-test-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("time")
            .as_nanos()
    ));
    std::fs::create_dir_all(&root).expect("temp dir");

    let dcx = Rc::new(DiagCtx::new(PathBuf::from(".")));
    dcx.enable_recording();
    let arenas = CompilerArenas::new();
    let store = CompilerStore::new(&arenas, root.clone(), &dcx, None, BuildProfile::Debug)
        .unwrap_or_else(|_| panic!("store"));
    let icx = CompilerContext::new(dcx, store);
    let config = icx.store.arenas.configs.alloc(Config {
        name: "mir-test".into(),
        identifier: "mir-test".into(),
        src: root.clone(),
        dependencies: FxHashMap::default(),
        index: PackageIndex::new(1),
        kind: PackageKind::Library,
        executable_out: None,
        no_std_prelude: true,
        is_script: true,
        profile: BuildProfile::Debug,
        codegen: Default::default(),
        overflow_checks: true,
        debug: DebugOptions::default(),
        test_mode: false,
        std_mode: StdMode::BootstrapStd,
        is_std_provider: true,
    });

    let result = f(Gcx::new(&icx, config));
    let _ = std::fs::remove_dir_all(root);
    result
}

pub(crate) fn minimal_body<'ctx>(gcx: Gcx<'ctx>) -> Body<'ctx> {
    let span = Span::empty(FileID::new(0));
    let mut locals = IndexVec::new();
    let return_local = locals.push(LocalDecl {
        ty: gcx.types.void,
        kind: LocalKind::Return,
        mutable: true,
        name: None,
        span,
    });
    let mut basic_blocks = IndexVec::new();
    let start_block = basic_blocks.push(BasicBlockData {
        note: Some("test-entry".into()),
        statements: Vec::new(),
        terminator: Some(Terminator {
            kind: TerminatorKind::Return,
            span,
        }),
    });

    Body {
        owner: DefinitionID::new(PackageIndex::new(1), DefinitionIndex::from_raw(0)),
        locals,
        basic_blocks,
        start_block,
        return_local,
        escape_locals: vec![false],
        phase: MirPhase::Built,
        is_async: false,
    }
}

pub(crate) fn push_temp<'ctx>(body: &mut Body<'ctx>, ty: crate::sema::models::Ty<'ctx>) -> LocalId {
    body.escape_locals.push(false);
    body.locals.push(LocalDecl {
        ty,
        kind: LocalKind::Temp,
        mutable: true,
        name: None,
        span: Span::empty(FileID::new(0)),
    })
}

pub(crate) fn pretty_body<'ctx>(gcx: Gcx<'ctx>, body: &Body<'ctx>) -> String {
    PrettyPrintMir { body, gcx }.to_string()
}
