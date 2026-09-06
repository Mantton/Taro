use crate::{
    PackageIndex,
    compile::context::Gcx,
    hir::DefinitionID,
    mir::{
        BasicBlockData, Body, LocalDecl, LocalId, LocalKind, MirPhase, Terminator, TerminatorKind,
        pretty::PrettyPrintMir,
    },
    sema::resolve::models::DefinitionIndex,
    span::{FileID, Span},
};
use index_vec::IndexVec;

pub(crate) use crate::test_support::with_test_gcx;

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
        source_scopes: Body::initial_source_scopes(DefinitionID::new(
            PackageIndex::new(1),
            DefinitionIndex::from_raw(0),
        )),
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
