use super::{BasicBlockId, CallUnwindAction, LocalId, Operand, Place, TerminatorKind};

#[test]
fn dead_local_compaction_preserves_projected_uses_and_copy_modifiers() {
    use super::test_support::{minimal_body, push_temp, with_test_gcx};
    use super::{CopyModifiers, PlaceElem, Rvalue, Statement, StatementKind};
    use crate::{
        hir::Mutability,
        sema::models::{Ty, TyKind},
    };

    with_test_gcx(|gcx| {
        for modifiers in [
            CopyModifiers {
                take: true,
                init: false,
            },
            CopyModifiers {
                take: false,
                init: true,
            },
            CopyModifiers {
                take: true,
                init: true,
            },
        ] {
            let mut body = minimal_body(gcx);
            let dead = push_temp(&mut body, gcx.types.uint);
            let source = push_temp(
                &mut body,
                Ty::new(TyKind::Pointer(gcx.types.uint, Mutability::Mutable), gcx),
            );
            body.locals[source].kind = super::LocalKind::Param;
            body.locals[body.return_local].ty =
                Ty::new(TyKind::Reference(gcx.types.uint, Mutability::Mutable), gcx);
            body.escape_locals[source.index()] = true;
            let span = body.locals[source].span;
            let projected = Place {
                local: source,
                projection: vec![PlaceElem::Deref],
            };
            body.basic_blocks[body.start_block].statements = vec![
                Statement {
                    kind: StatementKind::StorageLive(dead),
                    span,
                },
                Statement {
                    kind: StatementKind::SetInitialized(dead),
                    span,
                },
                Statement {
                    kind: StatementKind::KeepAlive(Operand::CopyWith(projected.clone(), modifiers)),
                    span,
                },
                Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(body.return_local),
                        Rvalue::Ref {
                            mutable: true,
                            place: projected,
                        },
                    ),
                    span,
                },
            ];

            super::optimize::simplify::eliminate_dead_locals(&mut body);

            assert_eq!(body.locals.len(), 2);
            assert_eq!(body.escape_locals, [false, true]);
            let statements = &body.basic_blocks[body.start_block].statements;
            assert!(matches!(statements[0].kind, StatementKind::Nop));
            assert!(matches!(statements[1].kind, StatementKind::Nop));
            let StatementKind::KeepAlive(Operand::CopyWith(place, actual)) = &statements[2].kind
            else {
                panic!("copy modifiers were lost during compaction");
            };
            assert_eq!(*actual, modifiers);
            assert_eq!(place.local.index(), 1);
            assert_eq!(place.projection, [PlaceElem::Deref]);
            let StatementKind::Assign(destination, Rvalue::Ref { mutable, place }) =
                &statements[3].kind
            else {
                panic!("reference was changed during compaction");
            };
            assert_eq!(destination.local, body.return_local);
            assert!(*mutable);
            assert_eq!(place.local.index(), 1);
            assert_eq!(place.projection, [PlaceElem::Deref]);
        }
    });
}

fn block(index: usize) -> BasicBlockId {
    BasicBlockId::from_usize(index)
}

fn place() -> Place<'static> {
    Place::from_local(LocalId::from_usize(0))
}

#[test]
fn successors_preserve_switch_order_and_duplicate_edges() {
    let branch = TerminatorKind::SwitchInt {
        discr: Operand::Copy(place()),
        targets: vec![(1, block(2)), (2, block(1)), (3, block(2))],
        otherwise: block(3),
    };
    assert_eq!(
        branch.successors(),
        vec![block(2), block(1), block(2), block(3)]
    );
}

#[test]
fn successors_include_call_cleanup_but_not_termination() {
    for (unwind, expected) in [
        (CallUnwindAction::Terminate, vec![block(1)]),
        (
            CallUnwindAction::Cleanup(block(2)),
            vec![block(1), block(2)],
        ),
    ] {
        let call = TerminatorKind::Call {
            func: Operand::Copy(place()),
            args: Vec::new(),
            devirt_hint: None,
            destination: place(),
            target: block(1),
            unwind,
        };
        assert_eq!(call.successors(), expected);
    }
    assert_eq!(
        TerminatorKind::Goto { target: block(1) }.successors(),
        vec![block(1)]
    );
    for exit in [
        TerminatorKind::Return,
        TerminatorKind::ResumeUnwind,
        TerminatorKind::Unreachable,
        TerminatorKind::UnresolvedGoto,
    ] {
        assert!(exit.successors().is_empty());
    }
}

#[test]
fn successors_include_yield_cancellation_and_unwind_not_completion_marker() {
    for (unwind, expected) in [
        (CallUnwindAction::Terminate, vec![block(1), block(2)]),
        (
            CallUnwindAction::Cleanup(block(3)),
            vec![block(1), block(2), block(3)],
        ),
    ] {
        let suspend = TerminatorKind::Yield {
            value: Operand::Copy(place()),
            resume: block(1),
            resume_arg: place(),
            cancel: block(2),
            cancel_complete: block(4),
            unwind,
        };
        assert_eq!(suspend.successors(), expected);
    }
}
