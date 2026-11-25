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
        for modifiers in [CopyModifiers { init: false }, CopyModifiers { init: true }] {
            let mut body = minimal_body(gcx);
            let dead = push_temp(&mut body, gcx.types.uint);
            let source = push_temp(
                &mut body,
                Ty::new(TyKind::Pointer(gcx.types.uint, Mutability::Mutable), gcx),
            );
            body.locals[source].kind = super::LocalKind::Param;
            body.locals[body.return_local].ty = Ty::new(TyKind::Reference(gcx.types.uint), gcx);
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
                        Rvalue::Ref { place: projected },
                    ),
                    span,
                },
            ];

            super::optimize::simplify::eliminate_dead_locals(&mut body);

            assert_eq!(body.locals.len(), 2);
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
            let StatementKind::Assign(destination, Rvalue::Ref { place }) = &statements[3].kind
            else {
                panic!("reference was changed during compaction");
            };
            assert_eq!(destination.local, body.return_local);
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
            no_result: None,
            cancel: block(2),
            cancel_complete: block(4),
            unwind,
        };
        assert_eq!(suspend.successors(), expected);
    }
}

#[test]
fn value_conditionals_preserve_the_source_on_both_outcomes() {
    let prefix = "struct Token { value: int32 }\nenum State { case empty; case token(Token) }\n";
    for body in [
        "var state: State = .empty; if case .token(token) = state {} else { var reused: State = state }",
        "var state: State = .token(Token { value: 1 }); if case .token(token) = state { var reused: State = state }",
        "var state: State = .empty; if case .empty = state {}; var reused: State = state",
        "var state: State = .empty; if case .token(token) = state {} ; var reused: State = state",
    ] {
        let source = format!("{prefix}func main() {{ {body} }}");
        let diagnostics = crate::test_support::analyze_script_mir_diagnostics(&source);
        assert!(diagnostics.is_empty(), "{source}\n{diagnostics:#?}");
    }
    // Primitive payloads follow the same value-copy rule.
    let diagnostics = crate::test_support::analyze_script_mir_diagnostics(
        "enum State { case empty; case count(int32) }\nfunc main() { var state: State = .count(1); if case .count(value) = state { var reused: State = state } }",
    );
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
}

#[test]
fn explicit_reads_bind_writable_conditional_copies() {
    for body in [
        "if case .token(token) = *&state { token.value = 2 }",
        "if case .token(token) = *&state { seen := token.value }",
        "if case .token(token) = *&state { seen := token.value }; var preserved: State = state",
        "if case .token(token) = *&state { token.value = 2 }; if case .token(token) = *&state { seen := token.value }; var preserved: State = state",
    ] {
        let source = format!(
            "struct Token {{ value: int32 }}\nenum State {{ case empty; case token(Token) }}\nfunc main() {{ var state: State = .token(Token {{ value: 1 }}); {body} }}"
        );
        let diagnostics = crate::test_support::analyze_script_mir_diagnostics(&source);
        assert!(diagnostics.is_empty(), "{source}\n{diagnostics:#?}");
    }
}

#[test]
fn guard_owners_survive_the_statement_and_borrowed_while_bindings_remain_usable() {
    for source in [
        "struct Token { value: int32 }\nenum State { case empty; case token(Token) }\nfunc inspect(_ state: State) { guard case .token(token) = state else { return }; seen := token.value; defer { last := token.value } }\nfunc main() {}",
        "struct Token { value: int32 }\nenum State { case empty; case token(Token) }\nfunc inspect(_ state: &State) { guard case .token(token) = *state else { return }; seen := token.value }\nfunc main() {}",
        "struct Token { value: int32 }\nenum State { case empty; case token(Token) }\nfunc main() { var state: State = .token(Token { value: 1 }); while case .token(token) = *&state && token.value < 3 { token.value += 1; state = .token(token) }; var preserved: State = state }",
    ] {
        let diagnostics = crate::test_support::analyze_script_mir_diagnostics(source);
        assert!(diagnostics.is_empty(), "{source}\n{diagnostics:#?}");
    }
}

#[test]
fn task_result_failure_edge_preserves_order_remapping_and_metadata() {
    super::test_support::with_test_gcx(|gcx| {
        for unwind in [
            CallUnwindAction::Terminate,
            CallUnwindAction::Cleanup(BasicBlockId::from_raw(3)),
        ] {
            let mut terminator = super::Terminator {
                kind: TerminatorKind::Yield {
                    value: Operand::Copy(Place::from_local(LocalId::from_raw(0))),
                    resume: BasicBlockId::from_raw(1),
                    resume_arg: Place::from_local(LocalId::from_raw(0)),
                    cancel: BasicBlockId::from_raw(2),
                    cancel_complete: BasicBlockId::from_raw(4),
                    no_result: Some(BasicBlockId::from_raw(5)),
                    unwind,
                },
                span: crate::span::Span::empty(crate::span::FileID::from_raw(0)),
            };
            let edges = terminator.kind.successors();
            assert_eq!(*edges.last().unwrap(), BasicBlockId::from_raw(5));
            let wire = crate::metadata::wire::terminator_to_wire(gcx.interner(), &terminator);
            let files = rustc_hash::FxHashMap::default();
            let roundtrip = crate::metadata::wire::terminator_from_wire(
                gcx,
                &wire,
                crate::metadata::wire::FileRemap { old_to_new: &files },
            );
            assert_eq!(roundtrip.kind.successors(), edges);
            assert!(
                terminator
                    .kind
                    .replace_successor(edges.len() - 1, BasicBlockId::from_raw(6))
            );
            terminator
                .kind
                .map_blocks(|block| BasicBlockId::from_raw(block.index() as u32 + 10));
            assert_eq!(
                *terminator.kind.successors().last().unwrap(),
                BasicBlockId::from_raw(16)
            );
        }
    });
}

#[test]
fn explicit_reference_matches_copy_fields_without_copying_the_enum() {
    use super::{Rvalue, StatementKind};
    use crate::sema::models::TyKind;
    for (guard, expect_snapshot) in [("", false), (" if value > 0", true)] {
        let source = format!(
            "enum Choice {{ case empty; case value(int32) }}\nfunc read(_ choice: &Choice) -> int32 {{ match *choice {{ case .value(value){guard} => value; case _ => 0; }} }}\nfunc main() {{}}"
        );
        crate::test_support::analyze_script_built_mir(&source, |bodies, gcx| {
            let body = bodies
                .iter()
                .find(|body| gcx.symbol_text(gcx.definition_ident(body.owner).symbol).as_str() == "read")
                .unwrap();
            let enum_copies = body.basic_blocks.iter().flat_map(|block| &block.statements).filter(|statement| {
                let StatementKind::Assign(destination, Rvalue::Use(Operand::Copy(_))) = &statement.kind else { return false };
                destination.projection.is_empty()
                    && matches!(body.locals[destination.local].ty.kind(), TyKind::Adt(def, _) if gcx.symbol_text(gcx.definition_ident(def.id).symbol).as_str() == "Choice")
            }).count();
            assert_eq!(enum_copies, usize::from(expect_snapshot), "guard={guard}");
        });
    }
}

#[test]
fn structural_reference_matching_uses_value_bindings() {
    for body in [
        "match choice { case .value(value) => {}; case .empty => {}; }",
        "if case .value(value) = choice {}",
        "match (choice,) { case (.value(value),) => {}; case _ => {}; }",
    ] {
        let source = format!(
            "enum Choice {{ case empty; case value(int32) }}\nfunc inspect(_ choice: &Choice) {{ {body} }}\nfunc main() {{}}"
        );
        let diagnostics = crate::test_support::analyze_script_mir_diagnostics(&source);
        assert!(diagnostics.is_empty(), "{source}\n{diagnostics:#?}");
    }
}
