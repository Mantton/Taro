//! Give cold compiler temporaries a proven scanner-initialization boundary.
//! This changes neither source initialization nor the frame's storage address.
use crate::{
    compile::context::Gcx,
    mir::{
        Body, LocalKind, PlaceElem, Statement, StatementKind,
        analysis::{
            control_flow::block_is_cyclic,
            dominators::{Dominators, compute_dominators},
            liveness::{MirLocation, for_each_storage_observation},
        },
    },
    sema::{
        models::{GenericArguments, TyKind},
        tycheck::utils::instantiate::instantiate_ty_with_args,
    },
};

#[cfg(test)]
use crate::mir::Rvalue;

fn point(location: MirLocation) -> (crate::mir::BasicBlockId, usize) {
    match location {
        MirLocation::Statement { block, index } => (block, index),
        MirLocation::Terminator { block } => (block, usize::MAX),
    }
}

fn dominates(dominators: &Dominators, before: MirLocation, after: MirLocation) -> bool {
    let (before_block, before_index) = point(before);
    let (after_block, after_index) = point(after);
    dominators.dominates(before_block, after_block)
        && (before_block != after_block || before_index <= after_index)
}

/// Run after escape placement and before safepoints/liveness. Only compiler
/// temporaries with no address exposure qualify. An inliner's eager, unique
/// lifetime start may move to a later block, provided it dominates that block
/// and there is no lifetime end. Storage
/// used on every returning path keeps its existing initialization. The
/// chosen first observation must dominate every read, write and destination;
/// scanner zeroing then precedes even the first partially initialized field.
/// Both old and new starts must be outside cycles, so each executes at most
/// once per invocation. Unrelated loops do not prevent deferral. Source-async
/// bodies remain conservative; source storage/escape boundaries never change.
pub(crate) fn insert_temporary_storage_lifetimes<'ctx>(
    gcx: Gcx<'ctx>,
    body: &mut Body<'ctx>,
    args: GenericArguments<'ctx>,
) -> usize {
    if body.is_async {
        return 0;
    }
    let mut eligible: Vec<_> = body
        .locals
        .iter_enumerated()
        .map(|(local, declaration)| {
            let ty = instantiate_ty_with_args(gcx, declaration.ty, args);
            ty != gcx.types.void
                && local != body.return_local
                && declaration.kind == LocalKind::Temp
                && body
                    .escape_locals
                    .get(local.index())
                    .is_some_and(|escapes| !escapes)
                && !matches!(
                    ty.kind(),
                    TyKind::Bool
                        | TyKind::Rune
                        | TyKind::Int(_)
                        | TyKind::UInt(_)
                        | TyKind::Float(_)
                        | TyKind::FnPointer { .. }
                        | TyKind::Never
                        | TyKind::Error
                )
        })
        .collect();
    let mut previous_starts = vec![None; body.locals.len()];
    for (block, data) in body.basic_blocks.iter_enumerated() {
        for (index, statement) in data.statements.iter().enumerate() {
            match &statement.kind {
                StatementKind::StorageLive(local) => {
                    if previous_starts[local.index()]
                        .replace(MirLocation::Statement { block, index })
                        .is_some()
                    {
                        eligible[local.index()] = false;
                    }
                }
                StatementKind::StorageDead(local) => {
                    eligible[local.index()] = false;
                }
                StatementKind::Assign(_, value) => {
                    if let Some(place) = value.addressed_place()
                        && !place.projection.contains(&PlaceElem::Deref)
                    {
                        eligible[place.local.index()] = false;
                    }
                }
                _ => {}
            }
        }
    }
    if !eligible.iter().any(|eligible| *eligible) {
        return 0;
    }
    let dominators = compute_dominators(body);
    let returns: Vec<_> = body
        .basic_blocks
        .iter_enumerated()
        .filter_map(|(block, data)| {
            (dominators.dominates(body.start_block, block)
                && matches!(
                    data.terminator.as_ref().map(|terminator| &terminator.kind),
                    Some(crate::mir::TerminatorKind::Return)
                ))
            .then_some(block)
        })
        .collect();
    if returns.is_empty() {
        return 0;
    }
    let mut starts = vec![None; body.locals.len()];
    for_each_storage_observation(body, |local, location| {
        if eligible[local.index()]
            && starts[local.index()].is_none_or(|old| dominates(&dominators, location, old))
        {
            starts[local.index()] = Some(location);
        }
    });
    // An incomparable branch can defeat the candidate. Do not invent a start
    // in a common ancestor: retain entry initialization unless an actual
    // observation dominates all the others.
    for_each_storage_observation(body, |local, location| {
        if let Some(start) = starts[local.index()] {
            if !dominates(&dominators, start, location) {
                eligible[local.index()] = false;
            }
        }
    });
    let mut insertions = vec![Vec::new(); body.basic_blocks.len()];
    let mut removals = Vec::new();
    let mut count = 0;
    let mut cycles = vec![None; body.basic_blocks.len()];
    let mut is_cyclic = |block: crate::mir::BasicBlockId| {
        *cycles[block.index()].get_or_insert_with(|| block_is_cyclic(body, block))
    };
    for local in body.locals.indices() {
        if eligible[local.index()]
            && let Some(start) = starts[local.index()]
        {
            let (block, index) = point(start);
            if is_cyclic(block) {
                continue;
            }
            if let Some(previous) = previous_starts[local.index()] {
                // Keep same-block starts and repeated lifetimes unchanged.
                // The old boundary must cover the new one; otherwise moving
                // it could create a lifetime on a previously bypassing path.
                if point(previous).0 == block
                    || !dominates(&dominators, previous, start)
                    || is_cyclic(point(previous).0)
                {
                    continue;
                }
            }
            if returns
                .iter()
                .all(|exit| dominators.dominates(block, *exit))
            {
                continue;
            }
            insertions[block.index()].push((index, local));
            if let Some(previous) = previous_starts[local.index()] {
                removals.push(previous);
            }
            count += 1;
        }
    }
    // Preserve indices until all decisions have been made. The new boundary
    // still initializes scanner bytes before the first partial write or call.
    for previous in removals {
        let (block, index) = point(previous);
        body.basic_blocks[block].statements[index].kind = StatementKind::Nop;
    }
    for (block, data) in body.basic_blocks.iter_mut().enumerate() {
        let sites = &mut insertions[block];
        if sites.is_empty() {
            continue;
        }
        sites.sort_unstable();
        let mut sites = sites.iter().peekable();
        let previous = std::mem::take(&mut data.statements);
        for (index, statement) in previous.into_iter().enumerate() {
            while let Some(&&(at, local)) = sites.peek()
                && at == index
            {
                data.statements.push(Statement {
                    kind: StatementKind::StorageLive(local),
                    span: body.locals[local].span,
                });
                sites.next();
            }
            data.statements.push(statement);
        }
        for &(_, local) in sites {
            data.statements.push(Statement {
                kind: StatementKind::StorageLive(local),
                span: body.locals[local].span,
            });
        }
    }
    count
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mir::{
        BasicBlockData, BasicBlockId, Constant, ConstantKind, LocalId, Operand, Place, Terminator,
        TerminatorKind,
        analysis::liveness::compute_liveness,
        test_support::{minimal_body, push_temp, with_test_gcx},
    };
    use crate::sema::models::Ty;

    fn fixture<'ctx>(gcx: Gcx<'ctx>) -> (Body<'ctx>, LocalId, Place<'ctx>) {
        let mut body = minimal_body(gcx);
        let reference = Ty::new(TyKind::Reference(gcx.types.int32), gcx);
        let source = push_temp(&mut body, reference);
        body.locals[source].kind = LocalKind::Param;
        let aggregate = Ty::new(
            TyKind::Tuple(gcx.store.interners.intern_ty_list(vec![reference; 3])),
            gcx,
        );
        let temporary = push_temp(&mut body, aggregate);
        let mut field = Place::from_local(temporary);
        field
            .projection
            .push(PlaceElem::Field(crate::thir::FieldIndex::new(0), reference));
        let span = body.locals[temporary].span;
        body.basic_blocks[body.start_block]
            .terminator
            .as_mut()
            .unwrap()
            .kind = TerminatorKind::SwitchInt {
            discr: Operand::Constant(Constant {
                ty: gcx.types.bool,
                value: ConstantKind::Bool(true),
            }),
            targets: vec![(1, BasicBlockId::from_usize(1))],
            otherwise: BasicBlockId::from_usize(2),
        };
        body.basic_blocks.push(BasicBlockData {
            note: None,
            statements: vec![
                Statement {
                    span,
                    kind: StatementKind::Nop,
                },
                Statement {
                    span,
                    kind: StatementKind::Assign(
                        field.clone(),
                        Rvalue::Use(Operand::copy(Place::from_local(source))),
                    ),
                },
                Statement {
                    span,
                    kind: StatementKind::Nop,
                },
                Statement {
                    span,
                    kind: StatementKind::KeepAlive(Operand::copy(field.clone())),
                },
            ],
            terminator: Some(Terminator {
                span,
                kind: TerminatorKind::Return,
            }),
        });
        body.basic_blocks.push(BasicBlockData {
            note: None,
            statements: vec![],
            terminator: Some(Terminator {
                span,
                kind: TerminatorKind::Return,
            }),
        });
        (body, temporary, field)
    }

    fn has_start(body: &Body<'_>, local: LocalId) -> bool {
        body.basic_blocks.iter().flat_map(|block| &block.statements)
            .any(|statement| matches!(statement.kind, StatementKind::StorageLive(found) if found == local))
    }

    #[test]
    fn cold_partial_storage_starts_before_its_first_write_without_source_initialization() {
        with_test_gcx(|gcx| {
            let (mut body, temporary, _) = fixture(gcx);
            assert_eq!(
                insert_temporary_storage_lifetimes(gcx, &mut body, GenericArguments::empty()),
                1
            );
            let cold = BasicBlockId::from_usize(1);
            assert!(
                matches!(body.basic_blocks[cold].statements[1].kind, StatementKind::StorageLive(local) if local == temporary)
            );
            let liveness = compute_liveness(&body);
            assert!(
                !liveness
                    .live_before_terminator(body.start_block)
                    .contains(&temporary)
            );
            assert!(liveness.live_before_statement(cold, 3).contains(&temporary));
            assert!(
                !liveness
                    .initialized_before(MirLocation::Statement {
                        block: cold,
                        index: 3
                    })
                    .contains(&temporary)
            );
            assert_eq!(
                insert_temporary_storage_lifetimes(gcx, &mut body, GenericArguments::empty()),
                0,
                "existing boundaries are left alone"
            );
        });
    }

    #[test]
    fn inlined_result_temporary_starts_in_its_cold_branch() {
        with_test_gcx(|gcx| {
            let (mut body, temporary, _) = fixture(gcx);
            body.basic_blocks[body.start_block]
                .statements
                .push(Statement {
                    span: body.locals[temporary].span,
                    kind: StatementKind::StorageLive(temporary),
                });
            assert_eq!(
                insert_temporary_storage_lifetimes(gcx, &mut body, GenericArguments::empty()),
                1,
                "the inliner's eager temporary boundary must move to the first cold write"
            );
            assert!(!body.basic_blocks[body.start_block].statements.iter().any(|statement| {
                matches!(statement.kind, StatementKind::StorageLive(local) if local == temporary)
            }));
            let cold = BasicBlockId::from_usize(1);
            assert!(
                matches!(body.basic_blocks[cold].statements[1].kind, StatementKind::StorageLive(local) if local == temporary)
            );
            let liveness = compute_liveness(&body);
            assert!(
                !liveness
                    .live_before_terminator(body.start_block)
                    .contains(&temporary)
            );
            assert!(liveness.live_before_statement(cold, 3).contains(&temporary));
            assert!(
                !liveness
                    .initialized_before(MirLocation::Statement {
                        block: cold,
                        index: 3
                    })
                    .contains(&temporary)
            );
            assert_eq!(
                insert_temporary_storage_lifetimes(gcx, &mut body, GenericArguments::empty()),
                0
            );
        });
    }

    #[test]
    fn cold_storage_outside_an_unrelated_loop_keeps_a_single_lifetime() {
        with_test_gcx(|gcx| {
            for eager_start in [false, true] {
                let (mut body, temporary, _) = fixture(gcx);
                let span = body.locals[temporary].span;
                let hot = BasicBlockId::from_usize(2);
                let exit = body.basic_blocks.push(BasicBlockData {
                    note: None,
                    statements: vec![],
                    terminator: Some(Terminator {
                        span,
                        kind: TerminatorKind::Return,
                    }),
                });
                body.basic_blocks[hot].terminator.as_mut().unwrap().kind =
                    TerminatorKind::SwitchInt {
                        discr: Operand::Constant(Constant {
                            ty: gcx.types.bool,
                            value: ConstantKind::Bool(true),
                        }),
                        targets: vec![(1, hot)],
                        otherwise: exit,
                    };
                if eager_start {
                    body.basic_blocks[body.start_block]
                        .statements
                        .push(Statement {
                            span,
                            kind: StatementKind::StorageLive(temporary),
                        });
                }
                assert_eq!(
                    insert_temporary_storage_lifetimes(gcx, &mut body, GenericArguments::empty()),
                    1,
                    "an unrelated loop must not force cold error buffers into the entry path"
                );
                assert!(matches!(
                    body.basic_blocks[BasicBlockId::from_usize(1)].statements[1].kind,
                    StatementKind::StorageLive(local) if local == temporary
                ));
                let liveness = compute_liveness(&body);
                assert!(
                    !liveness
                        .live_before_terminator(body.start_block)
                        .contains(&temporary)
                );
                assert!(!liveness.live_before_terminator(hot).contains(&temporary));
            }
        });
    }

    #[test]
    fn a_repeated_start_cannot_move_to_a_nonrepeating_exit() {
        with_test_gcx(|gcx| {
            let (mut body, temporary, _) = fixture(gcx);
            let span = body.locals[temporary].span;
            let cold = crate::mir::BasicBlockId::from_usize(1);
            let header = crate::mir::BasicBlockId::from_usize(2);
            let exit = body.basic_blocks.push(BasicBlockData {
                note: None,
                statements: vec![],
                terminator: Some(Terminator {
                    span,
                    kind: TerminatorKind::Return,
                }),
            });
            body.basic_blocks[body.start_block]
                .terminator
                .as_mut()
                .unwrap()
                .kind = TerminatorKind::Goto { target: header };
            body.basic_blocks[header].statements.push(Statement {
                span,
                kind: StatementKind::StorageLive(temporary),
            });
            body.basic_blocks[header].terminator.as_mut().unwrap().kind =
                TerminatorKind::SwitchInt {
                    discr: Operand::Constant(Constant {
                        ty: gcx.types.int32,
                        value: ConstantKind::Integer(0),
                    }),
                    targets: vec![(0, header), (1, cold)],
                    otherwise: exit,
                };
            assert_eq!(
                insert_temporary_storage_lifetimes(gcx, &mut body, GenericArguments::empty()),
                0,
                "a repeated lifetime boundary must not be moved out of its loop"
            );
            assert!(matches!(body.basic_blocks[header].statements[0].kind,
                StatementKind::StorageLive(local) if local == temporary));
        });
    }

    #[test]
    fn inlined_result_lifetimes_keep_repeated_ended_and_bypassed_boundaries() {
        with_test_gcx(|gcx| {
            for scenario in ["duplicate", "dead", "bypass", "loop", "async"] {
                let (mut body, temporary, _) = fixture(gcx);
                let cold = BasicBlockId::from_usize(1);
                let span = body.locals[temporary].span;
                let start = Statement {
                    span,
                    kind: StatementKind::StorageLive(temporary),
                };
                let entry = body.start_block;
                body.basic_blocks[entry].statements.push(start.clone());
                match scenario {
                    "duplicate" => body.basic_blocks[cold].statements.insert(0, start),
                    "dead" => body.basic_blocks[cold].statements.push(Statement {
                        span,
                        kind: StatementKind::StorageDead(temporary),
                    }),
                    "bypass" => {
                        body.basic_blocks[entry].statements.clear();
                        body.basic_blocks[BasicBlockId::from_usize(2)]
                            .statements
                            .push(start);
                    }
                    "loop" => {
                        body.basic_blocks[cold].terminator.as_mut().unwrap().kind =
                            TerminatorKind::Goto { target: cold }
                    }
                    "async" => body.is_async = true,
                    _ => unreachable!(),
                }
                assert_eq!(
                    insert_temporary_storage_lifetimes(gcx, &mut body, GenericArguments::empty()),
                    0,
                    "{scenario}"
                );
            }
        });
    }

    #[test]
    fn source_bindings_escape_address_and_existing_lifetimes_keep_their_boundaries() {
        with_test_gcx(|gcx| {
            for scenario in [
                "user",
                "parameter",
                "return",
                "constructor",
                "escape",
                "address",
                "live",
                "dead",
                "unknown",
                "return-role",
            ] {
                let (mut body, temporary, _) = fixture(gcx);
                let span = body.locals[temporary].span;
                let cold = BasicBlockId::from_usize(1);
                match scenario {
                    "user" => body.locals[temporary].kind = LocalKind::User,
                    "parameter" => body.locals[temporary].kind = LocalKind::Param,
                    "return" => body.locals[temporary].kind = LocalKind::Return,
                    "return-role" => body.return_local = temporary,
                    "constructor" => body.locals[temporary].kind = LocalKind::ConstructorSelf,
                    "escape" => body.escape_locals[temporary.index()] = true,
                    "unknown" => body.escape_locals.clear(),
                    "address" => {
                        let alias_ty = Ty::new(TyKind::Reference(body.locals[temporary].ty), gcx);
                        let alias = push_temp(&mut body, alias_ty);
                        body.basic_blocks[cold].statements.push(Statement {
                            span,
                            kind: StatementKind::Assign(
                                Place::from_local(alias),
                                Rvalue::Ref {
                                    place: Place::from_local(temporary),
                                },
                            ),
                        });
                    }
                    "live" => body.basic_blocks[cold].statements.insert(
                        0,
                        Statement {
                            span,
                            kind: StatementKind::StorageLive(temporary),
                        },
                    ),
                    "dead" => body.basic_blocks[cold].statements.push(Statement {
                        span,
                        kind: StatementKind::StorageDead(temporary),
                    }),
                    _ => unreachable!(),
                }
                let previous = body.basic_blocks[cold].statements.iter().filter(|statement| matches!(statement.kind, StatementKind::StorageLive(local) if local == temporary)).count();
                insert_temporary_storage_lifetimes(gcx, &mut body, GenericArguments::empty());
                let after = body.basic_blocks[cold].statements.iter().filter(|statement| matches!(statement.kind, StatementKind::StorageLive(local) if local == temporary)).count();
                assert_eq!(after, previous, "{scenario}");
            }
        });
    }

    #[test]
    fn incomparable_branch_writes_loops_and_source_async_remain_conservative() {
        with_test_gcx(|gcx| {
            for scenario in ["join", "loop", "async", "always", "noreturn"] {
                let (mut body, temporary, _) = fixture(gcx);
                let cold = BasicBlockId::from_usize(1);
                match scenario {
                    "join" => {
                        body.basic_blocks[BasicBlockId::from_usize(2)].statements =
                            body.basic_blocks[cold].statements.clone()
                    }
                    "loop" => {
                        body.basic_blocks[cold].terminator.as_mut().unwrap().kind =
                            TerminatorKind::Goto { target: cold }
                    }
                    "async" => body.is_async = true,
                    "always" => {
                        body.basic_blocks[body.start_block]
                            .terminator
                            .as_mut()
                            .unwrap()
                            .kind = TerminatorKind::Goto { target: cold }
                    }
                    "noreturn" => {
                        body.basic_blocks[cold].terminator.as_mut().unwrap().kind =
                            TerminatorKind::Unreachable;
                        body.basic_blocks[BasicBlockId::from_usize(2)]
                            .terminator
                            .as_mut()
                            .unwrap()
                            .kind = TerminatorKind::Unreachable;
                    }
                    _ => unreachable!(),
                }
                insert_temporary_storage_lifetimes(gcx, &mut body, GenericArguments::empty());
                assert!(!has_start(&body, temporary), "{scenario}");
            }
        });
    }

    #[test]
    fn call_destinations_start_before_the_call_and_block_order_does_not_choose_lifetimes() {
        with_test_gcx(|gcx| {
            let (mut body, temporary, field) = fixture(gcx);
            let cold = BasicBlockId::from_usize(1);
            let span = body.locals[temporary].span;
            let use_block = body.basic_blocks.push(body.basic_blocks[cold].clone());
            body.basic_blocks[use_block].statements.drain(..3);
            let output = body.place_ty(gcx, &field);
            let function = push_temp(
                &mut body,
                Ty::new(
                    TyKind::FnPointer {
                        effects: Default::default(),
                        inputs: gcx.store.interners.intern_ty_list(vec![]),
                        output,
                    },
                    gcx,
                ),
            );
            body.locals[function].kind = LocalKind::Param;
            body.basic_blocks[cold].statements.clear();
            body.basic_blocks[cold].terminator = Some(Terminator {
                span,
                kind: TerminatorKind::Call {
                    func: Operand::copy(Place::from_local(function)),
                    args: vec![],
                    destination: field,
                    target: use_block,
                    unwind: crate::mir::CallUnwindAction::Terminate,
                },
            });
            insert_temporary_storage_lifetimes(gcx, &mut body, GenericArguments::empty());
            assert!(
                matches!(body.basic_blocks[cold].statements.last().unwrap().kind, StatementKind::StorageLive(local) if local == temporary)
            );

            let (mut body, temporary, _) = fixture(gcx);
            body.basic_blocks[cold].statements.swap(1, 3);
            let definition = body.basic_blocks.push(body.basic_blocks[cold].clone());
            body.basic_blocks[definition].statements.drain(..3);
            body.basic_blocks[definition]
                .terminator
                .as_mut()
                .unwrap()
                .kind = TerminatorKind::Goto { target: cold };
            body.basic_blocks[body.start_block]
                .terminator
                .as_mut()
                .unwrap()
                .kind = TerminatorKind::SwitchInt {
                discr: Operand::Constant(Constant {
                    ty: gcx.types.bool,
                    value: ConstantKind::Bool(true),
                }),
                targets: vec![(1, definition)],
                otherwise: BasicBlockId::from_usize(2),
            };
            body.basic_blocks[cold].statements =
                vec![body.basic_blocks[cold].statements[1].clone()];
            insert_temporary_storage_lifetimes(gcx, &mut body, GenericArguments::empty());
            assert!(has_start(&body, temporary));
            assert!(
                matches!(body.basic_blocks[definition].statements[0].kind, StatementKind::StorageLive(local) if local == temporary)
            );
        });
    }
}
