//! GC safepoint placement restored from main, preserving cycle coverage
//! after concrete escape placement. Bounded acyclic leaves omit an entry poll.
use super::MirPass;
use crate::{
    compile::context::Gcx,
    error::{CompileResult, ReportedError},
    mir::{BasicBlockId, Body, Rvalue, Statement, StatementKind, TerminatorKind},
};
use rustc_hash::FxHashSet;

pub struct InsertSafepoints;

/// A short, acyclic leaf returns to its caller without allocating or extending
/// a call chain. Its caller's polls therefore bound GC cooperation without an
/// additional entry poll (and cold poll-call frame) in every tiny helper.
fn is_bounded_safepoint_free_leaf(body: &Body<'_>) -> bool {
    if body.is_async || body.escape_locals.iter().any(|escapes| *escapes) {
        return false;
    }
    let mut budget = 64_usize;
    for block in &body.basic_blocks {
        let Some(term) = &block.terminator else {
            return false;
        };
        if !matches!(
            term.kind,
            TerminatorKind::Return | TerminatorKind::Goto { .. } | TerminatorKind::SwitchInt { .. }
        ) {
            return false;
        }
        for statement in &block.statements {
            if matches!(
                statement.kind,
                StatementKind::SourceScope(_)
                    | StatementKind::StorageLive(_)
                    | StatementKind::StorageDead(_)
                    | StatementKind::Nop
            ) {
                continue;
            }
            if let StatementKind::Assign(_, value) = &statement.kind {
                if !matches!(
                    value,
                    Rvalue::Use(_)
                        | Rvalue::UnaryOp { .. }
                        | Rvalue::BinaryOp { .. }
                        | Rvalue::Discriminant { .. }
                ) {
                    return false;
                }
            } else if !matches!(
                statement.kind,
                StatementKind::SetDiscriminant { .. }
                    | StatementKind::SetInitialized(_)
                    | StatementKind::KeepAlive(_)
            ) {
                return false;
            }
            let Some(remaining) = budget.checked_sub(1) else {
                return false;
            };
            budget = remaining;
        }
        let Some(remaining) = budget.checked_sub(1) else {
            return false;
        };
        budget = remaining;
    }
    find_unpolled_cycle(body, &FxHashSet::default()).is_none()
}

impl<'ctx> MirPass<'ctx> for InsertSafepoints {
    fn name(&self) -> &'static str {
        "InsertSafepoints"
    }

    fn run(&mut self, gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
        if is_bounded_safepoint_free_leaf(body)
            || crate::mir::analysis::effects::is_pointer_offset_wrapper(gcx, body)
        {
            return Ok(());
        }
        let mut targets: FxHashSet<BasicBlockId> = FxHashSet::default();
        targets.insert(body.start_block);

        // Select a deterministic feedback vertex set. Repeatedly remove one
        // block from a discovered cycle until the remaining CFG is acyclic;
        // consequently every original cycle crosses at least one poll. This
        // covers irreducible control flow as well as natural loops.
        while let Some(cycle) = find_unpolled_cycle(body, &targets) {
            let selected = cycle
                .into_iter()
                .min_by_key(|block| block.index())
                .expect("reported cycle must contain a block");
            targets.insert(selected);
        }

        let span = body.locals[body.return_local].span;
        for bb in body.basic_blocks.indices() {
            if !targets.contains(&bb) {
                continue;
            }
            let statements = &mut body.basic_blocks[bb].statements;
            let insertion_index = statements
                .iter()
                .take_while(|stmt| matches!(stmt.kind, StatementKind::SourceScope(_)))
                .count();
            let needs = statements
                .get(insertion_index)
                .map(|stmt| !matches!(stmt.kind, StatementKind::GcSafepoint(_)))
                .unwrap_or(true);
            if needs {
                let kind = if bb == body.start_block {
                    crate::mir::GcSafepointKind::Entry
                } else {
                    crate::mir::GcSafepointKind::Loop
                };
                statements.insert(
                    insertion_index,
                    Statement {
                        kind: StatementKind::GcSafepoint(kind),
                        span,
                    },
                );
            }
        }

        if let Err(cycle) = verify_safepoint_cycle_coverage(body) {
            gcx.dcx().emit_error(
                format!(
                    "internal compiler error: GC safepoint placement left an unpolled CFG cycle through {cycle:?}"
                ),
                Some(span),
            );
            return Err(ReportedError);
        }
        Ok(())
    }
}

/// Verify that removing blocks containing an actual MIR safepoint leaves an
/// acyclic CFG. This deliberately inspects the body instead of the placement
/// pass's candidate set so callers can run it after subsequent CFG rewrites.
pub(crate) fn verify_safepoint_cycle_coverage(body: &Body<'_>) -> Result<(), Vec<BasicBlockId>> {
    let polled = body
        .basic_blocks
        .iter_enumerated()
        .filter_map(|(block, data)| {
            data.statements
                .iter()
                .any(|statement| matches!(statement.kind, StatementKind::GcSafepoint(_)))
                .then_some(block)
        })
        .collect();
    match find_unpolled_cycle(body, &polled) {
        Some(cycle) => Err(cycle),
        None => Ok(()),
    }
}

pub(super) fn find_unpolled_cycle(
    body: &Body<'_>,
    polled: &FxHashSet<BasicBlockId>,
) -> Option<Vec<BasicBlockId>> {
    fn visit(
        body: &Body<'_>,
        node: BasicBlockId,
        polled: &FxHashSet<BasicBlockId>,
        colors: &mut [u8],
        stack: &mut Vec<BasicBlockId>,
    ) -> Option<Vec<BasicBlockId>> {
        colors[node.index()] = 1;
        stack.push(node);
        if let Some(term) = &body.basic_blocks[node].terminator {
            for successor in term.kind.successors() {
                if polled.contains(&successor) {
                    continue;
                }
                match colors[successor.index()] {
                    0 => {
                        if let Some(cycle) = visit(body, successor, polled, colors, stack) {
                            return Some(cycle);
                        }
                    }
                    1 => {
                        let start = stack
                            .iter()
                            .position(|candidate| *candidate == successor)
                            .expect("active DFS node must be on stack");
                        return Some(stack[start..].to_vec());
                    }
                    _ => {}
                }
            }
        }
        stack.pop();
        colors[node.index()] = 2;
        None
    }

    let mut colors = vec![0u8; body.basic_blocks.len()];
    let mut stack = Vec::new();
    for block in body.basic_blocks.indices() {
        if polled.contains(&block) || colors[block.index()] != 0 {
            continue;
        }
        if let Some(cycle) = visit(body, block, polled, &mut colors, &mut stack) {
            return Some(cycle);
        }
    }
    None
}

/// Adjacent polls are redundant; an intervening collecting operation or store
/// retains its own site. This deliberately does not merge across other MIR.
pub fn merge_consecutive_safepoints(body: &mut Body<'_>) {
    for block in body.basic_blocks.iter_mut() {
        let mut previous = false;
        block.statements.retain(|statement| {
            let current = matches!(statement.kind, StatementKind::GcSafepoint(_));
            let keep = !current || !previous;
            previous = current;
            keep
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mir::{
        BasicBlockData, GcSafepointKind, Operand, Place, Terminator,
        test_support::{minimal_body, with_test_gcx},
    };
    #[test]
    fn bounded_leaf_omits_entry_poll_but_allocation_and_calls_keep_it() {
        with_test_gcx(|gcx| {
            let body = minimal_body(gcx);
            let mut leaf = body.clone();
            assert!(is_bounded_safepoint_free_leaf(&leaf));
            assert!(InsertSafepoints.run(gcx, &mut leaf).is_ok());
            assert!(leaf.basic_blocks[leaf.start_block].statements.is_empty());

            let span = body.locals[body.return_local].span;
            let mut allocating = body.clone();
            allocating.basic_blocks[body.start_block]
                .statements
                .push(Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(body.return_local),
                        Rvalue::Alloc {
                            ty: gcx.types.int32,
                        },
                    ),
                    span,
                });
            assert!(!is_bounded_safepoint_free_leaf(&allocating));
            assert!(InsertSafepoints.run(gcx, &mut allocating).is_ok());
            assert!(matches!(
                allocating.basic_blocks[body.start_block].statements[0].kind,
                StatementKind::GcSafepoint(GcSafepointKind::Entry)
            ));

            let mut calling = body.clone();
            calling.basic_blocks[body.start_block].terminator = Some(Terminator {
                kind: TerminatorKind::Call {
                    func: Operand::Copy(Place::from_local(body.return_local)),
                    args: Vec::new(),
                    destination: Place::from_local(body.return_local),
                    target: body.start_block,
                    unwind: crate::mir::CallUnwindAction::Terminate,
                },
                span,
            });
            assert!(!is_bounded_safepoint_free_leaf(&calling));
            let mut escaping = body.clone();
            escaping.escape_locals = vec![true];
            assert!(!is_bounded_safepoint_free_leaf(&escaping));
        });
    }

    #[test]
    fn leaf_poll_elision_rejects_cycles_and_large_bodies() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let span = body.locals[body.return_local].span;
            body.basic_blocks[body.start_block].statements = (0..64)
                .map(|_| Statement {
                    kind: StatementKind::SetInitialized(body.return_local),
                    span,
                })
                .collect();
            assert!(!is_bounded_safepoint_free_leaf(&body));
            body.basic_blocks[body.start_block].statements.clear();
            body.basic_blocks[body.start_block].terminator = Some(Terminator {
                kind: TerminatorKind::Goto {
                    target: body.start_block,
                },
                span,
            });
            assert!(!is_bounded_safepoint_free_leaf(&body));
            assert!(InsertSafepoints.run(gcx, &mut body).is_ok());
            assert!(verify_safepoint_cycle_coverage(&body).is_ok());
        });
    }

    #[test]
    fn safepoint_placement_covers_entry_and_every_cfg_cycle() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let span = body.locals[body.return_local].span;
            let loop_block = body.basic_blocks.push(BasicBlockData {
                note: Some("loop".into()),
                statements: Vec::new(),
                terminator: None,
            });
            body.basic_blocks[body.start_block].terminator = Some(Terminator {
                kind: TerminatorKind::Goto { target: loop_block },
                span,
            });
            body.basic_blocks[loop_block].terminator = Some(Terminator {
                kind: TerminatorKind::Goto { target: loop_block },
                span,
            });

            assert!(InsertSafepoints.run(gcx, &mut body).is_ok());

            assert!(matches!(
                body.basic_blocks[body.start_block].statements[0].kind,
                StatementKind::GcSafepoint(GcSafepointKind::Entry)
            ));
            assert!(matches!(
                body.basic_blocks[loop_block].statements[0].kind,
                StatementKind::GcSafepoint(GcSafepointKind::Loop)
            ));
            assert!(verify_safepoint_cycle_coverage(&body).is_ok());
        });
    }

    #[test]
    fn irreducible_cycles_remain_polled_after_ordinary_cfg_cleanup() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let span = body.locals[body.return_local].span;
            let left = body.basic_blocks.push(BasicBlockData {
                note: None,
                statements: vec![],
                terminator: None,
            });
            let right = body.basic_blocks.push(BasicBlockData {
                note: None,
                statements: vec![],
                terminator: None,
            });
            body.basic_blocks[body.start_block].terminator = Some(Terminator {
                span,
                kind: TerminatorKind::SwitchInt {
                    discr: Operand::Constant(crate::mir::Constant {
                        ty: gcx.types.bool,
                        value: crate::mir::ConstantKind::Bool(true),
                    }),
                    targets: vec![(0, left)],
                    otherwise: right,
                },
            });
            body.basic_blocks[left].terminator = Some(Terminator {
                span,
                kind: TerminatorKind::Goto { target: right },
            });
            body.basic_blocks[right].terminator = Some(Terminator {
                span,
                kind: TerminatorKind::Goto { target: left },
            });
            assert!(InsertSafepoints.run(gcx, &mut body).is_ok());
            assert!(verify_safepoint_cycle_coverage(&body).is_ok());
            use crate::mir::optimize::{
                coalesce::TempCoalescing, dse::DeadStoreElimination, passes::SimplifyCfg,
                propagate::CopyPropagation,
            };
            assert!(DeadStoreElimination.run(gcx, &mut body).is_ok());
            assert!(CopyPropagation.run(gcx, &mut body).is_ok());
            assert!(TempCoalescing.run(gcx, &mut body).is_ok());
            assert!(SimplifyCfg.run(gcx, &mut body).is_ok());
            merge_consecutive_safepoints(&mut body);
            assert!(verify_safepoint_cycle_coverage(&body).is_ok());
        });
    }

    #[test]
    fn safepoint_verifier_rejects_an_unpolled_cycle() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let span = body.locals[body.return_local].span;
            body.basic_blocks[body.start_block].terminator = Some(Terminator {
                kind: TerminatorKind::Goto {
                    target: body.start_block,
                },
                span,
            });

            assert_eq!(
                verify_safepoint_cycle_coverage(&body),
                Err(vec![body.start_block])
            );
        });
    }
}
