use crate::mir::{BasicBlockId, Body, LocalId, TerminatorKind};
use index_vec::IndexVec;

/// Collapse chains of empty blocks that only `goto`.
pub fn collapse_trivial_gotos(body: &mut Body<'_>) {
    let mut targets: IndexVec<BasicBlockId, Option<BasicBlockId>> =
        IndexVec::from(vec![None; body.basic_blocks.len()]);
    let mut path = Vec::new();
    for block in body.basic_blocks.indices() {
        let mut current = block;
        let target = loop {
            if let Some(target) = targets[current] {
                break target;
            }
            // A provisional self-target also detects cycles in the current
            // path. Once resolved, every node points straight to its target.
            targets[current] = Some(current);
            path.push(current);
            let data = &body.basic_blocks[current];
            match data.terminator.as_ref().map(|term| &term.kind) {
                Some(TerminatorKind::Goto { target }) if data.statements.is_empty() => {
                    current = *target;
                }
                _ => break current,
            }
        };
        for block in path.drain(..) {
            targets[block] = Some(target);
        }
    }

    for block in &mut body.basic_blocks {
        if let Some(term) = &mut block.terminator {
            term.kind
                .map_blocks(|target| targets[target].expect("resolved goto target"));
        }
    }
}

/// Merge a goto's target when the goto is its only incoming reference.
pub fn merge_linear_blocks(body: &mut Body<'_>) {
    let mut pred_count = vec![0usize; body.basic_blocks.len()];
    for block in &body.basic_blocks {
        if let Some(term) = &block.terminator {
            for target in term.kind.successors() {
                pred_count[target.index()] += 1;
            }
            if let TerminatorKind::Yield {
                cancel_complete, ..
            } = term.kind
            {
                // The cancellation marker must survive until async lowering,
                // even if its cleanup path diverges.
                pred_count[cancel_complete.index()] += 1;
            }
        }
    }
    pred_count[body.start_block.index()] += 1;

    for block in body.basic_blocks.indices() {
        loop {
            let Some(term) = &body.basic_blocks[block].terminator else {
                break;
            };
            let TerminatorKind::Goto { target } = term.kind else {
                break;
            };
            if target == block || pred_count[target.index()] != 1 {
                break;
            }
            let span = term.span;
            let statements = std::mem::take(&mut body.basic_blocks[target].statements);
            let terminator = body.basic_blocks[target]
                .terminator
                .replace(crate::mir::Terminator {
                    kind: TerminatorKind::Unreachable,
                    span,
                });
            body.basic_blocks[block].statements.extend(statements);
            body.basic_blocks[block].terminator = terminator;
            // Moving the target's outgoing references changes no other count.
            // Only this goto disappears; rescanning the whole CFG is unnecessary.
            pred_count[target.index()] = 0;
        }
    }
}

/// Remove unreachable blocks, retaining async cancellation marker references.
pub fn prune_unreachable_blocks(body: &mut Body<'_>) {
    let mut reachable = vec![false; body.basic_blocks.len()];
    let mut stack = vec![body.start_block];
    while let Some(block) = stack.pop() {
        if std::mem::replace(&mut reachable[block.index()], true) {
            continue;
        }
        if let Some(term) = &body.basic_blocks[block].terminator {
            stack.extend(term.kind.successors());
            if let TerminatorKind::Yield {
                cancel_complete, ..
            } = term.kind
            {
                // This is metadata, not a CFG edge. The transform still needs
                // the marker when a cleanup diverges before reaching it.
                stack.push(cancel_complete);
            }
        }
    }
    if reachable.iter().all(|&value| value) {
        return;
    }

    let mut remap: IndexVec<BasicBlockId, Option<BasicBlockId>> =
        IndexVec::from(vec![None; reachable.len()]);
    let mut blocks = IndexVec::new();
    for (old, data) in std::mem::take(&mut body.basic_blocks).into_iter_enumerated() {
        if reachable[old.index()] {
            remap[old] = Some(blocks.push(data));
        }
    }
    let remap_block = |block: BasicBlockId| remap[block].expect("reachable block must be remapped");
    for block in &mut blocks {
        if let Some(term) = &mut block.terminator {
            term.kind.map_blocks(remap_block);
        }
    }
    body.start_block = remap_block(body.start_block);
    body.basic_blocks = blocks;
}

/// Eliminate unused locals from the body.
/// This pass removes locals that are not used in the body.
pub fn eliminate_dead_locals(body: &mut Body<'_>) {
    use crate::mir::LocalKind;

    let num_locals = body.locals.len();
    let mut used = vec![false; num_locals];

    // Mark return local as always used
    used[body.return_local.index()] = true;

    // Mark param locals as always used
    for (local_id, local_decl) in body.locals.iter_enumerated() {
        if matches!(local_decl.kind, LocalKind::Param) {
            used[local_id.index()] = true;
        }
    }

    use crate::mir::{Operand, Place, Rvalue, StatementKind};

    // Helper to mark a place as used
    fn mark_place_used(place: &Place<'_>, used: &mut [bool]) {
        used[place.local.index()] = true;
    }

    // Helper to mark an operand as used
    fn mark_operand_used(op: &Operand<'_>, used: &mut [bool]) {
        if let Some(place) = op.place() {
            mark_place_used(place, used);
        }
    }

    // Helper to mark an rvalue as used
    fn mark_rvalue_used(rv: &Rvalue<'_>, used: &mut [bool]) {
        rv.for_each_place(|place| mark_place_used(place, used));
    }

    // Collect all used locals from statements and terminators
    for block in body.basic_blocks.iter() {
        for stmt in &block.statements {
            match &stmt.kind {
                StatementKind::Assign(dest, rv) => {
                    // Only mark destination as used if it has projections
                    // (the base local is read to compute the final address)
                    if !dest.projection.is_empty() {
                        mark_place_used(dest, &mut used);
                    }
                    mark_rvalue_used(rv, &mut used);
                }
                StatementKind::SetDiscriminant { place, .. } => {
                    if !place.projection.is_empty() {
                        mark_place_used(place, &mut used);
                    }
                }
                StatementKind::KeepAlive(operand) => mark_operand_used(operand, &mut used),
                StatementKind::SourceScope(_)
                | StatementKind::StorageLive(_)
                | StatementKind::SetInitialized(_)
                | StatementKind::GcSafepoint(_)
                | StatementKind::Nop => {}
            }
        }

        if let Some(term) = &block.terminator {
            match &term.kind {
                TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    ..
                } => {
                    mark_operand_used(func, &mut used);
                    for arg in args {
                        mark_operand_used(arg, &mut used);
                    }
                    // Call destinations must be kept
                    mark_place_used(destination, &mut used);
                }
                TerminatorKind::SwitchInt { discr, .. } => {
                    mark_operand_used(discr, &mut used);
                }
                TerminatorKind::Yield {
                    value, resume_arg, ..
                } => {
                    mark_operand_used(value, &mut used);
                    mark_place_used(resume_arg, &mut used);
                }
                TerminatorKind::Return => {
                    used[body.return_local.index()] = true;
                }
                TerminatorKind::Goto { .. }
                | TerminatorKind::ResumeUnwind
                | TerminatorKind::Unreachable
                | TerminatorKind::UnresolvedGoto => {}
            }
        }
    }

    // Check if all locals are used (no optimization needed)
    if used.iter().all(|&u| u) {
        return;
    }

    // Build remapping from old to new local indices
    let mut remap: IndexVec<LocalId, Option<LocalId>> = IndexVec::from(vec![None; num_locals]);
    let mut new_locals = IndexVec::new();
    let mut new_escape_locals = Vec::new();

    for (old_id, local_decl) in body.locals.iter_enumerated() {
        if used[old_id.index()] {
            let new_id = new_locals.push(local_decl.clone());
            if old_id.index() < body.escape_locals.len() {
                new_escape_locals.push(body.escape_locals[old_id.index()]);
            } else {
                new_escape_locals.push(false);
            }
            remap[old_id] = Some(new_id);
        }
    }

    let remap_place = |place: &mut Place<'_>| {
        place.local = remap[place.local].expect("used local must be remapped");
    };
    let remap_operand = |operand: &mut Operand<'_>| {
        if let Some(place) = operand.place_mut() {
            remap_place(place);
        }
    };

    for block in &mut body.basic_blocks {
        for stmt in &mut block.statements {
            match &mut stmt.kind {
                StatementKind::StorageLive(local) | StatementKind::SetInitialized(local) => {
                    if let Some(new_local) = remap[*local] {
                        *local = new_local;
                    } else {
                        stmt.kind = StatementKind::Nop;
                    }
                }
                StatementKind::Assign(dest, rv) => {
                    if let Some(new_local) = remap[dest.local] {
                        dest.local = new_local;
                        rv.for_each_place_mut(remap_place);
                    } else {
                        stmt.kind = StatementKind::Nop;
                    }
                }
                StatementKind::SetDiscriminant { place, .. } => {
                    if let Some(new_local) = remap[place.local] {
                        place.local = new_local;
                    } else {
                        stmt.kind = StatementKind::Nop;
                    }
                }
                StatementKind::KeepAlive(operand) => remap_operand(operand),
                StatementKind::SourceScope(_)
                | StatementKind::GcSafepoint(_)
                | StatementKind::Nop => {}
            }
        }

        if let Some(term) = &mut block.terminator {
            match &mut term.kind {
                TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    devirt_hint,
                    ..
                } => {
                    remap_operand(func);
                    args.iter_mut().for_each(remap_operand);
                    remap_place(destination);
                    *devirt_hint = None;
                }
                TerminatorKind::SwitchInt { discr, .. } => remap_operand(discr),
                TerminatorKind::Yield {
                    value, resume_arg, ..
                } => {
                    remap_operand(value);
                    remap_place(resume_arg);
                }
                TerminatorKind::Goto { .. }
                | TerminatorKind::Return
                | TerminatorKind::ResumeUnwind
                | TerminatorKind::Unreachable
                | TerminatorKind::UnresolvedGoto => {}
            }
        }
    }

    // Update body
    body.locals = new_locals;
    body.escape_locals = new_escape_locals;
    body.return_local = remap[body.return_local].expect("return local must be used");
}

/// Merge consecutive gc_safepoint statements within each basic block.
/// Multiple consecutive safepoints are redundant - only one is needed.
pub fn merge_consecutive_safepoints(body: &mut Body<'_>) {
    use crate::mir::StatementKind;

    for block in body.basic_blocks.iter_mut() {
        let mut prev_was_safepoint = false;
        block.statements.retain(|stmt| {
            let is_safepoint = matches!(stmt.kind, StatementKind::GcSafepoint(_));
            let keep = !is_safepoint || !prev_was_safepoint;
            prev_was_safepoint = is_safepoint;
            keep
        });
    }
}

#[cfg(test)]
mod tests {
    use crate::mir::{
        BasicBlockData, Operand, Place, Terminator, TerminatorKind,
        optimize::{MirPass, passes::SimplifyCfg},
        test_support::{minimal_body, with_test_gcx},
    };

    #[test]
    fn cfg_cleanup_preserves_and_remaps_a_diverging_cancellation_marker() {
        use crate::mir::{BasicBlockId, CallUnwindAction};
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let span = body.locals[body.return_local].span;
            let push = |body: &mut crate::mir::Body<'_>, kind| {
                body.basic_blocks.push(BasicBlockData {
                    note: None,
                    statements: Vec::new(),
                    terminator: Some(Terminator { kind, span }),
                })
            };
            let _dead = push(&mut body, TerminatorKind::Unreachable);
            let resume = push(&mut body, TerminatorKind::Return);
            let cancel = push(&mut body, TerminatorKind::Unreachable);
            let cancel_complete = push(&mut body, TerminatorKind::Return);
            body.basic_blocks[body.start_block].terminator = Some(Terminator {
                kind: TerminatorKind::Yield {
                    value: Operand::Copy(Place::from_local(body.return_local)),
                    resume,
                    resume_arg: Place::from_local(body.return_local),
                    cancel,
                    cancel_complete,
                    unwind: CallUnwindAction::Cleanup(cancel),
                },
                span,
            });

            assert!(SimplifyCfg.run(gcx, &mut body).is_ok());

            assert_eq!(body.basic_blocks.len(), 4);
            let TerminatorKind::Yield {
                resume,
                cancel,
                cancel_complete,
                unwind,
                ..
            } = &body.basic_blocks[body.start_block]
                .terminator
                .as_ref()
                .unwrap()
                .kind
            else {
                panic!("expected yield");
            };
            assert_eq!(*resume, BasicBlockId::from_raw(1));
            assert_eq!(*cancel, BasicBlockId::from_raw(2));
            assert_eq!(*cancel_complete, BasicBlockId::from_raw(3));
            assert_eq!(*unwind, CallUnwindAction::Cleanup(*cancel));
            assert!(matches!(
                body.basic_blocks[*cancel_complete]
                    .terminator
                    .as_ref()
                    .unwrap()
                    .kind,
                TerminatorKind::Return
            ));
        });
    }

    #[test]
    fn simplify_cfg_terminates_on_a_goto_cycle_with_multiple_entries() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let span = body.locals[body.return_local].span;
            let first = body.basic_blocks.push(BasicBlockData {
                note: None,
                statements: Vec::new(),
                terminator: None,
            });
            let second = body.basic_blocks.push(BasicBlockData {
                note: None,
                statements: Vec::new(),
                terminator: Some(Terminator {
                    kind: TerminatorKind::Goto { target: first },
                    span,
                }),
            });
            body.basic_blocks[first].terminator = Some(Terminator {
                kind: TerminatorKind::Goto { target: second },
                span,
            });
            body.basic_blocks[body.start_block].terminator = Some(Terminator {
                kind: TerminatorKind::SwitchInt {
                    discr: Operand::Copy(Place::from_local(body.return_local)),
                    targets: vec![(0, first)],
                    otherwise: second,
                },
                span,
            });

            assert!(SimplifyCfg.run(gcx, &mut body).is_ok());

            assert_eq!(body.basic_blocks.len(), 2);
            let TerminatorKind::SwitchInt {
                targets, otherwise, ..
            } = &body.basic_blocks[body.start_block]
                .terminator
                .as_ref()
                .unwrap()
                .kind
            else {
                panic!("expected entry switch");
            };
            assert_eq!(targets[0].1, *otherwise);
            assert!(
                matches!(body.basic_blocks[*otherwise].terminator.as_ref().unwrap().kind,
                TerminatorKind::Goto { target } if target == *otherwise)
            );
        });
    }
}
