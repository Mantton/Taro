use crate::mir::{BasicBlockId, Body, LocalId, TerminatorKind};
use index_vec::IndexVec;
use rustc_hash::FxHashMap;

/// Collapse chains of empty blocks that only `goto`.
pub fn collapse_trivial_gotos(body: &mut Body<'_>) {
    fn collapse_target(
        body: &Body<'_>,
        bb: BasicBlockId,
        cache: &mut FxHashMap<BasicBlockId, BasicBlockId>,
    ) -> BasicBlockId {
        if let Some(&cached) = cache.get(&bb) {
            return cached;
        }
        let mut cur = bb;
        loop {
            let block = &body.basic_blocks[cur];
            match block.terminator.as_ref().map(|t| &t.kind) {
                Some(TerminatorKind::Goto { target })
                    if block.statements.is_empty() && *target != cur =>
                {
                    cur = *target;
                    continue;
                }
                _ => break,
            }
        }
        cache.insert(bb, cur);
        cur
    }

    let mut cache: FxHashMap<BasicBlockId, BasicBlockId> = FxHashMap::default();
    for bb in body.basic_blocks.indices() {
        let _ = collapse_target(body, bb, &mut cache);
    }

    for block in body.basic_blocks.iter_mut() {
        if let Some(term) = block.terminator.as_mut() {
            match &mut term.kind {
                TerminatorKind::Goto { target } => *target = *cache.get(target).unwrap_or(target),
                TerminatorKind::SwitchInt {
                    targets, otherwise, ..
                } => {
                    *otherwise = *cache.get(otherwise).unwrap_or(otherwise);
                    for (_, t) in targets {
                        *t = *cache.get(t).unwrap_or(t);
                    }
                }
                TerminatorKind::Call { target, .. } => {
                    *target = *cache.get(target).unwrap_or(target);
                }
                _ => {}
            }
        }
    }
}

/// Merge linear chains of blocks where a block has a single successor via goto
/// and that successor has only one predecessor. This handles non-empty blocks too.
pub fn merge_linear_blocks(body: &mut Body<'_>) {
    // First, count predecessors for each block
    let mut pred_count = vec![0usize; body.basic_blocks.len()];

    for block in body.basic_blocks.iter() {
        if let Some(term) = &block.terminator {
            match &term.kind {
                TerminatorKind::Goto { target } => {
                    pred_count[target.index()] += 1;
                }
                TerminatorKind::SwitchInt {
                    targets, otherwise, ..
                } => {
                    pred_count[otherwise.index()] += 1;
                    for (_, t) in targets {
                        pred_count[t.index()] += 1;
                    }
                }
                TerminatorKind::Call { target, .. } => {
                    pred_count[target.index()] += 1;
                }
                _ => {}
            }
        }
    }

    // Entry block has an implicit predecessor
    pred_count[body.start_block.index()] += 1;

    // Find merge opportunities: block ends with goto, target has single pred
    let mut merged = true;
    while merged {
        merged = false;

        for bb_id in body.basic_blocks.indices() {
            let block = &body.basic_blocks[bb_id];

            // Check if this block ends with a goto
            let (target, old_span) = match block.terminator.as_ref() {
                Some(term) => match &term.kind {
                    TerminatorKind::Goto { target } => (*target, term.span),
                    _ => continue,
                },
                None => continue,
            };

            // Don't merge with self
            if target == bb_id {
                continue;
            }

            // Target must have exactly one predecessor (this block)
            if pred_count[target.index()] != 1 {
                continue;
            }

            // Merge: append target's statements and terminator to this block
            let target_block = body.basic_blocks[target].clone();
            let current_block = &mut body.basic_blocks[bb_id];

            current_block.statements.extend(target_block.statements);
            current_block.terminator = target_block.terminator;
            // Keep the note from the original block if it has one

            // Mark target as merged (clear it and make unreachable)
            body.basic_blocks[target].statements.clear();
            body.basic_blocks[target].terminator = Some(crate::mir::Terminator {
                kind: TerminatorKind::Unreachable,
                span: old_span,
            });

            merged = true;
            break; // Restart to recompute pred counts
        }

        if merged {
            // Recompute pred counts
            pred_count = vec![0usize; body.basic_blocks.len()];
            for block in body.basic_blocks.iter() {
                if let Some(term) = &block.terminator {
                    match &term.kind {
                        TerminatorKind::Goto { target } => {
                            pred_count[target.index()] += 1;
                        }
                        TerminatorKind::SwitchInt {
                            targets, otherwise, ..
                        } => {
                            pred_count[otherwise.index()] += 1;
                            for (_, t) in targets {
                                pred_count[t.index()] += 1;
                            }
                        }
                        TerminatorKind::Call { target, .. } => {
                            pred_count[target.index()] += 1;
                        }
                        _ => {}
                    }
                }
            }
            pred_count[body.start_block.index()] += 1;
        }
    }
}

/// Remove unreachable blocks from the body.
pub fn prune_unreachable_blocks(body: &mut Body<'_>) {
    let mut reachable = vec![false; body.basic_blocks.len()];
    let mut stack = vec![body.start_block];

    while let Some(bb) = stack.pop() {
        if reachable[bb.index()] {
            continue;
        }
        reachable[bb.index()] = true;
        if let Some(term) = &body.basic_blocks[bb].terminator {
            match &term.kind {
                TerminatorKind::Goto { target } => stack.push(*target),
                TerminatorKind::SwitchInt {
                    targets, otherwise, ..
                } => {
                    stack.push(*otherwise);
                    for (_, t) in targets {
                        stack.push(*t);
                    }
                }
                TerminatorKind::Call { target, .. } => stack.push(*target),
                TerminatorKind::Return
                | TerminatorKind::Unreachable
                | TerminatorKind::UnresolvedGoto => {}
            }
        }
    }

    if reachable.iter().all(|&r| r) {
        return;
    }

    let mut remap: IndexVec<BasicBlockId, Option<BasicBlockId>> =
        IndexVec::from(vec![None; reachable.len()]);
    let mut new_blocks = IndexVec::new();

    for (old, data) in body.basic_blocks.iter_enumerated() {
        if reachable[old.index()] {
            let new = new_blocks.push(data.clone());
            remap[old] = Some(new);
        }
    }

    let remap_bb = |bb: BasicBlockId| remap[bb].expect("reachable block must be remapped");

    for block in new_blocks.iter_mut() {
        if let Some(term) = block.terminator.as_mut() {
            match &mut term.kind {
                TerminatorKind::Goto { target } => *target = remap_bb(*target),
                TerminatorKind::SwitchInt {
                    targets, otherwise, ..
                } => {
                    *otherwise = remap_bb(*otherwise);
                    for (_, t) in targets {
                        *t = remap_bb(*t);
                    }
                }
                TerminatorKind::Call { target, .. } => *target = remap_bb(*target),
                TerminatorKind::Return
                | TerminatorKind::Unreachable
                | TerminatorKind::UnresolvedGoto => {}
            }
        }
    }

    body.start_block = remap_bb(body.start_block);
    body.basic_blocks = new_blocks;
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
        match op {
            Operand::Copy(place) | Operand::Move(place) => mark_place_used(place, used),
            Operand::Constant(_) => {}
        }
    }

    // Helper to mark an rvalue as used
    fn mark_rvalue_used(rv: &Rvalue<'_>, used: &mut [bool]) {
        match rv {
            Rvalue::Use(op) => mark_operand_used(op, used),
            Rvalue::UnaryOp { operand, .. } => mark_operand_used(operand, used),
            Rvalue::BinaryOp { lhs, rhs, .. } => {
                mark_operand_used(lhs, used);
                mark_operand_used(rhs, used);
            }
            Rvalue::Cast { operand, .. } => mark_operand_used(operand, used),
            Rvalue::Aggregate { fields, .. } => {
                for field in fields.iter() {
                    mark_operand_used(field, used);
                }
            }
            Rvalue::Ref { place, .. } => mark_place_used(place, used),
            Rvalue::Discriminant { place } => mark_place_used(place, used),
            Rvalue::Alloc { .. } => {}
            Rvalue::Repeat { operand, .. } => mark_operand_used(operand, used),
        }
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
                StatementKind::GcSafepoint | StatementKind::Nop => {}
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
                TerminatorKind::Return => {
                    used[body.return_local.index()] = true;
                }
                TerminatorKind::Goto { .. }
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

    // Remap locals in places
    fn remap_place<'ctx>(
        place: &Place<'ctx>,
        remap: &IndexVec<LocalId, Option<LocalId>>,
    ) -> Place<'ctx> {
        if let Some(new_local) = remap[place.local] {
            Place {
                local: new_local,
                projection: place.projection.clone(),
            }
        } else {
            panic!(
                "used local {:?} must be remapped. Place: {:?}",
                place.local, place
            );
        }
    }

    fn remap_operand<'ctx>(
        op: &Operand<'ctx>,
        remap: &IndexVec<LocalId, Option<LocalId>>,
    ) -> Operand<'ctx> {
        match op {
            Operand::Copy(place) => Operand::Copy(remap_place(place, remap)),
            Operand::Move(place) => Operand::Move(remap_place(place, remap)),
            Operand::Constant(c) => Operand::Constant(c.clone()),
        }
    }

    fn remap_rvalue<'ctx>(
        rv: &Rvalue<'ctx>,
        remap: &IndexVec<LocalId, Option<LocalId>>,
    ) -> Rvalue<'ctx> {
        match rv {
            Rvalue::Use(op) => Rvalue::Use(remap_operand(op, remap)),
            Rvalue::UnaryOp { op, operand } => Rvalue::UnaryOp {
                op: *op,
                operand: remap_operand(operand, remap),
            },
            Rvalue::BinaryOp { op, lhs, rhs } => Rvalue::BinaryOp {
                op: *op,
                lhs: remap_operand(lhs, remap),
                rhs: remap_operand(rhs, remap),
            },
            Rvalue::Cast { operand, ty, kind } => Rvalue::Cast {
                operand: remap_operand(operand, remap),
                ty: *ty,
                kind: *kind,
            },
            Rvalue::Aggregate { kind, fields } => Rvalue::Aggregate {
                kind: kind.clone(),
                fields: fields.iter().map(|f| remap_operand(f, remap)).collect(),
            },
            Rvalue::Ref { mutable, place } => Rvalue::Ref {
                mutable: *mutable,
                place: remap_place(place, remap),
            },
            Rvalue::Discriminant { place } => Rvalue::Discriminant {
                place: remap_place(place, remap),
            },
            Rvalue::Alloc { ty } => Rvalue::Alloc { ty: *ty },
            Rvalue::Repeat {
                operand,
                count,
                element,
            } => Rvalue::Repeat {
                operand: remap_operand(operand, remap),
                count: *count,
                element: *element,
            },
        }
    }

    // Remap all statements and terminators
    for block in body.basic_blocks.iter_mut() {
        for stmt in block.statements.iter_mut() {
            stmt.kind = match &stmt.kind {
                StatementKind::Assign(dest, rv) => {
                    if let Some(new_local) = remap[dest.local] {
                        StatementKind::Assign(
                            Place {
                                local: new_local,
                                projection: dest.projection.clone(),
                            },
                            remap_rvalue(rv, &remap),
                        )
                    } else {
                        StatementKind::Nop
                    }
                }
                StatementKind::SetDiscriminant {
                    place,
                    variant_index,
                } => {
                    if let Some(new_local) = remap[place.local] {
                        StatementKind::SetDiscriminant {
                            place: Place {
                                local: new_local,
                                projection: place.projection.clone(),
                            },
                            variant_index: *variant_index,
                        }
                    } else {
                        StatementKind::Nop
                    }
                }
                StatementKind::GcSafepoint => StatementKind::GcSafepoint,
                StatementKind::Nop => StatementKind::Nop,
            };
        }

        if let Some(term) = block.terminator.as_mut() {
            term.kind = match &term.kind {
                TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    target,
                } => TerminatorKind::Call {
                    func: remap_operand(func, &remap),
                    args: args.iter().map(|a| remap_operand(a, &remap)).collect(),
                    destination: remap_place(destination, &remap),
                    target: *target,
                },
                TerminatorKind::SwitchInt {
                    discr,
                    targets,
                    otherwise,
                } => TerminatorKind::SwitchInt {
                    discr: remap_operand(discr, &remap),
                    targets: targets.clone(),
                    otherwise: *otherwise,
                },
                TerminatorKind::Goto { target } => TerminatorKind::Goto { target: *target },
                TerminatorKind::Return => TerminatorKind::Return,
                TerminatorKind::Unreachable => TerminatorKind::Unreachable,
                TerminatorKind::UnresolvedGoto => TerminatorKind::UnresolvedGoto,
            };
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
        let mut new_statements = Vec::with_capacity(block.statements.len());
        let mut prev_was_safepoint = false;

        for stmt in block.statements.drain(..) {
            let is_safepoint = matches!(stmt.kind, StatementKind::GcSafepoint);

            if is_safepoint && prev_was_safepoint {
                // Skip consecutive safepoint
                continue;
            }

            prev_was_safepoint = is_safepoint;
            new_statements.push(stmt);
        }

        block.statements = new_statements;
    }
}
