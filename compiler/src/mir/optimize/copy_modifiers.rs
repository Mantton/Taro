use super::MirPass;
use crate::compile::context::Gcx;
use crate::error::CompileResult;
use crate::mir::analysis::liveness::compute_liveness;
use crate::mir::{
    BasicBlockId, Body, CallUnwindAction, LocalId, LocalKind, Operand, Place, Rvalue, Statement,
    StatementKind, TerminatorKind,
};
use index_vec::IndexVec;
use rustc_hash::FxHashSet;

/// Marks conservative copy modifiers on MIR copy operands:
/// - `[init]` when a destination is definitely not assigned on any incoming path.
/// - `[take]` when a source local is dead immediately after the copy site.
pub struct MarkCopyModifiers;

impl<'ctx> MirPass<'ctx> for MarkCopyModifiers {
    fn name(&self) -> &'static str {
        "MarkCopyModifiers"
    }

    fn run(&mut self, _gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
        let liveness = compute_liveness(body);
        let may_assigned_in = compute_may_assigned_in(body);
        let init_candidates = compute_init_candidates(body, &may_assigned_in);
        let take_blocked = compute_take_blocked_locals(body);
        let local_kinds: Vec<LocalKind> = body.locals.iter().map(|decl| decl.kind).collect();

        for bb in body.basic_blocks.indices() {
            let mut live = liveness.live_out[bb].clone();
            if let Some(term) = body.basic_blocks[bb].terminator.as_ref() {
                apply_terminator_liveness(body.return_local, &term.kind, &mut live);
            }

            let stmt_len = body.basic_blocks[bb].statements.len();
            for stmt_index in (0..stmt_len).rev() {
                let live_after = live.clone();
                let init_candidate = init_candidates[bb][stmt_index];
                let stmt = &mut body.basic_blocks[bb].statements[stmt_index];

                maybe_mark_statement_copy_modifiers(
                    stmt,
                    init_candidate,
                    &live_after,
                    &take_blocked,
                    &local_kinds,
                );

                apply_statement_liveness(stmt, &mut live);
            }
        }

        Ok(())
    }
}

fn maybe_mark_statement_copy_modifiers<'ctx>(
    stmt: &mut Statement<'ctx>,
    init_candidate: bool,
    live_after: &FxHashSet<LocalId>,
    take_blocked: &[bool],
    local_kinds: &[LocalKind],
) {
    let StatementKind::Assign(destination, rvalue) = &mut stmt.kind else {
        return;
    };
    let Rvalue::Use(operand) = rvalue else {
        return;
    };
    let Some((source, current_modifiers)) = operand.as_copy() else {
        return;
    };

    let mut new_modifiers = current_modifiers;
    if init_candidate {
        new_modifiers.init = true;
    }

    let source_local = source.local;
    let can_take = source.projection.is_empty()
        && destination.projection.is_empty()
        && source_local != destination.local
        && !take_blocked[source_local.index()]
        && !matches!(local_kinds[source_local.index()], LocalKind::Param)
        && !live_after.contains(&source_local);
    if can_take {
        new_modifiers.take = true;
    }

    if new_modifiers != current_modifiers {
        *operand = Operand::copy_with(source.clone(), new_modifiers);
    }
}

fn compute_init_candidates<'ctx>(
    body: &Body<'ctx>,
    may_assigned_in: &IndexVec<BasicBlockId, FxHashSet<LocalId>>,
) -> IndexVec<BasicBlockId, Vec<bool>> {
    let mut out: IndexVec<BasicBlockId, Vec<bool>> =
        IndexVec::from(vec![Vec::new(); body.basic_blocks.len()]);

    for bb in body.basic_blocks.indices() {
        let block = &body.basic_blocks[bb];
        let mut may_assigned = may_assigned_in[bb].clone();
        let mut flags = Vec::with_capacity(block.statements.len());

        for stmt in &block.statements {
            let is_init = match &stmt.kind {
                StatementKind::Assign(destination, _) => {
                    destination.projection.is_empty()
                        && !may_assigned.contains(&destination.local)
                        && !matches!(body.locals[destination.local].kind, LocalKind::Param)
                }
                _ => false,
            };
            flags.push(is_init);
            apply_statement_defs(stmt, &mut may_assigned);
        }

        out[bb] = flags;
    }

    out
}

fn compute_may_assigned_in(body: &Body<'_>) -> IndexVec<BasicBlockId, FxHashSet<LocalId>> {
    let mut in_sets: IndexVec<BasicBlockId, FxHashSet<LocalId>> =
        IndexVec::from(vec![FxHashSet::default(); body.basic_blocks.len()]);
    let mut out_sets: IndexVec<BasicBlockId, FxHashSet<LocalId>> =
        IndexVec::from(vec![FxHashSet::default(); body.basic_blocks.len()]);

    let preds = build_predecessors(body);
    let succs = build_successors(body);
    let mut entry_seed = FxHashSet::default();
    for (local_id, decl) in body.locals.iter_enumerated() {
        if matches!(decl.kind, LocalKind::Param) {
            entry_seed.insert(local_id);
        }
    }

    let mut worklist: Vec<BasicBlockId> = body.basic_blocks.indices().collect();
    while let Some(bb) = worklist.pop() {
        let mut new_in = FxHashSet::default();
        if bb == body.start_block {
            for &local in &entry_seed {
                new_in.insert(local);
            }
        }
        for &pred in &preds[bb] {
            for &local in &out_sets[pred] {
                new_in.insert(local);
            }
        }

        let mut new_out = new_in.clone();
        for stmt in &body.basic_blocks[bb].statements {
            apply_statement_defs(stmt, &mut new_out);
        }
        if let Some(term) = &body.basic_blocks[bb].terminator {
            apply_terminator_defs(&term.kind, &mut new_out);
        }

        let changed = new_in != in_sets[bb] || new_out != out_sets[bb];
        if changed {
            in_sets[bb] = new_in;
            out_sets[bb] = new_out;
            for &succ in &succs[bb] {
                worklist.push(succ);
            }
        }
    }

    in_sets
}

fn compute_take_blocked_locals(body: &Body<'_>) -> Vec<bool> {
    let mut blocked = vec![false; body.locals.len()];

    for (local_id, decl) in body.locals.iter_enumerated() {
        if matches!(decl.kind, LocalKind::Param) {
            blocked[local_id.index()] = true;
        }
    }

    for block in body.basic_blocks.iter() {
        for stmt in &block.statements {
            match &stmt.kind {
                StatementKind::Assign(destination, rvalue) => {
                    if !destination.projection.is_empty() {
                        blocked[destination.local.index()] = true;
                    }
                    mark_rvalue_take_blockers(rvalue, &mut blocked);
                }
                StatementKind::ShadowResync(locals) => {
                    for &local in locals {
                        blocked[local.index()] = true;
                    }
                }
                StatementKind::SetDiscriminant { place, .. } => {
                    if !place.projection.is_empty() {
                        blocked[place.local.index()] = true;
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
                    mark_operand_take_blocker(func, &mut blocked);
                    for arg in args {
                        mark_operand_take_blocker(arg, &mut blocked);
                    }
                    if !destination.projection.is_empty() {
                        blocked[destination.local.index()] = true;
                    }
                }
                TerminatorKind::SwitchInt { discr, .. } => {
                    mark_operand_take_blocker(discr, &mut blocked);
                }
                TerminatorKind::Yield {
                    value, resume_arg, ..
                } => {
                    mark_operand_take_blocker(value, &mut blocked);
                    if !resume_arg.projection.is_empty() {
                        blocked[resume_arg.local.index()] = true;
                    }
                }
                TerminatorKind::Goto { .. }
                | TerminatorKind::UnresolvedGoto
                | TerminatorKind::Return
                | TerminatorKind::ResumeUnwind
                | TerminatorKind::Unreachable => {}
            }
        }
    }

    blocked
}

fn mark_rvalue_take_blockers(rvalue: &Rvalue<'_>, blocked: &mut [bool]) {
    match rvalue {
        Rvalue::Use(op)
        | Rvalue::UnaryOp { operand: op, .. }
        | Rvalue::Cast { operand: op, .. } => mark_operand_take_blocker(op, blocked),
        Rvalue::BinaryOp { lhs, rhs, .. } => {
            mark_operand_take_blocker(lhs, blocked);
            mark_operand_take_blocker(rhs, blocked);
        }
        Rvalue::Ref { place, .. } => {
            // Address-taken locals are not safe for take invalidation.
            blocked[place.local.index()] = true;
        }
        Rvalue::Discriminant { place } => {
            if !place.projection.is_empty() {
                blocked[place.local.index()] = true;
            }
        }
        Rvalue::Aggregate { fields, .. } => {
            for field in fields {
                mark_operand_take_blocker(field, blocked);
            }
        }
        Rvalue::Repeat { operand, .. } => mark_operand_take_blocker(operand, blocked),
        Rvalue::Alloc { .. } => {}
    }
}

fn mark_operand_take_blocker(operand: &Operand<'_>, blocked: &mut [bool]) {
    let Some((place, _)) = operand.as_copy() else {
        return;
    };
    if !place.projection.is_empty() {
        blocked[place.local.index()] = true;
    }
}

fn apply_statement_defs(stmt: &Statement<'_>, may_assigned: &mut FxHashSet<LocalId>) {
    match &stmt.kind {
        StatementKind::Assign(destination, _) => {
            if destination.projection.is_empty() {
                may_assigned.insert(destination.local);
            }
        }
        StatementKind::SetDiscriminant { place, .. } => {
            if place.projection.is_empty() {
                may_assigned.insert(place.local);
            }
        }
        StatementKind::ShadowResync(_) | StatementKind::GcSafepoint | StatementKind::Nop => {}
    }
}

fn apply_terminator_defs(term: &TerminatorKind<'_>, may_assigned: &mut FxHashSet<LocalId>) {
    if let TerminatorKind::Call { destination, .. } = term {
        if destination.projection.is_empty() {
            may_assigned.insert(destination.local);
        }
    }
}

fn build_predecessors(body: &Body<'_>) -> IndexVec<BasicBlockId, Vec<BasicBlockId>> {
    let mut preds: IndexVec<BasicBlockId, Vec<BasicBlockId>> =
        IndexVec::from(vec![Vec::new(); body.basic_blocks.len()]);
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        if let Some(term) = &data.terminator {
            for succ in terminator_successors(&term.kind) {
                preds[succ].push(bb);
            }
        }
    }
    preds
}

fn build_successors(body: &Body<'_>) -> IndexVec<BasicBlockId, Vec<BasicBlockId>> {
    let mut succs: IndexVec<BasicBlockId, Vec<BasicBlockId>> =
        IndexVec::from(vec![Vec::new(); body.basic_blocks.len()]);
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        if let Some(term) = &data.terminator {
            succs[bb] = terminator_successors(&term.kind);
        }
    }
    succs
}

fn terminator_successors(term: &TerminatorKind<'_>) -> Vec<BasicBlockId> {
    match term {
        TerminatorKind::Goto { target } => vec![*target],
        TerminatorKind::SwitchInt {
            targets, otherwise, ..
        } => {
            let mut out = Vec::with_capacity(targets.len() + 1);
            for (_, bb) in targets {
                out.push(*bb);
            }
            out.push(*otherwise);
            out
        }
        TerminatorKind::Call { target, unwind, .. } => {
            let mut out = vec![*target];
            if let CallUnwindAction::Cleanup(bb) = unwind {
                out.push(*bb);
            }
            out
        }
        TerminatorKind::Yield { resume, .. } => vec![*resume],
        TerminatorKind::Return
        | TerminatorKind::ResumeUnwind
        | TerminatorKind::Unreachable
        | TerminatorKind::UnresolvedGoto => Vec::new(),
    }
}

fn apply_terminator_liveness(
    return_local: LocalId,
    term: &TerminatorKind<'_>,
    live: &mut FxHashSet<LocalId>,
) {
    match term {
        TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } => {
            if destination.projection.is_empty() {
                live.remove(&destination.local);
            } else {
                use_place(destination, live);
            }
            use_operand(func, live);
            for arg in args {
                use_operand(arg, live);
            }
        }
        TerminatorKind::SwitchInt { discr, .. } => use_operand(discr, live),
        TerminatorKind::Yield {
            value, resume_arg, ..
        } => {
            if resume_arg.projection.is_empty() {
                live.remove(&resume_arg.local);
            } else {
                use_place(resume_arg, live);
            }
            use_operand(value, live);
        }
        TerminatorKind::Return => {
            live.insert(return_local);
        }
        TerminatorKind::Goto { .. }
        | TerminatorKind::UnresolvedGoto
        | TerminatorKind::ResumeUnwind
        | TerminatorKind::Unreachable => {}
    }
}

fn apply_statement_liveness(stmt: &Statement<'_>, live: &mut FxHashSet<LocalId>) {
    match &stmt.kind {
        StatementKind::Assign(destination, rvalue) => {
            if destination.projection.is_empty() {
                live.remove(&destination.local);
            } else {
                use_place(destination, live);
            }
            use_rvalue(rvalue, live);
        }
        StatementKind::ShadowResync(locals) => {
            for &local in locals {
                live.insert(local);
            }
        }
        StatementKind::SetDiscriminant { place, .. } => {
            if !place.projection.is_empty() {
                use_place(place, live);
            }
        }
        StatementKind::GcSafepoint | StatementKind::Nop => {}
    }
}

fn use_rvalue(rvalue: &Rvalue<'_>, live: &mut FxHashSet<LocalId>) {
    match rvalue {
        Rvalue::Use(op)
        | Rvalue::UnaryOp { operand: op, .. }
        | Rvalue::Cast { operand: op, .. } => use_operand(op, live),
        Rvalue::BinaryOp { lhs, rhs, .. } => {
            use_operand(lhs, live);
            use_operand(rhs, live);
        }
        Rvalue::Ref { place, .. } | Rvalue::Discriminant { place } => use_place(place, live),
        Rvalue::Aggregate { fields, .. } => {
            for field in fields {
                use_operand(field, live);
            }
        }
        Rvalue::Repeat { operand, .. } => use_operand(operand, live),
        Rvalue::Alloc { .. } => {}
    }
}

fn use_operand(operand: &Operand<'_>, live: &mut FxHashSet<LocalId>) {
    if let Some((place, _)) = operand.as_copy() {
        use_place(place, live);
    }
}

fn use_place(place: &Place<'_>, live: &mut FxHashSet<LocalId>) {
    live.insert(place.local);
}
