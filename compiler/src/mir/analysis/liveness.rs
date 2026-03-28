use crate::mir::{BasicBlockId, Body, CallUnwindAction, LocalId, StatementKind, TerminatorKind};
use index_vec::IndexVec;
use rustc_hash::FxHashSet;

/// Result of liveness analysis.
pub struct LivenessResult {
    /// Variables live at the entry of each block.
    pub live_in: IndexVec<BasicBlockId, FxHashSet<LocalId>>,
    /// Variables live at the exit of each block.
    pub live_out: IndexVec<BasicBlockId, FxHashSet<LocalId>>,
}

/// Compute liveness for the given body.
/// Uses a backward dataflow analysis.
pub fn compute_liveness(body: &Body<'_>) -> LivenessResult {
    let preds = build_predecessors(body);
    let mut live_in = IndexVec::from(vec![FxHashSet::default(); body.basic_blocks.len()]);
    let mut live_out = IndexVec::from(vec![FxHashSet::default(); body.basic_blocks.len()]);
    let mut worklist: Vec<BasicBlockId> = body.basic_blocks.indices().collect();

    // Iterate to a predecessor-driven fixpoint.
    while let Some(bb) = worklist.pop() {
        // Compute live_out = Union(live_in(succ))
        let mut out_set = FxHashSet::default();
        if let Some(term) = &body.basic_blocks[bb].terminator {
            for succ in successors(&term.kind) {
                for &local in &live_in[succ] {
                    out_set.insert(local);
                }
            }
        }
        live_out[bb] = out_set.clone();

        // Compute live_in based on live_out and block contents
        let mut in_set = out_set;

        let block = &body.basic_blocks[bb];

        // Terminator
        if let Some(term) = &block.terminator {
            match &term.kind {
                TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    ..
                } => {
                    use_operand(func, &mut in_set);
                    for arg in args {
                        use_operand(arg, &mut in_set);
                    }
                    if destination.projection.is_empty() {
                        in_set.remove(&destination.local);
                    } else {
                        use_place(destination, &mut in_set);
                    }
                }
                TerminatorKind::SwitchInt { discr, .. } => use_operand(discr, &mut in_set),
                TerminatorKind::Yield {
                    value, resume_arg, ..
                } => {
                    use_operand(value, &mut in_set);
                    if resume_arg.projection.is_empty() {
                        in_set.remove(&resume_arg.local);
                    } else {
                        use_place(resume_arg, &mut in_set);
                    }
                }
                TerminatorKind::Return => {
                    in_set.insert(body.return_local);
                }
                _ => {}
            }
        }

        // Statements
        for stmt in block.statements.iter().rev() {
            match &stmt.kind {
                StatementKind::Assign(dest, rvalue) => {
                    if dest.projection.is_empty() {
                        in_set.remove(&dest.local);
                    } else {
                        use_place(&dest, &mut in_set);
                    }
                    use_rvalue(&rvalue, &mut in_set);
                }
                StatementKind::ShadowResync(locals) => {
                    for &local in locals {
                        in_set.insert(local);
                    }
                }
                StatementKind::SetDiscriminant { place, .. } => {
                    if !place.projection.is_empty() {
                        use_place(&place, &mut in_set);
                    }
                }
                _ => {}
            }
        }

        if in_set != live_in[bb] {
            live_in[bb] = in_set;
            if let Some(ps) = preds.get(&bb) {
                for &p in ps {
                    if !worklist.contains(&p) {
                        worklist.push(p);
                    }
                }
            }
        }
    }

    LivenessResult { live_in, live_out }
}

fn build_predecessors(body: &Body) -> std::collections::HashMap<BasicBlockId, Vec<BasicBlockId>> {
    let mut preds = std::collections::HashMap::new();
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        if let Some(term) = &data.terminator {
            for succ in successors(&term.kind) {
                preds.entry(succ).or_insert_with(Vec::new).push(bb);
            }
        }
    }
    preds
}

fn successors(term: &TerminatorKind) -> Vec<BasicBlockId> {
    match term {
        TerminatorKind::Goto { target } => vec![*target],
        TerminatorKind::SwitchInt {
            targets, otherwise, ..
        } => {
            let mut s: Vec<_> = targets.iter().map(|(_, t)| *t).collect();
            s.push(*otherwise);
            s
        }
        TerminatorKind::Call { target, unwind, .. } => {
            let mut succ = vec![*target];
            if let CallUnwindAction::Cleanup(bb) = unwind {
                succ.push(*bb);
            }
            succ
        }
        TerminatorKind::Yield { resume, .. } => vec![*resume],
        _ => vec![],
    }
}

use crate::mir::{Operand, Place, Rvalue};

fn use_place(place: &Place, live: &mut FxHashSet<LocalId>) {
    live.insert(place.local);
}

fn use_operand(op: &Operand, live: &mut FxHashSet<LocalId>) {
    match op {
        Operand::Copy(p) | Operand::CopyWith(p, _) => use_place(p, live),
        Operand::Constant(_) => {}
    }
}

fn use_rvalue(rv: &Rvalue, live: &mut FxHashSet<LocalId>) {
    match rv {
        Rvalue::Use(op) => use_operand(op, live),
        Rvalue::UnaryOp { operand, .. } => use_operand(operand, live),
        Rvalue::BinaryOp { lhs, rhs, .. } => {
            use_operand(lhs, live);
            use_operand(rhs, live);
        }
        Rvalue::Cast { operand, .. } => use_operand(operand, live),
        Rvalue::Ref { place, .. } => use_place(place, live),
        Rvalue::Discriminant { place } => use_place(place, live),
        Rvalue::Aggregate { fields, .. } => {
            for f in fields {
                use_operand(f, live);
            }
        }
        Rvalue::Repeat { operand, .. } => use_operand(operand, live),
        Rvalue::Alloc { .. } => {}
    }
}
