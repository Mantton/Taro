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
    let mut live_in = IndexVec::from(vec![FxHashSet::default(); body.basic_blocks.len()]);
    let mut live_out = IndexVec::from(vec![FxHashSet::default(); body.basic_blocks.len()]);
    let mut worklist: Vec<BasicBlockId> = body.basic_blocks.indices().collect();

    // Iterate until convergence
    while let Some(bb) = worklist.pop() {
        let block = &body.basic_blocks[bb];
        let mut current_live = live_out[bb].clone();

        // 1. Process terminator (uses)
        if let Some(term) = &block.terminator {
            match &term.kind {
                TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    ..
                } => {
                    // Function and args are uses
                    use_operand(func, &mut current_live);
                    for arg in args {
                        use_operand(arg, &mut current_live);
                    }
                    // Destination is a def (implicitly killed), but we don't handle defs here
                    // Defs are handled by 'removing' from live set, but Call terminator
                    // is atomic. The destination is written AFTER args are read.
                    // So if dest was live-out, it is killed here.
                    // HOWEVER, we are going BACKWARDS.
                    // So we start with live_out.
                    // Destination is written. So it is NOT live before the write.
                    // So we remove destination from set.
                    if destination.projection.is_empty() {
                        current_live.remove(&destination.local);
                    } else {
                        // Partial write / read-modify-write on projection -> effectively a use of base
                        use_place(destination, &mut current_live);
                    }
                }
                TerminatorKind::SwitchInt { discr, .. } => {
                    use_operand(discr, &mut current_live);
                }
                TerminatorKind::Return => {
                    // Return local is used
                    current_live.insert(body.return_local);
                }
                TerminatorKind::Goto { .. }
                | TerminatorKind::Unreachable
                | TerminatorKind::ResumeUnwind
                | TerminatorKind::UnresolvedGoto => {}
            }
        }

        // 2. Process statements backwards
        for stmt in block.statements.iter().rev() {
            use crate::mir::StatementKind;
            match &stmt.kind {
                StatementKind::Assign(dest, rvalue) => {
                    // Destination is defined. Remove from live set.
                    if dest.projection.is_empty() {
                        current_live.remove(&dest.local);
                    } else {
                        // Assignment to projection is a use of the base local
                        use_place(&dest, &mut current_live);
                    }

                    // Rvalue is used
                    use_rvalue(&rvalue, &mut current_live);
                }
                StatementKind::SetDiscriminant { place, .. } => {
                    if place.projection.is_empty() {
                        // Overwrites discriminant, effectively a partial def?
                        // For liveness of the WHOLE local, if it's an enum, setting discriminant
                        // doesn't kill the whole local unless it was uninit.
                        // Conservatively treat as use if we aren't sure it's a full kill.
                        // But usually SetDiscrim is followed by field assignments.
                        // Let's treat it as a use of base if projection, or partial def (no kill) if local.
                        // Safest: don't kill.
                    } else {
                        use_place(place, &mut current_live);
                    }
                }
                StatementKind::GcSafepoint | StatementKind::Nop => {}
            }
        }

        // 3. Update live_in
        if current_live != live_in[bb] {
            live_in[bb] = current_live.clone();

            // Add predecessors to worklist
            // We need a predecessor map or scan all blocks.
            // Since we don't have pred map locally, we accept scanning or we assume worklist order usually handles it.
            // But strict correctness requires processing preds.
            // Let's brute force scan for now or assume the user has a proper CFG API.
            // The existing code doesn't seem to expose predecessors easily.
            // We'll scan all blocks to find who jumps to 'bb'.

            // Optimization: Build predecessor map once at start.
        }
    }

    // Re-run with proper global fixpoint include pred handling
    // Efficient implementation:
    let preds = build_predecessors(body);

    // Reset and run real loop
    live_in = IndexVec::from(vec![FxHashSet::default(); body.basic_blocks.len()]);
    worklist = body.basic_blocks.indices().collect(); // Reverse postorder would be better but simple queue ok

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
        _ => vec![],
    }
}

use crate::mir::{Operand, Place, Rvalue};

fn use_place(place: &Place, live: &mut FxHashSet<LocalId>) {
    live.insert(place.local);
}

fn use_operand(op: &Operand, live: &mut FxHashSet<LocalId>) {
    match op {
        Operand::Copy(p) | Operand::Move(p) => use_place(p, live),
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
