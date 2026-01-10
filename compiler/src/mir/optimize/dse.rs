use crate::{
    compile::context::Gcx,
    error::CompileResult,
    mir::{Body, StatementKind, TerminatorKind, analysis::liveness::compute_liveness},
};

use super::MirPass;

pub struct DeadStoreElimination;

impl<'ctx> MirPass<'ctx> for DeadStoreElimination {
    fn name(&self) -> &'static str {
        "DeadStoreElimination"
    }

    fn run(&mut self, _gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
        let liveness = compute_liveness(body);
        let mut address_taken = vec![false; body.locals.len()];

        for block in body.basic_blocks.iter() {
            for stmt in &block.statements {
                if let StatementKind::Assign(_, Rvalue::Ref { place, .. }) = &stmt.kind {
                    address_taken[place.local.index()] = true;
                }
            }
        }

        for (bb, data) in body.basic_blocks.iter_mut_enumerated() {
            // Processing backwards naturally pairs with liveness
            // But we need to check liveness AT EACH STATEMENT.
            // Liveness result gives live_out.
            // We can reconstruct the live set as we walk backwards.

            let mut live = liveness.live_out[bb].clone();

            // Handle terminator uses first
            if let Some(term) = &data.terminator {
                match &term.kind {
                    TerminatorKind::Call {
                        func,
                        args,
                        destination,
                        ..
                    } => {
                        use_operand(func, &mut live);
                        for arg in args {
                            use_operand(arg, &mut live);
                        }
                        if destination.projection.is_empty() {
                            live.remove(&destination.local);
                        } else {
                            use_place(destination, &mut live);
                        }
                    }
                    TerminatorKind::SwitchInt { discr, .. } => use_operand(discr, &mut live),
                    TerminatorKind::Return => {
                        live.insert(body.return_local);
                    }
                    _ => {}
                }
            }

            // Iterate backwards and filter statements
            // We can't drain/retain easily while updating state backwards.
            // So we'll build a "keep" verification.

            let len = data.statements.len();
            let mut keep = vec![true; len];

            for (idx, stmt) in data.statements.iter().enumerate().rev() {
                match &stmt.kind {
                    StatementKind::Assign(dest, rvalue) => {
                        // Check if assignment is needed (destination is live)
                        let needed = if dest.projection.is_empty() {
                            live.contains(&dest.local) || address_taken[dest.local.index()]
                        } else {
                            true // Sideload/Partial write is always needed (or could check base local)
                        };

                        // Side effects?
                        let side_effects = rvalue_has_side_effects(rvalue);

                        if !needed && !side_effects {
                            // Remove statement
                            keep[idx] = false;
                        } else {
                            if dest.projection.is_empty() {
                                live.remove(&dest.local);
                            } else {
                                use_place(&dest, &mut live);
                            }
                            use_rvalue(&rvalue, &mut live);
                        }
                    }
                    StatementKind::SetDiscriminant { place, .. } => {
                        let needed = if place.projection.is_empty() {
                            live.contains(&place.local) || address_taken[place.local.index()]
                        } else {
                            true
                        };

                        if !needed {
                            keep[idx] = false;
                        } else {
                            use_place(place, &mut live);
                        }
                    }
                    _ => {}
                }
            }

            // Compact statements
            let mut i = 0;
            data.statements.retain(|_| {
                let k = keep[i];
                i += 1;
                k
            });
        }

        Ok(())
    }
}

// Reuse helper functions from liveness/mod if exported, or duplicate.
// Ideally should be shared.
use crate::mir::{LocalId, Operand, Place, Rvalue};
use rustc_hash::FxHashSet;

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

fn rvalue_has_side_effects(rv: &Rvalue) -> bool {
    match rv {
        Rvalue::Use(_)
        | Rvalue::UnaryOp { .. }
        | Rvalue::BinaryOp { .. }
        | Rvalue::Cast { .. }
        | Rvalue::Ref { .. }
        | Rvalue::Discriminant { .. }
        | Rvalue::Repeat { .. }
        | Rvalue::Alloc { .. } => false,
        Rvalue::Aggregate { .. } => false, // Initializing aggregate has no side effects (unless allocation?)
    }
}
