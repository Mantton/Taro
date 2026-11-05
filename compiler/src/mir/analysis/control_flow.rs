//! Structural control-flow queries shared by MIR optimizations.
use crate::mir::{BasicBlockId, Body};
use rustc_hash::FxHashSet;

/// Whether execution can return to this block along any nonempty path.
/// Includes irreducible and unreachable cycles, not just natural-loop headers.
pub fn block_is_cyclic(body: &Body<'_>, block: BasicBlockId) -> bool {
    let mut pending = Vec::new();
    if let Some(terminator) = &body.basic_blocks[block].terminator {
        pending.extend(terminator.kind.successors());
    }
    let mut visited = FxHashSet::default();
    while let Some(candidate) = pending.pop() {
        if candidate == block {
            return true;
        }
        if !visited.insert(candidate) {
            continue;
        }
        if let Some(terminator) = &body.basic_blocks[candidate].terminator {
            pending.extend(terminator.kind.successors());
        }
    }
    false
}
