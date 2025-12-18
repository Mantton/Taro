use crate::mir::{BasicBlockId, Body, TerminatorKind};
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
                TerminatorKind::SwitchInt { targets, otherwise, .. } => {
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
                TerminatorKind::SwitchInt { targets, otherwise, .. } => {
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
