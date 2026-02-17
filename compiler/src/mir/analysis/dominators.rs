use crate::mir::{BasicBlockId, Body, CallUnwindAction, TerminatorKind};
use index_vec::IndexVec;
use rustc_hash::FxHashSet;

pub struct Dominators {
    doms: IndexVec<BasicBlockId, FxHashSet<BasicBlockId>>,
}

impl Dominators {
    pub fn dominates(&self, a: BasicBlockId, b: BasicBlockId) -> bool {
        self.doms[b].contains(&a)
    }
}

pub fn compute_dominators(body: &Body<'_>) -> Dominators {
    let mut preds: IndexVec<BasicBlockId, Vec<BasicBlockId>> =
        IndexVec::from(vec![Vec::new(); body.basic_blocks.len()]);

    for (bb, data) in body.basic_blocks.iter_enumerated() {
        if let Some(term) = &data.terminator {
            for succ in successors(&term.kind) {
                preds[succ].push(bb);
            }
        }
    }

    let mut all = FxHashSet::default();
    for bb in body.basic_blocks.indices() {
        all.insert(bb);
    }

    let mut doms = IndexVec::from(vec![FxHashSet::default(); body.basic_blocks.len()]);
    for bb in body.basic_blocks.indices() {
        if bb == body.start_block {
            doms[bb].insert(bb);
        } else {
            doms[bb] = all.clone();
        }
    }

    let mut changed = true;
    while changed {
        changed = false;
        for bb in body.basic_blocks.indices() {
            if bb == body.start_block {
                continue;
            }

            let mut new_set = if preds[bb].is_empty() {
                FxHashSet::default()
            } else {
                doms[preds[bb][0]].clone()
            };

            for pred in preds[bb].iter().skip(1) {
                new_set = new_set.intersection(&doms[*pred]).cloned().collect();
            }

            new_set.insert(bb);
            if new_set != doms[bb] {
                doms[bb] = new_set;
                changed = true;
            }
        }
    }

    Dominators { doms }
}

fn successors(term: &TerminatorKind<'_>) -> Vec<BasicBlockId> {
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
