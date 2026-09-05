use crate::mir::{BasicBlockId, Body};
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
    let preds = body.predecessors();

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
