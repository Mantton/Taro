//! Compact CFG dominance for the large cleanup graphs produced by native loans.
//! Petgraph computes immediate dominators; dominator-tree intervals make each
//! query constant-time without materializing a quadratic set for every block.
use crate::mir::{BasicBlockId, Body};
use petgraph::{algo::dominators::simple_fast, graph::DiGraph};

pub struct Dominators {
    intervals: Vec<(usize, usize)>,
}

impl Dominators {
    /// Unreachable blocks dominate only themselves, never reachable storage.
    pub fn dominates(&self, a: BasicBlockId, b: BasicBlockId) -> bool {
        let (start, end) = self.intervals[a.index()];
        let (other, _) = self.intervals[b.index()];
        start <= other && other < end
    }
}

pub fn compute_dominators(body: &Body<'_>) -> Dominators {
    let mut graph = DiGraph::<(), ()>::new();
    let nodes: Vec<_> = body
        .basic_blocks
        .iter()
        .map(|_| graph.add_node(()))
        .collect();
    for (block, data) in body.basic_blocks.iter_enumerated() {
        if let Some(terminator) = &data.terminator {
            for next in terminator.kind.successors() {
                graph.add_edge(nodes[block.index()], nodes[next.index()], ());
            }
        }
    }
    let root = body.start_block.index();
    let immediate = simple_fast(&graph, nodes[root]);
    let mut children = vec![Vec::new(); nodes.len()];
    for (index, node) in nodes.iter().enumerate() {
        if let Some(parent) = immediate.immediate_dominator(*node) {
            children[parent.index()].push(index);
        }
    }
    // Iterative traversal also supports long straight-line cleanup chains.
    let mut intervals = vec![(usize::MAX, usize::MAX); nodes.len()];
    let mut clock = 0;
    let mut pending = vec![(root, false)];
    while let Some((node, exiting)) = pending.pop() {
        if exiting {
            intervals[node].1 = clock;
        } else {
            intervals[node].0 = clock;
            clock += 1;
            pending.push((node, true));
            pending.extend(children[node].iter().rev().map(|child| (*child, false)));
        }
    }
    for interval in &mut intervals {
        if interval.0 == usize::MAX {
            *interval = (clock, clock + 1);
            clock += 1;
        }
    }
    Dominators { intervals }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mir::{BasicBlockData, Constant, ConstantKind, Operand, Terminator, TerminatorKind};

    #[test]
    fn diamond_loops_and_unreachable_cycles_match_path_exclusion() {
        crate::test_support::with_test_gcx(|gcx| {
            // Entry diamond, loop, exit, plus a disconnected cycle.
            let edges: &[&[usize]] = &[&[1, 2], &[3], &[3], &[4, 5], &[3], &[], &[7], &[6]];
            let mut body = crate::mir::test_support::minimal_body(gcx);
            let span = body.locals[body.return_local].span;
            body.basic_blocks.clear();
            for successors in edges {
                let kind = if successors.is_empty() {
                    TerminatorKind::Return
                } else {
                    TerminatorKind::SwitchInt {
                        discr: Operand::Constant(Constant {
                            ty: gcx.types.bool,
                            value: ConstantKind::Bool(true),
                        }),
                        targets: successors
                            .iter()
                            .enumerate()
                            .map(|(index, next)| (index as u128, BasicBlockId::from_usize(*next)))
                            .collect(),
                        otherwise: BasicBlockId::from_usize(successors[0]),
                    }
                };
                body.basic_blocks.push(BasicBlockData {
                    note: None,
                    statements: vec![],
                    terminator: Some(Terminator { kind, span }),
                });
            }
            let dominates = compute_dominators(&body);
            let reachable = |target: usize, avoid: Option<usize>| {
                let mut seen = vec![false; edges.len()];
                let mut pending = vec![0];
                while let Some(node) = pending.pop() {
                    if Some(node) == avoid || seen[node] {
                        continue;
                    }
                    if node == target {
                        return true;
                    }
                    seen[node] = true;
                    pending.extend(edges[node]);
                }
                false
            };
            for a in 0..edges.len() {
                for b in 0..edges.len() {
                    let expected = a == b || (reachable(b, None) && !reachable(b, Some(a)));
                    assert_eq!(
                        dominates
                            .dominates(BasicBlockId::from_usize(a), BasicBlockId::from_usize(b)),
                        expected,
                        "{a} dominates {b}"
                    );
                }
            }
        });
    }

    #[test]
    fn large_cleanup_chain_needs_no_quadratic_sets_or_recursive_walk() {
        crate::test_support::with_test_gcx(|gcx| {
            let mut body = crate::mir::test_support::minimal_body(gcx);
            let span = body.locals[body.return_local].span;
            let count = 20_000;
            body.basic_blocks.clear();
            for index in 0..count {
                body.basic_blocks.push(BasicBlockData {
                    note: None,
                    statements: vec![],
                    terminator: Some(Terminator {
                        span,
                        kind: if index + 1 == count {
                            TerminatorKind::Return
                        } else {
                            TerminatorKind::Goto {
                                target: BasicBlockId::from_usize(index + 1),
                            }
                        },
                    }),
                });
            }
            let dominates = compute_dominators(&body);
            for index in [0, 1, count / 2, count - 1] {
                assert!(dominates.dominates(
                    BasicBlockId::from_usize(index),
                    BasicBlockId::from_usize(count - 1)
                ));
                assert_eq!(
                    dominates.dominates(
                        BasicBlockId::from_usize(count - 1),
                        BasicBlockId::from_usize(index)
                    ),
                    index == count - 1
                );
            }
        });
    }
}
