//! Cleanup execution order is distinct from registration order. Rebuild a
//! continuation chain when necessary so a panic in a reordered defer still
//! runs the remaining defers before ending their local storage.
use super::{CleanupAction, CleanupId, CleanupNode, CleanupScopeId};
use index_vec::IndexVec;
use std::{cmp::Reverse, collections::BTreeMap};

pub(super) fn reorder_chain(
    nodes: &mut IndexVec<CleanupId, CleanupNode>,
    scope_depths: &IndexVec<CleanupScopeId, u32>,
    from: Option<CleanupId>,
    target: Option<CleanupId>,
) -> Option<CleanupId> {
    let mut registration = Vec::new();
    let mut cursor = from;
    while cursor != target {
        let id = cursor.expect("cleanup target must be an ancestor");
        registration.push(id);
        cursor = nodes[id].parent;
    }
    let mut scopes: BTreeMap<Reverse<u32>, Vec<CleanupId>> = BTreeMap::new();
    for id in &registration {
        scopes
            .entry(Reverse(scope_depths[nodes[*id].scope]))
            .or_default()
            .push(*id);
    }
    let mut ordered = Vec::with_capacity(registration.len());
    // Lifetime-extended owners may be registered among inner-scope temporaries.
    // Use lexical depth rather than assuming contiguous registrations. Active
    // exited scopes must form one ancestor chain, never unrelated siblings.
    for scope in scopes.values() {
        assert!(
            scope
                .iter()
                .all(|id| nodes[*id].scope == nodes[scope[0]].scope),
            "unrelated lexical scopes on one cleanup chain"
        );
        ordered.extend(scope.iter().copied().filter(|id| {
            matches!(
                nodes[*id].action,
                CleanupAction::DeferBlock(..) | CleanupAction::ScopedTask(..)
            )
        }));
        ordered.extend(scope.iter().copied().filter(|id| {
            !matches!(
                nodes[*id].action,
                CleanupAction::DeferBlock(..) | CleanupAction::ScopedTask(..)
            )
        }));
    }
    if ordered == registration {
        return from;
    }
    let mut continuation = target;
    for id in ordered.into_iter().rev() {
        let mut node = nodes[id];
        node.parent = continuation;
        continuation = Some(nodes.push(node));
    }
    continuation
}

/// Finish a statement while retaining its newly declared block storage. Clone
/// links instead of editing old chains already captured by unwind edges.
pub(super) fn split_scope(
    nodes: &mut IndexVec<CleanupId, CleanupNode>,
    depths: &IndexVec<CleanupScopeId, u32>,
    mut from: Option<CleanupId>,
    target: Option<CleanupId>,
    scope: CleanupScopeId,
) -> (Option<CleanupId>, Option<CleanupId>) {
    let mut retained = vec![];
    let mut exiting = vec![];
    while from != target {
        let id = from.expect("statement cleanup must reach its entry chain");
        if depths[nodes[id].scope] < depths[scope] {
            retained.push(id);
        } else {
            exiting.push(id);
        }
        from = nodes[id].parent;
    }
    fn link(
        nodes: &mut IndexVec<CleanupId, CleanupNode>,
        ids: Vec<CleanupId>,
        mut tail: Option<CleanupId>,
    ) -> Option<CleanupId> {
        for id in ids.into_iter().rev() {
            let mut node = nodes[id];
            node.parent = tail;
            tail = Some(nodes.push(node));
        }
        tail
    }
    let retained = link(nodes, retained, target);
    (link(nodes, exiting, retained), retained)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        mir::{LocalId, builder::CleanupScopeId},
        span::{FileID, Span},
        thir::BlockId,
    };

    fn push(
        nodes: &mut IndexVec<CleanupId, CleanupNode>,
        parent: Option<CleanupId>,
        scope: u32,
        ordinal: u32,
        defer: bool,
    ) -> Option<CleanupId> {
        Some(nodes.push(CleanupNode {
            parent,
            scope: CleanupScopeId::from_raw(scope),
            span: Span::empty(FileID::new(0)),
            action: if defer {
                CleanupAction::DeferBlock(crate::hir::DeferKind::Always, BlockId::from_raw(ordinal))
            } else {
                CleanupAction::EndStorage(LocalId::from_raw(ordinal))
            },
        }))
    }
    fn ordinals(
        nodes: &IndexVec<CleanupId, CleanupNode>,
        mut from: Option<CleanupId>,
        target: Option<CleanupId>,
    ) -> Vec<u32> {
        let mut result = vec![];
        while from != target {
            let node = nodes[from.unwrap()];
            result.push(match node.action {
                CleanupAction::DeferBlock(_, id) => id.raw(),
                CleanupAction::ScopedTask(id) => id,
                CleanupAction::EndStorage(local) => local.raw(),
            });
            from = node.parent;
        }
        result
    }

    #[test]
    fn repeated_defer_lowering_gets_distinct_promoted_owner_storage() {
        crate::test_support::analyze_script_built_mir(
            "struct Record { value: int32 }\nextend Record {\nfunc get() -> &int32 { &self.value }\n}\nfunc observe(_ value: &int32) {}\nfunc touch() {}\nfunc main() { defer { saved := Record { value: 7 }.get(); observe(saved) }; touch() }",
            |bodies, gcx| {
                use crate::mir::{AggregateKind, Rvalue, StatementKind};
                let body = bodies
                    .iter()
                    .find(|body| gcx.definition_ident(body.owner).symbol.as_str() == "main")
                    .unwrap();
                let owners: Vec<_> = body
                    .basic_blocks
                    .iter()
                    .flat_map(|block| &block.statements)
                    .filter_map(|statement| {
                        if let StatementKind::Assign(
                            place,
                            Rvalue::Aggregate {
                                kind: AggregateKind::Adt { def_id, .. },
                                ..
                            },
                        ) = &statement.kind
                            && gcx.definition_ident(*def_id).symbol.as_str() == "Record"
                        {
                            Some(place.local)
                        } else {
                            None
                        }
                    })
                    .collect();
                assert!(
                    owners.len() > 1,
                    "fixture must lower defer on multiple exits"
                );
                let unique: rustc_hash::FxHashSet<_> = owners.iter().copied().collect();
                assert_eq!(
                    unique.len(),
                    owners.len(),
                    "each lowering needs independent storage and cleanup registration"
                );
            },
        );
    }

    #[test]
    fn cleanup_cfg_size_stays_bounded_with_many_owned_values_and_defers() {
        let mut source = "struct Task { token: uint64 }\nfunc touch() {}\nfunc main() {".to_owned();
        for index in 0..16 {
            source.push_str(&format!(
                "var task{index} = Task {{ token: {index} }}; defer {{ touch() }};"
            ));
        }
        source.push('}');
        crate::test_support::analyze_script_built_mir_with_items(
            &source,
            &[(crate::hir::StdItem::Task, "Task")],
            |bodies, gcx| {
                let body = bodies
                    .iter()
                    .find(|body| gcx.definition_ident(body.owner).symbol.as_str() == "main")
                    .unwrap();
                assert!(
                    body.basic_blocks.len() < 640,
                    "cleanup suffixes must be shared rather than rebuilt exponentially: {} blocks",
                    body.basic_blocks.len()
                );
            },
        );
    }

    #[test]
    fn statement_cleanup_keeps_new_block_owners_in_unwind_parents() {
        let mut nodes = IndexVec::new();
        let outer = push(&mut nodes, None, 0, 1, false);
        let statement_temp = push(&mut nodes, outer, 1, 2, false);
        let declaration = push(&mut nodes, statement_temp, 0, 3, false);
        let (exiting, retained) = split_scope(
            &mut nodes,
            &IndexVec::from(vec![0, 1]),
            declaration,
            outer,
            CleanupScopeId::from_raw(1),
        );
        assert_eq!(ordinals(&nodes, exiting, retained), [2]);
        assert_eq!(ordinals(&nodes, retained, None), [3, 1]);
        assert_eq!(ordinals(&nodes, exiting, None), [2, 3, 1]);
        // Previously captured unwind chains retain their original links.
        assert_eq!(ordinals(&nodes, declaration, None), [3, 2, 1]);
    }

    fn reorder(
        nodes: &mut IndexVec<CleanupId, CleanupNode>,
        from: Option<CleanupId>,
        target: Option<CleanupId>,
    ) -> Option<CleanupId> {
        reorder_chain(nodes, &IndexVec::from(vec![0, 1]), from, target)
    }

    #[test]
    fn defer_panic_continuation_includes_later_owned_locals() {
        let mut nodes = IndexVec::new();
        let owner = push(&mut nodes, None, 0, 0, false);
        let defer = push(&mut nodes, owner, 0, 1, true);
        let later_owner = push(&mut nodes, defer, 0, 2, false);
        let ordered = reorder(&mut nodes, later_owner, None);
        assert_eq!(ordinals(&nodes, ordered, None), [1, 2, 0]);
        // The emitted defer installs this parent as its panic continuation.
        assert_eq!(
            ordinals(&nodes, nodes[ordered.unwrap()].parent, None),
            [2, 0]
        );
        assert_eq!(
            ordinals(&nodes, later_owner, None),
            [2, 1, 0],
            "registration edges remain stable for other exits"
        );
    }

    #[test]
    fn nested_scopes_finish_before_outer_defers_and_partial_exits_preserve_the_target() {
        let mut nodes = IndexVec::new();
        let outer_owner = push(&mut nodes, None, 0, 0, false);
        let outer_defer = push(&mut nodes, outer_owner, 0, 1, true);
        let inner_owner = push(&mut nodes, outer_defer, 1, 2, false);
        let inner_defer = push(&mut nodes, inner_owner, 1, 3, true);
        let later_owner = push(&mut nodes, inner_defer, 1, 4, false);
        let later_defer = push(&mut nodes, later_owner, 1, 5, true);
        let whole = reorder(&mut nodes, later_defer, None);
        assert_eq!(ordinals(&nodes, whole, None), [5, 3, 4, 2, 1, 0]);
        let inner = reorder(&mut nodes, later_defer, outer_defer);
        assert_eq!(ordinals(&nodes, inner, outer_defer), [5, 3, 4, 2]);
        assert_eq!(ordinals(&nodes, outer_defer, None), [1, 0]);
    }

    #[test]
    fn promoted_owner_registrations_do_not_split_a_lexical_cleanup_scope() {
        let mut nodes = IndexVec::new();
        let outer_defer = push(&mut nodes, None, 0, 0, true);
        let outer_owner = push(&mut nodes, outer_defer, 0, 1, false);
        let inner_owner = push(&mut nodes, outer_owner, 1, 2, false);
        let promoted_owner = push(&mut nodes, inner_owner, 0, 3, false);
        let inner_defer = push(&mut nodes, promoted_owner, 1, 4, true);
        let ordered = reorder(&mut nodes, inner_defer, None);
        assert_eq!(ordinals(&nodes, ordered, None), [4, 2, 0, 3, 1]);
    }

    #[test]
    fn already_ordered_chains_are_reused_for_cleanup_unwind_suffixes() {
        let mut nodes = IndexVec::new();
        let owner = push(&mut nodes, None, 0, 0, false);
        let defer = push(&mut nodes, owner, 0, 1, true);
        let count = nodes.len();
        assert_eq!(reorder(&mut nodes, defer, None), defer);
        assert_eq!(reorder(&mut nodes, owner, None), owner);
        assert_eq!(nodes.len(), count);
        assert_eq!(reorder(&mut nodes, owner, owner), owner);
    }
}
