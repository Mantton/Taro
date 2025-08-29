use crate::{
    GlobalContext,
    ty::{Adjustment, FieldIndex, Ty},
};
use rustc_hash::FxHashMap;
use taroc_hir::{DefinitionID, DefinitionKind, NodeID, Resolution};

pub type NodeMap<T> = FxHashMap<NodeID, T>;

#[derive(Debug, Default)]
pub struct TypingResult<'ctx> {
    // Resolved Definitions of Associated Types, Method Calls and Overloaded Operators
    pub assoc_resolution: NodeMap<Result<(DefinitionID, DefinitionKind), ()>>,
    // expression adjustments
    pub adjustments: NodeMap<Vec<Adjustment<'ctx>>>,
    // expression node types
    pub node_types: NodeMap<Ty<'ctx>>,
    pub field_indices: NodeMap<FieldIndex>,
}

impl<'ctx> TypingResult<'ctx> {
    #[track_caller]
    pub fn type_of(&self, node: NodeID) -> Ty<'ctx> {
        *self.node_types.get(&node).expect("type_of node")
    }

    pub fn path_resolution(
        &self,
        id: NodeID,
        _: &taroc_hir::Path,
        gcx: GlobalContext<'ctx>,
    ) -> taroc_hir::Resolution {
        let partial = gcx.resolution(id);

        if let Some(resolution) = partial.full_resolution() {
            resolution
        } else {
            self.assoc_resolution
                .get(&id)
                .cloned()
                .and_then(|r| r.ok())
                .map_or(Resolution::Error, |v| Resolution::Definition(v.0, v.1))
        }
    }

    pub fn is_method_call(&self, expr: &taroc_hir::Expression) -> bool {
        if let taroc_hir::ExpressionKind::Path(_) = expr.kind {
            return false;
        }

        matches!(
            self.assoc_resolution.get(&expr.id),
            Some(Ok((
                _,
                DefinitionKind::AssociatedFunction | DefinitionKind::AssociatedOperator
            )))
        )
    }

    pub fn field_index(&self, id: NodeID) -> FieldIndex {
        *self.field_indices.get(&id).expect("field index")
    }

    pub fn assoc_res(&self, id: NodeID) -> Option<(DefinitionID, DefinitionKind)> {
        self.assoc_resolution.get(&id).cloned().and_then(|r| r.ok())
    }
}
