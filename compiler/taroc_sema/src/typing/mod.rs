use crate::ty::{Adjustment, Ty};
use rustc_hash::FxHashMap;
use taroc_hir::{DefinitionID, NodeID};

pub type NodeMap<T> = FxHashMap<NodeID, T>;

#[derive(Debug, Default)]
pub struct TypingResult<'ctx> {
    // Resolved Definitions of Associated Types, Method Calls and Overloaded Operators
    pub assoc_resolution: NodeMap<Result<DefinitionID, ()>>,
    // expression adjustments
    pub adjustments: NodeMap<Vec<Adjustment>>,
    // expression node types
    pub node_types: NodeMap<Ty<'ctx>>,
}
