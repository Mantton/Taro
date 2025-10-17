use crate::{
    ast::{Identifier, NodeID},
    sema::resolve::{DefinitionID, DefinitionIndex, DefinitionKind, PackageIndex},
};
use rustc_hash::FxHashMap;
use std::cell::RefCell;

pub struct Resolver {
    internal: RefCell<ResolverInternal>,
}

impl Resolver {
    pub fn new() -> Resolver {
        Resolver {
            internal: RefCell::new(ResolverInternal::new()),
        }
    }
}

impl Resolver {
    pub fn create_definition(
        &self,
        identifier: &Identifier,
        node_id: NodeID,
        kind: DefinitionKind,
        parent: Option<DefinitionID>,
    ) -> DefinitionID {
        let index = {
            let def_index = DefinitionIndex::new(self.internal.borrow().next_index);
            DefinitionID::new(PackageIndex::new(0), def_index)
        };

        {
            let mut this = self.internal.borrow_mut();
            this.node_to_def.insert(node_id, index);
            this.def_to_kind.insert(index, kind);
            this.def_to_ident.insert(index, identifier.clone());
            if let Some(parent) = parent {
                this.def_to_parent.insert(index, parent);
            }
            this.next_index += 1;
        }

        index
    }
}

struct ResolverInternal {
    node_to_def: FxHashMap<NodeID, DefinitionID>,
    def_to_kind: FxHashMap<DefinitionID, DefinitionKind>,
    def_to_ident: FxHashMap<DefinitionID, Identifier>,
    def_to_parent: FxHashMap<DefinitionID, DefinitionID>,
    next_index: usize,
}

impl ResolverInternal {
    pub fn new() -> ResolverInternal {
        ResolverInternal {
            node_to_def: Default::default(),
            def_to_kind: Default::default(),
            def_to_ident: Default::default(),
            def_to_parent: Default::default(),
            next_index: 0,
        }
    }
}
