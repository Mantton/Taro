use crate::{
    ast::{Identifier, NodeID},
    sema::resolve::{
        DefinitionID, DefinitionIndex, DefinitionKind, PackageIndex, Resolution, Scope, ScopeEntry,
        ScopeEntryID, ScopeEntryKind, ScopeID, ScopeKey, ScopeNamespace, ScopeTable, UsageEntry,
        UsageID,
    },
};
use index_vec::IndexVec;
use rustc_hash::{FxHashMap, FxHashSet};
use std::cell::RefCell;

pub struct Resolver {
    node_to_def: FxHashMap<NodeID, DefinitionID>,
    def_to_kind: FxHashMap<DefinitionID, DefinitionKind>,
    pub def_to_ident: FxHashMap<DefinitionID, Identifier>,
    def_to_parent: FxHashMap<DefinitionID, DefinitionID>,
    next_index: usize,
    pub scopes: IndexVec<ScopeID, Scope>,
    pub scope_entries: IndexVec<ScopeEntryID, ScopeEntry>,
    pub usages: IndexVec<UsageID, UsageEntry>,
    pub unresolved_imports: Vec<UsageID>,
    pub unresolved_exports: Vec<UsageID>,
    pub root_module_scope: Option<ScopeID>,
}

impl Resolver {
    pub fn new() -> Resolver {
        Resolver {
            node_to_def: Default::default(),
            def_to_kind: Default::default(),
            def_to_ident: Default::default(),
            def_to_parent: Default::default(),
            next_index: 0,

            scopes: Default::default(),
            scope_entries: Default::default(),
            usages: Default::default(),

            unresolved_exports: Default::default(),
            unresolved_imports: Default::default(),
            root_module_scope: None,
        }
    }
}

impl Resolver {
    pub fn create_definition(
        &mut self,
        identifier: &Identifier,
        node_id: NodeID,
        kind: DefinitionKind,
        parent: Option<DefinitionID>,
    ) -> DefinitionID {
        let index = {
            let def_index = DefinitionIndex::new(self.next_index);
            DefinitionID::new(PackageIndex::new(0), def_index)
        };

        {
            self.node_to_def.insert(node_id, index);
            self.def_to_kind.insert(index, kind);
            self.def_to_ident.insert(index, identifier.clone());
            if let Some(parent) = parent {
                self.def_to_parent.insert(index, parent);
            }
            self.next_index += 1;
        }

        index
    }

    pub fn def_id(&self, id: NodeID) -> DefinitionID {
        *self.node_to_def.get(&id).expect("bug! node not tagged")
    }

    pub fn def_kind(&self, id: DefinitionID) -> DefinitionKind {
        return *self.def_to_kind.get(&id).expect("bug! node not tagged");

        // if id.is_local(self.session().package_index) {
        // }

        // let resolutions = self.gcx.store.resolutions.borrow();
        // let data = resolutions.get(&id.package()).expect("resolution data");
        // let kind = *data.def_to_kind.get(&id).expect("def to kind");
        // kind
    }

    pub fn create_scope(&mut self, scope: Scope) -> ScopeID {
        self.scopes.push(scope)
    }

    pub fn get_scope(&self, id: ScopeID) -> &Scope {
        self.scopes.get(id).expect("no scope matching provided id")
    }

    pub fn get_scope_entry(&self, id: ScopeEntryID) -> &ScopeEntry {
        self.scope_entries
            .get(id)
            .expect("no entry matching provided id")
    }

    pub fn create_usage(&mut self, scope: UsageEntry) -> UsageID {
        self.usages.push(scope)
    }

    pub fn get_usage(&self, id: UsageID) -> &UsageEntry {
        self.usages.get(id).expect("no usage matching provided id")
    }
}

impl Resolver {
    pub fn define_in_scope(
        &mut self,
        scope: ScopeID,
        identifier: &Identifier,
        namespace: ScopeNamespace,
        resolution: Resolution,
    ) -> Result<(), ScopeEntryID> {
        let key = ScopeKey {
            name: identifier.symbol.clone(),
            namespace,
            disambiguator: 0,
        };

        let entry = ScopeEntry {
            kind: ScopeEntryKind::Resolution(resolution),
            span: identifier.span,
        };
        let entry_id = self.scope_entries.push(entry);
        self.define_in_scope_internal(scope, key, entry_id)
    }

    fn define_in_scope_internal(
        &mut self,
        scope: ScopeID,
        key: ScopeKey,
        entry: ScopeEntryID,
    ) -> Result<(), ScopeEntryID> {
        let scope = self.get_scope(scope);
        let mut table = scope.table.borrow_mut();
        self.define_in_scope_table(key, entry, &mut table)
    }

    fn define_in_scope_table(
        &self,
        key: ScopeKey,
        entry: ScopeEntryID,
        table: &mut ScopeTable,
    ) -> Result<(), ScopeEntryID> {
        if table.contains_key(&key) {
            if let Some(current_set) = table.get_mut(&key)
                && let Some(&nearest_entry) = current_set.iter().next()
            {
                let scope_entry = self.get_scope_entry(nearest_entry);

                let resolution = match &scope_entry.kind {
                    ScopeEntryKind::Resolution(resolution) => resolution,
                    ScopeEntryKind::Usage => todo!(),
                };

                let is_function = matches!(
                    resolution,
                    Resolution::Definition(
                        _,
                        DefinitionKind::Function | DefinitionKind::AssociatedFunction,
                    )
                );

                if !is_function {
                    return Err(nearest_entry);
                }

                current_set.insert(entry);
                return Ok(());
            } else {
                unreachable!()
            }
        } else {
            let mut set = FxHashSet::default();
            set.insert(entry);
            table.insert(key, set);
            return Ok(());
        }
    }
}
