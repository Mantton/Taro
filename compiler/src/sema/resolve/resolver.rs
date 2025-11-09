use crate::{
    ast::{Identifier, NodeID},
    compile::state::CompilerState,
    sema::resolve::{
        arena::ResolverArenas,
        models::{
            DefinitionID, DefinitionIndex, DefinitionKind, Holder, LexicalScope,
            LexicalScopeBinding, LexicalScopeSource, NameEntry, PackageIndex, Resolution,
            ResolutionError, ResolvedValue, Scope, ScopeData, ScopeEntry, ScopeEntryData,
            ScopeEntryKind, ScopeKind, ScopeNamespace, ScopeTable, UsageEntry, UsageEntryData,
        },
    },
    span::FileID,
    utils::intern::Interned,
};
use ecow::EcoString;
use index_vec::IndexVec;
use rustc_hash::{FxHashMap, FxHashSet};
use std::cell::RefCell;

pub struct Resolver<'arena, 'compiler> {
    pub arenas: &'arena ResolverArenas,
    pub compiler: &'compiler CompilerState,
    node_to_def: FxHashMap<NodeID, DefinitionID>,
    def_to_kind: FxHashMap<DefinitionID, DefinitionKind>,
    pub def_to_ident: FxHashMap<DefinitionID, Identifier>,
    def_to_parent: FxHashMap<DefinitionID, DefinitionID>,
    next_index: usize,
    pub unresolved_imports: Vec<UsageEntry<'arena>>,
    pub unresolved_exports: Vec<UsageEntry<'arena>>,
    pub root_module_scope: Option<Scope<'arena>>,
    pub file_scope_mapping: FxHashMap<FileID, Scope<'arena>>,
    pub module_scope_mapping: FxHashMap<usize, Scope<'arena>>,
    pub definition_scope_mapping: FxHashMap<DefinitionID, Scope<'arena>>,
    pub block_scope_mapping: FxHashMap<NodeID, Scope<'arena>>,
}

impl<'a, 'c> Resolver<'a, 'c> {
    pub fn new(arenas: &'a ResolverArenas, compiler: &'c CompilerState) -> Resolver<'a, 'c> {
        Resolver {
            arenas,
            compiler,
            node_to_def: Default::default(),
            def_to_kind: Default::default(),
            def_to_ident: Default::default(),
            def_to_parent: Default::default(),
            next_index: 0,

            unresolved_exports: Default::default(),
            unresolved_imports: Default::default(),
            root_module_scope: None,

            file_scope_mapping: Default::default(),
            module_scope_mapping: Default::default(),
            definition_scope_mapping: Default::default(),
            block_scope_mapping: Default::default(),
        }
    }
}

impl<'a, 'c> Resolver<'a, 'c> {
    pub fn create_definition(
        &mut self,
        identifier: &Identifier,
        node_id: NodeID,
        kind: DefinitionKind,
        parent: Option<DefinitionID>,
    ) -> DefinitionID {
        let index = {
            let def_index = DefinitionIndex::new(self.next_index);
            DefinitionID::new(PackageIndex::LOCAL, def_index)
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

    pub fn definition_id(&self, id: NodeID) -> DefinitionID {
        *self.node_to_def.get(&id).expect("bug! node not tagged")
    }

    pub fn definition_kind(&self, id: DefinitionID) -> DefinitionKind {
        return *self.def_to_kind.get(&id).expect("bug! node not tagged");

        // if id.is_local(self.session().package_index) {
        // }

        // let resolutions = self.gcx.store.resolutions.borrow();
        // let data = resolutions.get(&id.package()).expect("resolution data");
        // let kind = *data.def_to_kind.get(&id).expect("def to kind");
        // kind
    }

    pub fn get_definition_scope(&self, id: DefinitionID) -> Scope<'a> {
        *self
            .definition_scope_mapping
            .get(&id)
            .expect("definition tagged scope")
    }
}

impl<'a, 'c> Resolver<'a, 'c> {
    pub fn create_scope(&self, scope: ScopeData<'a>) -> Scope<'a> {
        Interned::new_unchecked(self.arenas.bump.alloc(scope))
    }

    pub fn create_scope_entry(&self, entry: ScopeEntryData<'a>) -> ScopeEntry<'a> {
        Interned::new_unchecked(self.arenas.bump.alloc(entry))
    }

    pub fn create_usage(&self, usage: UsageEntryData<'a>) -> UsageEntry<'a> {
        Interned::new_unchecked(self.arenas.bump.alloc(usage))
    }

    pub fn create_scope_entry_from_usage(
        &self,
        used_entry: ScopeEntry<'a>,
        used_scope: Scope<'a>,
        user: UsageEntry<'a>,
    ) -> ScopeEntry<'a> {
        user.module_scope.set(Some(used_scope));
        Interned::new_unchecked(self.arenas.bump.alloc(ScopeEntryData {
            kind: ScopeEntryKind::Usage {
                used_entry,
                used_scope,
                user,
            },
            span: user.span,
        }))
    }

    pub fn per_ns<F: FnMut(&mut Self, ScopeNamespace)>(&mut self, mut f: F) {
        f(self, ScopeNamespace::Type);
        f(self, ScopeNamespace::Value);
        f(self, ScopeNamespace::Module);
    }
}

impl<'a, 'c> Resolver<'a, 'c> {
    pub fn define_in_scope(
        &mut self,
        scope: Scope<'a>,
        identifier: &Identifier,
        namespace: ScopeNamespace,
        resolution: Resolution,
    ) -> Result<(), ScopeEntry<'a>> {
        let entry = self.create_scope_entry(ScopeEntryData {
            kind: ScopeEntryKind::Resolution(resolution),
            span: identifier.span,
        });

        self.define_in_scope_internal(scope, &identifier.symbol, entry, namespace)
    }

    fn define_in_scope_internal(
        &mut self,
        scope: Scope<'a>,
        name: &EcoString,
        entry: ScopeEntry<'a>,
        namespace: ScopeNamespace,
    ) -> Result<(), ScopeEntry<'a>> {
        let mut table = scope.table.borrow_mut();
        self.define_in_scope_table(&mut table, name, entry, namespace)
    }

    fn define_in_scope_table(
        &self,
        table: &mut ScopeTable<'a>,
        name: &EcoString,
        entry: ScopeEntry<'a>,
        namespace: ScopeNamespace,
    ) -> Result<(), ScopeEntry<'a>> {
        use ScopeNamespace::*;
        let slot = table.entry(name.clone()).or_default();

        match namespace {
            Type => {
                // Forbid spelling if value/module already present or type already set
                if slot.ty.is_some() || !slot.values.is_empty() || slot.module.is_some() {
                    return Err(entry);
                }
                slot.ty = Some(entry);
                Ok(())
            }
            Value => {
                // Forbid if a type or module already uses this spelling
                if slot.ty.is_some() || slot.module.is_some() {
                    return Err(entry);
                }
                slot.values.push(entry);
                Ok(())
            }
            Module => {
                // Must be the only occupant
                if slot.ty.is_some() || !slot.values.is_empty() || slot.module.is_some() {
                    return Err(entry);
                }
                slot.module = Some(entry);
                Ok(())
            }
        }
    }
}

impl<'a, 'c> Resolver<'a, 'c> {
    pub fn resolve_module_path(
        &self,
        path: &Vec<Identifier>,
    ) -> Result<Scope<'a>, ResolutionError> {
        debug_assert!(!path.is_empty(), "non empty module path");
        let mut scope: Option<Scope<'a>> = None;
        for (index, identifier) in path.iter().enumerate() {
            let next_scope = if let Some(scope) = scope {
                let result = self.resolve_in_scope(identifier, scope, ScopeNamespace::Module);
                match result {
                    Ok(value) => match value {
                        ResolvedValue::Scope(scope) => Some(scope),
                        ResolvedValue::Resolution(_) => {
                            return Err(ResolutionError::NotAModule(identifier.clone()));
                        }
                    },
                    Err(e) => return Err(e),
                }
            } else if index == 0 {
                self.resolve_package(identifier)
            } else {
                None
            };

            let Some(next_scope) = next_scope else {
                return Err(ResolutionError::UnknownSymbol(identifier.clone()));
            };
            scope = Some(next_scope);
        }

        if let Some(scope) = scope {
            return Ok(scope);
        }
        unreachable!("we must always have a scope at this point")
    }

    fn resolve_package(&self, identifier: &Identifier) -> Option<Scope<'a>> {
        if identifier.symbol == self.compiler.config.name {
            return self.root_module_scope;
        }

        todo!("resolve external package");
        None
    }
}

impl<'a, 'c> Resolver<'a, 'c> {
    pub fn resolve_in_scope(
        &self,
        name: &Identifier,
        scope: Scope<'a>,
        namespace: ScopeNamespace,
    ) -> Result<ResolvedValue<'a>, ResolutionError> {
        let holder = self.find_holder_in_scope(name, scope, namespace)?;
        let resolution = holder.resolution();

        let scope = match resolution {
            Resolution::Definition(id, kind)
                if matches!(kind, DefinitionKind::Module | DefinitionKind::Namespace) =>
            {
                Some(self.get_definition_scope(id))
            }
            _ => None,
        };

        if let Some(scope) = scope {
            return Ok(ResolvedValue::Scope(scope));
        }

        return Ok(ResolvedValue::Resolution(resolution));
    }
    pub fn find_holder_in_scope(
        &self,
        name: &Identifier,
        scope: Scope<'a>,
        namespace: ScopeNamespace,
    ) -> Result<Holder<'a>, ResolutionError> {
        {
            let table = scope.table.borrow();
            let entry = table.get(&name.symbol);
            if let Some(entry) = entry {
                let x = match namespace {
                    ScopeNamespace::Type => {
                        if let Some(value) = entry.ty {
                            return Ok(Holder::Single(value));
                        } else {
                            return Err(ResolutionError::NotAType(name.clone()));
                        };
                    }
                    ScopeNamespace::Value => {
                        if !entry.values.is_empty() {
                            if entry.values.len() == 1
                                && let Some(&first) = entry.values.iter().next()
                            {
                                return Ok(Holder::Single(first));
                            } else {
                                return Ok(Holder::Overloaded(entry.values.clone()));
                            }
                        }
                    }
                    ScopeNamespace::Module => {
                        if let Some(entry) = entry.module {
                            return Ok(Holder::Single(entry));
                        } else {
                            return Err(ResolutionError::NotAModule(name.clone()));
                        };
                    }
                };

                // let res = self.convert_to_resolution(result);
                // return ResolutionResult::Res(res);
            }
        }

        Err(ResolutionError::UnknownSymbol(name.clone()))
    }
    pub fn resolve_in_scopes(
        &mut self,
        name: &Identifier,
        namespace: ScopeNamespace,
        scopes: &[LexicalScope<'a>],
    ) -> Option<ResolvedValue<'a>> {
        for scope in scopes.iter().rev() {
            // Check in Local Table
            let resolution = scope.table.get(&name.symbol);
            if let Some(resolution) = resolution {
                return Some(ResolvedValue::Resolution(resolution.clone()));
            }

            let scope = match scope.source {
                LexicalScopeSource::Scoped(scope) => scope,
                _ => continue,
            };

            {
                match &scope.kind {
                    ScopeKind::Block(..) | ScopeKind::File(..) => {
                        // see through
                    }
                    _ => break,
                }
            }
            let result = self.resolve_in_scope(name, scope, namespace);

            match result {
                Err(_) => continue,
                Ok(value) => return Some(value),
            }
        }

        None
    }
}

impl<'a, 'c> Resolver<'a, 'c> {
    pub fn import(
        &mut self,
        scope: Scope<'a>,
        name: Identifier,
        entry: ScopeEntry<'a>,
        ns: ScopeNamespace,
    ) -> Result<(), ResolutionError> {
        assert!(matches!(
            scope.kind,
            ScopeKind::File(..)
                | ScopeKind::Block(..)
                | ScopeKind::Definition(_, DefinitionKind::Namespace)
        ));

        let result = self.define_in_scope_internal(scope, &name.symbol, entry, ns);
        match result {
            Ok(_) => Ok(()),
            Err(e) => Err(ResolutionError::AlreadyInScope(name, e.span)),
        }
    }

    pub fn export(
        &mut self,
        scope: Scope<'a>,
        name: Identifier,
        entry: ScopeEntry<'a>,
        ns: ScopeNamespace,
    ) -> Result<(), ResolutionError> {
        assert!(matches!(
            scope.kind,
            ScopeKind::Definition(_, DefinitionKind::Namespace | DefinitionKind::Module)
        ));

        let result = self.define_in_scope_internal(scope, &name.symbol, entry, ns);
        match result {
            Ok(_) => Ok(()),
            Err(e) => Err(ResolutionError::AlreadyInScope(name, e.span)),
        }
    }
}
