use crate::{
    PackageIndex,
    ast::{Identifier, NodeID, PathSegment},
    compile::context::GlobalContext,
    diagnostics::DiagCtx,
    sema::resolve::models::{
        DefinitionID, DefinitionIndex, DefinitionKind, ExpressionResolutionState, Holder,
        ImplicitScope, LexicalScope, LexicalScopeSource, PathResult, PrimaryType, Resolution,
        ResolutionError, ResolutionOutput, ResolutionSource, ResolutionState, ResolvedValue, Scope,
        ScopeData, ScopeEntry, ScopeEntryData, ScopeEntryKind, ScopeKind, ScopeNamespace,
        ScopeTable, UsageEntry, UsageEntryData,
    },
    span::{FileID, Symbol},
    utils::intern::Interned,
};
use rustc_hash::FxHashMap;

pub struct Resolver<'arena> {
    pub context: GlobalContext<'arena>,
    node_to_def: FxHashMap<NodeID, DefinitionID>,
    def_to_kind: FxHashMap<DefinitionID, DefinitionKind>,
    pub def_to_ident: FxHashMap<DefinitionID, Identifier>,
    def_to_parent: FxHashMap<DefinitionID, DefinitionID>,
    next_index: usize,
    pub unresolved_imports: Vec<UsageEntry<'arena>>,
    pub unresolved_exports: Vec<UsageEntry<'arena>>,
    pub root_module_scope: Option<Scope<'arena>>,
    pub file_scope_mapping: FxHashMap<FileID, Scope<'arena>>,
    pub definition_scope_mapping: FxHashMap<DefinitionID, Scope<'arena>>,
    pub block_scope_mapping: FxHashMap<NodeID, Scope<'arena>>,
    pub builin_types_bindings: FxHashMap<Symbol, Resolution>,
    pub resolutions: FxHashMap<NodeID, ResolutionState>,
    pub expression_resolutions: FxHashMap<NodeID, ExpressionResolutionState>,
}

impl<'a> Resolver<'a> {
    pub fn new(context: GlobalContext<'a>) -> Resolver<'a> {
        Resolver {
            context,
            node_to_def: Default::default(),
            def_to_kind: Default::default(),
            def_to_ident: Default::default(),
            def_to_parent: Default::default(),
            next_index: 0,

            unresolved_exports: Default::default(),
            unresolved_imports: Default::default(),
            root_module_scope: None,

            file_scope_mapping: Default::default(),
            definition_scope_mapping: Default::default(),
            block_scope_mapping: Default::default(),

            resolutions: Default::default(),
            expression_resolutions: Default::default(),

            builin_types_bindings: PrimaryType::ALL
                .iter()
                .map(|&ty| (Symbol::new(ty.name_str()), Resolution::PrimaryType(ty)))
                .collect(),
        }
    }

    pub fn dcx(&self) -> &DiagCtx {
        &self.context.dcx
    }
}

impl<'a> Resolver<'a> {
    pub fn create_definition(
        &mut self,
        identifier: Identifier,
        node_id: NodeID,
        kind: DefinitionKind,
        parent: Option<DefinitionID>,
    ) -> DefinitionID {
        let index = {
            let parent_index = self.package_index();
            let def_index = DefinitionIndex::new(self.next_index);
            DefinitionID::new(parent_index, def_index)
        };

        {
            self.node_to_def.insert(node_id, index);
            self.def_to_kind.insert(index, kind);
            self.def_to_ident.insert(index, identifier);
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
        if id.is_local_to_index(self.package_index()) {
            return *self.def_to_kind.get(&id).expect("bug! node not tagged");
        } else {
            let resolutions = self.context.store.resolution_outputs.borrow();
            let package = resolutions.get(&id.package()).unwrap();
            let kind = *package.definition_to_kind.get(&id).unwrap();
            kind
        }
    }

    pub fn get_definition_scope(&self, id: DefinitionID) -> Scope<'a> {
        if id.is_local_to_index(self.package_index()) {
            *self
                .definition_scope_mapping
                .get(&id)
                .expect("definition tagged scope")
        } else {
            let resolutions = self.context.store.resolution_outputs.borrow();
            let package = resolutions.get(&id.package()).unwrap();
            let scope = *package.definition_scope_mapping.get(&id).unwrap();
            scope
        }
    }

    pub fn package_index(&self) -> PackageIndex {
        self.context.config.index
    }
}

impl<'a> Resolver<'a> {
    pub fn create_scope(&self, scope: ScopeData<'a>) -> Scope<'a> {
        Interned::new_unchecked(self.context.store.arenas.scopes.alloc(scope))
    }

    pub fn create_scope_entry(&self, entry: ScopeEntryData<'a>) -> ScopeEntry<'a> {
        Interned::new_unchecked(self.context.store.arenas.scope_entries.alloc(entry))
    }

    pub fn create_usage(&self, usage: UsageEntryData<'a>) -> UsageEntry<'a> {
        Interned::new_unchecked(self.context.store.arenas.usage_entries.alloc(usage))
    }

    pub fn create_scope_entry_from_usage(
        &self,
        used_entry: ScopeEntry<'a>,
        used_scope: Scope<'a>,
        user: UsageEntry<'a>,
    ) -> ScopeEntry<'a> {
        user.module_scope.set(Some(used_scope));
        self.create_scope_entry(ScopeEntryData {
            kind: ScopeEntryKind::Usage {
                used_entry,
                used_scope,
                user,
            },
            span: user.span,
        })
    }
}

impl<'a> Resolver<'a> {
    pub fn record_resolution(&mut self, id: NodeID, state: ResolutionState) {
        if self.resolutions.insert(id, state).is_some() {
            panic!("bug – multiple resolutions recorded for node")
        }
    }

    pub fn get_resolution(&self, id: NodeID) -> Option<ResolutionState> {
        self.resolutions.get(&id).cloned()
    }
}

impl<'a> Resolver<'a> {
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

        self.define_in_scope_internal(scope, identifier.symbol, entry, namespace)
    }

    fn define_in_scope_internal(
        &mut self,
        scope: Scope<'a>,
        name: Symbol,
        entry: ScopeEntry<'a>,
        namespace: ScopeNamespace,
    ) -> Result<(), ScopeEntry<'a>> {
        let mut table = scope.table.borrow_mut();
        self.define_in_scope_table(&mut table, name, entry, namespace)
    }

    fn define_in_scope_table(
        &self,
        table: &mut ScopeTable<'a>,
        name: Symbol,
        entry: ScopeEntry<'a>,
        namespace: ScopeNamespace,
    ) -> Result<(), ScopeEntry<'a>> {
        use ScopeNamespace::*;
        let slot = table.entry(name).or_default();

        match namespace {
            Type => {
                // Forbid spelling if value already present or type already set
                if slot.ty.is_some() || !slot.values.is_empty() {
                    return Err(entry);
                }
                slot.ty = Some(entry);
                Ok(())
            }
            Value => {
                // Forbid if a type already uses this name
                if slot.ty.is_some() {
                    return Err(entry);
                }
                slot.values.push(entry);
                Ok(())
            }
        }
    }
}

impl<'a> Resolver<'a> {
    pub fn resolve_module_path(
        &self,
        path: &Vec<Identifier>,
    ) -> Result<Scope<'a>, ResolutionError> {
        debug_assert!(!path.is_empty(), "non empty module path");
        let mut scope: Option<Scope<'a>> = None;
        for (index, identifier) in path.iter().enumerate() {
            let next_scope = if let Some(scope) = scope {
                let result = self.resolve_in_scope(identifier, scope, ScopeNamespace::Type);
                match result {
                    Ok(value) => match value {
                        ResolvedValue::Scope(scope) => {
                            if let Some(resolution) = scope.resolution() {
                                let is_module = matches!(
                                    resolution,
                                    Resolution::Definition(_, DefinitionKind::Module)
                                );

                                if !is_module {
                                    return Err(ResolutionError::Expectation {
                                        expectation: ResolutionSource::Module,
                                        provided: resolution,
                                        span: identifier.span,
                                    });
                                }

                                Some(scope)
                            } else {
                                unreachable!("scope must provide resolution")
                            }
                        } // TODO: We need to check that this is actually an importable module
                        ResolvedValue::Resolution(provided) => {
                            return Err(ResolutionError::Expectation {
                                expectation: ResolutionSource::Module,
                                provided,
                                span: identifier.span,
                            });
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
                return Err(ResolutionError::UnknownSymbol(*identifier));
            };
            scope = Some(next_scope);
        }

        if let Some(scope) = scope {
            return Ok(scope);
        }
        unreachable!("we must always have a scope at this point")
    }

    fn resolve_package(&self, identifier: &Identifier) -> Option<Scope<'a>> {
        if identifier.symbol.as_str() == self.context.config.name {
            return self.root_module_scope;
        }

        if let Some(identifier) = self
            .context
            .config
            .dependencies
            .get(identifier.symbol.as_str())
            && let Some(index) = self
                .context
                .store
                .package_mapping
                .borrow()
                .get(identifier.as_str())
        {
            let mapping = self.context.store.resolution_outputs.borrow();
            return mapping.get(index).map(|table| table.root_scope).clone();
        };

        None
    }
}

impl<'a> Resolver<'a> {
    pub fn resolve_path_in_scopes(
        &mut self,
        path: &[PathSegment],
        namespace: ScopeNamespace,
        scopes: &[LexicalScope<'a>],
    ) -> PathResult<'a> {
        let mut resulting_scope: Option<Scope<'a>> = None;
        for (index, segment) in path.iter().enumerate() {
            let is_last = index == path.len() - 1;

            let namespace = if is_last {
                namespace
            } else {
                ScopeNamespace::Type
            };

            let result = if let Some(scope) = resulting_scope {
                self.resolve_in_scope(&segment.identifier, scope, namespace)
            } else {
                self.resolve_in_lexical_scopes(&segment.identifier, namespace, scopes)
            };

            let result = match result {
                Ok(result) => result,
                Err(e) => {
                    return PathResult::Failed { error: e };
                }
            };

            let resolution = result.resolution();
            let possibly_associated_type = ResolutionSource::Type.is_allowed(&resolution);

            if let Some(scope) = result.scope() {
                self.record_resolution(segment.id, ResolutionState::Complete(resolution));
                resulting_scope = Some(scope)
            } else if is_last {
                self.record_resolution(segment.id, ResolutionState::Complete(resolution.clone()));
                return PathResult::Resolution(ResolutionState::Complete(resolution));
            } else if possibly_associated_type {
                self.record_resolution(segment.id, ResolutionState::Complete(resolution.clone()));
                let unresolved_count = path.len() - 1 - index;
                return PathResult::Resolution(ResolutionState::Partial {
                    resolution,
                    unresolved_count,
                });
            } else {
                return PathResult::Failed {
                    error: ResolutionError::UnknownSymbol(segment.identifier),
                };
            }
        }

        match resulting_scope {
            Some(scope) => {
                return PathResult::Scope(scope);
            }
            None => {
                unreachable!("must return failing resolution earlier")
            }
        }
    }

    pub fn resolve_in_scope(
        &self,
        name: &Identifier,
        scope: Scope<'a>,
        namespace: ScopeNamespace,
    ) -> Result<ResolvedValue<'a>, ResolutionError> {
        if let Some(holder) = self.find_holder_in_scope(name, scope, namespace) {
            let resolution = holder.resolution();
            match resolution {
                Resolution::Definition(id, kind)
                    if matches!(kind, DefinitionKind::Module | DefinitionKind::Namespace) =>
                {
                    return Ok(ResolvedValue::Scope(self.get_definition_scope(id)));
                }
                _ => return Ok(ResolvedValue::Resolution(resolution)),
            };
        }

        let usages = match scope.kind {
            ScopeKind::File(..) | ScopeKind::Block(..) => &scope.glob_imports,
            ScopeKind::Definition(_, DefinitionKind::Module | DefinitionKind::Namespace) => {
                &scope.glob_exports
            }
            _ => return Err(ResolutionError::UnknownSymbol(*name)),
        };

        let mut candidates = vec![];
        for usage in usages.borrow().iter() {
            let scope = usage.module_scope.get();
            let Some(scope) = scope else {
                continue;
            };

            let result = self.resolve_in_scope(name, scope, namespace);
            match result {
                Ok(value) => {
                    candidates.push(value);
                }
                Err(_) => continue,
            }
        }

        match candidates.len() {
            0 => Err(ResolutionError::UnknownSymbol(*name)),
            1 => Ok(candidates.into_iter().next().unwrap()),
            _ => {
                match namespace {
                    ScopeNamespace::Type => {
                        return Err(ResolutionError::UnknownSymbol(*name));
                    }
                    ScopeNamespace::Value => {
                        // We can create a candidate set
                        let ids: Vec<_> = candidates
                            .into_iter()
                            .flat_map(|c| match c.resolution() {
                                Resolution::Definition(id, kind) => Some((id, kind)),
                                _ => None,
                            })
                            .collect();

                        let all_are_functions = ids
                            .iter()
                            .all(|(_, k)| matches!(k, DefinitionKind::Function));

                        if all_are_functions {
                            let ids = ids.into_iter().map(|(id, _)| id).collect();
                            return Ok(ResolvedValue::Resolution(Resolution::FunctionSet(ids)));
                        } else {
                            return Err(ResolutionError::AmbiguousUsage(*name));
                        }
                    }
                }
            }
        }
    }
    pub fn find_holder_in_scope(
        &self,
        name: &Identifier,
        scope: Scope<'a>,
        namespace: ScopeNamespace,
    ) -> Option<Holder<'a>> {
        {
            let table = scope.table.borrow();
            let entry = table.get(&name.symbol);
            if let Some(entry) = entry {
                match namespace {
                    ScopeNamespace::Type => {
                        if let Some(value) = entry.ty {
                            return Some(Holder::Single(value));
                        }
                    }
                    ScopeNamespace::Value => {
                        if !entry.values.is_empty() {
                            if entry.values.len() == 1
                                && let Some(&first) = entry.values.iter().next()
                            {
                                return Some(Holder::Single(first));
                            } else {
                                return Some(Holder::Overloaded(entry.values.clone()));
                            }
                        }
                    }
                };
            }
        }

        None
    }

    pub fn resolve_in_lexical_scopes(
        &self,
        name: &Identifier,
        namespace: ScopeNamespace,
        scopes: &[LexicalScope<'a>],
    ) -> Result<ResolvedValue<'a>, ResolutionError> {
        for scope in scopes.iter().rev() {
            // Check in Local Table
            let resolution = scope.table.get(&name.symbol);
            if let Some(resolution) = resolution {
                return Ok(ResolvedValue::Resolution(resolution.clone()));
            }

            let scope = match scope.source {
                LexicalScopeSource::Scoped(scope) => scope,
                _ => continue,
            };

            let result = self.resolve_in_scope(name, scope, namespace);

            match result {
                Err(ResolutionError::AmbiguousUsage(name)) => {
                    return Err(ResolutionError::AmbiguousUsage(name));
                }
                Err(_) => {}
                Ok(value) => return Ok(value),
            }

            match &scope.kind {
                ScopeKind::Block(..) | ScopeKind::File(..) => {
                    // see through to outer scopes
                }
                _ => break,
            }
        }

        let implicit_value = self.resolve_in_implicit_scopes(name, namespace);
        if let Some(value) = implicit_value {
            return Ok(value);
        }
        Err(ResolutionError::UnknownSymbol(*name))
    }
}

impl<'a> Resolver<'a> {
    fn resolve_in_implicit_scopes(
        &self,
        name: &Identifier,
        namespace: ScopeNamespace,
    ) -> Option<ResolvedValue<'a>> {
        let scopes: &[ImplicitScope] = match namespace {
            ScopeNamespace::Type => &[
                ImplicitScope::StdPrelude,
                ImplicitScope::Packages,
                ImplicitScope::BuiltinTypesPrelude,
            ],
            ScopeNamespace::Value => &[
                ImplicitScope::StdPrelude,
                ImplicitScope::BuiltinFunctionsPrelude,
            ],
        };

        for scope in scopes.into_iter() {
            match scope {
                ImplicitScope::Packages => {
                    let package = self.resolve_package(name);
                    if let Some(package) = package {
                        return Some(ResolvedValue::Scope(package));
                    };
                }
                ImplicitScope::StdPrelude => {}
                ImplicitScope::BuiltinFunctionsPrelude => {}
                ImplicitScope::BuiltinTypesPrelude => {
                    let value = self.builin_types_bindings.get(&name.symbol);
                    if let Some(value) = value {
                        return Some(ResolvedValue::Resolution(value.clone()));
                    }
                }
            }
        }

        None
    }
}

impl<'a> Resolver<'a> {
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

        let result = self.define_in_scope_internal(scope, name.symbol, entry, ns);
        match result {
            Ok(_) => Ok(()),
            Err(_) => Err(ResolutionError::AlreadyInScope(name)),
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

        let result = self.define_in_scope_internal(scope, name.symbol, entry, ns);
        match result {
            Ok(_) => Ok(()),
            Err(_) => Err(ResolutionError::AlreadyInScope(name)),
        }
    }
}

impl<'a> Resolver<'a> {
    pub fn build_output(self) -> ResolutionOutput<'a> {
        ResolutionOutput {
            resolutions: self.resolutions,
            node_to_definition: self.node_to_def,
            definition_scope_mapping: self.definition_scope_mapping,
            definition_to_kind: self.def_to_kind,
            definition_to_parent: self.def_to_parent,
            definition_to_ident: self.def_to_ident,
            expression_resolutions: self.expression_resolutions,
            root_scope: self.root_module_scope.unwrap(),
        }
    }
}
