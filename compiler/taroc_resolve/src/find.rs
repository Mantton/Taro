use crate::{arena::alloc_binding, resolver::Resolver};
use taroc_constants::STD_PREFIX;
use taroc_hir::{PackageIndex, PartialResolution, Resolution, SymbolNamespace};
use taroc_resolve_models::{
    BindingKey, ContextOrResolutionRoot, DefContextKind, DefinitionContext, Determinacy,
    ImplicitScopeSet, ImplicitScopes, LexicalScope, LexicalScopeBinding, LexicalScopeSource,
    NameBindingData, NameBindingKind, NameHolder, ParentScope, PathResult, PathSource, Segment,
};
use taroc_span::{Identifier, Symbol};

impl<'ctx> Resolver<'ctx> {
    pub fn resolve_path_with_scopes(
        &mut self,
        path: &[Segment],
        namespace: Option<SymbolNamespace>,
        scopes: &[LexicalScope<'ctx>],
        parent_scope: &ParentScope<'ctx>,
    ) -> PathResult<'ctx> {
        // let name: Vec<&str> = path.iter().map(|v| v.identifier.symbol.as_str()).collect();
        // println!("\n\n---- {}. {}", name.join("::"), path.len());
        let mut resulting_context: Option<ContextOrResolutionRoot> = None;
        for (index, segment) in path.iter().enumerate() {
            let record_resolution = |this: &mut Self, resolution: PartialResolution| {
                if let Some(id) = segment.id {
                    this.record_resolution(id, resolution);
                };
            };

            let is_last = index == path.len() - 1;
            let ns = if is_last {
                namespace.unwrap_or(SymbolNamespace::Type)
            } else {
                SymbolNamespace::Type
            };

            let name = segment.identifier.symbol;

            // Resolve Special Paths
            if ns == SymbolNamespace::Type {
                if index == 0 {
                    if name == Symbol::with("{{root}}") {
                        // Path Root
                        resulting_context =
                            Some(ContextOrResolutionRoot::PackageRootAndDependencyPrelude);
                        continue;
                    }
                }
            }

            // self.gcx.diagnostics.warn(
            //     format!("Resolving {} in {:?} NS", segment.identifier.symbol, ns),
            //     segment.identifier.span,
            // );
            // report special paths
            if name.is_path_segment_keyword() && index != 0 {
                todo!("report misplace keyword")
            }

            // For Nested Paths, The Non-Last Segments should resolve to a type
            let named_symbol = if let Some(context) = resulting_context {
                self.resolve_symbol_in_context(segment.identifier, ns, context, parent_scope)
            } else {
                let lexical_resolution = self.resolve_symbol_in_lexical_scope(
                    segment.identifier,
                    ns,
                    scopes,
                    parent_scope,
                );
                match lexical_resolution {
                    Some(LexicalScopeBinding::Declaration(binding)) => Ok(binding),
                    Some(LexicalScopeBinding::Resolution(resolution)) => {
                        if matches!(resolution, Resolution::Error) {
                            // Glob Ambiguity
                            Err(Determinacy::Undetermined)
                        } else {
                            record_resolution(self, PartialResolution::new(resolution.clone()));
                            return PathResult::NonContext(
                                PartialResolution::with_unresolved_segments(
                                    resolution,
                                    path.len() - 1,
                                ),
                            );
                        }
                    }
                    _ => Err(Determinacy::Determined),
                }
            };

            let named_symbol = match named_symbol {
                Ok(named_symbol) => named_symbol,
                Err(Determinacy::Undetermined) => return PathResult::Indeterminate,
                Err(Determinacy::Determined) => {
                    if let Some(ContextOrResolutionRoot::Context(ctx)) = resulting_context
                        && namespace.is_some()
                        && ctx.is_basic_def()
                    {
                        return PathResult::NonContext(
                            PartialResolution::with_unresolved_segments(
                                ctx.resolution().unwrap(),
                                path.len() - index,
                            ),
                        );
                    }

                    return PathResult::Failed {
                        segment: segment.identifier,
                        is_last_segment: is_last,
                    };
                }
            };

            // self.gcx
            //     .diagnostics
            //     .info("Resolved!".into(), segment.identifier.span);

            let resolution = named_symbol.resolution();
            let maybe_assoc = PathSource::Type.is_allowed(&resolution);

            if let Some(next_context) = named_symbol.context() {
                resulting_context = Some(ContextOrResolutionRoot::Context(next_context));
                record_resolution(self, PartialResolution::new(resolution));
            } else if namespace.is_some() && (is_last || maybe_assoc) {
                record_resolution(self, PartialResolution::new(resolution.clone()));
                let unresolved = path.len() - 1 - index;
                return PathResult::NonContext(PartialResolution::with_unresolved_segments(
                    resolution, unresolved,
                ));
            } else if matches!(resolution, Resolution::Error) {
                return PathResult::NonContext(PartialResolution::new(Resolution::Error));
            } else {
                return PathResult::Failed {
                    segment: segment.identifier,
                    is_last_segment: is_last,
                };
            }
        }

        match resulting_context {
            Some(_) => {
                return PathResult::Context(resulting_context.unwrap());
            }
            None => {
                unreachable!("must return failing resolution earlier")
            }
        }
    }
}

impl<'ctx> Resolver<'ctx> {
    pub fn resolve_symbol_in_context(
        &self,
        ident: Identifier,
        namespace: SymbolNamespace,
        context: ContextOrResolutionRoot<'ctx>,
        parent_scope: &ParentScope<'ctx>,
    ) -> Result<NameHolder<'ctx>, Determinacy> {
        let name = ident.symbol;
        let context = match context {
            ContextOrResolutionRoot::Context(context) => context,
            ContextOrResolutionRoot::PackageRootAndDependencyPrelude => {
                let binding = self.resolve_in_implicit_scopes(
                    ident,
                    ImplicitScopeSet::PackageAndDependencyRoot(namespace),
                    parent_scope,
                );

                return binding;
            }
        };

        // let symbols = context.namespace.borrow();
        // let symbols: std::collections::HashSet<Symbol> =
        //     symbols.data.keys().map(|f| f.symbol).collect();
        // println!(
        //     "\n\nSearching for {} in [{:?}]\nExplict Namespace ({:?})",
        //     name, context.kind, symbols
        // );

        let key = BindingKey::new(name, namespace);

        // Check Namespace
        let resolutions = context.namespace.borrow();
        let holder = resolutions.find(key);
        if let Some(holder) = holder {
            return Ok(holder);
        };

        // Check Imports
        let mut candidates = Vec::new();
        // Track if we encountered any undetermined resolutions
        let mut has_undetermined = false;

        match context.kind {
            DefContextKind::File | DefContextKind::Block => {
                for import in context.glob_imports.borrow().iter() {
                    if !import.is_resolved.get() {
                        continue;
                    }

                    let module_context = import
                        .module_context
                        .get()
                        .expect("module should be resolved");
                    match self.resolve_symbol_in_context(
                        ident,
                        namespace,
                        module_context,
                        parent_scope,
                    ) {
                        Ok(holder) => candidates.push(holder),
                        Err(Determinacy::Undetermined) => {
                            has_undetermined = true;
                        }
                        Err(Determinacy::Determined) => {}
                    }
                }
            }
            DefContextKind::Definition(
                _,
                taroc_hir::DefinitionKind::Module | taroc_hir::DefinitionKind::Namespace,
                _,
            ) => {
                for export in context.glob_exports.borrow().iter() {
                    if !export.is_resolved.get() {
                        continue;
                    }

                    let module_context = export
                        .module_context
                        .get()
                        .expect("module should be resolved");
                    match self.resolve_symbol_in_context(
                        ident,
                        namespace,
                        module_context,
                        parent_scope,
                    ) {
                        Ok(holder) => {
                            candidates.push(holder);
                        }
                        Err(Determinacy::Undetermined) => {
                            has_undetermined = true;
                        }
                        Err(Determinacy::Determined) => {}
                    }
                }
            }
            _ => {}
        }

        if has_undetermined {
            return Err(Determinacy::Undetermined);
        }

        if candidates.is_empty() {
            return Err(Determinacy::Determined);
        }

        if candidates.len() == 1 {
            let only_candidate = candidates
                .first()
                .expect("glob should have at least one candidate");
            Ok(*only_candidate)
        } else {
            Err(Determinacy::Undetermined)
        }
    }
}

impl<'ctx> Resolver<'ctx> {
    pub fn resolve_symbol_in_lexical_scope(
        &self,
        ident: Identifier,
        namespace: SymbolNamespace,
        scopes: &[LexicalScope<'ctx>],
        parent_scope: &ParentScope<'ctx>,
    ) -> Option<LexicalScopeBinding<'ctx>> {
        let name = ident.symbol;
        if name == Symbol::with("") {
            return Some(LexicalScopeBinding::Resolution(Resolution::Error));
        }

        let mut context = self.root_context;
        for (_, scope) in scopes.iter().enumerate().rev() {
            // Check Scope SymbolTable
            // println!("{:?}", scope.table);
            let resolution = scope.table.get(&name);
            if let Some(resolution) = resolution {
                return Some(LexicalScopeBinding::Resolution(resolution.clone()));
            }

            // Check for context
            context = match scope.source {
                LexicalScopeSource::Context(context) => context,
                _ => continue,
            };

            match context.kind {
                DefContextKind::Block | DefContextKind::File => {} // we see through these
                _ => {
                    break;
                }
            };

            let binding = self.resolve_symbol_in_context(
                ident,
                namespace,
                ContextOrResolutionRoot::Context(context),
                parent_scope,
            );

            match binding {
                Ok(binding) => {
                    return Some(LexicalScopeBinding::Declaration(binding));
                }
                _ => continue,
            }
        }

        self.resolve_in_implicit_scopes(
            ident,
            ImplicitScopeSet::FullResolution(namespace, context),
            parent_scope,
        )
        .ok()
        .map(LexicalScopeBinding::Declaration)
    }
}

impl<'ctx> Resolver<'ctx> {
    pub fn resolve_in_implicit_scopes(
        &self,
        ident: Identifier,
        set: ImplicitScopeSet<'ctx>,
        parent_scope: &ParentScope<'ctx>,
    ) -> Result<NameHolder<'ctx>, Determinacy> {
        if ident.is_path_segment_keyword() {
            return Err(Determinacy::Determined);
        }
        let ns = set.namespace();
        let name = ident.symbol;
        let result = self.visit_scopes(set, parent_scope, |this, scope| {
            let result = match scope {
                ImplicitScopes::Context(definition_context) => {
                    let holder = this.resolve_symbol_in_context(
                        ident,
                        ns,
                        ContextOrResolutionRoot::Context(definition_context),
                        parent_scope,
                    );

                    holder
                }
                ImplicitScopes::PackageRoot => {
                    let root = this.root_context;
                    let result = this.resolve_symbol_in_context(
                        ident,
                        ns,
                        ContextOrResolutionRoot::Context(root),
                        parent_scope,
                    );

                    match result {
                        Ok(holder) => Ok(holder),
                        Err(v) => Err(v),
                    }
                }

                ImplicitScopes::DependencyPrelude => {
                    let context = this.resolve_package_root(name);

                    match context {
                        Some((_, context)) => {
                            let binding = NameBindingData {
                                kind: NameBindingKind::Context(context),
                                span: ident.span,
                                vis: taroc_hir::TVisibility::Public,
                            };

                            let binding = alloc_binding(this.gcx, binding);
                            let holder = NameHolder::Single(binding);
                            Ok(holder)
                        }
                        None => Err(Determinacy::Determined),
                    }
                }
                ImplicitScopes::StdPrelude => Err(Determinacy::Determined), // TODO!
                ImplicitScopes::BuiltinPrelude => {
                    let holder = this.builin_types_bindings.get(&name);

                    match holder {
                        Some(holder) => Ok(*holder),
                        None => Err(Determinacy::Determined),
                    }
                }
            };

            match result {
                Ok(holder) => return Some(Ok(holder)),
                Err(_) => {}
            }
            None
        });

        if let Some(result) = result {
            return result;
        }

        return Err(Determinacy::Determined);
    }

    pub(crate) fn visit_scopes<T>(
        &self,
        scope_set: ImplicitScopeSet<'ctx>,
        parent_scope: &ParentScope<'ctx>,
        mut visitor: impl FnMut(&Self, ImplicitScopes<'ctx>) -> Option<T>,
    ) -> Option<T> {
        let (ns, is_root) = match scope_set {
            ImplicitScopeSet::All(ns) => (ns, false),
            ImplicitScopeSet::PackageAndDependencyRoot(ns) => (ns, true),
            ImplicitScopeSet::FullResolution(ns, _) => (ns, false),
        };

        let context = match scope_set {
            ImplicitScopeSet::FullResolution(_, definition_context) => definition_context,
            _ => parent_scope.context.nearest_context_scope(),
        };
        let mut scope = match ns {
            _ if is_root => ImplicitScopes::PackageRoot,
            _ => ImplicitScopes::Context(context),
        };

        loop {
            if let result @ Some(..) = visitor(self, scope) {
                return result;
            }

            scope = match scope {
                ImplicitScopes::PackageRoot => match ns {
                    SymbolNamespace::Type => ImplicitScopes::DependencyPrelude,
                    SymbolNamespace::Value => break,
                },
                ImplicitScopes::Context(context) => match context.parent {
                    Some(parent) => ImplicitScopes::Context(parent),
                    None => match ns {
                        SymbolNamespace::Type => ImplicitScopes::DependencyPrelude,
                        SymbolNamespace::Value => ImplicitScopes::StdPrelude,
                    },
                },
                ImplicitScopes::DependencyPrelude if is_root => break,
                ImplicitScopes::DependencyPrelude => ImplicitScopes::StdPrelude,
                ImplicitScopes::StdPrelude => match ns {
                    SymbolNamespace::Type => ImplicitScopes::BuiltinPrelude,
                    SymbolNamespace::Value => break,
                },
                ImplicitScopes::BuiltinPrelude => break,
            }
        }

        None
    }
}

impl<'ctx> Resolver<'ctx> {
    pub fn resolve_package_root(
        &self,
        name: Symbol,
    ) -> Option<(PackageIndex, DefinitionContext<'ctx>)> {
        // Refering to self
        if name.as_str() == &self.session().config.package_name() {
            return Some((self.session().index(), self.root_context));
        }

        // Refering to STD
        if name.as_str() == STD_PREFIX {
            let context = self
                .gcx
                .store
                .resolutions
                .borrow()
                .get(&PackageIndex::new(0))
                .expect("std to be resolved")
                .root;
            return Some((PackageIndex::new(0), context));
        }

        // Refering to Dependency
        if let Some(target) = self.session().config.dependency_map.get(name.as_str()) {
            let index = *self
                .gcx
                .store
                .package_mapping
                .borrow()
                .get(target)
                .expect("package index");
            let context = self
                .gcx
                .store
                .resolutions
                .borrow()
                .get(&index)
                .expect("package to be resolved")
                .root;
            return Some((index, context));
        }

        return None;
    }
}
