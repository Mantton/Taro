use std::thread::Scope;

use crate::{arena::alloc_binding, resolver::Resolver};
use taroc_constants::STD_PREFIX;
use taroc_hir::{Resolution, SymbolNamespace};
use taroc_resolve_models::{
    BindingKey, ContextOrResolutionRoot, DefContextKind, DefinitionContext, Determinacy,
    ImplicitScopeSet, ImplicitScopes, LexicalScope, LexicalScopeBinding, LexicalScopeSource,
    NameBindingData, NameBindingKind, NameHolder, ParentScope, PathResult, Segment,
};
use taroc_span::{Span, Symbol};

impl<'ctx> Resolver<'ctx> {
    pub fn resolve_path_with_scopes(
        &mut self,
        path: &[Segment],
        namespace: Option<SymbolNamespace>,
        scopes: &[LexicalScope<'ctx>],
        parent_scope: &ParentScope<'ctx>,
    ) -> PathResult<'ctx> {
        // let name: Vec<&str> = path.iter().map(|v| v.identifier.symbol.as_str()).collect();
        // println!("\n---- {}. {}", name.join("::"), path.len());
        let mut resulting_context: Option<ContextOrResolutionRoot> = None;
        for (index, segment) in path.iter().enumerate() {
            // println!("Segment ({:?})", segment.id);
            // self.context
            //     .diagnostics
            //     .info("Resolving".into(), segment.identifier.span);
            let record_resolution = |this: &mut Self, resolution: Resolution| {
                if let Some(id) = segment.id {
                    this.rescord_resolution(id, resolution.clone());
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

            // report special paths
            if name.is_path_segment_keyword() && index != 0 {
                todo!("report misplace keyword")
            }

            // For Nested Paths, The Non-Last Segments should resolve to a type

            let named_symbol = if let Some(context) = resulting_context {
                self.resolve_symbol_in_context(name, ns, context, parent_scope)
            } else {
                let lexical_resolution =
                    self.resolve_symbol_in_lexical_scope(name, ns, scopes, parent_scope);
                match lexical_resolution {
                    Some(LexicalScopeBinding::Declaration(binding)) => Ok(binding),
                    Some(LexicalScopeBinding::Resolution(resolution)) => {
                        if matches!(resolution, Resolution::Error) {
                            // Glob Ambiguity
                            Err(Determinacy::Undetermined)
                        } else {
                            record_resolution(self, resolution.clone());
                            let def_id = resolution.def_id();
                            if let Some(id) = def_id
                                && let Some(new_context) = self.get_context(&id)
                            {
                                resulting_context =
                                    Some(ContextOrResolutionRoot::Context(new_context));
                                continue;
                            } else {
                                if !is_last {
                                    self.gcx.diagnostics.error(
                                        format!(
                                            "{} does not have a namespace",
                                            segment.identifier.symbol
                                        ),
                                        segment.identifier.span,
                                    );
                                }
                                return PathResult::NonContext(resolution);
                            }
                        }
                    }
                    _ => Err(Determinacy::Determined),
                }
            };

            let named_symbol = match named_symbol {
                Ok(named_symbol) => named_symbol,
                Err(Determinacy::Undetermined) => return PathResult::Indeterminate,
                Err(Determinacy::Determined) => {
                    return PathResult::Failed {
                        segment: segment.identifier,
                        is_last_segment: is_last,
                    };
                }
            };

            let resolution = named_symbol.resolution();

            if let Some(next_context) = named_symbol.context() {
                resulting_context = Some(ContextOrResolutionRoot::Context(next_context));
                record_resolution(self, resolution.clone());
            } else if is_last {
                record_resolution(self, resolution.clone());
                return PathResult::NonContext(resolution);
            } else if matches!(resolution, Resolution::Error) {
                return PathResult::NonContext(Resolution::Error);
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
        name: Symbol,
        namespace: SymbolNamespace,
        context: ContextOrResolutionRoot<'ctx>,
        parent_scope: &ParentScope<'ctx>,
    ) -> Result<NameHolder<'ctx>, Determinacy> {
        let context = match context {
            ContextOrResolutionRoot::Context(context) => context,
            ContextOrResolutionRoot::PackageRootAndDependencyPrelude => {
                let binding = self.resolve_in_implicit_scopes(
                    name,
                    ImplicitScopeSet::PackageAndDependencyRoot(namespace),
                    parent_scope,
                );

                return binding;
            }
        };

        // let symbols: Vec<&Symbol> = resolutions.bindings.keys().collect();
        // println!("Find {} in {:?}, {:?}", name, symbols, context.resolution());
        let key = BindingKey::new(name, namespace);

        // Check Namespace
        let resolutions = context.namespace.borrow();
        let holder = resolutions.find(key);
        if let Some(holder) = holder {
            return Ok(holder);
        };

        // Check Export namespace
        let resolutions = context.explicit_exports.borrow();
        let holder = resolutions.find(key);
        if let Some(holder) = holder {
            return Ok(holder);
        };

        // if context == self.packages_root.unwrap() {
        //     if let Some(package) = self.resolve_package_root(name) {
        //         let binding = self.alloc_binding(NameBindingData {
        //             kind: NameBindingKind::Context(package),
        //             span: context.span,
        //             vis: TVisibility::Public,
        //         });

        //         let holder = NameHolder::Single(binding);
        //         return Ok(holder);
        //     } else {
        //         match state {
        //             ResolutionState::Usage(parent) if let Some(parent) = parent => {
        //                 let module_context = self
        //                     .get_context(&parent.module)
        //                     .expect("modules must always have a definition context");
        //                 let module_scope = LexicalScope {
        //                     source: LexicalScopeSource::Context(module_context),
        //                     table: Default::default(),
        //                 };

        //                 let file_context = self.get_file_context(&parent.file);
        //                 let file_scope = LexicalScope {
        //                     source: LexicalScopeSource::Context(file_context),
        //                     table: Default::default(),
        //                 };
        //                 let scopes = vec![module_scope, file_scope];
        //                 let result = self.resolve_symbol_in_lexical_scope(
        //                     name,
        //                     namespace,
        //                     &scopes,
        //                     ResolutionState::Full,
        //                 );

        //                 let Some(binding) = result else {
        //                     return Err(Determinacy::Determined);
        //                 };

        //                 match binding {
        //                     LexicalScopeBinding::Declaration(name_holder) => {
        //                         return Ok(name_holder);
        //                     }
        //                     LexicalScopeBinding::Resolution(_) => {
        //                         todo!("found resolution should not happen")
        //                     }
        //                 }
        //             }
        //             _ => {}
        //         }
        //     }

        //     return Err(Determinacy::Determined);
        // }

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
                        name,
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
                        name,
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
        name: Symbol,
        namespace: SymbolNamespace,
        scopes: &[LexicalScope<'ctx>],
        parent_scope: &ParentScope<'ctx>,
    ) -> Option<LexicalScopeBinding<'ctx>> {
        if name == Symbol::with("") {
            return Some(LexicalScopeBinding::Resolution(Resolution::Error));
        }

        let mut context = self.root_context;
        for (_, scope) in scopes.iter().enumerate().rev() {
            // Check Scope SymbolTable
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
                DefContextKind::Block | DefContextKind::File => {}
                _ => break,
            };

            let binding = self.resolve_symbol_in_context(
                name,
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
            name,
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
        name: Symbol,
        set: ImplicitScopeSet<'ctx>,
        parent_scope: &ParentScope<'ctx>,
    ) -> Result<NameHolder<'ctx>, Determinacy> {
        println!("Searching For {name}");
        if name.is_path_segment_keyword() {
            return Err(Determinacy::Determined);
        }
        let ns = set.namespace();
        let result = self.visit_scopes(set, parent_scope, |this, scope| {
            let result = match scope {
                ImplicitScopes::Context(definition_context) => {
                    let holder = this.resolve_symbol_in_context(
                        name,
                        ns,
                        ContextOrResolutionRoot::Context(definition_context),
                        parent_scope,
                    );

                    holder
                }
                ImplicitScopes::PackageRoot => {
                    let root = this.root_context;
                    let result = this.resolve_symbol_in_context(
                        name,
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
                        Some(context) => {
                            let binding = NameBindingData {
                                kind: NameBindingKind::Context(context),
                                span: Span::module(),
                                vis: taroc_hir::TVisibility::Public,
                            };

                            let binding = alloc_binding(this.gcx, binding);
                            let holder = NameHolder::Single(binding);
                            Ok(holder)
                        }
                        None => todo!("not found"),
                    }
                }
                ImplicitScopes::StdPrelude => todo!(),
                ImplicitScopes::BuiltinPrelude => todo!(),
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
            let visit = true;

            if visit {
                if let result @ Some(..) = visitor(self, scope) {
                    return result;
                }
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
    pub fn resolve_package_root(&self, name: Symbol) -> Option<DefinitionContext<'ctx>> {
        // Refering to self
        if name.as_str() == &self.session().config.package_name() {
            return Some(self.root_context);
        }

        // Refering to STD
        if name.as_str() == STD_PREFIX {
            let context = self
                .gcx
                .store
                .resolutions
                .borrow()
                .get(&0)
                .expect("std to be resolved")
                .root;
            return Some(context);
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
            return Some(context);
        }

        return None;
    }
}
