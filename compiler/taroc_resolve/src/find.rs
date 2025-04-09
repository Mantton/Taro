use crate::{models::ParentContext, resolver::Resolver};
use taroc_constants::STD_PREFIX;
use taroc_hir::{Resolution, TVisibility};
use taroc_resolve_models::{
    DefContextKind, DefinitionContext, Determinacy, LexicalScope, LexicalScopeBinding,
    LexicalScopeSource, NameBindingData, NameBindingKind, NameHolder, PathResult, Segment,
};
use taroc_span::Symbol;

#[derive(Clone, Copy)]
pub enum ResolutionState {
    Usage(Option<ParentContext>),
    Full,
    Alias,
}

impl<'ctx> Resolver<'ctx> {
    pub fn resolve_path_with_scopes(
        &mut self,
        path: &[Segment],
        scopes: &[LexicalScope<'ctx>],
        state: ResolutionState,
    ) -> PathResult<'ctx> {
        // let name: Vec<&str> = path.iter().map(|v| v.identifier.symbol.as_str()).collect();
        // println!("\n---- {}", name.join("::"));
        let mut resulting_context: Option<DefinitionContext<'ctx>> = None;
        for (index, segment) in path.iter().enumerate() {
            // println!("Segment ({:?})", segment.id);
            // self.context
            //     .diagnostics
            //     .info("Resolving".into(), segment.identifier.span);

            // package root
            if index == 0 && segment.identifier.symbol == Symbol::with("{{root}}") {
                resulting_context = self.packages_root;
                continue;
            }

            let is_last = index == path.len() - 1;
            let name = &segment.identifier.symbol;

            let record_resolution = |this: &mut Self, resolution: Resolution| {
                if let Some(id) = segment.id {
                    this.rescord_resolution(id, resolution.clone());
                };
            };

            // For Nested Paths, The Non-Last Segments should resolve to a type

            let named_symbol = if let Some(context) = resulting_context {
                self.resolve_symbol_in_context(name, context, state)
            } else {
                let lexical_resolution = self.resolve_symbol_in_lexical_scope(name, scopes, state);
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
                                resulting_context = Some(new_context);
                                continue;
                            } else {
                                if !is_last {
                                    self.context.diagnostics.error(
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
                resulting_context = Some(next_context);
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
        name: &Symbol,
        context: DefinitionContext<'ctx>,
        state: ResolutionState,
    ) -> Result<NameHolder<'ctx>, Determinacy> {
        let resolutions = context.resolutions.borrow();
        // let symbols: Vec<&Symbol> = resolutions.bindings.keys().collect();
        // println!("Find {} in {:?}, {:?}", name, symbols, context.resolution());
        let binding = resolutions.find(name);

        if let Some(binding) = binding {
            return Ok(binding);
        }

        let resolutions = context.resolutions.borrow();
        let binding = resolutions.find(name);

        if let Some(binding) = binding {
            return Ok(binding);
        }

        if context == self.packages_root.unwrap() {
            if let Some(package) = self.resolve_package_root(*name) {
                let binding = self.alloc_binding(NameBindingData {
                    kind: NameBindingKind::Context(package),
                    span: context.span,
                    vis: TVisibility::Public,
                });

                let holder = NameHolder::Single(binding);
                return Ok(holder);
            } else {
                match state {
                    ResolutionState::Usage(parent) if let Some(parent) = parent => {
                        let module_context = self
                            .get_context(&parent.module)
                            .expect("modules must always have a definition context");
                        let module_scope = LexicalScope {
                            source: LexicalScopeSource::Context(module_context),
                            table: Default::default(),
                        };

                        let file_context = self.get_file_context(&parent.file);
                        let file_scope = LexicalScope {
                            source: LexicalScopeSource::Context(file_context),
                            table: Default::default(),
                        };
                        let scopes = vec![module_scope, file_scope];
                        let result = self.resolve_symbol_in_lexical_scope(
                            name,
                            &scopes,
                            ResolutionState::Full,
                        );

                        let Some(binding) = result else {
                            return Err(Determinacy::Determined);
                        };

                        match binding {
                            LexicalScopeBinding::Declaration(name_holder) => {
                                return Ok(name_holder);
                            }
                            LexicalScopeBinding::Resolution(_) => {
                                todo!("found resolution should not happen")
                            }
                        }
                    }
                    _ => {}
                }
            }

            return Err(Determinacy::Determined);
        }

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
                    match self.resolve_symbol_in_context(name, module_context, state) {
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
                    match self.resolve_symbol_in_context(name, module_context, state) {
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
        name: &Symbol,
        scopes: &[LexicalScope<'ctx>],
        state: ResolutionState,
    ) -> Option<LexicalScopeBinding<'ctx>> {
        if name == &Symbol::with("") {
            return Some(LexicalScopeBinding::Resolution(Resolution::Error));
        }

        for (_, scope) in scopes.iter().enumerate().rev() {
            // Check Scope SymbolTable
            let resolution = scope.table.get(name);
            if let Some(resolution) = resolution {
                return Some(LexicalScopeBinding::Resolution(resolution.clone()));
            }

            // Check for context
            let context = match scope.source {
                LexicalScopeSource::Context(context) => context,
                _ => continue,
            };

            let binding = self.resolve_symbol_in_context(name, context, state);

            match binding {
                Ok(binding) => {
                    return Some(LexicalScopeBinding::Declaration(binding));
                }
                Err(Determinacy::Determined) => {
                    continue;
                } // unable to resolve
                Err(Determinacy::Undetermined) => {
                    return Some(LexicalScopeBinding::Resolution(Resolution::Error));
                }
            }
        }

        if *name == Symbol::with("{{root}}") && matches!(state, ResolutionState::Usage(..)) {
            let root = self.packages_root.unwrap();
            let binding = self.alloc_binding(NameBindingData {
                kind: NameBindingKind::Context(root),
                span: root.span,
                vis: taroc_hir::TVisibility::Public,
            });
            return Some(LexicalScopeBinding::Declaration(NameHolder::Single(
                binding,
            )));
        }

        return None;
    }
}

impl<'ctx> Resolver<'ctx> {
    pub fn resolve_package_root(&self, name: Symbol) -> Option<DefinitionContext<'ctx>> {
        // Refering to self
        if name.as_str() == &self.session().config.package_name() {
            return self.root_context;
        }

        // Refering to STD
        if name.as_str() == STD_PREFIX {
            let context = self
                .context
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
                .context
                .store
                .package_mapping
                .borrow()
                .get(target)
                .expect("package index");
            let context = self
                .context
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
