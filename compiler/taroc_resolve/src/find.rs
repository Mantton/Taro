use crate::resolver::Resolver;
use taroc_hir::{PartialRes, Resolution, SymbolNamespace};
use taroc_resolve_models::{
    DefContextKind, DefinitionContext, Determinacy, LexicalScope, LexicalScopeBinding,
    LexicalScopeSource, NameHolder, PathResult, PathSource, Segment,
};
use taroc_span::Symbol;

impl<'ctx> Resolver<'ctx> {
    pub fn resolve_path_with_scopes(
        &mut self,
        path: &[Segment],
        ns: SymbolNamespace,
        scopes: &[LexicalScope<'ctx>],
    ) -> PathResult<'ctx> {
        // let name: Vec<&str> = path.iter().map(|v| v.identifier.symbol.as_str()).collect();
        // println!("\n---- {}", name.join("::"));
        let mut context: Option<DefinitionContext<'ctx>> = None;
        for (index, segment) in path.iter().enumerate() {
            // println!("Segment ({:?})", segment.id);
            // self.context
            //     .diagnostics
            //     .info("Resolving".into(), segment.identifier.span);

            let is_last = index == path.len() - 1;
            let name = &segment.identifier.symbol;

            let record_resolution = |this: &mut Self, resolution: Resolution| {
                if let Some(id) = segment.id {
                    this.record_paratial_resolution(id, PartialRes::new(resolution.clone()));
                };
            };

            // For Nested Paths, The Non-Last Segments should resolve to a type
            let _ns = if is_last { ns } else { SymbolNamespace::Type };

            let named_symbol = if let Some(context) = context {
                self.resolve_symbol_in_context(name, context)
            } else {
                let lexical_resolution = self.resolve_symbol_in_lexical_scope(name, scopes);

                match lexical_resolution {
                    Some(LexicalScopeBinding::Declaration(binding)) => Ok(binding),
                    Some(LexicalScopeBinding::Resolution(resolution)) => {
                        if matches!(resolution, Resolution::Error) {
                            // Glob Ambiguity
                            Err(Determinacy::Undetermined)
                        } else {
                            record_resolution(self, resolution.clone());
                            return PathResult::NonContext(PartialRes::with_unresolved_segments(
                                resolution,
                                path.len() - 1,
                            ));
                        }
                    }
                    _ => Err(Determinacy::Determined),
                }
            };

            let named_symbol = match named_symbol {
                Ok(named_symbol) => named_symbol,
                Err(Determinacy::Undetermined) => return PathResult::Indeterminate,
                Err(Determinacy::Determined) => {
                    // perhaps we failed to determine soemthing like `List::new()`, if it's not a module kind, partial resolutions with unresolved segments are fine
                    if let Some(context) = context
                        && !context.kind.is_module_kind()
                    {
                        return PathResult::NonContext(PartialRes::with_unresolved_segments(
                            context.resolution().unwrap(),
                            path.len() - index,
                        ));
                    }

                    return PathResult::Failed {
                        segment: segment.identifier,
                        is_last_segment: is_last,
                    };
                }
            };

            let resolution = named_symbol.resolution();
            let maybe_assoc = PathSource::Type.is_allowed(&resolution);

            if let Some(next_context) = named_symbol.context() {
                context = Some(next_context);
                record_resolution(self, resolution.clone());
            } else if is_last || maybe_assoc {
                record_resolution(self, resolution.clone());
                return PathResult::NonContext(PartialRes::with_unresolved_segments(
                    resolution,
                    path.len() - index - 1,
                ));
            } else if matches!(resolution, Resolution::Error) {
                return PathResult::NonContext(PartialRes::new(Resolution::Error));
            } else {
                return PathResult::Failed {
                    segment: segment.identifier,
                    is_last_segment: is_last,
                };
            }
        }

        match context {
            Some(_) => {
                return PathResult::Context(context.unwrap());
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

        let mut candidates = Vec::new();
        // Track if we encountered any undetermined resolutions
        let mut has_undetermined = false;

        match context.kind {
            DefContextKind::File | DefContextKind::Block => {
                for import in context.glob_imports.borrow().iter() {
                    let module_context = import
                        .module_context
                        .get()
                        .expect("module should be resolved");
                    match self.resolve_symbol_in_context(name, module_context) {
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
                    let module_context = export
                        .module_context
                        .get()
                        .expect("module should be resolved");
                    match self.resolve_symbol_in_context(name, module_context) {
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

            match context.kind {
                DefContextKind::Block
                | DefContextKind::File
                | DefContextKind::Definition(
                    _,
                    taroc_hir::DefinitionKind::Module | taroc_hir::DefinitionKind::Namespace,
                    _,
                ) => {
                    // these blocks are transparent, meaning you don't need to qualify to get a member
                }
                _ => {
                    break;
                }
            }

            let binding = self.resolve_symbol_in_context(name, context);

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

        return None;
    }
}
