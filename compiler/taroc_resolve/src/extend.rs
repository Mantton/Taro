use crate::{find::ResolutionState, models::DefinitionExtensionData, resolver::Resolver};
use taroc_hir::DefinitionID;
use taroc_resolve_models::{
    DefinitionContext, LexicalScope, LexicalScopeSource, NameHolder, Segment,
};
use taroc_span::{FileID, Identifier};

pub struct ExtensionBinder<'res, 'ctx> {
    pub resolver: &'res mut Resolver<'ctx>,
}

impl<'res, 'ctx> ExtensionBinder<'res, 'ctx> {
    pub fn run(resolver: &'res mut Resolver<'ctx>, finalize: bool) {
        let mut actor = ExtensionBinder { resolver };
        actor.bind_extension(finalize);
    }
}

impl<'res, 'ctx> ExtensionBinder<'res, 'ctx> {
    fn bind_extension(&mut self, finalize: bool) {
        let extensions = std::mem::take(&mut self.resolver.unresolved_extensions);
        for (id, data) in extensions.into_iter() {
            let ok = self.resolve_extension(id, &data, finalize);

            if !ok {
                self.resolver.unresolved_extensions.insert(id, data);
            }
        }
    }

    fn resolve_extension(
        &mut self,
        _id: DefinitionID,
        data: &DefinitionExtensionData<'ctx>,
        finalize: bool,
    ) -> bool {
        let target = self.find_binding(&data.path, data.module_id, data.file_id, finalize);
        let Some(target) = target else { return false };

        if target.def_id().is_none() {
            unreachable!("target is not a definition")
        };
        self.merge_extension(target, data.extension_context);
        return true;
    }

    fn find_binding(
        &mut self,
        ty: &taroc_hir::TaggedPath,
        mod_id: DefinitionID,
        file_id: FileID,
        finalize: bool,
    ) -> Option<DefinitionContext<'ctx>> {
        // self.resolver
        //     .context
        //     .diagnostics
        //     .warn("Resolving Extension".into(), ty.path.span);
        let module_context = self
            .resolver
            .get_context(&mod_id)
            .expect("modules must always have a definition context");
        let module_scope = LexicalScope {
            source: LexicalScopeSource::Context(module_context),
            table: Default::default(),
        };

        let file_context = self.resolver.get_file_context(&file_id);
        let file_scope = LexicalScope {
            source: LexicalScopeSource::Context(file_context),
            table: Default::default(),
        };
        let scopes = vec![module_scope, file_scope];

        let segments = &Segment::from_path(&ty.path);
        let resolution =
            self.resolver
                .resolve_path_with_scopes(segments, &scopes, ResolutionState::Full);

        match resolution {
            taroc_resolve_models::PathResult::Context(definition_context) => {
                return Some(definition_context);
            }
            taroc_resolve_models::PathResult::NonContext(resolution) => {
                if finalize {
                    match resolution {
                        taroc_hir::Resolution::Definition(
                            id,
                            taroc_hir::DefinitionKind::TypeAlias,
                        ) => {
                            if let Some(res) = self.resolver.resolved_aliases.get(&id) {
                                return self.resolver.get_context(&res.def_id().expect("def_id"));
                            } else {
                                // Pre-Reported
                            }
                        }
                        taroc_hir::Resolution::Error => {}
                        _ => {
                            let message = format!(
                                "cannot extend {} '{}'.",
                                resolution.description(),
                                segments.last().unwrap().identifier.symbol
                            );
                            self.resolver
                                .context
                                .diagnostics
                                .error(message, segments.last().unwrap().identifier.span);
                        }
                    }
                }

                return None;
            }
            taroc_resolve_models::PathResult::Indeterminate => {
                todo!("ambiguous usage!")
            }
            taroc_resolve_models::PathResult::Failed { segment, .. } => {
                // todo!("Failed!")
                if finalize {
                    self.resolver
                        .context
                        .diagnostics
                        .error("Failed to Bind Extension".into(), segment.span);
                }

                return None;
            }
        }
    }
}

impl<'res, 'ctx> ExtensionBinder<'res, 'ctx> {
    fn merge_extension(
        &mut self,
        target: DefinitionContext<'ctx>,
        extension: DefinitionContext<'ctx>,
    ) {
        let def_id = target.def_id().unwrap();
        if def_id.is_local(self.resolver.context.session().package_index) {
            self.merge_local_definition(target, extension);
        } else {
            self.merge_external_definition(target, extension);
        }

        self.resolver
            .resolved_extensions
            .insert(extension.def_id().unwrap(), target);
    }

    fn merge_local_definition(
        &mut self,
        target: DefinitionContext<'ctx>,
        extension: DefinitionContext<'ctx>,
    ) {
        // Merge Local Definitions Directly into Namespace
        let extension_resolutions = extension.resolutions.borrow();
        for (symbol, holder) in extension_resolutions.bindings.iter() {
            match holder {
                NameHolder::Single(binding) => {
                    let ident = Identifier {
                        symbol: *symbol,
                        span: binding.span,
                    };
                    self.resolver
                        .define_in_parent(target, ident, *binding, false);
                }
                NameHolder::Set(bindings) => {
                    for binding in *bindings {
                        let ident = Identifier {
                            symbol: *symbol,
                            span: binding.span,
                        };
                        self.resolver
                            .define_in_parent(target, ident, *binding, false);
                    }
                }
            }
        }
    }

    fn merge_external_definition(
        &mut self,
        _target: DefinitionContext<'ctx>,
        _extension: DefinitionContext<'ctx>,
    ) {
    }
}
