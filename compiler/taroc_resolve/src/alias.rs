use taroc_hir::{DefinitionID, DefinitionKind, Resolution};
use taroc_resolve_models::{LexicalScope, LexicalScopeSource, PathResult, ResolvedAlias, Segment};
use taroc_span::Symbol;

use crate::{find::ResolutionState, models::UnresolvedAlias, resolver::Resolver};

pub struct TypeAliasResolver<'res, 'ctx> {
    pub resolver: &'res mut Resolver<'ctx>,
    pub finalize: bool,
}

impl<'res, 'ctx> TypeAliasResolver<'res, 'ctx> {
    pub fn run(resolver: &'res mut Resolver<'ctx>, finalize: bool) {
        let actor = TypeAliasResolver { resolver, finalize };
        actor.resolve();
    }
}

impl<'res, 'ctx> TypeAliasResolver<'res, 'ctx> {
    fn resolve(mut self) {
        let extensions = std::mem::take(&mut self.resolver.unresolved_aliases);
        for (id, data) in extensions.into_iter() {
            let ok = self.resolve_alias(id, &data);

            if !ok {
                self.resolver.unresolved_aliases.insert(id, data);
            }
        }
    }

    fn resolve_alias(&mut self, id: DefinitionID, node: &UnresolvedAlias<'ctx>) -> bool {
        // self.resolver
        //     .context
        //     .diagnostics
        //     .warn("Resolving Alias".into(), node.span);

        // This should basically resolve the ty ahead of time
        // Find Resolution
        debug_assert!(
            node.alias.ty.is_some(),
            "initial pass must ensure the rhs of the alias is resolved"
        );
        let ty = node.alias.ty.clone().unwrap();
        let path = match &ty.kind {
            taroc_hir::TypeKind::Path(path) => path,
            _ => {
                if self.finalize {
                    self.resolver.context.diagnostics.error(
                        "extensions on non-pathed types is not permitted".into(),
                        ty.span,
                    );
                }
                return false;
            }
        };

        let segments = Segment::from_path(&path);

        // Create Scopes
        let mut scopes = Vec::new();
        let mut next = Some(node.parent);
        while let Some(mut value) = next {
            if let Some(mut id) = value.def_id() {
                if matches!(self.resolver.def_kind(id), DefinitionKind::Extension)
                    && let Some(resolved_id) = self.resolver.resolved_extensions.get(&id).cloned()
                {
                    id = resolved_id;
                    value = self
                        .resolver
                        .get_context(&id)
                        .expect("defintion should have context");
                }

                let kind = self.resolver.def_kind(id);

                let res = match kind {
                    DefinitionKind::Enum | DefinitionKind::Struct => {
                        Some(Resolution::SelfTypeAlias(id))
                    }
                    DefinitionKind::Interface => Some(Resolution::InterfaceSelfTypeAlias(id)),
                    _ => None,
                };

                // Self Res
                if let Some(res) = res {
                    let mut scope = LexicalScope::new(LexicalScopeSource::Plain);
                    scope.define(Symbol::with("Self"), res);
                    scopes.push(scope);
                }

                // Generics
                let generics = self.resolver.generics_table.get(&id);
                if let Some(generics) = generics {
                    let mut scope = LexicalScope::new(LexicalScopeSource::Plain);
                    for (symbol, id) in generics.into_iter() {
                        scope.define(
                            *symbol,
                            Resolution::Definition(*id, DefinitionKind::TypeParameter),
                        );
                    }
                    scopes.push(scope);
                };
            };

            scopes.push(LexicalScope::new(LexicalScopeSource::Context(value)));
            next = value.parent
        }

        // Insert FileScope
        scopes.insert(
            1,
            LexicalScope::new(LexicalScopeSource::Context(
                self.resolver.get_file_context(&node.span.file),
            )),
        );

        // Resolve In Lexical Scope

        let result =
            self.resolver
                .resolve_path_with_scopes(&segments, &scopes, ResolutionState::Alias);

        match result {
            PathResult::Context(ctx) => {
                let node = ResolvedAlias {
                    ty: *ty,
                    res: ctx.resolution().expect("context resolution"),
                };
                self.resolver.resolved_aliases.insert(id, node);
                return true;
            }
            PathResult::NonContext(resolution) => match resolution {
                taroc_hir::Resolution::Definition(res_id, kind) => {
                    if matches!(kind, DefinitionKind::TypeAlias) {
                        if let Some(ty) = self.resolver.resolved_aliases.get(&res_id) {
                            self.resolver.resolved_aliases.insert(id, ty.clone());
                            return true;
                        } else {
                            if self.finalize {
                                // TODO: Failed resolution on T1
                                // type T3 = INVALID_TYPE
                                // type T4 = T3

                                self.resolver
                                    .context
                                    .diagnostics
                                    .error("potentially recursive alias".into(), ty.span);
                            }
                            return false;
                        }
                    } else {
                        let node = ResolvedAlias {
                            ty: *ty,
                            res: resolution,
                        };
                        self.resolver.resolved_aliases.insert(id, node);
                        return true;
                    }
                }
                _ => {
                    if self.finalize {
                        self.resolver
                            .context
                            .diagnostics
                            .error("Cannot alias Non-Definition".into(), ty.span);
                    }
                    return false;
                }
            },
            PathResult::Indeterminate => {
                if self.finalize {
                    self.resolver
                        .context
                        .diagnostics
                        .error("Ambiguous usage".into(), ty.span);
                }

                return false;
            }
            PathResult::Failed { segment, .. } => {
                if self.finalize {
                    self.resolver
                        .context
                        .diagnostics
                        .error("Failed to Resolve".into(), segment.span);
                }

                return false;
            }
        };
    }
}
