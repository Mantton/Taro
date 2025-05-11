use super::resolver::Resolver;
use rustc_hash::FxHashSet;
use taroc_error::CompileResult;
use taroc_hir::{
    Declaration, DefinitionID, DefinitionKind, NodeID, PartialResolution, Resolution,
    SelfTypeAlias, SymbolNamespace,
    visitor::{self, AssocContext, HirVisitor},
};
use taroc_resolve_models::{
    ContextOrResolutionRoot, LexicalScope, LexicalScopeSource, ParentScope, PathResult, PathSource,
    PatternSource, ResolutionError, Segment,
};
use taroc_span::{FileID, Identifier, Span, Spanned, Symbol};

pub fn run(package: &taroc_hir::Package, resolver: &mut Resolver) -> CompileResult<()> {
    let actor = Actor::new(resolver);
    actor.run(package);
    resolver.gcx.diagnostics.report()
}

struct Actor<'res, 'ctx> {
    pub resolver: &'res mut Resolver<'ctx>,
    pub scopes: Vec<LexicalScope<'ctx>>,
    pub current_file: Option<FileID>,
    pub parent_scope: ParentScope<'ctx>,
}

impl Actor<'_, '_> {
    fn new<'res, 'ctx>(resolver: &'res mut Resolver<'ctx>) -> Actor<'res, 'ctx> {
        let root = resolver.root_context;
        Actor {
            resolver,
            scopes: Default::default(),
            current_file: None,
            parent_scope: ParentScope { context: root },
        }
    }

    fn run(mut self, package: &taroc_hir::Package) {
        taroc_hir::visitor::walk_package(&mut self, package);
        assert!(self.scopes.is_empty(), "no hanging scopes")
    }
}

impl<'res, 'ctx> Actor<'res, 'ctx> {
    fn with_scope<T>(
        &mut self,
        source: LexicalScopeSource<'ctx>,
        work: impl FnOnce(&mut Self) -> T,
    ) -> T {
        self.scopes.push(LexicalScope::new(source));
        let result = work(self);
        self.scopes.pop();
        result
    }

    fn with_generics_scope(&mut self, id: DefinitionID, work: impl FnOnce(&mut Self)) {
        let generics = if id.is_local(self.resolver.session().package_index) {
            self.resolver.generics_table.get(&id).cloned()
        } else {
            self.resolver.gcx.resolution_generics(id)
        };

        let Some(generics) = generics else {
            work(self);
            return;
        };

        let mut scope = LexicalScope::new(LexicalScopeSource::Plain);
        for (symbol, id) in generics.into_iter() {
            scope.define(
                symbol,
                Resolution::Definition(id, DefinitionKind::TypeParameter),
            );
        }

        self.scopes.push(scope);
        work(self);
        self.scopes.pop();
    }

    fn with_self_alias_scope(&mut self, self_res: Resolution, work: impl FnOnce(&mut Self)) {
        let mut scope = LexicalScope::new(LexicalScopeSource::Plain);
        scope.define(Symbol::with("Self"), self_res);
        self.scopes.push(scope);
        work(self);
        self.scopes.pop();
    }
}

impl HirVisitor for Actor<'_, '_> {
    fn visit_module(&mut self, module: &taroc_hir::Module) -> Self::Result {
        // Soft Reset on Modular Level, So Module Root is Scope Count
        let previous = std::mem::take(&mut self.scopes);
        self.scopes = vec![];

        let module_id = self.resolver.def_id(module.id);
        let context = if module.id == NodeID::new(0) {
            self.resolver.root_context
        } else {
            self.resolver
                .get_context(&module_id)
                .expect("modules must always have a definition context")
        };

        self.with_scope(LexicalScopeSource::Context(context), |this| {
            taroc_hir::visitor::walk_module(this, module)
        });
        self.scopes = previous;
    }

    fn visit_file(&mut self, file: &taroc_hir::File) -> Self::Result {
        // File
        let context = self.resolver.get_file_context(&file.id);
        self.current_file = Some(file.id);

        // Visit
        self.with_scope(LexicalScopeSource::Context(context), |this| {
            taroc_hir::visitor::walk_file(this, file)
        })
    }

    fn visit_block(&mut self, b: &taroc_hir::Block) -> Self::Result {
        self.resolve_block(b);
    }

    fn visit_declaration(&mut self, d: &taroc_hir::Declaration) -> Self::Result {
        self.resolve_declaration(d);
    }

    fn visit_assoc_declaration(
        &mut self,
        declaration: &taroc_hir::AssociatedDeclaration,
        context: visitor::AssocContext,
    ) -> Self::Result {
        self.resolve_assoc_declaration(declaration, context);
    }

    fn visit_function_declaration(&mut self, d: &taroc_hir::FunctionDeclaration) -> Self::Result {
        self.resolve_function_declaration(d);
    }

    fn visit_foreign_declaration(&mut self, d: &taroc_hir::ForeignDeclaration) -> Self::Result {
        self.resolve_foreign_declaration(d);
    }

    fn visit_type(&mut self, ty: &taroc_hir::Type) -> Self::Result {
        match &ty.kind {
            taroc_hir::TypeKind::Path(path) => {
                self.resolve_path_with_source(ty.id, path, PathSource::Type);
            }
            taroc_hir::TypeKind::Exisitential(paths) | taroc_hir::TypeKind::Opaque(paths) => {
                for path in paths {
                    self.resolve_path_with_source(path.id, &path.path, PathSource::Interface);
                }
            }
            _ => {}
        }
        taroc_hir::visitor::walk_type(self, ty);
    }

    fn visit_generic_requirement(&mut self, n: &taroc_hir::GenericRequirement) -> Self::Result {
        match n {
            taroc_hir::GenericRequirement::SameTypeRequirement(c) => {
                self.visit_type(&c.bounded_type);
                self.visit_type(&c.bound);
            }
            taroc_hir::GenericRequirement::ConformanceRequirement(c) => {
                self.visit_type(&c.bounded_type);
                self.visit_generic_bounds(&c.bounds);
            }
        }
    }

    fn visit_generic_bound(&mut self, n: &taroc_hir::GenericBound) -> Self::Result {
        self.resolve_path_with_source(n.path.id, &n.path.path, PathSource::Interface);
    }

    fn visit_expression(&mut self, e: &taroc_hir::Expression) -> Self::Result {
        self.resolve_expression(e);
    }

    fn visit_local(&mut self, l: &taroc_hir::Local) -> Self::Result {
        self.resolve_local(l);
    }

    fn visit_function(
        &mut self,
        _: NodeID,
        f: &taroc_hir::Function,
        _: visitor::FunctionContext,
    ) -> Self::Result {
        if let Some(body) = &f.block {
            self.with_scope(LexicalScopeSource::Function, |this| {
                this.visit_generics(&f.generics);
                this.resolve_function_signature(&f.signature);
                this.with_scope(LexicalScopeSource::Plain, |this| this.visit_block(body));
            })
        } else {
            self.visit_generics(&f.generics);
            self.resolve_function_signature(&f.signature);
        }
    }

    fn visit_inheritance(&mut self, n: &taroc_hir::Inheritance) -> Self::Result {
        for interface_ref in &n.interfaces {
            self.resolve_path_with_source(
                interface_ref.id,
                &interface_ref.path,
                PathSource::Interface,
            );

            visitor::walk_tagged_path(self, interface_ref);
        }
    }
}

impl Actor<'_, '_> {
    fn resolve_declaration(&mut self, declaration: &taroc_hir::Declaration) {
        let def_id = self.resolver.def_id(declaration.id);
        let def_kind = self.resolver.def_kind(def_id);

        match &declaration.kind {
            taroc_hir::DeclarationKind::Function(..) => {
                self.with_scope(LexicalScopeSource::Definition(def_kind), |this| {
                    this.with_generics_scope(def_id, |this| {
                        taroc_hir::visitor::walk_declaration(this, declaration);
                    });
                });
            }
            taroc_hir::DeclarationKind::Extend(extend) => {
                self.resolve_extend(extend, declaration);
            }
            taroc_hir::DeclarationKind::TypeAlias(..) => {
                self.with_scope(LexicalScopeSource::Definition(def_kind), |this| {
                    this.with_generics_scope(def_id, |this| {
                        taroc_hir::visitor::walk_declaration(this, declaration);
                    })
                });
            }
            taroc_hir::DeclarationKind::Extern(_) => {
                taroc_hir::visitor::walk_declaration(self, declaration);
            }
            taroc_hir::DeclarationKind::Static(_) | taroc_hir::DeclarationKind::Constant(..) => {
                taroc_hir::visitor::walk_declaration(self, declaration);
            }
            taroc_hir::DeclarationKind::Namespace(_) => {
                let def_context = self
                    .resolver
                    .get_context(&def_id)
                    .expect("namespace must have context");
                self.with_scope(LexicalScopeSource::Context(def_context), |this| {
                    taroc_hir::visitor::walk_declaration(this, declaration)
                })
            }
            taroc_hir::DeclarationKind::Bridge(_) => {}
            taroc_hir::DeclarationKind::Export(..) | taroc_hir::DeclarationKind::Import(..) => {
                taroc_hir::visitor::walk_declaration(self, declaration)
            }
            taroc_hir::DeclarationKind::Interface(..) => {
                self.with_scope(LexicalScopeSource::Definition(def_kind), |this| {
                    this.with_generics_scope(def_id, |this| {
                        this.with_self_alias_scope(
                            Resolution::InterfaceSelfTypeAlias(def_id),
                            |this| {
                                taroc_hir::visitor::walk_declaration(this, declaration);
                            },
                        );
                    })
                })
            }
            taroc_hir::DeclarationKind::Struct(..) => {
                self.with_scope(LexicalScopeSource::Definition(def_kind), |this| {
                    this.with_generics_scope(def_id, |this| {
                        this.with_self_alias_scope(
                            Resolution::SelfTypeAlias(taroc_hir::SelfTypeAlias::Def(def_id)),
                            |this| {
                                taroc_hir::visitor::walk_declaration(this, declaration);
                            },
                        );
                    })
                })
            }
            taroc_hir::DeclarationKind::Enum(..) => {
                self.with_scope(LexicalScopeSource::Definition(def_kind), |this| {
                    this.with_generics_scope(def_id, |this| {
                        this.with_self_alias_scope(
                            Resolution::SelfTypeAlias(SelfTypeAlias::Def(def_id)),
                            |this| {
                                taroc_hir::visitor::walk_declaration(this, declaration);
                            },
                        );
                    })
                })
            }
            taroc_hir::DeclarationKind::Malformed => todo!(),
        }
    }

    fn resolve_assoc_declaration(
        &mut self,
        declaration: &taroc_hir::AssociatedDeclaration,
        ctx: AssocContext,
    ) {
        let def_id = self.resolver.def_id(declaration.id);
        let def_kind = self.resolver.def_kind(def_id);
        match &declaration.kind {
            taroc_hir::AssociatedDeclarationKind::Constant(_) => {
                taroc_hir::visitor::walk_assoc_declaration(self, declaration, ctx);
            }
            taroc_hir::AssociatedDeclarationKind::Function(..) => {
                self.with_scope(LexicalScopeSource::Definition(def_kind), |this| {
                    this.with_generics_scope(def_id, |this| {
                        taroc_hir::visitor::walk_assoc_declaration(this, declaration, ctx);
                    });
                });
            }
            taroc_hir::AssociatedDeclarationKind::Type(..) => {
                self.with_scope(LexicalScopeSource::Definition(def_kind), |this| {
                    this.with_generics_scope(def_id, |this| {
                        taroc_hir::visitor::walk_assoc_declaration(this, declaration, ctx);
                    })
                });
            }
            taroc_hir::AssociatedDeclarationKind::Operator(_, ..) => {
                self.with_scope(LexicalScopeSource::Definition(def_kind), |this| {
                    this.with_generics_scope(def_id, |this| {
                        taroc_hir::visitor::walk_assoc_declaration(this, declaration, ctx);
                    })
                });
            }
        }
    }
    fn resolve_function_declaration(&mut self, declaration: &taroc_hir::FunctionDeclaration) {
        let def_id = self.resolver.def_id(declaration.id);
        let def_kind = self.resolver.def_kind(def_id);
        match &declaration.kind {
            taroc_hir::FunctionDeclarationKind::Struct(..) => {
                self.with_scope(LexicalScopeSource::Definition(def_kind), |this| {
                    this.with_generics_scope(def_id, |this| {
                        this.with_self_alias_scope(
                            Resolution::SelfTypeAlias(SelfTypeAlias::Def(def_id)),
                            |this| {
                                taroc_hir::visitor::walk_function_declaration(this, declaration);
                            },
                        );
                    })
                })
            }
            taroc_hir::FunctionDeclarationKind::Enum(..) => {
                self.with_scope(LexicalScopeSource::Definition(def_kind), |this| {
                    this.with_generics_scope(def_id, |this| {
                        this.with_self_alias_scope(
                            Resolution::SelfTypeAlias(SelfTypeAlias::Def(def_id)),
                            |this| {
                                taroc_hir::visitor::walk_function_declaration(this, declaration);
                            },
                        );
                    })
                })
            }
            taroc_hir::FunctionDeclarationKind::Function(..) => {
                self.with_scope(LexicalScopeSource::Definition(def_kind), |this| {
                    this.with_generics_scope(def_id, |this| {
                        taroc_hir::visitor::walk_function_declaration(this, declaration);
                    });
                });
            }
            taroc_hir::FunctionDeclarationKind::Constant(_) => {
                taroc_hir::visitor::walk_function_declaration(self, declaration);
            }
            taroc_hir::FunctionDeclarationKind::Import(_) => {
                taroc_hir::visitor::walk_function_declaration(self, declaration);
            }
            taroc_hir::FunctionDeclarationKind::TypeAlias(..) => {
                self.with_scope(LexicalScopeSource::Definition(def_kind), |this| {
                    this.with_generics_scope(def_id, |this| {
                        taroc_hir::visitor::walk_function_declaration(this, declaration);
                    })
                });
            }
        }
    }
    fn resolve_foreign_declaration(&mut self, declaration: &taroc_hir::ForeignDeclaration) {
        let def_id = self.resolver.def_id(declaration.id);
        let def_kind = self.resolver.def_kind(def_id);
        match &declaration.kind {
            taroc_hir::ForeignDeclarationKind::Function(..) => {
                self.with_scope(LexicalScopeSource::Definition(def_kind), |this| {
                    this.with_generics_scope(def_id, |this| {
                        taroc_hir::visitor::walk_foreign_declaration(this, declaration);
                    });
                });
            }
            taroc_hir::ForeignDeclarationKind::Type(..) => {
                self.with_scope(LexicalScopeSource::Definition(def_kind), |this| {
                    this.with_generics_scope(def_id, |this| {
                        taroc_hir::visitor::walk_foreign_declaration(this, declaration);
                    });
                });
            }
        }
    }
}

impl<'res, 'ctx> Actor<'res, 'ctx> {
    fn resolve_block(&mut self, block: &taroc_hir::Block) {
        let scope = if let Some(context) = self.resolver.get_block_context(&block.id) {
            LexicalScope::new(LexicalScopeSource::Context(context))
        } else {
            LexicalScope::new(LexicalScopeSource::Plain)
        };

        self.scopes.push(scope);
        taroc_hir::visitor::walk_block(self, block);
        self.scopes.pop();
    }
}

impl<'res, 'ctx> Actor<'res, 'ctx> {
    fn resolve_extend(&mut self, node: &taroc_hir::Extend, decl: &Declaration) {
        let target = self.resolve_extension_target(&node.ty);
        let Some(target) = target else { return };
        let self_res = Resolution::SelfTypeAlias(target);

        match target {
            SelfTypeAlias::Def(definition_id) => self.with_generics_scope(definition_id, |this| {
                this.with_self_alias_scope(self_res, |this| {
                    taroc_hir::visitor::walk_declaration(this, &decl);
                });
            }),
            SelfTypeAlias::Primary(_) => {
                self.with_self_alias_scope(self_res, |this| {
                    taroc_hir::visitor::walk_declaration(this, &decl);
                });
            }
        }
    }

    fn resolve_extension_target(&mut self, ty: &taroc_hir::Type) -> Option<SelfTypeAlias> {
        let path = match &ty.kind {
            taroc_hir::TypeKind::Path(path) => path,
            _ => {
                self.resolver
                    .gcx
                    .diagnostics
                    .error("cannot extend non-nominal type".into(), ty.span);
                return None;
            }
        };
        let result = self.resolve_path_with_source(ty.id, path, PathSource::Type);

        if result.unresolved_segments != 0 {
            if !matches!(result.resolution(), Resolution::Error) {
                self.resolver
                    .gcx
                    .diagnostics
                    .error("ambiguous extension, cannot extend type".into(), ty.span);
            } else {
                self.resolver
                    .gcx
                    .diagnostics
                    .error("cannot locate type".into(), ty.span);
            }

            return None;
        }

        let res = result.resolution();

        let res = match res {
            Resolution::PrimaryType(primary_type) => SelfTypeAlias::Primary(primary_type),
            Resolution::Definition(definition_id, _) => SelfTypeAlias::Def(definition_id),
            _ => {
                self.resolver
                    .gcx
                    .diagnostics
                    .error("cannot extend non-nominal type".into(), ty.span);
                return None;
            }
        };

        return Some(res);
    }
}

impl<'res, 'ctx> Actor<'res, 'ctx> {
    fn resolve_expression(&mut self, expr: &taroc_hir::Expression) {
        match &expr.kind {
            taroc_hir::ExpressionKind::Path(path) => {
                self.resolve_path_with_source(expr.id, path, PathSource::Expression);
                taroc_hir::visitor::walk_expression(self, expr);
            }
            taroc_hir::ExpressionKind::StructLiteral(literal) => {
                self.resolve_path_with_source(expr.id, &literal.path, PathSource::Type);
                taroc_hir::visitor::walk_expression(self, expr);
            }
            _ => taroc_hir::visitor::walk_expression(self, expr),
        }
    }

    fn resolve_local(&mut self, local: &taroc_hir::Local) {
        if let Some(ty) = &local.ty {
            self.visit_type(ty);
        }

        if let Some(expr) = &local.initializer {
            self.visit_expression(expr)
        }

        self.resolve_top_level_binding_pattern(&local.pattern, PatternSource::Variable);
    }

    fn resolve_function_signature(&mut self, sg: &taroc_hir::FunctionSignature) {
        if let Some(ty) = &sg.prototype.output {
            self.visit_type(ty);
        }

        self.resolve_function_parameters(&sg.prototype.inputs);
    }
    fn resolve_function_parameters(&mut self, params: &Vec<taroc_hir::FunctionParameter>) {
        let mut seen = FxHashSet::default();
        for param in params.iter() {
            self.visit_type(&param.annotated_type);

            if let Some(e) = &param.default_value {
                self.visit_expression(e)
            }

            let pat = taroc_hir::BindingPattern {
                id: param.id,
                span: param.span,
                kind: taroc_hir::BindingPatternKind::Identifier(param.name.clone()),
            };

            self.resolve_binding_pattern(&pat, PatternSource::FunctionParameter, &mut seen);
        }
    }
}

impl<'res, 'ctx> Actor<'res, 'ctx> {
    fn resolve_top_level_binding_pattern(
        &mut self,
        pat: &taroc_hir::BindingPattern,
        source: PatternSource,
    ) {
        let mut bindings = FxHashSet::default();
        self.resolve_binding_pattern(pat, source, &mut bindings)
    }
    fn resolve_binding_pattern(
        &mut self,
        pat: &taroc_hir::BindingPattern,
        source: PatternSource,
        bindings: &mut FxHashSet<Symbol>,
    ) {
        match &pat.kind {
            taroc_hir::BindingPatternKind::Wildcard => {}
            taroc_hir::BindingPatternKind::Identifier(identifier) => {
                let res = self
                    .try_resolve_as_non_binding(source, &identifier)
                    .unwrap_or_else(|| {
                        self.fresh_var_from_binding_pattern(&identifier, pat.id, source, bindings)
                    });

                self.resolver
                    .record_resolution(pat.id, PartialResolution::new(res));
            }
            taroc_hir::BindingPatternKind::Tuple(binding_patterns) => {
                for pattern in binding_patterns {
                    self.resolve_binding_pattern(pattern, source, bindings);
                }
            }
        }
    }

    fn try_resolve_as_non_binding(
        &mut self,
        _source: PatternSource,
        _ident: &Identifier,
    ) -> Option<Resolution> {
        return None;
    }
    fn fresh_var_from_binding_pattern(
        &mut self,
        ident: &Identifier,
        id: NodeID,
        source: PatternSource,
        bindings: &mut FxHashSet<Symbol>,
    ) -> Resolution {
        let seen = bindings.contains(&ident.symbol);

        if seen {
            let err = match source {
                PatternSource::FunctionParameter => {
                    ResolutionError::IdentifierBoundMoreThanOnceInParameterList
                }
                _ => ResolutionError::IdentifierBoundMoreThanOnceInSamePattern,
            };

            self.report_error(err, ident.span);
        }

        let res = Resolution::Local(id);

        bindings.insert(ident.symbol.clone());

        let indx = self.scopes.len() - 1;
        self.scopes
            .get_mut(indx)
            .unwrap()
            .define(ident.symbol, res.clone());

        return res;
    }
}

impl<'res, 'ctx> Actor<'res, 'ctx> {
    fn resolve_path_with_source(
        &mut self,
        id: NodeID,
        path: &taroc_hir::Path,
        source: PathSource,
    ) -> PartialResolution {
        let segments = Segment::from_path(path);
        let result = self.resolve_path_anywhere(
            &segments,
            source.namespace(),
            source.defer_to_type_checker(),
        );

        let report_error = |this: &mut Self, res: Option<Resolution>| {
            this.report_error_with_context(path, source, res);
            return PartialResolution::new(Resolution::Error);
        };

        let res = match result {
            Ok(Some(partial)) if let Some(res) = partial.full_resolution() => {
                if source.is_allowed(&res) || res.is_error() {
                    partial
                } else {
                    report_error(self, Some(res))
                }
            }
            Ok(Some(res)) if source.defer_to_type_checker() => res,
            Err(err) => {
                self.report_error(err.value, err.span);
                PartialResolution::new(Resolution::Error)
            }

            _ => report_error(self, None),
        };

        self.resolver.record_resolution(id, res.clone());
        res
    }

    fn resolve_path_anywhere(
        &mut self,
        path: &[Segment],
        ns: SymbolNamespace,
        defer_to_ty_check: bool,
    ) -> Result<Option<PartialResolution>, Spanned<ResolutionError>> {
        let mut final_resolution = None;

        for (_, &namespace) in [ns, SymbolNamespace::Type, SymbolNamespace::Value]
            .iter()
            .enumerate()
        {
            match self.resolve_path_convert_result(path, namespace)? {
                Some(resolution) if resolution.unresolved_segments() == 0 || defer_to_ty_check => {
                    return Ok(Some(resolution));
                }
                resolution => {
                    if final_resolution.is_none() {
                        final_resolution = resolution;
                    }
                }
            }
        }

        Ok(final_resolution)
    }

    fn resolve_path_convert_result(
        &mut self,
        path: &[Segment],
        ns: SymbolNamespace,
    ) -> Result<Option<PartialResolution>, Spanned<ResolutionError>> {
        let result = match self.resolve_path_with_scopes(path, ns) {
            PathResult::NonContext(resolution) => resolution,
            PathResult::Context(ContextOrResolutionRoot::Context(ctx)) => {
                PartialResolution::new(ctx.resolution().unwrap())
            }
            PathResult::Failed {
                segment,
                is_last_segment: false,
            } => {
                return Err(Spanned {
                    span: segment.span,
                    value: ResolutionError::FailedToResolve {
                        segment: segment.symbol,
                    },
                });
            }
            PathResult::Indeterminate => unreachable!(),
            _ => return Ok(None),
        };

        Ok(Some(result))
    }

    fn resolve_path_with_scopes(
        &mut self,
        path: &[Segment],
        ns: SymbolNamespace,
    ) -> PathResult<'ctx> {
        let res = self.resolver.resolve_path_with_scopes(
            path,
            Some(ns),
            &self.scopes,
            &self.parent_scope,
        );
        return res;
    }
}

impl<'res, 'ctx> Actor<'res, 'ctx> {
    fn report_error(&mut self, err: ResolutionError, span: Span) {
        let message = match err {
            ResolutionError::FailedToResolve { segment } => {
                format!("failed to resolve '{}'", segment)
            }
            ResolutionError::Ambiguous { segment } => {
                format!("ambiguous usage of glob '{}'", segment)
            }
            ResolutionError::IdentifierBoundMoreThanOnceInParameterList => {
                format!("identifier is bound more than once in the parameter list")
            }
            ResolutionError::IdentifierBoundMoreThanOnceInSamePattern => {
                format!("identifier is bound more than once in the pattern")
            }
            ResolutionError::CannotExtend { segment } => {
                format!("cannot extend {segment}")
            }
        };

        self.resolver.gcx.diagnostics.error(message, span);
    }

    fn report_error_with_context(
        &mut self,
        path: &taroc_hir::Path,
        source: PathSource,
        resolution: Option<Resolution>,
    ) {
        let item = path.segments.last().unwrap().identifier.symbol;
        let expectation = source.expected();

        if let Some(res) = resolution {
            let provided = res.description();
            let message = format!("expected {expectation}, got {provided} '{item}'");
            self.resolver.gcx.diagnostics.error(message, path.span);
            return;
        } else {
            let mod_name = if path.segments.len() == 1 {
                "scope"
            } else {
                path.segments[path.segments.len() - 2]
                    .identifier
                    .symbol
                    .as_str()
            };

            let message = format!("cannot find {expectation} '{item}' in {mod_name}");
            self.resolver.gcx.diagnostics.error(message, path.span);
        }
    }
}
