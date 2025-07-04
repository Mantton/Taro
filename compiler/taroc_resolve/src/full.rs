use super::resolver::Resolver;
use rustc_hash::FxHashMap;
use taroc_error::CompileResult;
use taroc_hir::{
    Declaration, DefinitionID, DefinitionKind, NodeID, PartialResolution, PatternExpressionKind,
    PatternKind, Resolution, SelfTypeAlias, SymbolNamespace,
    visitor::{self, AssocContext, HirVisitor},
};
use taroc_resolve_models::{
    BindingError, ContextOrResolutionRoot, LexicalScope, LexicalScopeSource, ParentScope,
    PatBoundCtx, PathResult, PathSource, PatternSource, ResolutionError, Segment,
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
            parent_scope: ParentScope {
                context: root,
                file: root,
            },
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

    fn visit_match_arm(&mut self, node: &taroc_hir::MatchArm) -> Self::Result {
        self.resolve_match_arm(node)
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
            taroc_hir::DeclarationKind::Export(..) | taroc_hir::DeclarationKind::Import(..) => {
                taroc_hir::visitor::walk_declaration(self, declaration)
            }
            taroc_hir::DeclarationKind::Interface(..) => self.with_generics_scope(def_id, |this| {
                this.with_self_alias_scope(
                    Resolution::InterfaceSelfTypeParameter(def_id),
                    |this| {
                        taroc_hir::visitor::walk_declaration(this, declaration);
                    },
                );
            }),
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
                self.resolve_path_with_source(expr.id, &literal.path, PathSource::StructLiteral);
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

        self.resolve_top_level_pattern(&local.pattern, PatternSource::Variable);
    }

    fn resolve_function_signature(&mut self, sg: &taroc_hir::FunctionSignature) {
        if let Some(ty) = &sg.prototype.output {
            self.visit_type(ty);
        }

        self.resolve_function_parameters(&sg.prototype.inputs);
    }
    fn resolve_function_parameters(&mut self, params: &Vec<taroc_hir::FunctionParameter>) {
        let mut bindings = vec![(PatBoundCtx::Product, Default::default())];
        for param in params.iter() {
            self.visit_type(&param.annotated_type);

            if let Some(e) = &param.default_value {
                self.visit_expression(e)
            }

            let pat = taroc_hir::Pattern {
                id: param.id,
                span: param.span,
                kind: taroc_hir::PatternKind::Identifier(param.name),
            };

            self.resolve_pattern_inner(&pat, PatternSource::FunctionParameter, &mut bindings);
        }

        self.apply_pattern_bindings(bindings);
    }
}

type PatternBindings = Vec<(PatBoundCtx, FxHashMap<Symbol, Resolution>)>;

impl<'res, 'ctx> Actor<'res, 'ctx> {
    fn resolve_match_arm(&mut self, node: &taroc_hir::MatchArm) {
        self.with_scope(LexicalScopeSource::Plain, |this| {
            this.resolve_top_level_pattern(&node.pattern, PatternSource::MatchArm);
            if let Some(guard) = &node.guard {
                this.visit_expression(guard)
            }
            this.visit_expression(&node.body)
        })
    }

    fn resolve_top_level_pattern(&mut self, pat: &taroc_hir::Pattern, source: PatternSource) {
        let mut bindings = vec![(PatBoundCtx::Product, Default::default())];
        self.resolve_pattern(pat, source, &mut bindings);
        self.apply_pattern_bindings(bindings);
    }

    fn apply_pattern_bindings(&mut self, mut bindings: PatternBindings) {
        let scope = self.scopes.last_mut().unwrap();

        let Some((_, pat_bindings)) = bindings.pop() else {
            unreachable!("ICE: expected at least one pat binding set")
        };

        if scope.table.is_empty() {
            scope.table = pat_bindings
        } else {
            scope.table.extend(pat_bindings);
        }
    }

    fn resolve_pattern(
        &mut self,
        pat: &taroc_hir::Pattern,
        source: PatternSource,
        bindings: &mut PatternBindings,
    ) {
        self.resolve_pattern_inner(pat, source, bindings);
        self.check_match_pattern_consistency(pat);
    }

    fn resolve_pattern_inner(
        &mut self,
        pat: &taroc_hir::Pattern,
        source: PatternSource,
        bindings: &mut PatternBindings,
    ) {
        pat.walk(&mut |pat| {
            match &pat.kind {
                taroc_hir::PatternKind::Wildcard | taroc_hir::PatternKind::Tuple(..) => {}
                taroc_hir::PatternKind::Identifier(ident) => {
                    let res = self.fresh_var_binding(*ident, pat.id, bindings, source);
                    self.resolver
                        .record_resolution(pat.id, PartialResolution::new(res));
                }
                taroc_hir::PatternKind::Expression(PatternExpressionKind::Path(path)) => {
                    self.resolve_path_with_source(pat.id, path, PathSource::MatchPatternUnit);
                }
                taroc_hir::PatternKind::PathTuple(path, ..) => {
                    self.resolve_path_with_source(
                        pat.id,
                        path,
                        PathSource::MatchPatternTupleStruct,
                    );
                }
                taroc_hir::PatternKind::PathStruct(path, ..) => {
                    self.resolve_path_with_source(pat.id, path, PathSource::StructLiteral);
                }
                taroc_hir::PatternKind::Or(pats, _) => {
                    // Add new set of bindings
                    bindings.push((PatBoundCtx::Or, Default::default()));
                    for pat in pats {
                        // add another binding set to stack so each subpattern can reject duplicates
                        bindings.push((PatBoundCtx::Product, Default::default()));
                        self.resolve_pattern_inner(pat, source, bindings);
                        // Move up the non-overlapping bindings to the or-pattern.
                        // Existing bindings just get "merged".
                        let collected = bindings.pop().unwrap().1;
                        bindings.last_mut().unwrap().1.extend(collected);
                    }

                    // This or-pattern itself can itself be part of a product,
                    // e.g. `(V1(a) | V2(a), a)` or `(a, V1(a) | V2(a))`.
                    // Both cases bind `a` again in a product pattern and must be rejected.
                    let collected = bindings.pop().unwrap().1;
                    bindings.last_mut().unwrap().1.extend(collected);

                    return false;
                }
                _ => {}
            };

            return true;
        });
    }

    fn fresh_var_binding(
        &mut self,
        ident: Identifier,
        id: NodeID,
        bindings: &mut PatternBindings,
        source: PatternSource,
    ) -> Resolution {
        // Already bound in produce pattern: (a, a)
        let already_bound_and = bindings
            .iter()
            .any(|(ctx, map)| *ctx == PatBoundCtx::Product && map.contains_key(&ident.symbol));

        if already_bound_and {
            let err = match source {
                PatternSource::FunctionParameter => {
                    ResolutionError::IdentifierBoundMoreThanOnceInParameterList
                }
                _ => ResolutionError::IdentifierBoundMoreThanOnceInSamePattern,
            };

            self.report_error(err, ident.span);
        }

        let already_bound_or = bindings.iter().find_map(|(ctx, map)| {
            if *ctx == PatBoundCtx::Or {
                map.get(&ident.symbol).cloned()
            } else {
                None
            }
        });

        let res = if let Some(res) = already_bound_or {
            // reuse variant def
            res
        } else {
            Resolution::Local(id)
        };

        // Record as bound.
        bindings
            .last_mut()
            .unwrap()
            .1
            .insert(ident.symbol, res.clone());

        res
    }
}

impl<'res, 'ctx> Actor<'res, 'ctx> {
    fn check_match_pattern_consistency(&mut self, pattern: &taroc_hir::Pattern) {
        let mut is_or_pattern = false;
        pattern.walk(&mut |pat| match pat.kind {
            PatternKind::Or(..) => {
                is_or_pattern = true;
                false
            }
            _ => true,
        });
        if is_or_pattern {
            let _ = self.compute_and_check_match_pattern_binding_map(pattern);
        }
    }

    fn is_base_res_local(&self, id: NodeID) -> bool {
        matches!(
            self.resolver
                .resolution_map
                .get(&id)
                .map(|res| res.full_resolution().expect("full res")),
            Some(Resolution::Local(..))
        )
    }
    fn compute_and_check_match_pattern_binding_map(
        &mut self,
        pat: &taroc_hir::Pattern,
    ) -> FxHashMap<Symbol, Span> {
        let mut map = FxHashMap::default();

        pat.walk(&mut |pat| {
            match &pat.kind {
                PatternKind::Identifier(ident) if self.is_base_res_local(pat.id) => {
                    map.insert(ident.symbol, ident.span);
                }
                PatternKind::Or(sub_patterns, _) => {
                    let res = self.compute_and_check_or_match_pattern_binding_map(sub_patterns);
                    map.extend(res);
                }
                _ => {}
            }

            return true;
        });

        map
    }

    fn compute_and_check_or_match_pattern_binding_map(
        &mut self,
        pats: &[taroc_hir::Pattern],
    ) -> FxHashMap<Symbol, Span> {
        let mut missing_vars = FxHashMap::default();

        let binding_maps = pats
            .iter()
            .map(|pat| {
                let binding = self.compute_and_check_match_pattern_binding_map(pat);
                (binding, pat)
            })
            .collect::<Vec<_>>();

        // For Each SubPattern, Compare to other arms
        for (map_outer, pat_outer) in binding_maps.iter() {
            let others = binding_maps
                .iter()
                .filter(|(_, p)| p.id != pat_outer.id)
                .flat_map(|(m, _)| m);

            for (&name, &span) in others {
                match map_outer.get(&name) {
                    None => {
                        let err = missing_vars.entry(name).or_insert_with(|| BindingError {
                            name,
                            origin: Default::default(),
                            target: Default::default(),
                        });

                        err.origin.insert(span);
                        err.target.insert(pat_outer.span);
                    }
                    _ => {}
                }
            }
        }

        for (_, v) in missing_vars {
            let span = *v.origin.iter().next().unwrap();
            self.report_error(ResolutionError::VariableNotBoundInPattern(v), span);
        }

        let mut binding_map = FxHashMap::default();
        for (bm, _) in binding_maps {
            binding_map.extend(bm);
        }
        binding_map
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
                format!("failed to resolve '{}' in scope", segment)
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
            ResolutionError::InconsistentBindingMode(name, span_1) => {
                self.resolver.gcx.diagnostics.error(
                    format!("variable '{name}' is bound with different mutabilities"),
                    span,
                );

                self.resolver
                    .gcx
                    .diagnostics
                    .info(format!("'{name}' is originally bound here"), span_1);

                return;
            }
            ResolutionError::VariableNotBoundInPattern(err) => {
                let msg = format!("variable '{}' is not bound in all patterns", err.name);
                self.resolver.gcx.diagnostics.error(msg, span);

                for sp in err.target.into_iter() {
                    let msg = format!("pattern does not bind variable '{}'", err.name);
                    self.resolver.gcx.diagnostics.warn(msg, sp);
                }

                return;
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
