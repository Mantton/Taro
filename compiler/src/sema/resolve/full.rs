use crate::{
    ast::{self, AssocContext, AstVisitor, Identifier, NodeID, Path, PathSegment},
    error::CompileResult,
    sema::resolve::{
        models::{
            BindingError, DefinitionKind, ExpressionResolutionState, LexicalScope,
            LexicalScopeBinding, LexicalScopeSource, PathResult, Resolution, ResolutionError,
            ResolutionSource, ResolutionState, Scope, ScopeNamespace,
        },
        resolver::Resolver,
    },
    span::{Span, Symbol},
};
use rustc_hash::FxHashMap;

pub fn resolve_package(package: &ast::Package, resolver: &mut Resolver) -> CompileResult<()> {
    let mut actor = Actor {
        resolver,
        scopes: vec![],
    };
    ast::walk_package(&mut actor, package);
    resolver.context.dcx.ok()
}

struct Actor<'r, 'a> {
    resolver: &'r mut Resolver<'a>,
    scopes: Vec<LexicalScope<'a>>,
}

impl<'r, 'a> Actor<'r, 'a> {
    fn with_scope_source<T>(
        &mut self,
        source: LexicalScopeSource<'a>,
        work: impl FnOnce(&mut Self) -> T,
    ) -> T {
        self.scopes.push(LexicalScope::new(source));
        let result = work(self);
        self.scopes.pop();
        result
    }

    fn with_built_scope<T>(
        &mut self,
        scope: LexicalScope<'a>,
        work: impl FnOnce(&mut Self) -> T,
    ) -> T {
        self.scopes.push(scope);
        let result = work(self);
        self.scopes.pop();
        result
    }

    fn with_scope<T>(&mut self, scope: Scope<'a>, work: impl FnOnce(&mut Self) -> T) -> T {
        self.scopes
            .push(LexicalScope::new(LexicalScopeSource::Scoped(scope)));
        let result = work(self);
        self.scopes.pop();
        result
    }

    fn with_generics_scope(&mut self, generics: &ast::Generics, work: impl FnOnce(&mut Self)) {
        let type_parameters = &generics.type_parameters;
        let Some(type_parameters) = type_parameters else {
            work(self);
            return;
        };

        let mut seen_bindings: FxHashMap<Symbol, Span> = Default::default();

        let mut scope = LexicalScope::new(LexicalScopeSource::Plain);
        for param in &type_parameters.parameters {
            let def_id = self.resolver.definition_id(param.id);
            let name = param.identifier.symbol;
            let entry = seen_bindings.entry(name);

            match entry {
                std::collections::hash_map::Entry::Occupied(_) => {
                    // param has already been defined
                    self.resolver.dcx().emit_error(
                        format!(
                            "type parameter – {} – has already been defined",
                            param.identifier.symbol
                        ),
                        Some(param.identifier.span),
                    );
                    continue;
                }
                std::collections::hash_map::Entry::Vacant(entry) => {
                    // mark as seen
                    entry.insert(param.identifier.span);
                }
            }

            self.resolver.record_resolution(
                param.id,
                ResolutionState::Complete(Resolution::Definition(
                    def_id,
                    self.resolver.definition_kind(def_id),
                )),
            );
            scope.define(
                name,
                Resolution::Definition(def_id, DefinitionKind::TypeParameter),
            );
        }

        self.with_built_scope(scope, work);
    }

    fn with_self_alias_scope(&mut self, self_res: Resolution, work: impl FnOnce(&mut Self)) {
        let mut scope = LexicalScope::new(LexicalScopeSource::Plain);
        scope.define(Symbol::new("Self"), self_res);
        self.with_built_scope(scope, work);
    }
}

impl<'r, 'a> ast::AstVisitor for Actor<'r, 'a> {
    fn visit_module(&mut self, node: &ast::Module, _: bool) -> Self::Result {
        // Soft Reset on Modular Level, So Module Root is Scope Count
        self.scopes = vec![];
        let def_id = self.resolver.definition_id(node.id);
        let scope = self.resolver.get_definition_scope(def_id);
        self.with_scope(scope, |this| ast::walk_module(this, node));
        self.scopes = vec![]
    }

    fn visit_file(&mut self, node: &ast::File) -> Self::Result {
        let scope = *self
            .resolver
            .file_scope_mapping
            .get(&node.id)
            .expect("unmapped file scope");
        self.with_scope(scope, |this| ast::walk_file(this, node))
    }

    fn visit_declaration(&mut self, node: &ast::Declaration) -> Self::Result {
        self.resolve_declaration(node);
    }

    fn visit_assoc_declaration(
        &mut self,
        node: &ast::AssociatedDeclaration,
        context: ast::AssocContext,
    ) -> Self::Result {
        self.resolve_associated_declaration(node, context);
    }

    fn visit_function_declaration(&mut self, node: &ast::FunctionDeclaration) -> Self::Result {
        self.resolve_function_declaration(node);
    }

    fn visit_namespace_declaration(&mut self, node: &ast::NamespaceDeclaration) -> Self::Result {
        self.resolve_namespace_declaration(node);
    }

    fn visit_extern_declaration(&mut self, node: &ast::ExternDeclaration) -> Self::Result {
        self.resolve_extern_declaration(node);
    }

    fn visit_block(&mut self, node: &ast::Block) -> Self::Result {
        let scope = if let Some(&scope) = self.resolver.block_scope_mapping.get(&node.id) {
            LexicalScopeSource::Scoped(scope)
        } else {
            LexicalScopeSource::Plain
        };
        self.with_scope_source(scope, |this| ast::walk_block(this, node))
    }

    fn visit_function(
        &mut self,
        _: NodeID,
        f: &ast::Function,
        _: ast::FunctionContext,
    ) -> Self::Result {
        if let Some(body) = &f.block {
            self.with_scope_source(LexicalScopeSource::Plain, |this| {
                this.visit_generics(&f.generics);
                this.resolve_function_signature(&f.signature);
                this.with_scope_source(LexicalScopeSource::Plain, |this| this.visit_block(body));
            })
        } else {
            self.visit_generics(&f.generics);
            self.resolve_function_signature(&f.signature);
        }
    }

    fn visit_type(&mut self, node: &ast::Type) -> Self::Result {
        match &node.kind {
            ast::TypeKind::Nominal(path) => {
                self.resolve_path_with_source(node.id, path, ResolutionSource::Type);
            }
            ast::TypeKind::BoxedExistential { interfaces } => {
                for node in interfaces {
                    self.resolve_path_with_source(node.id, &node.path, ResolutionSource::Interface);
                }
            }
            ast::TypeKind::ImplicitSelf => {
                // Record the resolution for the synthetic `Self` type so lowering can build a HIR
                // nominal path with the correct identity.
                let ident = Identifier {
                    symbol: Symbol::new("Self"),
                    span: node.span,
                };
                match self.resolver.resolve_in_lexical_scopes(
                    &ident,
                    ScopeNamespace::Type,
                    &self.scopes,
                ) {
                    Ok(value) => {
                        let res = match value {
                            LexicalScopeBinding::Declaration(holder) => holder.resolution(),
                            LexicalScopeBinding::Resolution(resolution) => resolution,
                        };

                        self.resolver
                            .record_resolution(node.id, ResolutionState::Complete(res));
                    }
                    Err(e) => {
                        self.resolver.dcx().emit(e.diag());
                    }
                }
            }
            _ => {}
        }
        ast::walk_type(self, node)
    }

    fn visit_local(&mut self, node: &ast::Local) -> Self::Result {
        self.resolve_local(node);
    }

    fn visit_match_arm(&mut self, node: &ast::MatchArm) -> Self::Result {
        self.resolve_match_arm(node)
    }

    fn visit_generic_bound(&mut self, node: &ast::GenericBound) -> Self::Result {
        self.resolve_path_with_source(node.path.id, &node.path.path, ResolutionSource::Interface);
    }

    fn visit_statement(&mut self, node: &ast::Statement) -> Self::Result {
        self.resolve_statement(node)
    }

    fn visit_expression(&mut self, node: &ast::Expression) -> Self::Result {
        self.resolve_expression(node);
    }

    fn visit_conformance(&mut self, node: &ast::Conformances) -> Self::Result {
        for bound in node.bounds.iter() {
            self.resolve_path_with_source(bound.id, &bound.path, ResolutionSource::Interface);
        }
    }
}

impl<'r, 'a> Actor<'r, 'a> {
    fn resolve_declaration(&mut self, declaration: &ast::Declaration) {
        match &declaration.kind {
            ast::DeclarationKind::TypeAlias(ast::TypeAlias { generics, .. })
            | ast::DeclarationKind::Function(ast::Function { generics, .. }) => {
                let def_id = self.resolver.definition_id(declaration.id);
                self.with_scope_source(LexicalScopeSource::Definition(def_id), |this| {
                    this.with_generics_scope(generics, |this| {
                        ast::walk_declaration(this, declaration)
                    });
                })
            }
            ast::DeclarationKind::Interface(node) => {
                let def_id = self.resolver.definition_id(declaration.id);
                let self_res = Resolution::InterfaceSelfTypeParameter(def_id);
                self.with_scope_source(LexicalScopeSource::Definition(def_id), |this| {
                    this.with_generics_scope(&node.generics, |this| {
                        this.with_self_alias_scope(self_res, |this| {
                            ast::walk_declaration(this, declaration)
                        });
                    });
                })
            }
            ast::DeclarationKind::Enum(ast::Enum { generics, .. })
            | ast::DeclarationKind::Struct(ast::Struct { generics, .. }) => {
                let def_id = self.resolver.definition_id(declaration.id);
                let self_res = Resolution::SelfTypeAlias(def_id);
                self.with_scope_source(LexicalScopeSource::Definition(def_id), |this| {
                    this.with_generics_scope(generics, |this| {
                        this.with_self_alias_scope(self_res, |this| {
                            ast::walk_declaration(this, declaration)
                        });
                    });
                })
            }
            ast::DeclarationKind::Variable(..)
            | ast::DeclarationKind::Constant(..)
            | ast::DeclarationKind::Import(..)
            | ast::DeclarationKind::Export(..) => ast::walk_declaration(self, declaration),
            ast::DeclarationKind::Namespace(..) => {
                let def_id = self.resolver.definition_id(declaration.id);
                let scope = self.resolver.get_definition_scope(def_id);
                self.with_scope(scope, |this| ast::walk_declaration(this, declaration))
            }
            ast::DeclarationKind::ExternBlock(..) => ast::walk_declaration(self, declaration),
            ast::DeclarationKind::Extension(node) => self.resolve_extension(declaration.id, node),
            ast::DeclarationKind::Operator(..) => {
                unreachable!("top level operator")
            }
        }
    }

    fn resolve_extern_declaration(&mut self, declaration: &ast::ExternDeclaration) {
        match &declaration.kind {
            ast::ExternDeclarationKind::Function(ast::Function { generics, .. }) => {
                let def_id = self.resolver.definition_id(declaration.id);
                self.with_scope_source(LexicalScopeSource::Definition(def_id), |this| {
                    this.with_generics_scope(generics, |this| {
                        ast::walk_extern_declaration(this, declaration)
                    });
                })
            }
        }
    }

    fn resolve_function_declaration(&mut self, declaration: &ast::FunctionDeclaration) {
        match &declaration.kind {
            ast::FunctionDeclarationKind::Enum(ast::Enum { generics, .. })
            | ast::FunctionDeclarationKind::Struct(ast::Struct { generics, .. }) => {
                let def_id = self.resolver.definition_id(declaration.id);
                let self_res = Resolution::SelfTypeAlias(def_id);
                self.with_scope_source(LexicalScopeSource::Definition(def_id), |this| {
                    this.with_generics_scope(generics, |this| {
                        this.with_self_alias_scope(self_res, |this| {
                            ast::walk_function_declaration(this, declaration)
                        });
                    });
                })
            }
            ast::FunctionDeclarationKind::TypeAlias(ast::TypeAlias { generics, .. })
            | ast::FunctionDeclarationKind::Function(ast::Function { generics, .. }) => {
                let def_id = self.resolver.definition_id(declaration.id);
                self.with_scope_source(LexicalScopeSource::Definition(def_id), |this| {
                    this.with_generics_scope(generics, |this| {
                        ast::walk_function_declaration(this, declaration)
                    });
                })
            }
            ast::FunctionDeclarationKind::Constant(..)
            | ast::FunctionDeclarationKind::Import(..) => {
                ast::walk_function_declaration(self, declaration)
            }
        }
    }

    fn resolve_namespace_declaration(&mut self, declaration: &ast::NamespaceDeclaration) {
        match &declaration.kind {
            ast::NamespaceDeclarationKind::Enum(ast::Enum { generics, .. })
            | ast::NamespaceDeclarationKind::Struct(ast::Struct { generics, .. }) => {
                let def_id = self.resolver.definition_id(declaration.id);
                let self_res = Resolution::SelfTypeAlias(def_id);
                self.with_scope_source(LexicalScopeSource::Definition(def_id), |this| {
                    this.with_generics_scope(generics, |this| {
                        this.with_self_alias_scope(self_res, |this| {
                            ast::walk_namespace_declaration(this, declaration)
                        });
                    });
                })
            }
            ast::NamespaceDeclarationKind::TypeAlias(ast::TypeAlias { generics, .. })
            | ast::NamespaceDeclarationKind::Function(ast::Function { generics, .. }) => {
                let def_id = self.resolver.definition_id(declaration.id);
                self.with_scope_source(LexicalScopeSource::Definition(def_id), |this| {
                    this.with_generics_scope(generics, |this| {
                        ast::walk_namespace_declaration(this, declaration)
                    });
                })
            }
            ast::NamespaceDeclarationKind::Interface(node) => {
                let def_id = self.resolver.definition_id(declaration.id);
                let self_res = Resolution::InterfaceSelfTypeParameter(def_id);
                self.with_scope_source(LexicalScopeSource::Definition(def_id), |this| {
                    this.with_generics_scope(&node.generics, |this| {
                        this.with_self_alias_scope(self_res, |this| {
                            ast::walk_namespace_declaration(this, declaration)
                        });
                    });
                })
            }
            ast::NamespaceDeclarationKind::Namespace(..) => {
                let def_id = self.resolver.definition_id(declaration.id);
                let scope = self.resolver.get_definition_scope(def_id);
                self.with_scope(scope, |this| {
                    ast::walk_namespace_declaration(this, declaration)
                })
            }
            ast::NamespaceDeclarationKind::Constant(..)
            | ast::NamespaceDeclarationKind::Import(..)
            | ast::NamespaceDeclarationKind::Export(..) => {
                ast::walk_namespace_declaration(self, declaration)
            }
        }
    }

    fn resolve_associated_declaration(
        &mut self,
        declaration: &ast::AssociatedDeclaration,
        ctx: AssocContext,
    ) {
        match &declaration.kind {
            ast::AssociatedDeclarationKind::Constant(..) => {
                ast::walk_assoc_declaration(self, declaration, ctx);
            }
            ast::AssociatedDeclarationKind::AssociatedType(ast::TypeAlias { generics, .. }) => {
                let def_id = self.resolver.definition_id(declaration.id);
                self.with_scope_source(LexicalScopeSource::Definition(def_id), |this| {
                    this.with_generics_scope(generics, |this| {
                        ast::walk_assoc_declaration(this, declaration, ctx);
                    });
                })
            }
            ast::AssociatedDeclarationKind::Function(function) => {
                let def_id = self.resolver.definition_id(declaration.id);
                self.with_scope_source(LexicalScopeSource::Definition(def_id), |this| {
                    this.with_generics_scope(&function.generics, |this| {
                        if matches!(ctx, AssocContext::Extension(..)) {
                            if let Some(pos) = explicit_self_param_position(&function.signature) {
                                if pos != 0 {
                                    this.resolver.dcx().emit_error(
                                        "`self` must be the first parameter of a method"
                                            .to_string(),
                                        Some(declaration.span),
                                    );
                                }
                            }
                        }

                        ast::walk_assoc_declaration(this, declaration, ctx);
                    });
                })
            }
            ast::AssociatedDeclarationKind::Operator(node) => {
                let def_id = self.resolver.definition_id(declaration.id);
                self.with_scope_source(LexicalScopeSource::Definition(def_id), |this| {
                    this.with_generics_scope(&node.function.generics, |this| {
                        ast::walk_assoc_declaration(this, declaration, ctx);
                    });
                })
            }
        }
    }
}

fn explicit_self_param_position(signature: &ast::FunctionSignature) -> Option<usize> {
    signature
        .prototype
        .inputs
        .iter()
        .position(|param| param.name.symbol.as_str() == "self")
}

#[derive(Debug, Clone)]
enum ResolvedEntity<'a> {
    Scoped(Scope<'a>),
    Resolved(Resolution),
    DeferredAssociatedType,
    DeferredAssociatedValue,
}

impl<'r, 'a> Actor<'r, 'a> {
    fn resolve_statement(&mut self, node: &ast::Statement) {
        match &node.kind {
            ast::StatementKind::For(for_node) => {
                self.visit_expression(&for_node.iterator);
                self.with_scope_source(LexicalScopeSource::Plain, |this| {
                    this.resolve_top_level_pattern(&for_node.pattern, PatternSource::ForLoop);
                    this.visit_block(&for_node.block);
                });
            }
            ast::StatementKind::Guard {
                condition,
                else_block,
            } => {
                // Resolve else block first
                self.visit_block(else_block);
                self.visit_expression(condition);
            }

            ast::StatementKind::While {
                condition, block, ..
            } => {
                self.with_scope_source(LexicalScopeSource::Plain, |this| {
                    this.visit_expression(condition);
                    this.visit_block(block)
                });
            }
            _ => ast::walk_statement(self, node),
        }
    }
}

impl<'r, 'a> Actor<'r, 'a> {
    fn resolve_expression(&mut self, node: &ast::Expression) {
        match &node.kind {
            ast::ExpressionKind::Identifier(name) => {
                let result = self.lookup_unqualified(node.id, name, ScopeNamespace::Value);

                match result {
                    Ok(v) => match v {
                        ResolvedEntity::Scoped(scope) => {
                            if let Some(resolution) = scope.resolution() {
                                let adjusted = self.adjust_nominal_value_resolution(resolution);
                                self.resolver
                                    .expression_resolutions
                                    .insert(node.id, ExpressionResolutionState::Resolved(adjusted));
                            }
                        }
                        ResolvedEntity::Resolved(resolution) => {
                            let adjusted = self.adjust_nominal_value_resolution(resolution);
                            self.resolver
                                .expression_resolutions
                                .insert(node.id, ExpressionResolutionState::Resolved(adjusted));
                        }
                        ResolvedEntity::DeferredAssociatedType => {
                            self.resolver
                                .expression_resolutions
                                .insert(node.id, ExpressionResolutionState::DeferredAssociatedType);
                        }
                        ResolvedEntity::DeferredAssociatedValue => {
                            self.resolver.expression_resolutions.insert(
                                node.id,
                                ExpressionResolutionState::DeferredAssociatedValue,
                            );
                        }
                    },
                    Err(e) => {
                        self.report_error(e);
                    }
                }
            }
            ast::ExpressionKind::Member { .. } => {
                let result = self.resolve_expression_entity(node);
                let walk_children = result.is_ok();

                match result {
                    Ok(v) => match v {
                        ResolvedEntity::Scoped(scope) => {
                            if let Some(resolution) = scope.resolution() {
                                self.resolver.expression_resolutions.insert(
                                    node.id,
                                    ExpressionResolutionState::Resolved(resolution),
                                );
                            }
                        }
                        ResolvedEntity::Resolved(resolution) => {
                            self.resolver
                                .expression_resolutions
                                .insert(node.id, ExpressionResolutionState::Resolved(resolution));
                        }
                        ResolvedEntity::DeferredAssociatedType => {
                            self.resolver
                                .expression_resolutions
                                .insert(node.id, ExpressionResolutionState::DeferredAssociatedType);
                        }
                        ResolvedEntity::DeferredAssociatedValue => {
                            self.resolver.expression_resolutions.insert(
                                node.id,
                                ExpressionResolutionState::DeferredAssociatedValue,
                            );
                        }
                    },
                    Err(e) => {
                        self.report_error(e);
                    }
                }

                if walk_children {
                    // Ensure nested member chains like `a.b.c` have resolution entries for each
                    // intermediate member node (`a.b`), so lowering can compact fully-resolved paths.
                    ast::walk_expression(self, node);
                }
            }
            ast::ExpressionKind::Specialize {
                target,
                type_arguments,
            } => {
                let result = self.resolve_expression_entity(target);
                if let Ok(result) = result {
                    let result = self.apply_specialization(result, type_arguments.span);
                    match result {
                        Ok(_) => {}
                        Err(e) => {
                            self.report_error(e);
                        }
                    }
                }

                // Walk into the target and type arguments so nested expressions/types get
                // resolved and recorded.
                ast::walk_expression(self, node);
            }
            ast::ExpressionKind::If(if_node) => {
                self.with_scope_source(LexicalScopeSource::Plain, |this| {
                    this.visit_expression(&if_node.condition);
                    this.visit_expression(&if_node.then_block);
                });

                if let Some(node) = &if_node.else_block {
                    self.visit_expression(node)
                }
            }
            ast::ExpressionKind::PatternBinding(binding_node)
            | ast::ExpressionKind::OptionalPatternBinding(binding_node) => {
                self.visit_expression(&binding_node.expression);
                self.resolve_top_level_pattern(
                    &binding_node.pattern,
                    PatternSource::BindingCondition,
                );
            }
            ast::ExpressionKind::StructLiteral(literal) => {
                // Resolve the path as a type
                self.resolve_path_with_source(node.id, &literal.path, ResolutionSource::Type);
                ast::walk_expression(self, node);
            }
            _ => ast::walk_expression(self, node),
        }
    }

    fn resolve_expression_entity(
        &mut self,
        node: &ast::Expression,
    ) -> Result<ResolvedEntity<'a>, ResolutionError> {
        match &node.kind {
            ast::ExpressionKind::Identifier(name) => {
                self.lookup_unqualified(node.id, name, ScopeNamespace::Value)
            }
            ast::ExpressionKind::Member { target, name } => {
                let entity = self.resolve_expression_entity(target)?;
                self.resolve_member_access(entity, name, ScopeNamespace::Value)
            }
            ast::ExpressionKind::Specialize { target, .. } => {
                let entity = self.resolve_expression_entity(target)?;
                self.apply_specialization(entity.clone(), node.span)?;
                return Ok(entity);
            }
            // Anything else produces a value expression
            _ => return Ok(ResolvedEntity::DeferredAssociatedValue),
        }
    }

    fn lookup_unqualified(
        &mut self,
        id: NodeID,
        name: &Identifier,
        preferred: ScopeNamespace,
    ) -> Result<ResolvedEntity<'a>, ResolutionError> {
        // `resolve_path_in_scopes` records into `resolver.resolutions` keyed by `segment.id` and
        // panics on duplicates. Identifier expressions can be reached multiple times (e.g. once
        // via `resolve_expression_entity` and again during a later AST walk), so if we've already
        // recorded a resolution for this node, reuse it.
        if let Some(state) = self.resolver.get_resolution(id) {
            match state {
                ResolutionState::Complete(resolution) => {
                    if let Resolution::Definition(def_id, kind) = resolution {
                        if matches!(kind, DefinitionKind::Module | DefinitionKind::Namespace) {
                            return Ok(ResolvedEntity::Scoped(
                                self.resolver.get_definition_scope(def_id),
                            ));
                        }
                    }

                    return Ok(ResolvedEntity::Resolved(resolution));
                }
                ResolutionState::Partial { resolution, .. } => {
                    return Ok(ResolvedEntity::Resolved(resolution));
                }
            }
        }

        let path = vec![PathSegment {
            id,
            identifier: *name,
            arguments: None,
            span: name.span,
        }];

        let mut entity = None;
        let fallback = match preferred {
            ScopeNamespace::Type => ScopeNamespace::Value,
            ScopeNamespace::Value => ScopeNamespace::Type,
        };
        for &ns in &[preferred, fallback] {
            let result = self
                .resolver
                .resolve_path_in_scopes(&path, ns, &self.scopes);

            match result {
                PathResult::Scope(scope) => {
                    entity = Some(ResolvedEntity::Scoped(scope));
                    break;
                }
                PathResult::Resolution(state) => match state {
                    ResolutionState::Complete(resolution) => {
                        entity = Some(ResolvedEntity::Resolved(resolution.clone()));
                        break;
                    }
                    ResolutionState::Partial { .. } => unreachable!(),
                },
                PathResult::Failed { error, .. }
                    if matches!(error, ResolutionError::AmbiguousUsage(..)) =>
                {
                    return Err(error);
                }
                _ => {
                    continue;
                }
            }
        }

        let Some(entity) = entity else {
            return Err(ResolutionError::UnknownSymbol(*name));
        };

        return Ok(entity);
    }

    fn resolve_member_access(
        &self,
        base: ResolvedEntity<'a>,
        name: &Identifier,
        preferred: ScopeNamespace,
    ) -> Result<ResolvedEntity<'a>, ResolutionError> {
        match base {
            ResolvedEntity::Scoped(scope) => {
                let fallback = match preferred {
                    ScopeNamespace::Type => ScopeNamespace::Value,
                    ScopeNamespace::Value => ScopeNamespace::Type,
                };
                for &ns in &[preferred, fallback] {
                    let result = self.resolver.resolve_in_scope(name, scope, ns);
                    match result {
                        Ok(value) => {
                            if let Some(scope) = self.resolver.scope_for_holder(&value) {
                                return Ok(ResolvedEntity::Scoped(scope));
                            } else {
                                let res = value.resolution();
                                return Ok(ResolvedEntity::Resolved(res));
                            }
                        }
                        Err(ResolutionError::AmbiguousUsage(name)) => {
                            return Err(ResolutionError::AmbiguousUsage(name));
                        }
                        _ => continue,
                    }
                }
            }
            ResolvedEntity::Resolved(resolution) => match resolution {
                Resolution::PrimaryType(..) => {
                    return Ok(ResolvedEntity::DeferredAssociatedType);
                }
                Resolution::Definition(_, kind) => match kind {
                    DefinitionKind::Module | DefinitionKind::Namespace => unreachable!(),
                    DefinitionKind::Enum
                    | DefinitionKind::Struct
                    | DefinitionKind::TypeAlias
                    | DefinitionKind::Interface
                    | DefinitionKind::TypeParameter
                    | DefinitionKind::AssociatedType => {
                        return Ok(ResolvedEntity::DeferredAssociatedType);
                    }
                    DefinitionKind::Constant | DefinitionKind::ModuleVariable => {
                        return Ok(ResolvedEntity::DeferredAssociatedValue);
                    }
                    DefinitionKind::ConstParameter => {
                        return Err(ResolutionError::UnknownMember(*name));
                    }
                    DefinitionKind::Function | DefinitionKind::VariantConstructor(..) => {
                        return Err(ResolutionError::UnknownMember(*name));
                    }
                    _ => unreachable!(),
                },
                Resolution::SelfTypeAlias(_) => {
                    return Ok(ResolvedEntity::DeferredAssociatedType);
                }
                Resolution::InterfaceSelfTypeParameter(_) => {
                    return Ok(ResolvedEntity::DeferredAssociatedType);
                }
                Resolution::LocalVariable(_) => return Ok(ResolvedEntity::DeferredAssociatedValue),
                Resolution::FunctionSet(..) | Resolution::SelfConstructor(..) => {
                    return Err(ResolutionError::UnknownMember(*name));
                }
                // Variants Not Created By Resolver Step
                Resolution::Foundation(_) | Resolution::Error => unreachable!(),
            },
            ResolvedEntity::DeferredAssociatedValue => {
                return Ok(ResolvedEntity::DeferredAssociatedValue);
            }
            ResolvedEntity::DeferredAssociatedType => {
                return Ok(ResolvedEntity::DeferredAssociatedType);
            }
        }

        return Err(ResolutionError::UnknownSymbol(*name));
    }

    fn apply_specialization(
        &self,
        base: ResolvedEntity<'a>,
        span: Span,
    ) -> Result<(), ResolutionError> {
        let resolution = match base {
            ResolvedEntity::Scoped(scope) => scope.resolution().expect("resolution"),
            ResolvedEntity::Resolved(resolution) => resolution.clone(),
            ResolvedEntity::DeferredAssociatedType => return Ok(()),
            ResolvedEntity::DeferredAssociatedValue => {
                return Err(ResolutionError::SpecializationDisallowed(None, span));
            }
        };

        match resolution {
            res @ (Resolution::PrimaryType(..)
            | Resolution::LocalVariable(..)
            | Resolution::Definition(
                _,
                DefinitionKind::Module | DefinitionKind::Namespace,
            )) => {
                self.report_error(ResolutionError::SpecializationDisallowed(Some(res), span));
            }
            Resolution::Definition(..)
            | Resolution::SelfTypeAlias(..)
            | Resolution::InterfaceSelfTypeParameter(..)
            | Resolution::FunctionSet(..)
            | Resolution::SelfConstructor(..) => {}
            // Variants Not Created By Resolver Step
            Resolution::Foundation(_) | Resolution::Error => unreachable!(),
        }

        return Ok(());
    }

    fn adjust_nominal_value_resolution(&self, resolution: Resolution) -> Resolution {
        match resolution {
            Resolution::Definition(def_id, kind)
                if matches!(kind, DefinitionKind::Struct | DefinitionKind::Enum) =>
            {
                Resolution::SelfConstructor(def_id)
            }
            Resolution::SelfTypeAlias(def_id) => {
                if matches!(
                    self.resolver.definition_kind(def_id),
                    DefinitionKind::Struct | DefinitionKind::Enum
                ) {
                    Resolution::SelfConstructor(def_id)
                } else {
                    resolution
                }
            }
            _ => resolution,
        }
    }
}

impl<'r, 'a> Actor<'r, 'a> {
    fn resolve_local(&mut self, local: &ast::Local) {
        if let Some(ty) = &local.ty {
            self.visit_type(ty);
        }

        if let Some(expr) = &local.initializer {
            self.visit_expression(expr)
        }

        self.resolve_top_level_pattern(&local.pattern, PatternSource::Variable);
    }

    fn resolve_function_signature(&mut self, sg: &ast::FunctionSignature) {
        if let Some(ty) = &sg.prototype.output {
            self.visit_type(ty);
        }

        self.resolve_function_parameters(&sg.prototype.inputs);
    }
    fn resolve_function_parameters(&mut self, params: &Vec<ast::FunctionParameter>) {
        let mut bindings = vec![(PatBoundCtx::Product, Default::default())];
        for param in params.iter() {
            self.visit_type(&param.annotated_type);

            if let Some(e) = &param.default_value {
                self.visit_expression(e)
            }

            let pat = ast::Pattern {
                id: param.id,
                span: param.span,
                kind: ast::PatternKind::Identifier(param.name),
            };

            self.resolve_pattern_inner(&pat, PatternSource::FunctionParameter, &mut bindings);
        }

        self.apply_pattern_bindings(bindings);
    }
}

type PatternBindings = Vec<(PatBoundCtx, FxHashMap<Symbol, Resolution>)>;

impl<'r, 'a> Actor<'r, 'a> {
    fn resolve_match_arm(&mut self, node: &ast::MatchArm) {
        self.with_scope_source(LexicalScopeSource::Plain, |this| {
            this.resolve_top_level_pattern(&node.pattern, PatternSource::MatchArm);
            if let Some(guard) = &node.guard {
                this.visit_expression(guard)
            }
            this.visit_expression(&node.body)
        })
    }

    fn resolve_top_level_pattern(&mut self, pat: &ast::Pattern, source: PatternSource) {
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
        pat: &ast::Pattern,
        source: PatternSource,
        bindings: &mut PatternBindings,
    ) {
        self.resolve_pattern_inner(pat, source, bindings);
        self.check_match_pattern_consistency(pat);
    }

    fn resolve_pattern_inner(
        &mut self,
        pat: &ast::Pattern,
        source: PatternSource,
        bindings: &mut PatternBindings,
    ) {
        pat.walk(&mut |pat| {
            match &pat.kind {
                ast::PatternKind::Literal(..)
                | ast::PatternKind::Wildcard
                | ast::PatternKind::Tuple(..) => {}
                ast::PatternKind::Identifier(ident) => {
                    let res = self.fresh_var_binding(ident, pat.id, bindings, source);
                    self.resolver
                        .record_resolution(pat.id, ResolutionState::Complete(res));
                }
                ast::PatternKind::Member(path) => match path {
                    ast::PatternPath::Qualified { path } => {
                        self.resolve_path_with_source(
                            pat.id,
                            path,
                            ResolutionSource::MatchPatternUnit,
                        );
                    }
                    _ => {}
                },
                ast::PatternKind::PathTuple { path, .. } => match path {
                    ast::PatternPath::Qualified { path } => {
                        self.resolve_path_with_source(
                            pat.id,
                            path,
                            ResolutionSource::MatchPatternTupleStruct,
                        );
                    }
                    _ => {}
                },
                ast::PatternKind::Or(pats, _) => {
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
        ident: &Identifier,
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
                    ResolutionError::IdentifierBoundMoreThanOnceInParameterList(*ident)
                }
                _ => ResolutionError::IdentifierBoundMoreThanOnceInSamePattern(*ident),
            };

            self.report_error(err);
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
            Resolution::LocalVariable(id)
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

impl<'r, 'a> Actor<'r, 'a> {
    fn check_match_pattern_consistency(&mut self, pattern: &ast::Pattern) {
        let mut is_or_pattern = false;
        pattern.walk(&mut |pat| match pat.kind {
            ast::PatternKind::Or(..) => {
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
            self.resolver.get_resolution(id),
            Some(ResolutionState::Complete(Resolution::LocalVariable(..)))
        )
    }
    fn compute_and_check_match_pattern_binding_map(
        &mut self,
        pat: &ast::Pattern,
    ) -> FxHashMap<Symbol, Span> {
        let mut map = FxHashMap::default();

        pat.walk(&mut |pat| {
            match &pat.kind {
                ast::PatternKind::Identifier(ident) if self.is_base_res_local(pat.id) => {
                    map.insert(ident.symbol.clone(), ident.span);
                }
                ast::PatternKind::Or(sub_patterns, _) => {
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
        pats: &[ast::Pattern],
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
            self.report_error(ResolutionError::VariableNotBoundInPattern(v, span));
        }

        let mut binding_map = FxHashMap::default();
        for (bm, _) in binding_maps {
            binding_map.extend(bm);
        }
        binding_map
    }
}

impl<'r, 'a> Actor<'r, 'a> {
    fn resolve_extension(&mut self, id: ast::NodeID, node: &ast::Extension) {
        let def_id = self.resolver.definition_id(id);
        self.with_scope_source(LexicalScopeSource::Definition(def_id), |this| {
            this.with_generics_scope(&node.generics, |this| {
                let self_res = Resolution::SelfTypeAlias(def_id);
                this.with_self_alias_scope(self_res, |this| {
                    this.visit_type(&node.ty);
                    this.visit_generics(&node.generics);
                    if let Some(conformances) = &node.conformances {
                        this.visit_conformance(conformances)
                    }
                    for declaration in &node.declarations {
                        this.visit_assoc_declaration(declaration, AssocContext::Extension(id));
                    }
                });
            });
        })
    }
}

impl<'r, 'a> Actor<'r, 'a> {
    fn resolve_path_with_source(&mut self, id: NodeID, path: &Path, source: ResolutionSource) {
        let result =
            self.resolver
                .resolve_path_in_scopes(&path.segments, source.namespace(), &self.scopes);

        let resolution = match result {
            PathResult::Scope(scope) => {
                let resolution = scope.resolution().unwrap();
                self.resolver
                    .record_resolution(id, ResolutionState::Complete(resolution.clone()));
                Some(resolution)
            }
            PathResult::Resolution(value) => {
                self.resolver.record_resolution(id, value.clone());
                match value {
                    ResolutionState::Complete(resolution) => Some(resolution),
                    ResolutionState::Partial { .. } => None,
                }
            }
            PathResult::Failed { error, .. } => {
                self.resolver.dcx().emit(error.diag());
                return;
            }
        };

        let expected = source.expected();

        if let Some(resolution) = resolution {
            if !source.is_allowed(&resolution) {
                let provided = resolution.description();
                let symbol = &path.segments.last().unwrap().identifier.symbol;
                let message = format!("expected {expected}, got {provided} '{symbol}'");
                self.resolver.dcx().emit_error(message, Some(path.span));
            }
        } else if !source.defer_to_type_checker() {
            let symbol = &path.segments.last().unwrap().identifier.symbol;
            let message = format!("cannot resolve {expected} '{symbol}'");
            self.resolver.dcx().emit_error(message, Some(path.span));
        }
    }
}

impl<'r, 'a> Actor<'r, 'a> {
    fn report_error(&self, e: ResolutionError) {
        self.resolver.dcx().emit(e.diag());
    }
}

#[derive(PartialEq)]
pub enum PatBoundCtx {
    /// A product pattern context, e.g., `Variant(a, b)`.
    Product,
    /// An or-pattern context, e.g., `p_0 | ... | p_n`.
    Or,
}

#[derive(Debug, Clone, Copy)]
pub enum PatternSource {
    Variable,
    FunctionParameter,
    MatchArm,
    ForLoop,
    BindingCondition,
}
