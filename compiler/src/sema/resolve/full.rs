use crate::{
    ast::{self, AssocContext, AstVisitor, Identifier, NodeID, Path, PathSegment},
    error::CompileResult,
    sema::resolve::{
        models::{
            BindingError, DefinitionKind, ExpressionResolutionState, LexicalScope,
            LexicalScopeBinding, LexicalScopeSource, PathResult, Resolution, ResolutionError,
            ResolutionSource, ResolutionState, Scope, ScopeKind, ScopeNamespace,
        },
        resolver::Resolver,
    },
    span::{Span, Symbol},
};
use rustc_hash::FxHashMap;

#[cfg(test)]
mod qualified_access_tests {
    use crate::test_support::analyze_script_diagnostics;

    #[test]
    fn qualified_namespace_and_instance_access_are_distinct() {
        let diagnostics = analyze_script_diagnostics(
            "namespace Tools { func answer() -> int32 { 42 }; }\n\
             struct Counter { value: int32; }\n\
             func inspect(_ counter: Counter) -> int32 { Tools::answer() + counter.value }",
        );
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }

    #[test]
    fn incorrect_member_separator_has_a_specific_diagnostic() {
        for (source, expected) in [
            (
                "namespace Tools { func answer() {}; }; func inspect() { Tools.answer() }",
                "qualified access to `answer` requires `::`",
            ),
            (
                "struct Counter { value: int32; }; func inspect(_ counter: Counter) { counter::value }",
                "instance access to `value` requires `.`",
            ),
        ] {
            let diagnostics = analyze_script_diagnostics(source);
            assert!(
                diagnostics.iter().any(|d| d.message == expected),
                "{diagnostics:#?}"
            );
        }
    }

    #[test]
    fn qualified_enum_value_can_be_followed_by_instance_access() {
        let diagnostics = analyze_script_diagnostics(
            "enum Mode { case enabled; }\nextend Mode {\nfunc active() -> bool { true };\nstatic func viaSelf() -> bool { Self::enabled.active() };\n}\nfunc inspect() -> bool { Mode::enabled.active() }",
        );
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }
}

pub fn resolve_package(package: &ast::Package, resolver: &mut Resolver) -> CompileResult<()> {
    let mut actor = Actor {
        resolver,
        scopes: vec![],
        type_source_override: None,
        next_scope_id: 0,
        owner: 0,
        next_owner: 0,
        active_loop_labels: Vec::new(),
    };
    ast::walk_package(&mut actor, package);
    resolver.context.dcx.ok()
}

struct Actor<'r, 'a> {
    resolver: &'r mut Resolver<'a>,
    scopes: Vec<LexicalScope<'a>>,
    type_source_override: Option<ResolutionSource>,
    /// Identity for the next lexical scope; see `LexicalScope::id`.
    next_scope_id: u32,
    /// The function or closure whose body is being resolved, so the
    /// shadowing check only relates bindings of the same body.
    owner: u32,
    next_owner: u32,
    /// Active loop labels visible in the current function/closure body.
    active_loop_labels: Vec<Option<Symbol>>,
}

impl<'r, 'a> Actor<'r, 'a> {
    fn with_type_source<T>(
        &mut self,
        source: ResolutionSource,
        work: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let previous = self.type_source_override.replace(source);
        let result = work(self);
        self.type_source_override = previous;
        result
    }

    fn with_scope_source<T>(
        &mut self,
        source: LexicalScopeSource<'a>,
        work: impl FnOnce(&mut Self) -> T,
    ) -> T {
        self.with_built_scope(LexicalScope::new(source), work)
    }

    fn with_owner<T>(&mut self, work: impl FnOnce(&mut Self) -> T) -> T {
        self.next_owner += 1;
        let previous = std::mem::replace(&mut self.owner, self.next_owner);
        let previous_labels = std::mem::take(&mut self.active_loop_labels);
        let result = work(self);
        self.active_loop_labels = previous_labels;
        self.owner = previous;
        result
    }

    fn with_loop_label<T>(
        &mut self,
        label: Option<ast::Label>,
        work: impl FnOnce(&mut Self) -> T,
    ) -> T {
        self.active_loop_labels
            .push(label.map(|l| l.identifier.symbol));
        let result = work(self);
        self.active_loop_labels.pop();
        result
    }

    fn with_built_scope<T>(
        &mut self,
        mut scope: LexicalScope<'a>,
        work: impl FnOnce(&mut Self) -> T,
    ) -> T {
        self.next_scope_id += 1;
        scope.id = self.next_scope_id;
        self.scopes.push(scope);
        let result = work(self);
        self.scopes.pop();
        result
    }

    fn with_scope<T>(&mut self, scope: Scope<'a>, work: impl FnOnce(&mut Self) -> T) -> T {
        self.with_scope_source(LexicalScopeSource::Scoped(scope), work)
    }

    fn with_definition_generics(
        &mut self,
        id: NodeID,
        generics: &ast::Generics,
        work: impl FnOnce(&mut Self),
    ) {
        let def_id = self.resolver.definition_id(id);
        let self_binding = match self.resolver.definition_kind(def_id) {
            DefinitionKind::Struct | DefinitionKind::Enum => {
                Some(Resolution::SelfTypeAlias(def_id))
            }
            DefinitionKind::Interface => Some(Resolution::InterfaceSelfTypeParameter(def_id)),
            _ => None,
        };
        self.with_scope_source(LexicalScopeSource::Plain, |this| {
            this.with_generics_scope(generics, |this| {
                if let Some(binding) = self_binding {
                    this.with_self_alias_scope(binding, work);
                } else {
                    work(this);
                }
            });
        });
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
            // Anonymous inputs refer directly to their parameter definition.
            // Even escaped user identifiers cannot capture that definition.
            if param.is_anonymous {
                continue;
            }
            let def_id = self.resolver.definition_id(param.id);
            let def_kind = self.resolver.definition_kind(def_id);
            let name = param.identifier.symbol;
            let entry = seen_bindings.entry(name);

            match entry {
                std::collections::hash_map::Entry::Occupied(_) => {
                    // param has already been defined
                    self.resolver.dcx().emit_error(
                        format!(
                            "type parameter – {} – has already been defined",
                            self.resolver.context.symbol_text(param.identifier.symbol)
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
                ResolutionState::Complete(Resolution::Definition(def_id, def_kind)),
            );
            scope.define(name, Resolution::Definition(def_id, def_kind));
        }

        self.with_built_scope(scope, work);
    }

    fn with_self_alias_scope(&mut self, self_res: Resolution, work: impl FnOnce(&mut Self)) {
        let mut scope = LexicalScope::new(LexicalScopeSource::Plain);
        scope.define(self.resolver.context.intern_symbol("Self"), self_res);
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
            self.with_owner(|this| {
                this.with_scope_source(LexicalScopeSource::Plain, |this| {
                    this.visit_generics(&f.generics);
                    this.resolve_function_signature(&f.signature);
                    this.with_scope_source(LexicalScopeSource::Plain, |this| {
                        this.visit_block(body)
                    });
                })
            })
        } else {
            self.visit_generics(&f.generics);
            self.resolve_function_signature(&f.signature);
        }
    }

    fn visit_type(&mut self, node: &ast::Type) -> Self::Result {
        match &node.kind {
            ast::TypeKind::Nominal(path) => {
                let source = self
                    .type_source_override
                    .take()
                    .unwrap_or(ResolutionSource::Type);
                self.resolve_path_with_source(node.id, path, source);
            }
            ast::TypeKind::QualifiedAccess {
                target, interface, ..
            } => {
                // In (T as I).Item only T is an ordinary type. The right
                // operand names the interface providing the associated type.
                self.visit_type(target);
                self.with_type_source(ResolutionSource::Interface, |this| {
                    this.visit_type(interface);
                });
                return;
            }
            ast::TypeKind::BoxedExistential { interfaces }
            | ast::TypeKind::ImplTrait { interfaces } => {
                for node in interfaces {
                    self.resolve_path_with_source(node.id, &node.path, ResolutionSource::Interface);
                }
            }
            ast::TypeKind::ImplicitSelf => {
                // Record the resolution for the synthetic `Self` type so lowering can build a HIR
                // nominal path with the correct identity.
                let ident = Identifier {
                    symbol: self.resolver.context.intern_symbol("Self"),
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
                        self.resolver.dcx().emit(e.diag(self.resolver.context));
                    }
                }
            }
            _ => {}
        }
        ast::walk_type(self, node)
    }

    fn visit_type_argument(&mut self, node: &ast::TypeArgument) -> Self::Result {
        match node {
            ast::TypeArgument::Type(ty) => {
                self.with_type_source(ResolutionSource::TypeArgument, |this| {
                    this.visit_type(ty);
                });
            }
            ast::TypeArgument::Const(_) => {
                // Constants are resolved in type checking
            }
            ast::TypeArgument::AssocType(_, ty) => {
                self.visit_type(ty);
            }
        }
    }

    fn visit_alias(&mut self, node: &ast::TypeAlias) -> Self::Result {
        self.visit_generics(&node.generics);
        if let Some(ty) = &node.ty {
            self.with_type_source(ResolutionSource::AliasTarget, |this| {
                this.visit_type(ty);
            });
        }
        if let Some(interface_set) = &node.interface_set {
            self.visit_generic_bounds(interface_set);
        }
        if let Some(bounds) = &node.bounds {
            self.visit_generic_bounds(bounds);
        }
    }

    fn visit_local(&mut self, node: &ast::Local) -> Self::Result {
        self.resolve_local(node);
    }

    fn visit_match_arm(&mut self, node: &ast::MatchArm) -> Self::Result {
        self.resolve_match_arm(node)
    }

    fn visit_select_arm(&mut self, node: &ast::SelectArm) -> Self::Result {
        self.resolve_select_arm(node)
    }

    fn visit_generic_bound(&mut self, node: &ast::GenericBound) -> Self::Result {
        self.resolve_path_with_source(node.path.id, &node.path.path, ResolutionSource::Interface);
        ast::walk_generic_bound(self, node)
    }

    fn visit_statement(&mut self, node: &ast::Statement) -> Self::Result {
        self.resolve_statement(node)
    }

    fn visit_expression(&mut self, node: &ast::Expression) -> Self::Result {
        self.resolve_expression(node);
    }

    fn visit_class_definition(&mut self, node: &ast::Class) -> Self::Result {
        self.visit_generics(&node.generics);
        if let Some(bounds) = &node.conformances {
            for bound in bounds.bounds.iter() {
                // A class header contains one class base plus interfaces.
                // AliasTarget admits both categories; hierarchy collection
                // subsequently validates and separates them.
                self.resolve_path_with_source(bound.id, &bound.path, ResolutionSource::AliasTarget);
                ast::walk_path_node(self, bound);
            }
        }
        for field in &node.fields {
            self.visit_field_definition(field);
        }
    }

    fn visit_conformance(&mut self, node: &ast::Conformances) -> Self::Result {
        for bound in node.bounds.iter() {
            self.resolve_path_with_source(bound.id, &bound.path, ResolutionSource::Interface);
        }
        // Walk conformance to resolve type arguments inside paths (e.g., `Foo<Bar>`)
        ast::walk_conformance(self, node)
    }
}

impl<'r, 'a> Actor<'r, 'a> {
    fn resolve_declaration(&mut self, declaration: &ast::Declaration) {
        match &declaration.kind {
            ast::DeclarationKind::Class(ast::Class { generics, .. })
            | ast::DeclarationKind::TypeAlias(ast::TypeAlias { generics, .. })
            | ast::DeclarationKind::Function(ast::Function { generics, .. })
            | ast::DeclarationKind::Interface(ast::Interface { generics, .. })
            | ast::DeclarationKind::Enum(ast::Enum { generics, .. })
            | ast::DeclarationKind::Struct(ast::Struct { generics, .. }) => {
                self.with_definition_generics(declaration.id, generics, |this| {
                    ast::walk_declaration(this, declaration)
                });
            }
            ast::DeclarationKind::Namespace(..) => {
                let def_id = self.resolver.definition_id(declaration.id);
                let scope = self.resolver.get_definition_scope(def_id);
                self.with_scope(scope, |this| ast::walk_declaration(this, declaration));
            }
            ast::DeclarationKind::Impl(node) => self.resolve_impl(declaration.id, node),
            ast::DeclarationKind::StaticVariable(..)
            | ast::DeclarationKind::Constant(..)
            | ast::DeclarationKind::Import(..)
            | ast::DeclarationKind::Export(..)
            | ast::DeclarationKind::ExternBlock(..) => ast::walk_declaration(self, declaration),
        }
    }

    fn resolve_extern_declaration(&mut self, declaration: &ast::ExternDeclaration) {
        if let ast::ExternDeclarationKind::Function(function) = &declaration.kind {
            self.with_definition_generics(declaration.id, &function.generics, |this| {
                ast::walk_extern_declaration(this, declaration)
            });
        }
    }

    fn resolve_function_declaration(&mut self, declaration: &ast::FunctionDeclaration) {
        match &declaration.kind {
            ast::FunctionDeclarationKind::Enum(ast::Enum { generics, .. })
            | ast::FunctionDeclarationKind::Struct(ast::Struct { generics, .. })
            | ast::FunctionDeclarationKind::TypeAlias(ast::TypeAlias { generics, .. })
            | ast::FunctionDeclarationKind::Function(ast::Function { generics, .. }) => {
                self.with_definition_generics(declaration.id, generics, |this| {
                    ast::walk_function_declaration(this, declaration)
                });
            }
            ast::FunctionDeclarationKind::Constant(..)
            | ast::FunctionDeclarationKind::Import(..) => {
                ast::walk_function_declaration(self, declaration)
            }
        }
    }

    fn resolve_namespace_declaration(&mut self, declaration: &ast::NamespaceDeclaration) {
        match &declaration.kind {
            ast::NamespaceDeclarationKind::Class(ast::Class { generics, .. })
            | ast::NamespaceDeclarationKind::Enum(ast::Enum { generics, .. })
            | ast::NamespaceDeclarationKind::Struct(ast::Struct { generics, .. })
            | ast::NamespaceDeclarationKind::TypeAlias(ast::TypeAlias { generics, .. })
            | ast::NamespaceDeclarationKind::Function(ast::Function { generics, .. })
            | ast::NamespaceDeclarationKind::Interface(ast::Interface { generics, .. }) => {
                self.with_definition_generics(declaration.id, generics, |this| {
                    ast::walk_namespace_declaration(this, declaration)
                });
            }
            ast::NamespaceDeclarationKind::Namespace(..) => {
                let def_id = self.resolver.definition_id(declaration.id);
                let scope = self.resolver.get_definition_scope(def_id);
                self.with_scope(scope, |this| {
                    ast::walk_namespace_declaration(this, declaration)
                });
            }
            ast::NamespaceDeclarationKind::StaticVariable(..)
            | ast::NamespaceDeclarationKind::Constant(..)
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
            ast::AssociatedDeclarationKind::Initializer(initializer) => {
                self.with_definition_generics(
                    declaration.id,
                    &initializer.function.generics,
                    |this| ast::walk_assoc_declaration(this, declaration, ctx),
                );
            }
            ast::AssociatedDeclarationKind::AssociatedType(ast::TypeAlias { generics, .. }) => {
                self.with_definition_generics(declaration.id, generics, |this| {
                    ast::walk_assoc_declaration(this, declaration, ctx)
                });
            }
            ast::AssociatedDeclarationKind::Function(function) => {
                self.with_definition_generics(declaration.id, &function.generics, |this| {
                    if matches!(ctx, AssocContext::Impl(..)) {
                        if let Some(pos) =
                            explicit_self_param_position(&function.signature, this.resolver.context)
                        {
                            if pos != 0 {
                                this.resolver.dcx().emit_error(
                                    "`self` must be the first parameter of a method".to_string(),
                                    Some(declaration.span),
                                );
                            }
                        }
                    }
                    ast::walk_assoc_declaration(this, declaration, ctx);
                });
            }
            ast::AssociatedDeclarationKind::Constant(..)
            | ast::AssociatedDeclarationKind::Subscript(..)
            | ast::AssociatedDeclarationKind::Property(..) => {
                ast::walk_assoc_declaration(self, declaration, ctx)
            }
        }
    }
}

fn explicit_self_param_position(
    signature: &ast::FunctionSignature,
    gcx: crate::compile::context::GlobalContext<'_>,
) -> Option<usize> {
    signature
        .prototype
        .inputs
        .iter()
        .position(|param| gcx.symbol_eq(param.name.symbol, "self"))
}

#[derive(Debug, Clone)]
enum ResolvedEntity<'a> {
    Scoped(Scope<'a>),
    Resolved(Resolution),
    DeferredAssociatedType,
    DeferredAssociatedValue,
    /// `Enum.variant`, which is a value even though it is spelled like a
    /// type-relative path. Kept apart from `DeferredAssociatedType` so that a
    /// further member access lands on the variant rather than extending the
    /// path, while the variant itself still lowers as a relative path for the
    /// type checker to resolve.
    DeferredEnumVariant,
}

impl<'r, 'a> Actor<'r, 'a> {
    fn resolve_statement(&mut self, node: &ast::Statement) {
        match &node.kind {
            ast::StatementKind::For(for_node) => {
                self.visit_expression(&for_node.iterator);
                self.with_loop_label(for_node.label, |this| {
                    this.with_scope_source(LexicalScopeSource::Plain, |this| {
                        this.resolve_top_level_pattern(&for_node.pattern, PatternSource::ForLoop);
                        if let Some(clause) = &for_node.clause {
                            this.visit_expression(clause);
                        }
                        this.visit_block(&for_node.block);
                    });
                });
            }
            ast::StatementKind::ComptimeFor {
                pattern,
                target_type,
                body,
            } => {
                self.visit_type(target_type);
                self.with_scope_source(LexicalScopeSource::Plain, |this| {
                    this.resolve_top_level_pattern(pattern, PatternSource::ForLoop);
                    this.visit_block(body);
                });
            }
            ast::StatementKind::Loop { label, block } => {
                self.with_loop_label(*label, |this| {
                    this.visit_block(block);
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
                label,
                condition,
                block,
            } => {
                self.with_loop_label(*label, |this| {
                    this.with_scope_source(LexicalScopeSource::Plain, |this| {
                        this.visit_expression(condition);
                        this.visit_block(block)
                    });
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
                let lookup = if self.resolver.context.symbol_text(name.symbol).as_str() == "super" {
                    Identifier {
                        symbol: self.resolver.context.intern_symbol("self"),
                        ..*name
                    }
                } else {
                    *name
                };
                let result = self.lookup_unqualified(node.id, &lookup, ScopeNamespace::Value);

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
                        // A variant still lowers as a relative path, so that the
                        // type checker resolves it against the enum as before.
                        ResolvedEntity::DeferredEnumVariant => {
                            self.resolver
                                .expression_resolutions
                                .insert(node.id, ExpressionResolutionState::DeferredAssociatedType);
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
                        // A variant still lowers as a relative path, so that the
                        // type checker resolves it against the enum as before.
                        ResolvedEntity::DeferredEnumVariant => {
                            self.resolver
                                .expression_resolutions
                                .insert(node.id, ExpressionResolutionState::DeferredAssociatedType);
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
                index,
            } => {
                let result = self.resolve_expression_entity(target);
                if result.as_ref().is_ok_and(Self::entity_is_value) {
                    self.resolver
                        .expression_resolutions
                        .insert(node.id, ExpressionResolutionState::DeferredAssociatedValue);
                    self.visit_expression(target);
                    if matches!(
                        target.kind,
                        ast::ExpressionKind::Member {
                            qualified: false,
                            ..
                        }
                    ) {
                        let context = self.resolver.context;
                        let (_, types) = context.dcx().with_deferred_diagnostics(|| {
                            self.visit_type_arguments(type_arguments)
                        });
                        let (_, index_errors) = context.dcx().with_deferred_diagnostics(|| {
                            if let Some(index) = index {
                                for argument in index {
                                    self.visit_expression_argument(argument);
                                }
                            }
                        });
                        self.resolver.member_bracket_diagnostics.insert(
                            node.id,
                            crate::diagnostics::BracketDiagnostics {
                                types,
                                index: index_errors,
                            },
                        );
                        return;
                    }
                    if let Some(index) = index {
                        for argument in index {
                            self.visit_expression_argument(argument);
                        }
                    } else {
                        self.resolver.dcx().emit_error(
                            "a value subscript requires index expressions".into(),
                            Some(type_arguments.span),
                        );
                    }
                } else {
                    if matches!(target.kind, ast::ExpressionKind::Specialize { .. }) {
                        self.resolver.dcx().emit_error(
                            "extra type arguments provided".into(),
                            Some(type_arguments.span),
                        );
                    }
                    if let Ok(result) = result {
                        if let Err(error) = self.apply_specialization(result, type_arguments.span) {
                            self.report_error(error);
                        }
                    }
                    self.visit_expression(target);
                    self.visit_type_arguments(type_arguments);
                }
            }
            ast::ExpressionKind::Index { target, index } => {
                self.visit_expression(target);
                for argument in index {
                    self.visit_expression_argument(argument);
                }
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
            | ast::ExpressionKind::PatternIs(binding_node)
            | ast::ExpressionKind::OptionalPatternBinding(binding_node) => {
                self.visit_expression(&binding_node.expression);
                self.resolve_top_level_pattern(
                    &binding_node.pattern,
                    PatternSource::BindingCondition,
                );
            }
            ast::ExpressionKind::StructLiteral(literal) => {
                if let ast::ConstructorPath::Qualified { path } = &literal.path {
                    self.resolve_path_with_source(node.id, path, ResolutionSource::Constructor);
                }
                ast::walk_expression(self, node);
            }
            ast::ExpressionKind::Closure(closure) => {
                if closure.has_implicit_it {
                    let it_ident = Identifier {
                        symbol: self.resolver.context.intern_symbol("it"),
                        span: closure.signature.span,
                    };
                    if self
                        .resolver
                        .resolve_in_lexical_scopes(&it_ident, ScopeNamespace::Value, &self.scopes)
                        .is_ok()
                    {
                        self.resolver.dcx().emit_warning(
                            "implicit 'it' parameter shadows an outer 'it' binding; name the parameter explicitly (e.g. 'x => ...')".into(),
                            Some(closure.signature.span),
                        );
                    }
                }
                // Resolve closure in a new lexical scope
                self.with_owner(|this| {
                    this.with_scope_source(LexicalScopeSource::Plain, |this| {
                        // Resolve signature (registers parameters in current scope)
                        this.resolve_function_signature(&closure.signature);
                        // Resolve the body expression in the same scope
                        this.visit_expression(&closure.body);
                    })
                });
            }
            ast::ExpressionKind::Loop { label, block } => {
                self.with_loop_label(*label, |this| {
                    this.visit_block(block);
                });
            }
            ast::ExpressionKind::Break { label, value } => {
                // For bare `break name`, a visible in-scope loop label wins
                // over any local or outer value binding with the same name.
                if let (Some(ident), Some(_)) = (label, value) {
                    if self
                        .active_loop_labels
                        .iter()
                        .rev()
                        .any(|entry| *entry == Some(ident.symbol))
                    {
                        self.resolver
                            .break_label_resolutions
                            .insert(node.id, *ident);
                        return;
                    }
                }
                if let Some(value) = value {
                    self.visit_expression(value);
                }
            }
            ast::ExpressionKind::Assign(target, _) => {
                if let Some(lint) = &self.resolver.lint {
                    let mut lint = lint.borrow_mut();
                    note_assign_targets(&mut lint, target);
                }
                ast::walk_expression(self, node)
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
                let lookup = if self.resolver.context.symbol_text(name.symbol).as_str() == "super" {
                    Identifier {
                        symbol: self.resolver.context.intern_symbol("self"),
                        ..*name
                    }
                } else {
                    *name
                };
                self.lookup_unqualified(node.id, &lookup, ScopeNamespace::Value)
            }
            ast::ExpressionKind::Member {
                target,
                name,
                qualified,
            } => {
                let entity = self.resolve_expression_entity(target)?;
                // The preceding type-relative member may be an associated
                // type or a value (notably `Self::unitCase`). A dot ends the
                // path; type checking validates the resulting instance target.
                if !qualified && matches!(entity, ResolvedEntity::DeferredAssociatedType) {
                    return Ok(ResolvedEntity::DeferredAssociatedValue);
                }
                let requires_qualified = matches!(
                    &entity,
                    ResolvedEntity::Scoped(_)
                        | ResolvedEntity::DeferredAssociatedType
                        | ResolvedEntity::Resolved(
                            Resolution::PrimaryType(..)
                                | Resolution::SelfTypeAlias(_)
                                | Resolution::InterfaceSelfTypeParameter(_)
                                | Resolution::Definition(
                                    _,
                                    DefinitionKind::Enum
                                        | DefinitionKind::Struct
                                        | DefinitionKind::TypeAlias
                                        | DefinitionKind::Interface
                                        | DefinitionKind::TypeParameter
                                        | DefinitionKind::AssociatedType
                                )
                        )
                );
                if *qualified != requires_qualified {
                    return Err(ResolutionError::WrongMemberSeparator {
                        name: *name,
                        qualified: requires_qualified,
                        span: Span {
                            start: target.span.end,
                            end: name.span.start,
                            file: node.span.file,
                        },
                    });
                }
                if let ResolvedEntity::Resolved(base) = &entity
                    && let Some(nested) = self.nested_type_member(base, name)
                {
                    if matches!(target.kind, ast::ExpressionKind::Specialize { .. }) {
                        return Err(ResolutionError::NestedTypeOnSpecializedOwner(target.span));
                    }
                    return Ok(ResolvedEntity::Resolved(nested));
                }
                self.resolve_member_access(entity, name, ScopeNamespace::Value)
            }
            ast::ExpressionKind::Specialize { target, .. } => {
                let entity = self.resolve_expression_entity(target)?;
                if Self::entity_is_value(&entity) {
                    return Ok(ResolvedEntity::DeferredAssociatedValue);
                }
                self.apply_specialization(entity.clone(), node.span)?;
                return Ok(entity);
            }
            // Anything else produces a value expression
            _ => return Ok(ResolvedEntity::DeferredAssociatedValue),
        }
    }

    fn entity_is_value(entity: &ResolvedEntity<'_>) -> bool {
        matches!(
            entity,
            ResolvedEntity::DeferredAssociatedValue
                | ResolvedEntity::Resolved(
                    Resolution::LocalVariable(_)
                        | Resolution::Definition(
                            _,
                            DefinitionKind::ModuleVariable | DefinitionKind::Constant
                        )
                )
        )
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
                .resolve_path_in_scopes(&path, ns, None, &self.scopes);

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

    fn nested_type_member(&self, base: &Resolution, name: &Identifier) -> Option<Resolution> {
        let scope = match *base {
            Resolution::Definition(id, DefinitionKind::Struct | DefinitionKind::Enum) => {
                self.resolver.nested_scope(id)?
            }
            Resolution::SelfTypeAlias(id)
                if self.resolver.definition_kind(id) == DefinitionKind::Impl =>
            {
                self.scopes
                    .iter()
                    .rev()
                    .find_map(|lexical| match lexical.source {
                        LexicalScopeSource::Scoped(scope)
                            if matches!(
                                scope.kind,
                                ScopeKind::Definition(
                                    _,
                                    DefinitionKind::Struct | DefinitionKind::Enum
                                )
                            ) =>
                        {
                            Some(scope)
                        }
                        _ => None,
                    })?
            }
            Resolution::SelfTypeAlias(id) => self.resolver.nested_scope(id)?,
            _ => return None,
        };
        self.resolver
            .resolve_in_scope(name, scope, ScopeNamespace::Type)
            .ok()
            .map(|h| h.resolution())
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
                Resolution::Definition(def_id, kind) => match kind {
                    DefinitionKind::Module | DefinitionKind::Namespace => unreachable!(),
                    DefinitionKind::Enum if self.resolver.has_enum_variant(def_id, name.symbol) => {
                        return Ok(ResolvedEntity::DeferredEnumVariant);
                    }
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
                Resolution::StdItem(_) | Resolution::Error => unreachable!(),
            },
            ResolvedEntity::DeferredAssociatedValue => {
                return Ok(ResolvedEntity::DeferredAssociatedValue);
            }
            ResolvedEntity::DeferredAssociatedType => {
                return Ok(ResolvedEntity::DeferredAssociatedType);
            }
            // Reached for `Enum.variant.member`. The base is a value, so the
            // member belongs to it and the type-relative path stops here.
            ResolvedEntity::DeferredEnumVariant => {
                return Ok(ResolvedEntity::DeferredAssociatedValue);
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
            ResolvedEntity::DeferredAssociatedType | ResolvedEntity::DeferredEnumVariant => {
                return Ok(());
            }
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
            Resolution::StdItem(_) | Resolution::Error => unreachable!(),
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

            // Ignored closure parameters occupy an ABI slot but bind no name.
            if self.resolver.context.symbol_text(param.name.symbol).as_str() == "_" {
                continue;
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

    fn resolve_select_arm(&mut self, node: &ast::SelectArm) {
        self.visit_expression(&node.operation);
        self.with_scope_source(LexicalScopeSource::Plain, |this| {
            this.resolve_top_level_pattern(&node.pattern, PatternSource::Variable);
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
                ast::PatternKind::TypeTest { target, .. } => { self.visit_type(target); }
                ast::PatternKind::Range { start, end, .. } => {
                    self.visit_expression(start);
                    self.visit_expression(end);
                }
                ast::PatternKind::Literal(..)
                | ast::PatternKind::Wildcard
                | ast::PatternKind::Tuple(..) => {}
                ast::PatternKind::Identifier(ident) => {
                    let res = self.fresh_var_binding(ident, pat.id, bindings, source);
                    self.resolver
                        .record_resolution(pat.id, ResolutionState::Complete(res));
                }
                ast::PatternKind::Member(path) => match path {
                    ast::ConstructorPath::Qualified { path } => {
                        self.resolve_path_with_source(
                            pat.id,
                            path,
                            ResolutionSource::MatchPatternUnit,
                        );
                    }
                    _ => {}
                },
                ast::PatternKind::PathTuple { path, .. } => match path {
                    ast::ConstructorPath::Qualified { path } => {
                        self.resolve_path_with_source(
                            pat.id,
                            path,
                            ResolutionSource::MatchPatternTupleStruct,
                        );
                    }
                    _ => {}
                },
                ast::PatternKind::PathNamed { path, .. } => {
                    if let ast::ConstructorPath::Qualified { path } = path {
                        self.resolve_path_with_source(pat.id, path, ResolutionSource::Constructor);
                    }
                }
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
            if let Some(lint) = &self.resolver.lint {
                let mut lint = lint.borrow_mut();
                match source {
                    // Parameters are exempt from the unused-variable lint.
                    PatternSource::FunctionParameter => lint.note_parameter(id, *ident, self.owner),
                    // Only a declaration can be a mistaken assignment;
                    // conditional, loop and match bindings shadow on purpose.
                    PatternSource::Variable => {
                        lint.note_declaration(id, *ident, self.owner, &self.scopes)
                    }
                    _ => lint.note_local(id, *ident, self.owner),
                }
            }
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
                    map.insert(ident.symbol, ident.span);
                }
                ast::PatternKind::Or(sub_patterns, _) => {
                    let res = self.compute_and_check_or_match_pattern_binding_map(sub_patterns);
                    map.extend(res);
                    return false; // Recursive binding maps already cover the alternatives.
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

            for (name, &span) in others {
                match map_outer.get(&name) {
                    None => {
                        let err = missing_vars.entry(*name).or_insert_with(|| BindingError {
                            name: *name,
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
    fn resolve_impl(&mut self, id: ast::NodeID, node: &ast::Impl) {
        let def_id = self.resolver.definition_id(id);
        if let Some(first) = node.nested_types.first() {
            let owner = self
                .resolver
                .nested_type_parent(self.resolver.definition_id(first.id));
            let scope = self.resolver.get_definition_scope(owner);
            self.with_scope(scope, |this| {
                for nested in &node.nested_types {
                    this.visit_declaration(nested);
                }
            });
        }
        let owner_scope_index = self.scopes.len();
        self.with_scope_source(LexicalScopeSource::Plain, |this| {
            this.with_generics_scope(&node.generics, |this| {
                let self_res = Resolution::SelfTypeAlias(def_id);
                this.with_self_alias_scope(self_res, |this| {
                    // Resolve the interface type if present
                    if let Some(interface) = &node.interface {
                        this.with_type_source(ResolutionSource::Interface, |this| {
                            this.visit_type(interface);
                        });
                    }
                    // Resolve the target type
                    this.with_type_source(ResolutionSource::ImplTarget, |this| {
                        this.visit_type(&node.target);
                    });
                    this.visit_generics(&node.generics);
                    let scope = match this.resolver.resolutions.get(&node.target.id) {
                        Some(ResolutionState::Complete(Resolution::Definition(
                            owner,
                            DefinitionKind::Struct | DefinitionKind::Enum,
                        ))) => this.resolver.nested_scope(*owner),
                        _ => None,
                    };
                    if let Some(scope) = scope {
                        // Explicit extension and method generics shadow a sibling type.
                        this.scopes[owner_scope_index].source = LexicalScopeSource::Scoped(scope);
                    }
                    for declaration in &node.declarations {
                        this.visit_assoc_declaration(declaration, AssocContext::Impl(id));
                    }
                });
            });
        })
    }
}

impl<'r, 'a> Actor<'r, 'a> {
    fn resolve_path_with_source(&mut self, id: NodeID, path: &Path, source: ResolutionSource) {
        let fallback = matches!(source, ResolutionSource::MatchPatternTupleStruct)
            .then_some(ScopeNamespace::Type);
        let result = self.resolver.resolve_path_in_scopes(
            &path.segments, source.namespace(), fallback, &self.scopes,
        );

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
                self.resolver.dcx().emit(error.diag(self.resolver.context));
                return;
            }
        };

        let expected = source.expected();

        if let Some(resolution) = resolution {
            if !source.is_allowed(&resolution) {
                let provided = resolution.description();
                let symbol = self.resolver.context.symbol_text(path.segments.last().unwrap().identifier.symbol);
                if matches!(
                    source,
                    ResolutionSource::Type | ResolutionSource::TypeArgument
                ) && matches!(
                    resolution,
                    Resolution::Definition(_, DefinitionKind::Interface)
                ) {
                    let message = format!(
                        "interface '{symbol}' cannot be used as a type; use `any {symbol}`"
                    );
                    self.resolver.dcx().emit_error(message, Some(path.span));
                } else {
                    let message = format!("expected {expected}, got {provided} '{symbol}'");
                    self.resolver.dcx().emit_error(message, Some(path.span));
                }
            }
        } else if !source.defer_to_type_checker() {
            let symbol = self.resolver.context.symbol_text(path.segments.last().unwrap().identifier.symbol);
            let message = format!("cannot resolve {expected} '{symbol}'");
            self.resolver.dcx().emit_error(message, Some(path.span));
        }
    }
}

impl<'r, 'a> Actor<'r, 'a> {
    fn report_error(&self, e: ResolutionError) {
        self.resolver.dcx().emit(e.diag(self.resolver.context));
    }
}

/// Identifiers assigned by `=`, including inside a tuple target, are writes
/// rather than reads of the local they name.
fn note_assign_targets(lint: &mut super::lint::LintState, target: &ast::Expression) {
    match &target.kind {
        ast::ExpressionKind::Identifier(_) => lint.note_assign_target(target.id),
        ast::ExpressionKind::Tuple(elements, _) => {
            for element in elements {
                note_assign_targets(lint, element);
            }
        }
        ast::ExpressionKind::Parenthesis(inner) => note_assign_targets(lint, inner),
        _ => {}
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
