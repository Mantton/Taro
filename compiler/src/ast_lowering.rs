use crate::parse::escape;
use crate::{
    ast::{self, Identifier},
    cfg::TargetInfo,
    compile::context::GlobalContext,
    error::CompileResult,
    hir::{self, StdItem},
    sema::resolve::{
        models::{
            ExpressionResolutionState, Holder, Resolution, ResolutionOutput, ResolutionState,
            Scope, ScopeNamespace,
        },
        scope_lookup,
    },
    span::{Span, Symbol},
};
use rustc_hash::FxHashMap;

pub fn lower_package<'a, 'c>(
    package: ast::Package,
    gcx: GlobalContext<'c>,
    resolutions: &'a ResolutionOutput<'c>,
) -> CompileResult<hir::Package> {
    let mut actor = Actor::new(gcx, resolutions);
    let root = actor.lower_module(package.root);
    gcx.dcx.ok()?;
    Ok(hir::Package { root })
}

#[derive(Default, Clone, Copy)]
enum LocationScope {
    #[default]
    Lexical,
    DefaultArgument,
    Caller([hir::NodeID; 3]),
}

pub struct Actor<'a, 'c> {
    pub context: GlobalContext<'c>,
    pub resolutions: &'a ResolutionOutput<'c>,
    pub next_index: u32,
    pub node_mapping: FxHashMap<ast::NodeID, hir::NodeID>,
    optional_unwrap_replacement: Option<OptionalUnwrapReplacement>,
    lowering_deferred_bracket: bool,
    location_scope: LocationScope,
    target: TargetInfo,
}

impl<'a, 'c> Actor<'a, 'c> {
    fn new(context: GlobalContext<'c>, resolutions: &'a ResolutionOutput<'c>) -> Actor<'a, 'c> {
        Actor {
            context,
            resolutions,
            next_index: 0,
            node_mapping: Default::default(),
            optional_unwrap_replacement: None,
            lowering_deferred_bracket: false,
            location_scope: LocationScope::Lexical,
            target: crate::cfg_eval::target_info(context),
        }
    }

    fn next_index(&mut self) -> hir::NodeID {
        let index = hir::NodeID::from_raw(self.next_index);
        self.next_index += 1;
        index
    }

    fn definition_id(&self, id: ast::NodeID) -> hir::DefinitionID {
        *self
            .resolutions
            .node_to_definition
            .get(&id)
            .expect("definition mapping")
    }
}

impl<'a, 'c> Actor<'a, 'c> {
    fn lower_module(&mut self, module: ast::Module) -> hir::Module {
        let id = self.definition_id(module.id);
        let file_ids = module.files.iter().map(|file| file.id).collect();
        let declarations: Vec<hir::Declaration> = module
            .files
            .into_iter()
            .flat_map(|file| self.lower_file(file))
            .collect();

        let submodules: Vec<hir::Module> = module
            .submodules
            .into_iter()
            .map(|file| self.lower_module(file))
            .collect();

        hir::Module {
            id,
            name: module.name,
            files: file_ids,
            declarations,
            submodules,
        }
    }

    fn lower_file(&mut self, file: ast::File) -> Vec<hir::Declaration> {
        file.declarations
            .into_iter()
            .flat_map(|node| self.lower_declaration(node))
            .collect()
    }

    fn lower_attributes(&mut self, attributes: ast::AttributeList) -> hir::AttributeList {
        attributes
            .into_iter()
            .map(|attr| hir::Attribute {
                identifier: attr.identifier,
                args: attr.args.map(|args| self.lower_attribute_args(args)),
                span: attr.span,
            })
            .collect()
    }

    fn lower_attribute_args(&mut self, args: ast::AttributeArgs) -> hir::AttributeArgs {
        hir::AttributeArgs {
            items: args
                .items
                .into_iter()
                .map(|arg| self.lower_attribute_arg(arg))
                .collect(),
            span: args.span,
        }
    }

    fn lower_attribute_arg(&mut self, arg: ast::AttributeArg) -> hir::AttributeArg {
        match arg {
            ast::AttributeArg::KeyValue { key, value, span } => {
                let hir_lit = match convert_ast_literal(self.context, value) {
                    Ok(lit) => lit,
                    Err(err) => {
                        self.context.dcx.emit_error(err.into(), Some(span));
                        hir::Literal::Nil
                    }
                };
                hir::AttributeArg::KeyValue {
                    key,
                    value: hir_lit,
                    span,
                }
            }
            ast::AttributeArg::Flag { key, span } => hir::AttributeArg::Flag { key, span },
            ast::AttributeArg::Literal { value, span } => {
                let hir_lit = match convert_ast_literal(self.context, value) {
                    Ok(lit) => lit,
                    Err(err) => {
                        self.context.dcx.emit_error(err.into(), Some(span));
                        hir::Literal::Nil
                    }
                };
                hir::AttributeArg::Literal {
                    value: hir_lit,
                    span,
                }
            }
        }
    }
}

impl<'a, 'c> Actor<'a, 'c> {
    fn lower_declaration(&mut self, node: ast::Declaration) -> Vec<hir::Declaration> {
        // Check @cfg attributes - if any cfg condition fails, skip this declaration
        if !self.should_include_declaration(&node.attributes) {
            // Resolution saw this declaration (a `@test` function outside
            // `taro test`, say) but type checking will not, so its method
            // calls cannot mark the interface imports they rely on.
            crate::cfg_eval::note_removed(self.context, node.span, |collector| {
                ast::AstVisitor::visit_declaration(collector, &node)
            });
            return vec![];
        }

        let ast::Declaration {
            id,
            kind,
            span,
            identifier,
            attributes,
            ..
        } = node;

        let mut nested = Vec::new();
        let kind = match kind {
            ast::DeclarationKind::Interface(node) => {
                hir::DeclarationKind::Interface(self.lower_interface(node))
            }
            ast::DeclarationKind::Class(node) => {
                hir::DeclarationKind::Struct(self.lower_class(node))
            }
            ast::DeclarationKind::Struct(node) => {
                hir::DeclarationKind::Struct(self.lower_struct(node))
            }
            ast::DeclarationKind::Enum(node) => hir::DeclarationKind::Enum(self.lower_enum(node)),
            ast::DeclarationKind::TypeAlias(node) => {
                hir::DeclarationKind::TypeAlias(self.lower_alias(node))
            }
            ast::DeclarationKind::Function(node) => {
                hir::DeclarationKind::Function(self.lower_function(node, identifier.symbol))
            }
            ast::DeclarationKind::ExternBlock(node) => {
                return node
                    .declarations
                    .into_iter()
                    .map(|decl| self.lower_extern_declaration(decl, node.abi))
                    .collect();
            }
            ast::DeclarationKind::Constant(node) => {
                hir::DeclarationKind::Constant(self.lower_constant(node))
            }
            ast::DeclarationKind::Import(node) => {
                hir::DeclarationKind::Import(self.lower_use_tree(node))
            }
            ast::DeclarationKind::Export(node) => {
                hir::DeclarationKind::Export(self.lower_use_tree(node))
            }
            ast::DeclarationKind::Namespace(node) => {
                hir::DeclarationKind::Namespace(self.lower_namespace(node))
            }
            ast::DeclarationKind::StaticVariable(node) => {
                hir::DeclarationKind::StaticVariable(self.lower_static_variable(node))
            }
            ast::DeclarationKind::Impl(mut node) => {
                let type_only = !node.nested_types.is_empty()
                    && node.declarations.is_empty()
                    && node.generics.type_parameters.is_none();
                nested.extend(
                    std::mem::take(&mut node.nested_types)
                        .into_iter()
                        .flat_map(|d| self.lower_declaration(d)),
                );
                if type_only {
                    return nested;
                }
                hir::DeclarationKind::Impl(self.lower_impl(node))
            }
        };

        nested.push(hir::Declaration {
            id: self.definition_id(id),
            span,
            identifier,
            kind,
            attributes: self.lower_attributes(attributes),
        });
        nested
    }

    /// Check if a declaration should be included based on @cfg attributes.
    /// Returns true if all @cfg conditions pass (or if there are no @cfg attrs).
    fn should_include_declaration(&self, attributes: &ast::AttributeList) -> bool {
        // Harness declarations are compiled only for their matching command.
        // `@skip` belongs to both harnesses, while expected panics only make
        // sense for tests.
        for attr in attributes {
            let sym = attr.identifier.symbol;
            if self.context.symbol_eq(sym, "test") && !self.context.config.harness_mode.is_test() {
                return false;
            }
            if self.context.symbol_eq(sym, "bench") && !self.context.config.harness_mode.is_bench()
            {
                return false;
            }
            if self.context.symbol_eq(sym, "expectPanic")
                && !self.context.config.harness_mode.is_enabled()
            {
                return false;
            }
            if self.context.symbol_eq(sym, "skip") && !self.context.config.harness_mode.is_enabled()
            {
                return false;
            }
        }

        crate::cfg_eval::should_include_attrs(attributes, &self.target, self.context)
    }

    fn evaluate_cfg_expr(&self, expr: &ast::CfgExpr) -> bool {
        crate::cfg_eval::eval_cfg_expr(expr, &self.target, self.context)
    }

    fn lower_extern_declaration(
        &mut self,
        node: ast::ExternDeclaration,
        abi: Symbol,
    ) -> hir::Declaration {
        let ast::Declaration {
            id,
            kind,
            span,
            identifier,
            attributes,
            ..
        } = node;

        let kind = match kind {
            ast::ExternDeclarationKind::Function(mut node) => {
                if node.abi.is_none() {
                    node.abi = Some(abi);
                }
                hir::DeclarationKind::Function(self.lower_function(node, identifier.symbol))
            }
            ast::ExternDeclarationKind::Type(_) => hir::DeclarationKind::OpaqueType,
        };

        hir::Declaration {
            id: self.definition_id(id),
            span,
            identifier,
            kind,
            attributes: self.lower_attributes(attributes),
        }
    }

    fn lower_function_declaration(&mut self, node: ast::FunctionDeclaration) -> hir::Declaration {
        let ast::Declaration {
            id,
            kind,
            span,
            identifier,
            attributes,
            ..
        } = node;

        let kind = match kind {
            ast::FunctionDeclarationKind::Struct(node) => {
                hir::DeclarationKind::Struct(self.lower_struct(node))
            }
            ast::FunctionDeclarationKind::Enum(node) => {
                hir::DeclarationKind::Enum(self.lower_enum(node))
            }
            ast::FunctionDeclarationKind::TypeAlias(node) => {
                hir::DeclarationKind::TypeAlias(self.lower_alias(node))
            }
            ast::FunctionDeclarationKind::Import(node) => {
                hir::DeclarationKind::Import(self.lower_use_tree(node))
            }
            ast::FunctionDeclarationKind::Function(node) => {
                hir::DeclarationKind::Function(self.lower_function(node, identifier.symbol))
            }
            ast::FunctionDeclarationKind::Constant(node) => {
                hir::DeclarationKind::Constant(self.lower_constant(node))
            }
        };

        hir::Declaration {
            id: self.definition_id(id),
            span,
            identifier,
            kind,
            attributes: self.lower_attributes(attributes),
        }
    }

    fn lower_namespace_declaration(&mut self, node: ast::NamespaceDeclaration) -> hir::Declaration {
        let ast::Declaration {
            id,
            kind,
            span,
            identifier,
            attributes,
            ..
        } = node;

        let kind = match kind {
            ast::NamespaceDeclarationKind::Class(node) => {
                hir::DeclarationKind::Struct(self.lower_class(node))
            }
            ast::NamespaceDeclarationKind::Struct(node) => {
                hir::DeclarationKind::Struct(self.lower_struct(node))
            }
            ast::NamespaceDeclarationKind::Enum(node) => {
                hir::DeclarationKind::Enum(self.lower_enum(node))
            }
            ast::NamespaceDeclarationKind::Interface(node) => {
                hir::DeclarationKind::Interface(self.lower_interface(node))
            }
            ast::NamespaceDeclarationKind::TypeAlias(node) => {
                hir::DeclarationKind::TypeAlias(self.lower_alias(node))
            }
            ast::NamespaceDeclarationKind::Import(node) => {
                hir::DeclarationKind::Import(self.lower_use_tree(node))
            }
            ast::NamespaceDeclarationKind::Export(node) => {
                hir::DeclarationKind::Export(self.lower_use_tree(node))
            }
            ast::NamespaceDeclarationKind::Function(node) => {
                hir::DeclarationKind::Function(self.lower_function(node, identifier.symbol))
            }
            ast::NamespaceDeclarationKind::StaticVariable(node) => {
                hir::DeclarationKind::StaticVariable(self.lower_static_variable(node))
            }
            ast::NamespaceDeclarationKind::Constant(node) => {
                hir::DeclarationKind::Constant(self.lower_constant(node))
            }
            ast::NamespaceDeclarationKind::Namespace(node) => {
                hir::DeclarationKind::Namespace(self.lower_namespace(node))
            }
        };

        hir::Declaration {
            id: self.definition_id(id),
            span,
            identifier,
            kind,
            attributes: self.lower_attributes(attributes),
        }
    }

    fn lower_assoc_declaration(
        &mut self,
        node: ast::AssociatedDeclaration,
    ) -> hir::AssociatedDeclaration {
        let ast::Declaration {
            id,
            kind,
            span,
            identifier,
            attributes,
            ..
        } = node;

        let kind = match kind {
            ast::AssociatedDeclarationKind::Initializer(initializer) => {
                let function = initializer.function;
                let mut function = self.lower_function(function, identifier.symbol);
                function.initializer_kind = Some(hir::InitializerKind {
                    is_required: initializer.is_required,
                    is_convenience: initializer.is_convenience,
                });
                hir::AssociatedDeclarationKind::Initializer(function)
            }
            ast::AssociatedDeclarationKind::Constant(node) => {
                hir::AssociatedDeclarationKind::Constant(self.lower_constant(node))
            }
            ast::AssociatedDeclarationKind::Function(node) => {
                hir::AssociatedDeclarationKind::Function(
                    self.lower_function(node, identifier.symbol),
                )
            }
            ast::AssociatedDeclarationKind::AssociatedType(node) => {
                hir::AssociatedDeclarationKind::Type(self.lower_alias(node))
            }
            ast::AssociatedDeclarationKind::Property(node) => {
                hir::AssociatedDeclarationKind::Property(hir::ComputedProperty {
                    ty: self.lower_type(node.ty),
                    getter_id: self.definition_id(node.getter_id),
                })
            }
            ast::AssociatedDeclarationKind::Subscript(node) => {
                hir::AssociatedDeclarationKind::Subscript(hir::NativeSubscript {
                    ty: self.lower_type(node.ty),
                    getter_id: node.getter_id.map(|id| self.definition_id(id)),
                    setter_id: node.setter_id.map(|id| self.definition_id(id)),
                    address_id: node.address_id.map(|id| self.definition_id(id)),
                    getter_is_default: node.getter_is_default,
                    setter_is_default: node.setter_is_default,
                    is_override: node.is_override,
                    is_final: node.is_final,
                })
            }
        };

        hir::AssociatedDeclaration {
            id: self.definition_id(id),
            span,
            identifier,
            kind,
            attributes: self.lower_attributes(attributes),
        }
    }
}

impl Actor<'_, '_> {
    fn lower_interface(&mut self, node: ast::Interface) -> hir::Interface {
        hir::Interface {
            generics: self.lower_generics(node.generics),
            declarations: node
                .declarations
                .into_iter()
                .map(|n| self.lower_assoc_declaration(n))
                .collect(),
            conformances: node.conformances.map(|n| self.lower_conformances(n)),
        }
    }

    fn lower_class(&mut self, node: ast::Class) -> hir::Struct {
        let header = hir::ClassHeader {
            is_final: node.is_final,
        };
        let mut value = self.lower_struct(ast::Struct {
            positional: false,
            generics: node.generics,
            fields: node.fields,
            conformances: node.conformances,
        });
        value.class_header = Some(header);
        value
    }

    fn lower_struct(&mut self, node: ast::Struct) -> hir::Struct {
        hir::Struct {
            positional: node.positional,
            class_header: None,
            generics: self.lower_generics(node.generics),
            fields: node
                .fields
                .into_iter()
                .map(|n| self.lower_field_definition(n))
                .collect(),
            conformances: node.conformances.map(|n| self.lower_conformances(n)),
        }
    }

    fn lower_enum(&mut self, node: ast::Enum) -> hir::Enum {
        hir::Enum {
            generics: self.lower_generics(node.generics),
            variants: node
                .cases
                .into_iter()
                .flat_map(|c| c.variants)
                .map(|v| self.lower_variant(v))
                .collect(),
            conformances: node.conformances.map(|n| self.lower_conformances(n)),
        }
    }

    fn lower_alias(&mut self, node: ast::TypeAlias) -> hir::TypeAlias {
        hir::TypeAlias {
            generics: self.lower_generics(node.generics),
            ty: node.ty.map(|n| self.lower_type(n)),
            interface_set: node.interface_set.map(|n| self.lower_generic_bounds(n)),
            bounds: node.bounds.map(|n| self.lower_generic_bounds(n)),
        }
    }

    fn lower_constant(&mut self, node: ast::Constant) -> hir::Constant {
        hir::Constant {
            identifier: node.identifier,
            ty: self.lower_type(node.ty),
            expr: node.expr.map(|e| self.lower_expression(e)),
        }
    }

    fn lower_use_tree(&mut self, node: ast::UseTree) -> hir::UseTree {
        match node.kind {
            ast::UseTreeKind::Glob => hir::UseTree {
                span: node.span,
                path: self.lower_use_tree_module_path(&node.path.nodes),
                kind: hir::UseTreeKind::Glob,
            },
            ast::UseTreeKind::Simple { alias } => {
                let mut nodes = node.path.nodes;
                let source = nodes.pop().expect("non-empty use tree path");
                let path = self.lower_use_tree_module_path(&nodes);
                let module_scope = self.resolve_module_scope(&nodes);
                hir::UseTree {
                    span: node.span,
                    path,
                    kind: hir::UseTreeKind::Simple {
                        source: self.lower_use_tree_source_segment(source, module_scope),
                        alias: alias.map(|identifier| self.lower_use_tree_alias(identifier)),
                    },
                }
            }
            ast::UseTreeKind::Nested { nodes, span } => {
                let path = self.lower_use_tree_module_path(&node.path.nodes);
                let module_scope = self.resolve_module_scope(&node.path.nodes);
                let items = nodes
                    .into_iter()
                    .map(|item| {
                        let alias_span = item.alias.map(|alias| alias.span);
                        let source = self.lower_use_tree_source_segment(item.name, module_scope);
                        hir::UseTreeNestedItem {
                            span: source.span.to(alias_span.unwrap_or(source.span)),
                            source,
                            alias: item
                                .alias
                                .map(|identifier| self.lower_use_tree_alias(identifier)),
                        }
                    })
                    .collect();

                hir::UseTree {
                    span: node.span,
                    path,
                    kind: hir::UseTreeKind::Nested { items, span },
                }
            }
        }
    }
}

impl<'a, 'c> Actor<'a, 'c> {
    fn lower_use_tree_alias(&mut self, identifier: Identifier) -> hir::UseTreeAlias {
        hir::UseTreeAlias {
            id: self.next_index(),
            identifier,
            span: identifier.span,
        }
    }

    fn lower_use_tree_module_path(&mut self, nodes: &[Identifier]) -> hir::UseTreePath {
        let span = if let Some((first, rest)) = nodes.split_first() {
            let end = rest.last().copied().unwrap_or(*first).span;
            first.span.to(end)
        } else {
            Span::empty(crate::span::FileID::new(0))
        };

        hir::UseTreePath {
            span,
            segments: self.resolve_module_path_segments(nodes),
        }
    }

    fn lower_use_tree_source_segment(
        &mut self,
        identifier: Identifier,
        module_scope: Option<Scope<'c>>,
    ) -> hir::PathSegment {
        let resolution = if let Some(scope) = module_scope {
            if let Some(holder) = self.resolve_in_scope(scope, identifier) {
                self.lower_resolution(holder.resolution())
            } else {
                hir::Resolution::Error
            }
        } else if let Some(scope) = self.resolve_package_scope(identifier) {
            if let Some(resolution) = scope.resolution() {
                self.lower_resolution(resolution)
            } else {
                hir::Resolution::Error
            }
        } else {
            hir::Resolution::Error
        };

        hir::PathSegment {
            id: self.next_index(),
            identifier,
            arguments: None,
            span: identifier.span,
            resolution,
        }
    }

    fn resolve_module_path_segments(&mut self, nodes: &[Identifier]) -> Vec<hir::PathSegment> {
        let mut scope = None;
        let mut segments = Vec::with_capacity(nodes.len());

        for identifier in nodes.iter().copied() {
            let (resolution, next_scope) = if let Some(current_scope) = scope {
                let holder = match self.resolve_in_scope(current_scope, identifier) {
                    Some(holder) => holder,
                    None => {
                        segments.push(self.use_tree_error_segment(identifier));
                        break;
                    }
                };
                let next_scope = match self.scope_for_holder(&holder) {
                    Some(scope) => scope,
                    None => {
                        segments.push(self.use_tree_error_segment(identifier));
                        break;
                    }
                };
                (self.lower_resolution(holder.resolution()), next_scope)
            } else {
                let Some(next_scope) = self.resolve_package_scope(identifier) else {
                    segments.push(self.use_tree_error_segment(identifier));
                    break;
                };
                let resolution = next_scope
                    .resolution()
                    .map(|resolution| self.lower_resolution(resolution))
                    .unwrap_or(hir::Resolution::Error);
                (resolution, next_scope)
            };

            segments.push(hir::PathSegment {
                id: self.next_index(),
                identifier,
                arguments: None,
                span: identifier.span,
                resolution,
            });
            scope = Some(next_scope);
        }

        segments
    }

    fn resolve_module_scope(&self, nodes: &[Identifier]) -> Option<Scope<'c>> {
        let mut scope: Option<Scope<'c>> = None;

        for identifier in nodes.iter().copied() {
            scope = Some(if let Some(current_scope) = scope {
                let holder = self.resolve_in_scope(current_scope, identifier)?;
                self.scope_for_holder(&holder)?
            } else {
                self.resolve_package_scope(identifier)?
            });
        }

        scope
    }

    fn resolve_package_scope(&self, identifier: Identifier) -> Option<Scope<'c>> {
        scope_lookup::resolve_package_scope(self.context, self.resolutions, identifier)
    }

    fn resolve_in_scope(&self, scope: Scope<'c>, identifier: Identifier) -> Option<Holder<'c>> {
        self.find_holder_in_scope(scope, identifier, ScopeNamespace::Type)
            .or_else(|| self.find_holder_in_scope(scope, identifier, ScopeNamespace::Value))
            .or_else(|| {
                scope_lookup::resolve_in_scope(scope, identifier, ScopeNamespace::Type)
                    .ok()
                    .or_else(|| {
                        scope_lookup::resolve_in_scope(scope, identifier, ScopeNamespace::Value)
                            .ok()
                    })
            })
    }

    fn find_holder_in_scope(
        &self,
        scope: Scope<'c>,
        identifier: Identifier,
        namespace: ScopeNamespace,
    ) -> Option<Holder<'c>> {
        scope_lookup::find_holder_in_scope(scope, identifier.symbol, namespace)
    }

    fn scope_for_holder(&self, holder: &Holder<'c>) -> Option<Scope<'c>> {
        scope_lookup::scope_for_holder(self.context, self.resolutions, holder)
    }

    fn use_tree_error_segment(&mut self, identifier: Identifier) -> hir::PathSegment {
        hir::PathSegment {
            id: self.next_index(),
            identifier,
            arguments: None,
            span: identifier.span,
            resolution: hir::Resolution::Error,
        }
    }

    fn lower_function(&mut self, node: ast::Function, name: Symbol) -> hir::Function {
        if let Some(block) = &node.block {
            self.context.dcx.register_function_span(block.span, name);
        }
        let enclosing_default = std::mem::take(&mut self.location_scope);
        let abi = self.lower_abi(node.abi, node.signature.span);
        let function = hir::Function {
            generics: self.lower_generics(node.generics),
            signature: self.lower_function_signature(node.signature),
            block: node.block.map(|n| self.lower_block(n)),
            is_unsafe: node.is_unsafe,
            is_const: node.is_const,
            is_async: node.is_async,
            is_final: node.is_final,
            is_override: node.is_override,
            initializer_kind: None,
            abi,
        };
        self.location_scope = enclosing_default;
        function
    }

    fn lower_abi(&mut self, abi: Option<Symbol>, span: Span) -> Option<hir::Abi> {
        let Some(abi) = abi else { return None };
        let abi_text = self.context.symbol_text(abi);
        match abi_text.as_str() {
            "C" | "c" => Some(hir::Abi::C),
            "blocking" => Some(hir::Abi::Blocking),
            "taro_rt" | "rt" => Some(hir::Abi::Runtime),
            "taro_intrinsic" | "intrinsic" => Some(hir::Abi::Intrinsic),
            other => {
                self.context.dcx.emit_error(
                    format!(
                        "unknown ABI \"{}\" (supported: \"C\", \"blocking\", \"taro_rt\", \"taro_intrinsic\")",
                        other
                    ),
                    Some(span),
                );
                None
            }
        }
    }

    fn lower_function_signature(&mut self, node: ast::FunctionSignature) -> hir::FunctionSignature {
        hir::FunctionSignature {
            span: node.span,
            prototype: self.lower_function_prototype(node.prototype),
        }
    }

    fn lower_function_prototype(&mut self, node: ast::FunctionPrototype) -> hir::FunctionPrototype {
        hir::FunctionPrototype {
            inputs: node
                .inputs
                .into_iter()
                .map(|n| self.lower_function_parameter(n))
                .collect(),
            output: node.output.map(|n| self.lower_type(n)),
        }
    }

    fn lower_function_parameter(&mut self, node: ast::FunctionParameter) -> hir::FunctionParameter {
        let ast::FunctionParameter {
            id: node_id,
            attributes,
            label,
            name,
            annotated_type,
            default_value,
            is_lazy,
            is_variadic,
            span,
        } = node;
        let id = self.next_index();
        self.node_mapping.insert(node_id, id);
        let attributes = self.lower_attributes(attributes);
        let annotated_type = self.lower_type(annotated_type);
        let enclosing_default =
            std::mem::replace(&mut self.location_scope, LocationScope::DefaultArgument);
        let default_value = default_value.map(|n| {
            let expr = self.lower_expression(n);
            if is_lazy {
                let def = self
                    .context
                    .allocate_synthetic_id(self.context.package_index());
                Box::new(hir::Expression::lazy_argument(self.next_index(), def, expr))
            } else {
                expr
            }
        });
        let caller_bindings = match std::mem::replace(&mut self.location_scope, enclosing_default) {
            LocationScope::Caller(bindings) => Some(bindings),
            _ => None,
        };
        hir::FunctionParameter {
            id,
            attributes,
            label,
            name,
            annotated_type,
            default_value,
            caller_bindings,
            is_lazy,
            is_variadic,
            span,
        }
    }
}

impl Actor<'_, '_> {
    fn lower_impl(&mut self, node: ast::Impl) -> hir::Impl {
        hir::Impl {
            generics: self.lower_generics(node.generics),
            interface: node.interface.map(|ty| self.lower_type(ty)),
            delegate: node.delegate,
            target: self.lower_type(node.target),
            declarations: node
                .declarations
                .into_iter()
                .map(|n| self.lower_assoc_declaration(n))
                .collect(),
        }
    }
    fn lower_namespace(&mut self, node: ast::Namespace) -> hir::Namespace {
        hir::Namespace {
            declarations: node
                .declarations
                .into_iter()
                .map(|n| self.lower_namespace_declaration(n))
                .collect(),
        }
    }
}

impl Actor<'_, '_> {
    fn lower_generics(&mut self, node: ast::Generics) -> hir::Generics {
        hir::Generics {
            type_parameters: node.type_parameters.map(|n| self.lower_type_parameters(n)),
            where_clause: node
                .where_clause
                .map(|n| self.lower_generic_where_clause(n)),
        }
    }

    fn lower_type_parameters(&mut self, node: ast::TypeParameters) -> hir::TypeParameters {
        hir::TypeParameters {
            span: node.span,
            parameters: node
                .parameters
                .into_iter()
                .map(|n| self.lower_type_parameter(n))
                .collect(),
        }
    }

    fn lower_type_parameter(&mut self, node: ast::TypeParameter) -> hir::TypeParameter {
        hir::TypeParameter {
            is_anonymous: node.is_anonymous,
            id: self.definition_id(node.id),
            span: node.span,
            identifier: node.identifier,
            bounds: node.bounds.map(|n| self.lower_generic_bounds(n)),
            kind: match node.kind {
                ast::TypeParameterKind::Type { default } => hir::TypeParameterKind::Type {
                    default: default.map(|n| self.lower_type(n)),
                },
                ast::TypeParameterKind::Constant { ty, default } => {
                    hir::TypeParameterKind::Constant {
                        ty: self.lower_type(ty),
                        default: default.map(|n| self.lower_anon_const(n)),
                    }
                }
            },
        }
    }

    fn lower_type_arguments(&mut self, node: ast::TypeArguments) -> hir::TypeArguments {
        hir::TypeArguments {
            span: node.span,
            arguments: node
                .arguments
                .into_iter()
                .map(|n| self.lower_type_argument(n))
                .collect(),
        }
    }

    fn lower_type_argument(&mut self, node: ast::TypeArgument) -> hir::TypeArgument {
        match node {
            ast::TypeArgument::Type(n) => hir::TypeArgument::Type(self.lower_type(n)),
            ast::TypeArgument::Const(n) => hir::TypeArgument::Const(self.lower_anon_const(n)),
            ast::TypeArgument::AssocType(ident, ty) => {
                hir::TypeArgument::AssociatedType(ident, self.lower_type(ty))
            }
        }
    }

    fn lower_conformances(&mut self, node: ast::Conformances) -> hir::Conformances {
        hir::Conformances {
            bounds: node
                .bounds
                .into_iter()
                .map(|node| self.lower_path_node(node))
                .collect(),
            span: node.span,
        }
    }

    fn lower_generic_bounds(&mut self, node: ast::GenericBounds) -> hir::GenericBounds {
        node.into_iter()
            .map(|n| self.lower_generic_bound(n))
            .collect()
    }

    fn lower_generic_bound(&mut self, node: ast::GenericBound) -> hir::GenericBound {
        hir::GenericBound {
            path: self.lower_path_node(node.path),
        }
    }

    fn lower_generic_where_clause(
        &mut self,
        node: ast::GenericWhereClause,
    ) -> hir::GenericWhereClause {
        hir::GenericWhereClause {
            requirements: node
                .requirements
                .into_iter()
                .map(|node| self.lower_generic_requirement(node))
                .collect(),
            span: node.span,
        }
    }

    fn lower_generic_requirement(
        &mut self,
        node: ast::GenericRequirement,
    ) -> hir::GenericRequirement {
        match node {
            ast::GenericRequirement::SameTypeRequirement(constraint) => {
                hir::GenericRequirement::SameTypeRequirement(hir::RequiredTypeConstraint {
                    bounded_type: self.lower_type(constraint.bounded_type),
                    bound: self.lower_type(constraint.bound),
                    span: constraint.span,
                })
            }
            ast::GenericRequirement::ConformanceRequirement(constraint) => {
                hir::GenericRequirement::ConformanceRequirement(hir::ConformanceConstraint {
                    bounded_type: self.lower_type(constraint.bounded_type),
                    bounds: self.lower_generic_bounds(constraint.bounds),
                    span: constraint.span,
                })
            }
        }
    }
}

impl Actor<'_, '_> {
    fn lower_type(&mut self, node: Box<ast::Type>) -> Box<hir::Type> {
        let kind = match node.kind {
            ast::TypeKind::Nominal(path) => hir::TypeKind::Nominal(self.lower_path(node.id, path)),
            ast::TypeKind::Pointer(ty, mt) => hir::TypeKind::Pointer(self.lower_type(ty), mt),
            ast::TypeKind::Reference(ty) => hir::TypeKind::Reference(self.lower_type(ty)),
            ast::TypeKind::Parenthesis(ty) => return self.lower_type(ty),
            ast::TypeKind::Tuple(items, labels) => {
                let items = items.into_iter().map(|n| self.lower_type(n)).collect();
                hir::TypeKind::Tuple(items, labels)
            }
            ast::TypeKind::Array { size, element } => hir::TypeKind::Array {
                size: self.lower_anon_const(size),
                element: self.lower_type(element),
            },
            ast::TypeKind::Optional(element) => {
                let inner = self.lower_type(element);
                self.mk_foundation_type(
                    node.span,
                    hir::StdItem::Optional,
                    vec![hir::TypeArgument::Type(inner)],
                )
            }
            ast::TypeKind::Slice(element) => {
                let inner = self.lower_type(element);
                self.mk_foundation_type(
                    node.span,
                    hir::StdItem::Span,
                    vec![hir::TypeArgument::Type(inner)],
                )
            }
            ast::TypeKind::List(element) => {
                let inner = self.lower_type(element);
                self.mk_foundation_type(
                    node.span,
                    hir::StdItem::List,
                    vec![hir::TypeArgument::Type(inner)],
                )
            }
            ast::TypeKind::Dictionary { key, value } => {
                let key_ty = self.lower_type(key);
                let value_ty = self.lower_type(value);
                self.mk_foundation_type(
                    node.span,
                    hir::StdItem::Dictionary,
                    vec![
                        hir::TypeArgument::Type(key_ty),
                        hir::TypeArgument::Type(value_ty),
                    ],
                )
            }
            ast::TypeKind::Function { inputs, output } => hir::TypeKind::Function {
                inputs: inputs
                    .into_iter()
                    .map(|node| self.lower_type(node))
                    .collect(),
                output: self.lower_type(output),
            },
            ast::TypeKind::ImplicitSelf | ast::TypeKind::AnonymousParameter(..) => {
                let (resolution, identifier) = match node.kind {
                    ast::TypeKind::AnonymousParameter(id, name) => (
                        hir::Resolution::Definition(
                            self.definition_id(id),
                            hir::DefinitionKind::TypeParameter,
                        ),
                        name,
                    ),
                    _ => (
                        self.get_resolution(node.id),
                        Identifier::new(self.context.intern_symbol("Self"), node.span),
                    ),
                };
                let path = hir::Path {
                    span: node.span,
                    resolution: resolution.clone(),
                    segments: vec![hir::PathSegment {
                        id: self.next_index(),
                        identifier,
                        arguments: None,
                        span: node.span,
                        resolution,
                    }],
                };
                let path = hir::ResolvedPath::Resolved(path);
                hir::TypeKind::Nominal(path)
            }
            ast::TypeKind::BoxedExistential { interfaces } => hir::TypeKind::BoxedExistential {
                interfaces: interfaces
                    .into_iter()
                    .map(|n| self.lower_path_node(n))
                    .collect(),
            },
            ast::TypeKind::ImplTrait { interfaces } => hir::TypeKind::ImplTrait {
                interfaces: interfaces
                    .into_iter()
                    .map(|n| self.lower_path_node(n))
                    .collect(),
            },
            ast::TypeKind::QualifiedAccess {
                target,
                interface,
                member,
            } => hir::TypeKind::QualifiedAccess {
                target: self.lower_type(target),
                interface: self.lower_type(interface),
                member,
            },
            ast::TypeKind::Never => hir::TypeKind::Never,
            ast::TypeKind::Infer | ast::TypeKind::InferedClosureParameter => hir::TypeKind::Infer,
        };

        Box::new(hir::Type {
            id: self.next_index(),
            span: node.span,
            kind,
        })
    }

    fn mk_foundation_type(
        &mut self,
        span: Span,
        kind: StdItem,
        arguments: Vec<hir::TypeArgument>,
    ) -> hir::TypeKind {
        let name = kind.name_str().expect("foundation type must have a name");

        let path = hir::Path {
            span,
            resolution: Resolution::StdItem(kind),
            segments: vec![hir::PathSegment {
                id: self.next_index(),
                identifier: Identifier::new(self.context.intern_symbol(name), span),
                arguments: Some(hir::TypeArguments { span, arguments }),
                span,
                resolution: Resolution::StdItem(kind),
            }],
        };

        let path = hir::ResolvedPath::Resolved(path);
        hir::TypeKind::Nominal(path)
    }
}

impl Actor<'_, '_> {
    fn lower_pattern(&mut self, node: ast::Pattern) -> hir::Pattern {
        let id = self.next_index();
        let kind = match node.kind {
            ast::PatternKind::Wildcard => hir::PatternKind::Wildcard,
            ast::PatternKind::Rest => hir::PatternKind::Rest,
            ast::PatternKind::Identifier(ident) => {
                self.node_mapping.insert(node.id, id);
                hir::PatternKind::Binding { name: ident }
            }
            ast::PatternKind::Tuple(items, span) => hir::PatternKind::Tuple(
                items
                    .into_iter()
                    .map(|node| self.lower_pattern(node))
                    .collect(),
                span,
            ),

            ast::PatternKind::Member(constructor_path) => {
                hir::PatternKind::Member(self.lower_constructor_path(node.id, constructor_path))
            }
            ast::PatternKind::PathTuple {
                path,
                fields,
                field_span,
            } => hir::PatternKind::PathTuple {
                path: self.lower_constructor_path(node.id, path),
                fields: fields
                    .into_iter()
                    .map(|field| self.lower_pattern(field))
                    .collect(),
                field_span,
            },
            ast::PatternKind::PathNamed {
                path,
                fields,
                rest,
                field_span,
            } => hir::PatternKind::PathNamed {
                path: self.lower_constructor_path(node.id, path),
                fields: fields
                    .into_iter()
                    .map(|field| hir::NamedPatternField {
                        name: field.name,
                        pattern: self.lower_pattern(field.pattern),
                    })
                    .collect(),
                rest,
                field_span,
            },
            ast::PatternKind::Or(items, span) => hir::PatternKind::Or(
                items
                    .into_iter()
                    .map(|node| self.lower_pattern(node))
                    .collect(),
                span,
            ),
            ast::PatternKind::At { binding, pattern } => hir::PatternKind::At {
                binding: Box::new(self.lower_pattern(*binding)),
                pattern: Box::new(self.lower_pattern(*pattern)),
            },
            ast::PatternKind::TypeTest { target, binding } => hir::PatternKind::TypeTest {
                target: self.lower_type(target),
                binding: binding.map(|p| Box::new(self.lower_pattern(*p))),
            },
            ast::PatternKind::Range { start, end, inclusive } => hir::PatternKind::Range {
                start: self.lower_expression(start),
                end: self.lower_expression(end),
                inclusive,
            },
            ast::PatternKind::Literal(expr) => {
                let value = *expr.value;
                let (kind, negative) = match value.kind {
                    ast::ExpressionKind::Unary(ast::UnaryOperator::Negate, operand) => {
                        (operand.kind, true)
                    }
                    kind => (kind, false),
                };
                let mut literal = match kind {
                    ast::ExpressionKind::Literal(lit)
                        if !negative
                            || matches!(
                                lit,
                                ast::Literal::Integer { .. } | ast::Literal::Float { .. }
                            ) =>
                    {
                        match convert_ast_literal(self.context, lit) {
                            Ok(lit) => lit,
                            Err(err) => {
                                self.context.dcx.emit_error(err.into(), Some(value.span));
                                hir::Literal::Nil
                            }
                        }
                    }
                    _ => {
                        self.context.dcx.emit_error(
                            "pattern literals must be a literal value".into(),
                            Some(value.span),
                        );
                        hir::Literal::Nil
                    }
                };
                if negative {
                    negate_literal(&mut literal);
                }
                hir::PatternKind::Literal { value: literal }
            }
        };

        hir::Pattern {
            id,
            span: node.span,
            kind,
        }
    }
}

impl Actor<'_, '_> {
    fn lower_block(&mut self, node: ast::Block) -> hir::Block {
        let mut statements = node.statements;
        let tail_expr = match statements.pop() {
            Some(ast::Statement {
                kind: ast::StatementKind::Expression(expr),
                ..
            }) => Some(expr),
            Some(stmt) => {
                statements.push(stmt);
                None
            }
            None => None,
        };

        let id = self.next_index();
        let mut lowered = Vec::with_capacity(statements.len());
        for statement in statements {
            self.lower_statement(statement, &mut lowered);
        }
        hir::Block {
            id,
            statements: lowered,
            tail: tail_expr.map(|expr| self.lower_expression(expr)),
            span: node.span,
        }
    }

    fn lower_statement(&mut self, node: ast::Statement, statements: &mut Vec<hir::Statement>) {
        let kind = match node.kind {
            ast::StatementKind::Declaration(node) => {
                hir::StatementKind::Declaration(self.lower_function_declaration(node))
            }
            ast::StatementKind::Expression(node) => {
                hir::StatementKind::Expression(self.lower_expression(node))
            }
            ast::StatementKind::Variable(local) => {
                hir::StatementKind::Variable(self.lower_local(local))
            }
            ast::StatementKind::Using(local) => {
                let local = self.lower_local(local);
                let hir::PatternKind::Binding { name } = local.pattern.kind else {
                    unreachable!("using requires a named binding")
                };
                let binding = local.pattern.id;
                statements.push(self.mk_statement(hir::StatementKind::Variable(local), node.span));
                self.lower_using_cleanup(name, binding)
            }
            ast::StatementKind::AsyncVariable(local) => {
                hir::StatementKind::Variable(self.lower_async_local(local, node.span))
            }
            ast::StatementKind::Loop { label, block } => hir::StatementKind::Loop {
                label,
                block: self.lower_block(block),
            },
            ast::StatementKind::While {
                label,
                condition,
                block,
            } => {
                /*
                    --- ast ---
                    while <condition> { ... }

                    --- hir ---
                    loop {
                        if <condition> {...} else { break }
                    }
                */
                let condition = self.lower_expression(condition);
                let then_block = self.lower_block(block);
                let break_expr = self.mk_expression(
                    hir::ExpressionKind::Break {
                        label: None,
                        value: None,
                    },
                    node.span,
                );
                let break_statement =
                    self.mk_statement(hir::StatementKind::Expression(break_expr), node.span);
                let else_block = self.mk_block(vec![break_statement], node.span);
                let if_node = hir::IfExpression {
                    condition,
                    then_block: self
                        .mk_expression(hir::ExpressionKind::Block(then_block), node.span),
                    else_block: Some(
                        self.mk_expression(hir::ExpressionKind::Block(else_block), node.span),
                    ),
                };
                let core_expression =
                    self.mk_expression(hir::ExpressionKind::If(if_node), node.span);
                let core_statement =
                    self.mk_statement(hir::StatementKind::Expression(core_expression), node.span);
                let block = self.mk_block(vec![core_statement], node.span);
                hir::StatementKind::Loop { label, block }
            }
            ast::StatementKind::For(for_stmt) => self.lower_for_statement(for_stmt, node.span),
            ast::StatementKind::Defer(kind, node) => {
                hir::StatementKind::Defer(kind, self.lower_block(node))
            }
            ast::StatementKind::Guard {
                condition,
                else_block,
            } => hir::StatementKind::Guard {
                condition: self.lower_expression(condition),
                else_block: self.lower_block(else_block),
            },
            ast::StatementKind::ComptimeFor {
                pattern,
                target_type,
                body,
            } => hir::StatementKind::ComptimeFor {
                pattern: self.lower_pattern(pattern),
                target_type: self.lower_type(target_type),
                body: self.lower_block(body),
            },
            ast::StatementKind::ComptimeIf {
                condition,
                then_block,
                else_block,
            } => hir::StatementKind::ComptimeIf {
                condition: self.lower_expression(condition),
                then_block: self.lower_block(then_block),
                else_block: else_block.map(|b| self.lower_block(b)),
            },
        };
        statements.push(self.mk_statement(kind, node.span));
    }

    /// Register cleanup in the binding's lexical scope, after its initializer completes.
    /// The resolved binding and qualified call survive local shadowing and inherent methods.
    fn lower_using_cleanup(
        &mut self,
        name: Identifier,
        binding: hir::NodeID,
    ) -> hir::StatementKind {
        let span = name.span;
        let path = self.mk_single_segment_resolved_path(name, Resolution::LocalVariable(binding));
        let receiver = self.mk_expression(hir::ExpressionKind::Path(path), span);
        let close = self.mk_expression(
            hir::ExpressionKind::MethodCall {
                interface: Some(StdItem::Closeable),
                receiver,
                name: Identifier::new(self.context.intern_symbol("close"), span),
                arguments: Vec::new(),
            },
            span,
        );
        let discard = hir::Local {
            id: self.next_index(),
            mutability: hir::Mutability::Mutable,
            pattern: hir::Pattern {
                id: self.next_index(),
                kind: hir::PatternKind::Wildcard,
                span,
            },
            ty: None,
            initializer: Some(close),
            is_async: false,
        };
        let statement = self.mk_statement(hir::StatementKind::Variable(discard), span);
        hir::StatementKind::Defer(hir::DeferKind::Always, self.mk_block(vec![statement], span))
    }
}

impl Actor<'_, '_> {
    /// Keep language operations qualified until requirements are available.
    /// In particular, compiling std must not use ordinary method lookup for loops.
    fn lower_language_method_call(
        &mut self,
        item: StdItem,
        interface_name: &str,
        method_name: &str,
        receiver: Box<hir::Expression>,
        span: Span,
    ) -> Box<hir::Expression> {
        let base = hir::PathSegment {
            id: self.next_index(),
            identifier: Identifier::new(self.context.intern_symbol(interface_name), span),
            arguments: None,
            span,
            resolution: Resolution::StdItem(item),
        };
        let interface = hir::Type {
            id: self.next_index(),
            span,
            kind: hir::TypeKind::Nominal(hir::ResolvedPath::Resolved(hir::Path {
                span,
                resolution: Resolution::StdItem(item),
                segments: vec![base],
            })),
        };
        let method = hir::PathSegment {
            id: self.next_index(),
            identifier: Identifier::new(self.context.intern_symbol(method_name), span),
            arguments: None,
            span,
            resolution: Resolution::Error,
        };
        let path = hir::ResolvedPath::Relative(Box::new(interface), method);
        let callee = self.mk_expression(hir::ExpressionKind::Path(path), span);
        self.mk_expression(
            hir::ExpressionKind::Call {
                callee,
                arguments: vec![hir::ExpressionArgument {
                    label: None,
                    expression: receiver,
                    span,
                }],
            },
            span,
        )
    }

    fn lower_for_statement(&mut self, node: ast::ForStatement, span: Span) -> hir::StatementKind {
        /*
        Desugars:
            for pattern in collection { body }
        to:
            {
                var __for_iter = collection.iter();
                loop {
                    var element = __for_iter.next()
                    match element {
                        case Optional.some(pattern) => { body }
                        case Optional.none => break
                    }
                }
            }
        */
        let (iterable_std_item, iterable_interface_name, make_iterator_name) = if node.is_await {
            (StdItem::AsyncIterable, "AsyncIterable", "iter")
        } else {
            (StdItem::Iterable, "Iterable", "iter")
        };
        let iterator_std_item = if node.is_await {
            StdItem::AsyncIterator
        } else {
            StdItem::Iterator
        };
        let iterator_interface_name = if node.is_await {
            "AsyncIterator"
        } else {
            "Iterator"
        };

        // 1. Lower the iterator expression. As `Self` of the call below, a literal
        // would stay open for a representation that no context here can choose, and
        // the loop body would be checked without knowing its element type.
        let iterates_literal = matches!(node.iterator.kind, ast::ExpressionKind::Array(_));
        let collection = self.lower_expression(node.iterator);
        let mut outer_statements = vec![];
        let collection = if iterates_literal {
            let values_ident = Identifier::new(self.context.intern_symbol("$for_values"), span);
            let values_pattern_id = self.next_index();
            let values_local = hir::Local {
                id: self.next_index(),
                mutability: hir::Mutability::Immutable,
                pattern: hir::Pattern {
                    id: values_pattern_id,
                    span,
                    kind: hir::PatternKind::Binding { name: values_ident },
                },
                ty: None,
                initializer: Some(collection),
                is_async: false,
            };
            outer_statements
                .push(self.mk_statement(hir::StatementKind::Variable(values_local), span));
            let values_path = self.mk_single_segment_resolved_path(
                values_ident,
                Resolution::LocalVariable(values_pattern_id),
            );
            self.mk_expression(hir::ExpressionKind::Path(values_path), span)
        } else {
            collection
        };

        // 2. Create local binding: var __for_iter = collection.iter()
        let iter_ident = Identifier::new(self.context.intern_symbol("$for_iter"), span);
        let iter_pattern_id = self.next_index();
        let iter_pattern = hir::Pattern {
            id: iter_pattern_id,
            span,
            kind: hir::PatternKind::Binding { name: iter_ident },
        };

        let make_iterator_call = self.lower_language_method_call(
            iterable_std_item,
            iterable_interface_name,
            make_iterator_name,
            collection,
            span,
        );
        self.context
            .register_for_loop_iter_call(make_iterator_call.id, node.is_await);

        let iter_local = hir::Local {
            id: self.next_index(),
            mutability: hir::Mutability::Mutable,
            pattern: iter_pattern,
            ty: None,
            initializer: Some(make_iterator_call),
            is_async: false,
        };

        // 3. Create __for_iter.next() call
        let iter_ref_path = self.mk_single_segment_resolved_path(
            iter_ident,
            Resolution::LocalVariable(iter_pattern_id),
        );
        let iter_ref_expr = self.mk_expression(hir::ExpressionKind::Path(iter_ref_path), span);

        let next_call = self.lower_language_method_call(
            iterator_std_item,
            iterator_interface_name,
            "next",
            iter_ref_expr,
            span,
        );

        // var element = __for_iter.next();
        let element_ident = Identifier::new(self.context.intern_symbol("$element"), span);
        let element_pattern_id = self.next_index();
        let element_pattern = hir::Pattern {
            id: element_pattern_id,
            span,
            kind: hir::PatternKind::Binding {
                name: element_ident,
            },
        };

        let element_local = hir::Local {
            id: self.next_index(),
            mutability: hir::Mutability::Mutable,
            pattern: element_pattern,
            ty: None,
            initializer: Some(if node.is_await {
                self.mk_expression(hir::ExpressionKind::Await(next_call), span)
            } else {
                next_call
            }),
            is_async: false,
        };

        // 5. Lower the user's pattern from the for loop
        let user_pattern = self.lower_pattern(node.pattern);

        // 6. Create Optional.some(user_pattern)
        let some_path = self.mk_optional_variant_path("some", span);
        let some_pattern = hir::Pattern {
            id: self.next_index(),
            span,
            kind: hir::PatternKind::PathTuple {
                path: hir::ConstructorPath::Qualified { path: some_path },
                fields: vec![user_pattern],
                field_span: span,
            },
        };

        // 7. Create the loop body (with optional where clause)
        let loop_body_block = self.lower_block(node.block);
        let body_expr = if let Some(clause) = node.clause {
            // Add: if !(condition) { continue }
            let condition = self.lower_expression(clause);
            let negated = self.mk_expression(
                hir::ExpressionKind::Unary(hir::UnaryOperator::LogicalNot, condition),
                span,
            );
            let continue_expr =
                self.mk_expression(hir::ExpressionKind::Continue { label: None }, span);
            let continue_stmt =
                self.mk_statement(hir::StatementKind::Expression(continue_expr), span);
            let continue_block = self.mk_block(vec![continue_stmt], span);
            let guard_if = hir::IfExpression {
                condition: negated,
                then_block: self.mk_expression(hir::ExpressionKind::Block(continue_block), span),
                else_block: None,
            };
            let guard_expr = self.mk_expression(hir::ExpressionKind::If(guard_if), span);
            let guard_stmt = self.mk_statement(hir::StatementKind::Expression(guard_expr), span);

            // Prepend guard to body statements
            let mut stmts = vec![guard_stmt];
            stmts.extend(loop_body_block.statements);
            let combined_block = hir::Block {
                id: self.next_index(),
                statements: stmts,
                tail: loop_body_block.tail,
                span: loop_body_block.span,
            };
            self.mk_expression(hir::ExpressionKind::Block(combined_block), span)
        } else {
            self.mk_expression(hir::ExpressionKind::Block(loop_body_block), span)
        };

        // Arm 1: case Optional.some(pattern) => { body }
        let some_arm = hir::MatchArm {
            pattern: some_pattern,
            body: body_expr,
            guard: None,
            span,
        };

        // 8. Create Optional.none pattern
        let none_path = self.mk_optional_variant_path("none", span);
        let none_pattern = hir::Pattern {
            id: self.next_index(),
            span,
            kind: hir::PatternKind::Member(hir::ConstructorPath::Qualified { path: none_path }),
        };

        // Arm 2: case Optional.none => break
        let break_expr = self.mk_expression(
            hir::ExpressionKind::Break {
                label: None,
                value: None,
            },
            span,
        );
        let break_stmt = self.mk_statement(hir::StatementKind::Expression(break_expr), span);
        let break_block = self.mk_block(vec![break_stmt], span);
        let none_arm = hir::MatchArm {
            pattern: none_pattern,
            body: self.mk_expression(hir::ExpressionKind::Block(break_block), span),
            guard: None,
            span,
        };

        // 9. Create match expression on 'element'
        let element_ref_path = self.mk_single_segment_resolved_path(
            element_ident,
            Resolution::LocalVariable(element_pattern_id),
        );
        let element_ref_expr =
            self.mk_expression(hir::ExpressionKind::Path(element_ref_path), span);

        let match_expr = hir::MatchExpression {
            source: hir::MatchSource::desugared(hir::MatchKind::ForLoop),
            value: element_ref_expr,
            arms: vec![some_arm, none_arm],
            kw_span: span,
        };

        let match_expr_node = self.mk_expression(hir::ExpressionKind::Match(match_expr), span);
        let match_stmt = self.mk_statement(hir::StatementKind::Expression(match_expr_node), span);
        let element_stmt = self.mk_statement(hir::StatementKind::Variable(element_local), span);

        // 10. Create loop block containing the element binding and match
        let loop_block = self.mk_block(vec![element_stmt, match_stmt], span);
        let loop_stmt_kind = hir::StatementKind::Loop {
            label: node.label,
            block: loop_block,
        };

        // 11. Create outer block: { var __for_iter = ...; defer { Iterator::close(__for_iter) }; loop { ... } }
        let iter_stmt = self.mk_statement(hir::StatementKind::Variable(iter_local), span);
        outer_statements.push(iter_stmt);
        {
            let close_iter_path = self.mk_single_segment_resolved_path(
                iter_ident,
                Resolution::LocalVariable(iter_pattern_id),
            );
            let close_iter_expr =
                self.mk_expression(hir::ExpressionKind::Path(close_iter_path), span);
            let close_method_name = if node.is_await {
                "close"
            } else {
                "closeIterator"
            };
            let close_call = self.lower_language_method_call(
                iterator_std_item,
                iterator_interface_name,
                close_method_name,
                close_iter_expr,
                span,
            );
            let close_stmt = self.mk_statement(hir::StatementKind::Expression(close_call), span);
            let defer_block = self.mk_block(vec![close_stmt], span);
            outer_statements.push(self.mk_statement(
                hir::StatementKind::Defer(hir::DeferKind::Always, defer_block),
                span,
            ));
        }
        let loop_stmt = self.mk_statement(loop_stmt_kind, span);
        outer_statements.push(loop_stmt);
        let outer_block = self.mk_block(outer_statements, span);

        hir::StatementKind::Expression(
            self.mk_expression(hir::ExpressionKind::Block(outer_block), span),
        )
    }
}
impl Actor<'_, '_> {
    fn index_expression(
        &mut self,
        target: Box<hir::Expression>,
        index: Vec<hir::ExpressionArgument>,
    ) -> hir::ExpressionKind {
        let nodes = hir::IndexCallNodes {
            call: self.next_index(),
            receiver: self.next_index(),
        };
        hir::ExpressionKind::Index {
            target,
            index,
            nodes,
        }
    }

    fn lower_expression(&mut self, node: Box<ast::Expression>) -> Box<hir::Expression> {
        if let ast::ExpressionKind::OptionalUnwrap(_) = &node.kind {
            if let Some(replacement) = &self.optional_unwrap_replacement {
                if replacement.target_id == node.id {
                    return replacement.expression.clone();
                }
            }
        }

        let kind = match node.kind {
            ast::ExpressionKind::Literal(lit) => self.lower_literal(lit, node.span),
            ast::ExpressionKind::Identifier(ident) => {
                let resolved_path = self.lower_identifier_expression_path(node.id, ident);
                hir::ExpressionKind::Path(resolved_path)
            }
            ast::ExpressionKind::InferredMember { name } => {
                hir::ExpressionKind::InferredMember { name }
            }
            ast::ExpressionKind::Member { target, name, .. } => {
                match self
                    .resolutions
                    .expression_resolutions
                    .get(&node.id)
                    .cloned()
                {
                    Some(ExpressionResolutionState::Resolved(_)) => {
                        let Some(path) = self.try_lower_resolved_member_chain_as_path(
                            node.id, &target, name, node.span,
                        ) else {
                            unreachable!("resolved member access must be a compactable path");
                        };
                        hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path))
                    }
                    Some(ExpressionResolutionState::DeferredAssociatedType) => {
                        let path = self.lower_deferred_associated_type_member_chain(target, name);
                        hir::ExpressionKind::Path(path)
                    }
                    Some(ExpressionResolutionState::DeferredAssociatedValue) | None => {
                        hir::ExpressionKind::Member {
                            target: self.lower_expression(target),
                            name,
                        }
                    }
                }
            }
            ast::ExpressionKind::Specialize {
                target,
                type_arguments,
                index,
            } => {
                if let Some(diagnostics) = self
                    .resolutions
                    .member_bracket_diagnostics
                    .get(&node.id)
                    .cloned()
                {
                    let member = self.lower_expression(target);
                    let previous = self.lowering_deferred_bracket;
                    self.lowering_deferred_bracket = true;
                    let type_arguments = self.lower_type_arguments(type_arguments);
                    let indexed = index.map(|index| {
                        let index = self.lower_expression_arguments(index);
                        let kind = self.index_expression(member.clone(), index);
                        Box::new(hir::Expression {
                            id: self.next_index(),
                            kind,
                            span: node.span,
                        })
                    });
                    self.lowering_deferred_bracket = previous;
                    hir::ExpressionKind::MemberBrackets {
                        member,
                        type_arguments,
                        indexed,
                        diagnostics,
                    }
                } else if matches!(
                    self.resolutions.expression_resolutions.get(&node.id),
                    Some(ExpressionResolutionState::DeferredAssociatedValue)
                ) {
                    if let Some(index) = index {
                        let target = self.lower_expression(target);
                        let index = self.lower_expression_arguments(index);
                        self.index_expression(target, index)
                    } else {
                        hir::ExpressionKind::Malformed
                    }
                } else {
                    // Convert Specialize into a path with type arguments on the final segment
                    match self.lower_specialize_as_path(&target, type_arguments, node.span) {
                        Some(path) => hir::ExpressionKind::Path(path),
                        None => {
                            self.context.dcx.emit_error(
                                "type arguments can only be applied to path-like expressions"
                                    .into(),
                                Some(node.span),
                            );
                            hir::ExpressionKind::Malformed
                        }
                    }
                }
            }
            ast::ExpressionKind::Index { target, index } => {
                let target = self.lower_expression(target);
                let index = self.lower_expression_arguments(index);
                self.index_expression(target, index)
            }
            ast::ExpressionKind::Spread(source) => {
                hir::ExpressionKind::Spread(self.lower_expression(source))
            }
            ast::ExpressionKind::Array(nodes) => hir::ExpressionKind::Array(
                nodes
                    .into_iter()
                    .map(|expr| self.lower_expression(expr))
                    .collect(),
            ),
            ast::ExpressionKind::Repeat { value, count } => hir::ExpressionKind::Repeat {
                value: self.lower_expression(value),
                count: self.lower_anon_const(count),
            },
            ast::ExpressionKind::Tuple(nodes, labels) => hir::ExpressionKind::Tuple(
                nodes
                    .into_iter()
                    .map(|expr| self.lower_expression(expr))
                    .collect(),
                labels,
            ),
            ast::ExpressionKind::If(node) => {
                hir::ExpressionKind::If(self.lower_if_expression(node))
            }
            ast::ExpressionKind::Match(node) => {
                hir::ExpressionKind::Match(self.lower_match_expression(node))
            }
            ast::ExpressionKind::Select(node) => {
                hir::ExpressionKind::Select(self.lower_select_expression(node))
            }
            ast::ExpressionKind::Loop { label, block } => hir::ExpressionKind::Loop {
                label,
                block: self.lower_block(block),
            },
            ast::ExpressionKind::Return { value } => hir::ExpressionKind::Return {
                value: value.map(|expr| self.lower_expression(expr)),
            },
            ast::ExpressionKind::Break { label, value } => {
                if let Some(&resolved_label) =
                    self.resolutions.break_label_resolutions.get(&node.id)
                {
                    hir::ExpressionKind::Break {
                        label: Some(resolved_label),
                        value: None,
                    }
                } else {
                    hir::ExpressionKind::Break {
                        label: if value.is_some() { None } else { label },
                        value: value.map(|expr| self.lower_expression(expr)),
                    }
                }
            }
            ast::ExpressionKind::Continue { label } => hir::ExpressionKind::Continue { label },
            ast::ExpressionKind::Call(node, args) => self.lower_call(node, args),
            ast::ExpressionKind::Reference(node) => {
                hir::ExpressionKind::Reference(self.lower_expression(node))
            }
            ast::ExpressionKind::Dereference(node) => {
                hir::ExpressionKind::Dereference(self.lower_expression(node))
            }
            ast::ExpressionKind::Binary(op, lhs, rhs) => hir::ExpressionKind::Binary(
                op,
                self.lower_expression(lhs),
                self.lower_expression(rhs),
            ),
            ast::ExpressionKind::Unary(op, rhs) => {
                // Fold only one minus directly applied to a numeric literal.
                // Nested negations remain operations, including overflow checks.
                let mut rhs = self.lower_expression(rhs);
                if op == hir::UnaryOperator::Negate
                    && let hir::ExpressionKind::Literal(ref mut literal) = rhs.kind
                    && negate_literal(literal)
                {
                    hir::ExpressionKind::Literal(literal.clone())
                } else {
                    hir::ExpressionKind::Unary(op, rhs)
                }
            }
            ast::ExpressionKind::TupleAccess(lhs, index) => hir::ExpressionKind::TupleAccess(
                self.lower_expression(lhs),
                self.lower_anon_const(index),
            ),
            ast::ExpressionKind::AssignOp(op, lhs, rhs) => hir::ExpressionKind::AssignOp(
                op,
                self.lower_expression(lhs),
                self.lower_expression(rhs),
            ),
            ast::ExpressionKind::Assign(lhs, rhs) => {
                hir::ExpressionKind::Assign(self.lower_assignee(lhs), self.lower_expression(rhs))
            }
            ast::ExpressionKind::AssignOptional(lhs, rhs) => hir::ExpressionKind::AssignOptional(
                self.lower_expression(lhs),
                self.lower_expression(rhs),
            ),
            ast::ExpressionKind::Parenthesis(node) => {
                return self.lower_expression(node);
            }
            ast::ExpressionKind::CastAs(node, ty) => {
                hir::ExpressionKind::CastAs(self.lower_expression(node), self.lower_type(ty))
            }
            ast::ExpressionKind::CastAsTry(node, ty) => {
                hir::ExpressionKind::CastAsTry(self.lower_expression(node), self.lower_type(ty))
            }
            ast::ExpressionKind::TypeIs(node, ty) => {
                hir::ExpressionKind::TypeIs(self.lower_expression(node), self.lower_type(ty))
            }
            ast::ExpressionKind::Pipe(lhs, rhs) => {
                return self.lower_pipe_expression(lhs, rhs, node.span);
            }
            ast::ExpressionKind::PatternBinding(node) | ast::ExpressionKind::PatternIs(node) => {
                let source = hir::MatchSource::user(hir::MatchKind::Match);
                hir::ExpressionKind::PatternBinding(
                    self.lower_pattern_binding_condition(node, source),
                )
            }
            ast::ExpressionKind::Ternary(condition, lhs, rhs) => {
                // `a ? b : c` -> if a { b } else { c }
                let condition = self.lower_expression(condition);
                let lhs_span = lhs.span;
                let rhs_span = rhs.span;

                // Expressions
                let lhs = self.lower_expression(lhs);
                let rhs = self.lower_expression(rhs);

                // Statements
                let lhs = self.mk_statement(hir::StatementKind::Expression(lhs), lhs_span);
                let rhs = self.mk_statement(hir::StatementKind::Expression(rhs), rhs_span);

                // Block
                let lhs = self.mk_block(vec![lhs], lhs_span);
                let rhs = self.mk_block(vec![rhs], rhs_span);

                // Block-Expressions
                let lhs = self.mk_expression(hir::ExpressionKind::Block(lhs), lhs_span);
                let rhs = self.mk_expression(hir::ExpressionKind::Block(rhs), rhs_span);

                let if_node = hir::IfExpression {
                    condition,
                    then_block: lhs,
                    else_block: Some(rhs),
                };

                hir::ExpressionKind::If(if_node)
            }
            ast::ExpressionKind::Block(block) => {
                hir::ExpressionKind::Block(self.lower_block(block))
            }
            ast::ExpressionKind::UnsafeBlock(block) => {
                hir::ExpressionKind::UnsafeBlock(self.lower_block(block))
            }
            ast::ExpressionKind::Range(lhs, rhs, inclusive) => {
                // `a..b`, `a..=b`, `a..`, `..b`, `..=b`, `..`
                let (foundational, bounds) = match (lhs, rhs, inclusive) {
                    (Some(lhs), Some(rhs), false) => (StdItem::Range, vec![lhs, rhs]),
                    (Some(lhs), Some(rhs), true) => (StdItem::ClosedRange, vec![lhs, rhs]),
                    (Some(lhs), None, false) => (StdItem::RangeFrom, vec![lhs]),
                    (None, Some(rhs), false) => (StdItem::RangeTo, vec![rhs]),
                    (None, Some(rhs), true) => (StdItem::RangeToInclusive, vec![rhs]),
                    (None, None, false) => (StdItem::RangeFull, vec![]),
                    _ => {
                        self.context.dcx().emit_error(
                            "inclusive range requires an upper bound".into(),
                            Some(node.span),
                        );
                        return self.mk_expression(hir::ExpressionKind::Malformed, node.span);
                    }
                };

                let factory = self.mk_foundation_factory(foundational, node.span);

                let arguments = bounds
                    .into_iter()
                    .map(|bound| {
                        let expression = self.lower_expression(bound);
                        hir::ExpressionArgument {
                            label: None,
                            span: expression.span,
                            expression,
                        }
                    })
                    .collect();

                let call = self.mk_expression(
                    hir::ExpressionKind::Call {
                        callee: factory,
                        arguments,
                    },
                    node.span,
                );
                return call;
            }
            ast::ExpressionKind::DictionaryLiteral(map_pairs) => {
                // Dictionary literals call the ordinary `Dictionary::new`
                // factory explicitly; type paths have no implicit value meaning.
                let constructor = self.mk_foundation_factory(hir::StdItem::Dictionary, node.span);
                let initializer = self.mk_expression(
                    hir::ExpressionKind::Call {
                        callee: constructor,
                        arguments: vec![],
                    },
                    node.span,
                );

                // Bind the dictionary to a mutable local so we can perform insertions.
                let dictionary_ident =
                    Identifier::new(self.context.intern_symbol("__dictionary"), node.span);
                let pattern = hir::Pattern {
                    id: self.next_index(),
                    span: node.span,
                    kind: hir::PatternKind::Binding {
                        name: dictionary_ident,
                    },
                };

                // Store the pattern's ID - this is what THIR uses to register the local binding
                let pattern_id = pattern.id;

                // Keep temporary dictionary typed as `Dictionary[_, _]` so method calls
                // on the local can constrain key/value inference from inserted pairs.
                let inferred_key_ty = self.mk_ty(hir::TypeKind::Infer, node.span);
                let inferred_value_ty = self.mk_ty(hir::TypeKind::Infer, node.span);
                let dictionary_local_ty_kind = self.mk_foundation_type(
                    node.span,
                    hir::StdItem::Dictionary,
                    vec![
                        hir::TypeArgument::Type(inferred_key_ty),
                        hir::TypeArgument::Type(inferred_value_ty),
                    ],
                );
                let dictionary_local_ty = self.mk_ty(dictionary_local_ty_kind, node.span);

                let local = hir::Local {
                    id: self.next_index(),
                    mutability: hir::Mutability::Mutable,
                    pattern,
                    ty: Some(dictionary_local_ty),
                    initializer: Some(initializer),
                    is_async: false,
                };

                // Use the pattern ID for local variable resolution (not the Local's ID)
                let local_id = pattern_id;

                let mut statements =
                    vec![self.mk_statement(hir::StatementKind::Variable(local), node.span)];

                let insert_ident = Identifier::new(self.context.intern_symbol("insert"), node.span);
                for pair in map_pairs {
                    let key = self.lower_expression(pair.key);
                    let value = self.lower_expression(pair.value);

                    let dictionary_path = self.mk_single_segment_resolved_path(
                        dictionary_ident,
                        Resolution::LocalVariable(local_id),
                    );
                    let target =
                        self.mk_expression(hir::ExpressionKind::Path(dictionary_path), node.span);
                    let key_label = hir::Label {
                        identifier: Identifier::new(self.context.intern_symbol("key"), node.span),
                        span: node.span,
                    };
                    let value_label = hir::Label {
                        identifier: Identifier::new(self.context.intern_symbol("value"), node.span),
                        span: node.span,
                    };
                    let arguments = vec![
                        hir::ExpressionArgument {
                            label: Some(key_label),
                            span: key.span,
                            expression: key,
                        },
                        hir::ExpressionArgument {
                            label: Some(value_label),
                            span: value.span,
                            expression: value,
                        },
                    ];

                    let call = self.mk_expression(
                        hir::ExpressionKind::MethodCall {
                            interface: None,
                            receiver: target,
                            name: insert_ident,
                            arguments,
                        },
                        node.span,
                    );
                    statements
                        .push(self.mk_statement(hir::StatementKind::Expression(call), node.span));
                }

                // The block expression evaluates to the populated dictionary.
                let dictionary_path = self.mk_single_segment_resolved_path(
                    dictionary_ident,
                    Resolution::LocalVariable(local_id),
                );
                let result =
                    self.mk_expression(hir::ExpressionKind::Path(dictionary_path), node.span);
                statements
                    .push(self.mk_statement(hir::StatementKind::Expression(result), node.span));

                let block = self.mk_block(statements, node.span);
                let block_expr = self.mk_expression(hir::ExpressionKind::Block(block), node.span);

                return block_expr;
            }
            ast::ExpressionKind::OptionalPatternBinding(node) => {
                // Lower `if let foo = bar`
                hir::ExpressionKind::PatternBinding(self.lower_optional_pattern_binding(node))
            }
            ast::ExpressionKind::OptionalDefault(lhs, rhs) => {
                // Lower `lhs ?? rhs` to:
                // match lhs {
                //    case .some(val) => val
                //    case .none => rhs
                // }
                let lhs = self.lower_expression(lhs);
                hir::ExpressionKind::Match(self.lower_optional_default(lhs, rhs, node.span))
            }
            ast::ExpressionKind::Propagate(expr) => {
                hir::ExpressionKind::Propagate(self.lower_expression(expr))
            }
            ast::ExpressionKind::Closure(closure) => {
                self.lower_closure_expression(closure, node.span)
            }
            ast::ExpressionKind::OptionalUnwrap(_) => {
                // `OptionalUnwrap` should only be encountered within `OptionalEvaluation`.
                // If we hit this directly, it's an error in the parser or lowerer logic unless
                // we implement "force unwrap" semantics here, but currently `?` is for chaining.
                self.context.dcx.emit_error(
                    "optional unwrap operator '?' cannot be used outside of an optional chain"
                        .into(),
                    Some(node.span),
                );
                hir::ExpressionKind::Malformed
            }
            ast::ExpressionKind::OptionalEvaluation(expr) => {
                // Lower `expr` which contains `OptionalUnwrap`s.
                // For a simple `target?.member`, `expr` is `Member(target=OptionalUnwrap(target), name)`.
                // We need to unwrap the `OptionalUnwrap` node and wrap the whole operation in a match.
                self.lower_optional_evaluation(expr, node.span)
            }
            ast::ExpressionKind::Wildcard => {
                self.context.dcx.emit_error(
                    "wildcard expressions are only valid as top-level pipe arguments".into(),
                    Some(node.span),
                );
                hir::ExpressionKind::Malformed
            }
            ast::ExpressionKind::StructLiteral(struct_literal) => {
                // Use the struct-literal expression node id, which is the key used by
                // resolver.resolve_path_with_source(...) for this path.
                let path = self.lower_constructor_path(node.id, struct_literal.path.clone());
                let fields = struct_literal
                    .fields
                    .iter()
                    .map(|f| hir::ExpressionField {
                        label: f.label,
                        expression: self.lower_expression(f.expression.clone()),
                        span: f.span,
                    })
                    .collect();
                let base = struct_literal.base.map(|base| self.lower_expression(base));
                hir::ExpressionKind::StructLiteral(hir::StructLiteral { path, fields, base })
            }
            ast::ExpressionKind::Embed { path, bytes } => {
                match self.context.read_embedded(node.span.file, &path, bytes) {
                    Ok(literal) => hir::ExpressionKind::Literal(literal),
                    Err(message) => {
                        self.context.dcx.emit_error(message, Some(node.span));
                        hir::ExpressionKind::Malformed
                    }
                }
            }
            ast::ExpressionKind::SourceLocation(location) => {
                if matches!(self.location_scope, LocationScope::DefaultArgument) {
                    self.location_scope =
                        LocationScope::Caller(std::array::from_fn(|_| self.next_index()));
                }
                match self.location_scope {
                    LocationScope::Caller(bindings) => {
                        let name = Identifier::new(
                            self.context.intern_symbol(location.parameter_name()),
                            node.span,
                        );
                        hir::ExpressionKind::Path(self.mk_single_segment_resolved_path(
                            name,
                            Resolution::LocalVariable(bindings[location as usize]),
                        ))
                    }
                    _ => hir::ExpressionKind::Literal(
                        self.context.source_location(location, node.span),
                    ),
                }
            }
            ast::ExpressionKind::CfgCheck(cfg_expr) => {
                // Evaluate the cfg expression at compile time
                let result = self.evaluate_cfg_expr(&cfg_expr);
                hir::ExpressionKind::Literal(hir::Literal::Bool(result))
            }
            ast::ExpressionKind::TypeName(ty) => {
                hir::ExpressionKind::TypeName(self.lower_type(ty))
            }
            ast::ExpressionKind::Await(expr) => {
                hir::ExpressionKind::Await(self.lower_expression(expr))
            }
            ast::ExpressionKind::Yield(expr) => {
                hir::ExpressionKind::Yield(self.lower_expression(expr))
            }
        };

        Box::new(hir::Expression {
            id: self.next_index(),
            kind,
            span: node.span,
        })
    }

    fn try_lower_resolved_member_chain_as_path(
        &mut self,
        member_expr_id: ast::NodeID,
        target: &ast::Expression,
        name: Identifier,
        span: Span,
    ) -> Option<hir::Path> {
        // Reuse path lowering so explicit arguments on intermediate segments
        // survive qualification, e.g. Interface[Arg]::method(receiver).
        let hir::ResolvedPath::Resolved(mut path) = self.try_expr_as_resolved_path(target)? else {
            return None;
        };
        let ExpressionResolutionState::Resolved(resolution) = self
            .resolutions
            .expression_resolutions
            .get(&member_expr_id)?
            .clone()
        else {
            return None;
        };
        let resolution = self.lower_resolution(resolution);
        path.segments.push(hir::PathSegment {
            id: self.next_index(),
            identifier: name,
            arguments: None,
            span: name.span,
            resolution: resolution.clone(),
        });
        path.resolution = resolution;
        path.span = span;
        Some(path)
    }

    fn lower_deferred_associated_type_member_chain(
        &mut self,
        target: Box<ast::Expression>,
        name: Identifier,
    ) -> hir::ResolvedPath {
        // Build a `ResolvedPath::Relative` chain for type-relative member access. These segments
        // are intentionally left unresolved; typechecking resolves them using the type head.
        let mut segs: Vec<Identifier> = vec![name];
        let mut base_expr = target;

        loop {
            let ast::ExpressionKind::Member {
                target: inner,
                name: seg_name,
                ..
            } = &base_expr.kind
            else {
                break;
            };

            let Some(ExpressionResolutionState::DeferredAssociatedType) = self
                .resolutions
                .expression_resolutions
                .get(&base_expr.id)
                .cloned()
            else {
                break;
            };

            segs.push(*seg_name);
            base_expr = inner.clone();
        }

        let base_hir = self.lower_expression(base_expr);
        let hir::ExpressionKind::Path(base_path) = &base_hir.kind else {
            unreachable!("deferred associated type access must have a path base");
        };

        let mut base_ty = self.mk_ty(hir::TypeKind::Nominal(base_path.clone()), base_hir.span);
        let mut span = base_hir.span;

        segs.reverse();
        let seg_count = segs.len();

        for (idx, ident) in segs.into_iter().enumerate() {
            let seg = hir::PathSegment {
                id: self.next_index(),
                identifier: ident,
                arguments: None,
                span: ident.span,
                resolution: Resolution::Error,
            };

            let path = hir::ResolvedPath::Relative(base_ty, seg);
            if idx == seg_count - 1 {
                return path;
            }

            span = span.to(ident.span);
            base_ty = self.mk_ty(hir::TypeKind::Nominal(path), span);
        }

        unreachable!()
    }

    /// Attempts to convert an AST expression to a resolved path suitable for attaching type arguments.
    /// Returns None if the expression cannot be converted to a path.
    fn try_expr_as_resolved_path(&mut self, expr: &ast::Expression) -> Option<hir::ResolvedPath> {
        match &expr.kind {
            ast::ExpressionKind::Identifier(ident) => {
                let resolved_path = self.lower_identifier_expression_path(expr.id, *ident);
                Some(resolved_path)
            }
            ast::ExpressionKind::Member { target, name, .. } => {
                // Check resolution state to determine how to handle
                match self
                    .resolutions
                    .expression_resolutions
                    .get(&expr.id)
                    .cloned()
                {
                    Some(ExpressionResolutionState::Resolved(_)) => {
                        let path = self.try_lower_resolved_member_chain_as_path(
                            expr.id, target, *name, expr.span,
                        )?;
                        Some(hir::ResolvedPath::Resolved(path))
                    }
                    Some(ExpressionResolutionState::DeferredAssociatedType) => {
                        let path =
                            self.lower_deferred_associated_type_member_chain(target.clone(), *name);
                        Some(path)
                    }
                    // DeferredAssociatedValue and None cannot be converted to paths for specialization
                    _ => None,
                }
            }
            ast::ExpressionKind::Specialize {
                target,
                type_arguments,
                ..
            } => {
                // Recursively handle nested Specialize - attach type arguments to the inner path
                let mut path = self.try_expr_as_resolved_path(target)?;
                // Attach these type arguments to the path
                match &mut path {
                    hir::ResolvedPath::Resolved(p) => {
                        if let Some(last) = p.segments.last_mut() {
                            last.arguments =
                                Some(self.lower_type_arguments(type_arguments.clone()));
                            last.span = last.span.to(type_arguments.span);
                            p.span = p.span.to(type_arguments.span);
                        }
                    }
                    hir::ResolvedPath::Relative(_, seg) => {
                        seg.arguments = Some(self.lower_type_arguments(type_arguments.clone()));
                        seg.span = seg.span.to(type_arguments.span);
                    }
                }
                Some(path)
            }
            _ => None,
        }
    }

    /// Converts an AST Specialize expression to a path with type arguments on the final segment.
    fn lower_specialize_as_path(
        &mut self,
        target: &ast::Expression,
        type_arguments: ast::TypeArguments,
        _span: Span,
    ) -> Option<hir::ResolvedPath> {
        // Try to build a path from the target expression
        let mut path = self.try_expr_as_resolved_path(target)?;

        // Attach type arguments to the last segment
        match &mut path {
            hir::ResolvedPath::Resolved(p) => {
                if let Some(last) = p.segments.last_mut() {
                    last.arguments = Some(self.lower_type_arguments(type_arguments.clone()));
                    last.span = last.span.to(type_arguments.span);
                    p.span = p.span.to(type_arguments.span);
                }
            }
            hir::ResolvedPath::Relative(_, seg) => {
                seg.arguments = Some(self.lower_type_arguments(type_arguments.clone()));
                seg.span = seg.span.to(type_arguments.span);
            }
        }

        Some(path)
    }

    fn lower_anon_const(&mut self, node: ast::AnonConst) -> hir::AnonConst {
        hir::AnonConst {
            value: self.lower_expression(node.value),
        }
    }

    fn lower_literal(&mut self, node: ast::Literal, span: Span) -> hir::ExpressionKind {
        let result = convert_ast_literal(self.context, node);

        match result {
            Ok(v) => return hir::ExpressionKind::Literal(v),
            Err(e) => {
                self.context.dcx.emit_error(e, Some(span));
                return hir::ExpressionKind::Malformed;
            }
        }
    }
    fn lower_if_expression(&mut self, node: ast::IfExpression) -> hir::IfExpression {
        hir::IfExpression {
            condition: self.lower_expression(node.condition),
            then_block: self.lower_expression(node.then_block),
            else_block: node.else_block.map(|expr| self.lower_expression(expr)),
        }
    }

    fn lower_match_expression(&mut self, node: ast::MatchExpression) -> hir::MatchExpression {
        hir::MatchExpression {
            source: hir::MatchSource::user(hir::MatchKind::Match),
            value: self.lower_expression(node.value),
            arms: node
                .arms
                .into_iter()
                .map(|arm| self.lower_match_arm(arm))
                .collect(),
            kw_span: node.kw_span,
        }
    }

    fn lower_match_arm(&mut self, node: ast::MatchArm) -> hir::MatchArm {
        hir::MatchArm {
            pattern: self.lower_pattern(node.pattern),
            body: self.lower_expression(node.body),
            guard: node.guard.map(|expr| self.lower_expression(expr)),
            span: node.span,
        }
    }

    fn lower_expression_arguments(
        &mut self,
        args: Vec<ast::ExpressionArgument>,
    ) -> Vec<hir::ExpressionArgument> {
        args.into_iter()
            .map(|arg| {
                let expression = self.lower_expression(arg.expression);
                if arg.interpolated {
                    self.context.mark_interpolation_argument(expression.id);
                }
                if arg.is_trailing_closure {
                    self.context.mark_trailing_closure_argument(expression.id);
                }
                hir::ExpressionArgument {
                    label: arg.label,
                    expression,
                    span: arg.span,
                }
            })
            .collect()
    }

    fn lower_closure_expression(
        &mut self,
        closure: ast::ClosureExpression,
        span: Span,
    ) -> hir::ExpressionKind {
        // Allocate a synthetic definition ID for this closure
        let def_id = self
            .context
            .allocate_synthetic_id(self.context.package_index());

        // Lower closure parameters
        let params: Vec<hir::ClosureParam> = closure
            .signature
            .prototype
            .inputs
            .into_iter()
            .map(|param| {
                let id = self.next_index();
                // Map the AST node ID to the HIR node ID for later resolution
                self.node_mapping.insert(param.id, id);

                // Create a simple binding pattern from the parameter name
                let pattern = hir::Pattern {
                    id,
                    span: param.span,
                    kind: if param.name.symbol.as_str() == "_" {
                        hir::PatternKind::Wildcard
                    } else {
                        hir::PatternKind::Binding { name: param.name }
                    },
                };

                hir::ClosureParam {
                    id,
                    pattern,
                    ty: Some(self.lower_type(param.annotated_type)),
                    span: param.span,
                }
            })
            .collect();

        // Lower return type if specified
        let return_ty = closure
            .signature
            .prototype
            .output
            .map(|ty| self.lower_type(ty));

        // Lower the closure body
        let body = self.lower_expression(closure.body);

        hir::ExpressionKind::Closure(hir::ClosureExpr {
            def_id,
            params,
            return_ty,
            is_async: closure.is_async,
            implicit_await: false,
            body,
            snapshot_captures: false,
            span,
        })
    }

    fn lower_pattern_binding_condition(
        &mut self,
        node: ast::PatternBindingCondition,
        source: hir::MatchSource,
    ) -> hir::PatternBindingCondition {
        hir::PatternBindingCondition {
            source,
            pattern: self.lower_pattern(node.pattern),
            expression: self.lower_expression(node.expression),
            span: node.span,
        }
    }

    fn lower_optional_pattern_binding(
        &mut self,
        node: ast::PatternBindingCondition,
    ) -> hir::PatternBindingCondition {
        // Transform `var x = opt` into `case Optional.some(x) = opt`
        let inner_pattern = self.lower_pattern(node.pattern);
        let some_span = inner_pattern.span;

        let pattern = hir::Pattern {
            id: self.next_index(),
            span: some_span,
            kind: hir::PatternKind::PathTuple {
                path: hir::ConstructorPath::Qualified {
                    path: self.mk_optional_variant_path("some", some_span),
                },
                fields: vec![inner_pattern],
                field_span: some_span,
            },
        };

        hir::PatternBindingCondition {
            source: hir::MatchSource::user(hir::MatchKind::OptionalBinding),
            pattern,
            expression: self.lower_expression(node.expression),
            span: node.span,
        }
    }

    fn lower_optional_default(
        &mut self,
        lhs: Box<hir::Expression>,
        rhs: Box<ast::Expression>,
        span: Span,
    ) -> hir::MatchExpression {
        // Lower `lhs ?? rhs` to:
        // match lhs {
        //    case Optional.some(__optional_val) => __optional_val
        //    case Optional.none => rhs
        // }

        let lhs_span = lhs.span;
        let rhs_lowered = self.lower_expression(rhs);
        let rhs_span = rhs_lowered.span;

        // Create binding for extracted value: __optional_val
        let val_ident = Identifier::new(self.context.intern_symbol("__optional_val"), lhs_span);
        let val_pattern_id = self.next_index();
        let val_binding_pattern = hir::Pattern {
            id: val_pattern_id,
            span: lhs_span,
            kind: hir::PatternKind::Binding { name: val_ident },
        };

        // Create Optional.some(__optional_val) pattern using qualified path
        let some_path = self.mk_optional_variant_path("some", lhs_span);
        let some_pattern = hir::Pattern {
            id: self.next_index(),
            span: lhs_span,
            kind: hir::PatternKind::PathTuple {
                path: hir::ConstructorPath::Qualified { path: some_path },
                fields: vec![val_binding_pattern],
                field_span: lhs_span,
            },
        };

        // Create expression that references the bound value
        let val_ref_path = self
            .mk_single_segment_resolved_path(val_ident, Resolution::LocalVariable(val_pattern_id));
        let val_ref_expr = self.mk_expression(hir::ExpressionKind::Path(val_ref_path), lhs_span);

        // Arm 1: case Optional.some(__optional_val) => __optional_val
        let some_arm = hir::MatchArm {
            pattern: some_pattern,
            body: val_ref_expr,
            guard: None,
            span: lhs_span,
        };

        // Create Optional.none pattern using qualified path
        let none_path = self.mk_optional_variant_path("none", rhs_span);
        let none_pattern = hir::Pattern {
            id: self.next_index(),
            span: rhs_span,
            kind: hir::PatternKind::Member(hir::ConstructorPath::Qualified { path: none_path }),
        };

        // Arm 2: case Optional.none => rhs
        let none_arm = hir::MatchArm {
            pattern: none_pattern,
            body: rhs_lowered,
            guard: None,
            span: rhs_span,
        };

        hir::MatchExpression {
            source: hir::MatchSource::desugared(hir::MatchKind::OptionalDefault),
            value: lhs,
            arms: vec![some_arm, none_arm],
            kw_span: span,
        }
    }

    /// Creates a resolved path for an Optional variant (e.g., `Optional.some` or `Optional.none`)
    /// using std-item resolution.
    fn mk_optional_variant_path(&mut self, variant_name: &str, span: Span) -> hir::ResolvedPath {
        let ctor_item = match variant_name {
            "some" => StdItem::OptionalSomeCtor,
            "none" => StdItem::OptionalNoneCtor,
            _ => {
                self.context.dcx().emit_error(
                    format!("unknown Optional variant '{}' in lowering", variant_name),
                    Some(span),
                );
                StdItem::OptionalNoneCtor
            }
        };
        let optional_ident = Identifier::new(self.context.intern_symbol("Optional"), span);
        let variant_ident = Identifier::new(self.context.intern_symbol(variant_name), span);
        let base_segment = hir::PathSegment {
            id: self.next_index(),
            identifier: optional_ident,
            arguments: None,
            span,
            resolution: hir::Resolution::StdItem(StdItem::Optional),
        };
        let variant_segment = hir::PathSegment {
            id: self.next_index(),
            identifier: variant_ident,
            arguments: None,
            span,
            resolution: hir::Resolution::StdItem(ctor_item),
        };
        hir::ResolvedPath::Resolved(hir::Path {
            span,
            resolution: hir::Resolution::StdItem(ctor_item),
            segments: vec![base_segment, variant_segment],
        })
    }

    fn lower_optional_evaluation(
        &mut self,
        expr: Box<ast::Expression>,
        _span: Span,
    ) -> hir::ExpressionKind {
        let (expr, _) = self.lower_optional_expr(&expr, None, true);
        let hir::Expression { kind, .. } = *expr;
        kind
    }

    fn lower_call(
        &mut self,
        node: Box<ast::Expression>,
        args: Vec<ast::ExpressionArgument>,
    ) -> hir::ExpressionKind {
        let callee_state = self
            .resolutions
            .expression_resolutions
            .get(&node.id)
            .cloned();
        let callee = self.lower_expression(node);
        let args = self.lower_expression_arguments(args);

        let treat_as_method = matches!(
            callee_state,
            None | Some(ExpressionResolutionState::DeferredAssociatedValue)
        ) && matches!(callee.kind, hir::ExpressionKind::Member { .. });

        if treat_as_method {
            let hir::ExpressionKind::Member { target, name } = callee.kind else {
                unreachable!()
            };

            hir::ExpressionKind::MethodCall {
                interface: None,
                receiver: target,
                name,
                arguments: args,
            }
        } else {
            hir::ExpressionKind::Call {
                callee,
                arguments: args,
            }
        }
    }

    /// Only assignees (`_ = value` and tuple leaves) interpret `_` as a
    /// discard. Other wildcard expressions retain their ordinary
    /// pipe-placeholder validation.
    fn lower_assignee(&mut self, node: Box<ast::Expression>) -> Box<hir::Expression> {
        let kind = match node.kind {
            ast::ExpressionKind::Tuple(items, labels) => hir::ExpressionKind::Tuple(
                items
                    .into_iter()
                    .map(|item| self.lower_assignee(item))
                    .collect(),
                labels,
            ),
            ast::ExpressionKind::Parenthesis(inner) => return self.lower_assignee(inner),
            ast::ExpressionKind::Wildcard => hir::ExpressionKind::Discard,
            _ => return self.lower_expression(node),
        };
        self.mk_expression(kind, node.span)
    }

    fn lower_pipe_expression(
        &mut self,
        lhs: Box<ast::Expression>,
        rhs: Box<ast::Expression>,
        span: Span,
    ) -> Box<hir::Expression> {
        let lhs_span = lhs.span;
        let (callee, mut args) = match *rhs {
            ast::Expression {
                kind: ast::ExpressionKind::Call(callee, args),
                ..
            } => (callee, args),
            rhs => (Box::new(rhs), Vec::new()),
        };
        if let Some(arg) = args
            .iter_mut()
            .find(|arg| matches!(arg.expression.kind, ast::ExpressionKind::Wildcard))
        {
            arg.expression = lhs;
        } else {
            args.insert(
                0,
                ast::ExpressionArgument {
                    label: None,
                    expression: lhs,
                    span: lhs_span,
                    interpolated: false,
                    is_trailing_closure: false,
                },
            );
        }
        let kind = self.lower_call(callee, args);
        self.mk_expression(kind, span)
    }
}

impl Actor<'_, '_> {
    fn lower_variant(&mut self, node: ast::Variant) -> hir::Variant {
        let named = matches!(&node.kind, ast::VariantKind::Struct(..));
        hir::Variant {
            def_id: self.definition_id(node.id),
            ctor_def_id: self.definition_id(node.ctor_id),
            identifier: node.identifier,
            kind: match node.kind {
                ast::VariantKind::Unit => hir::VariantKind::Unit,
                ast::VariantKind::Tuple(fields) | ast::VariantKind::Struct(fields) => {
                    let fields = fields
                        .into_iter()
                        .map(|field| self.lower_field_definition(field))
                        .collect();
                    if named {
                        hir::VariantKind::Struct(fields)
                    } else {
                        hir::VariantKind::Tuple(fields)
                    }
                }
            },
            discriminant: node.discriminant.map(|node| self.lower_anon_const(node)),
            span: node.span,
        }
    }

    fn lower_field_definition(&mut self, node: ast::FieldDefinition) -> hir::FieldDefinition {
        hir::FieldDefinition {
            def_id: self.definition_id(node.id),
            attributes: self.lower_attributes(node.attributes),
            default_value: node.default_value.map(|expr| self.lower_expression(expr)),
            mutability: node.mutability,
            label: node.label,
            identifier: node.identifier,
            ty: self.lower_type(node.ty),
            span: node.span,
        }
    }
}

impl Actor<'_, '_> {
    fn lower_path(&mut self, id: ast::NodeID, node: ast::Path) -> hir::ResolvedPath {
        let state = self.resolutions.resolutions.get(&id).cloned();
        let state = state.unwrap_or_else(|| {
            if self.lowering_deferred_bracket {
                // Resolution intentionally retained an erroneous alternative.
                // Its diagnostic is replayed only if this branch is selected.
                ResolutionState::Complete(Resolution::Error)
            } else {
                unreachable!("resolved path mapping")
            }
        });

        let (base_resolution, unresolved_count) = match state {
            ResolutionState::Complete(resolution) => (resolution, 0),
            ResolutionState::Partial {
                resolution,
                unresolved_count,
            } => (resolution, unresolved_count),
        };
        let base_resolution = self.lower_resolution(base_resolution);
        let x = node.segments.len() - unresolved_count;

        let path = hir::Path {
            span: node.span.to(node.segments[..x].last().unwrap().span),
            resolution: base_resolution,
            segments: node.segments[..x]
                .iter()
                .map(|segment| self.lower_path_segment(segment.clone()))
                .collect(),
        };

        let path_span = path.span;

        if unresolved_count == 0 {
            return hir::ResolvedPath::Resolved(path);
        }

        let mut base_ty = {
            let path = hir::ResolvedPath::Resolved(path);
            self.mk_ty(hir::TypeKind::Nominal(path), path_span)
        };

        let count = node.segments.len();
        for (index, node) in node.segments.into_iter().enumerate().skip(x) {
            let segment = self.lower_path_segment(node);
            let segment_span = segment.span;
            let path = hir::ResolvedPath::Relative(base_ty, segment);
            if index == count - 1 {
                return path;
            }
            base_ty = self.mk_ty(hir::TypeKind::Nominal(path), path_span.to(segment_span));
        }

        unreachable!()
    }

    fn lower_path_segment(&mut self, node: ast::PathSegment) -> hir::PathSegment {
        let state = self.resolutions.resolutions.get(&node.id).cloned();
        let resolution = self.convert_resolution_state(state);

        hir::PathSegment {
            id: self.next_index(),
            identifier: node.identifier,
            arguments: node.arguments.map(|n| self.lower_type_arguments(n)),
            span: node.span,
            resolution,
        }
    }

    fn lower_path_node(&mut self, node: ast::PathNode) -> hir::PathNode {
        hir::PathNode {
            id: self.next_index(),
            span: node.path.span,
            path: self.lower_path(node.id, node.path),
        }
    }

    fn lower_constructor_path(
        &mut self,
        id: ast::NodeID,
        path: ast::ConstructorPath,
    ) -> hir::ConstructorPath {
        match path {
            ast::ConstructorPath::Qualified { path } => {
                let path = self.lower_path(id, path);
                hir::ConstructorPath::Qualified { path }
            }
            ast::ConstructorPath::Inferred { name, span } => {
                hir::ConstructorPath::Inferred { name, span }
            }
        }
    }

    fn lower_select_expression(&mut self, node: ast::SelectExpression) -> hir::SelectExpression {
        let arms = node
            .arms
            .into_iter()
            .map(|arm| {
                let op_body = self.lower_expression(arm.operation);
                let op_span = op_body.span;
                let def_id = self
                    .context
                    .allocate_synthetic_id(self.context.package_index());
                let operation = self.mk_expression(
                    hir::ExpressionKind::Closure(hir::ClosureExpr {
                        def_id,
                        params: Vec::new(),
                        return_ty: None,
                        is_async: true,
                        implicit_await: true,
                        body: op_body,
                        snapshot_captures: false,
                        span: op_span,
                    }),
                    op_span,
                );
                hir::SelectArm {
                    pattern: self.lower_pattern(arm.pattern),
                    operation,
                    body: self.lower_expression(arm.body),
                    span: arm.span,
                }
            })
            .collect();
        hir::SelectExpression {
            arms,
            kw_span: node.kw_span,
        }
    }

    fn lower_local(&mut self, node: ast::Local) -> hir::Local {
        let id = self.next_index();
        self.node_mapping.insert(node.id, id);

        hir::Local {
            id,
            mutability: node.mutability,
            pattern: self.lower_pattern(node.pattern),
            ty: node.ty.map(|n| self.lower_type(n)),
            initializer: node.initializer.map(|n| self.lower_expression(n)),
            is_async: false,
        }
    }

    fn lower_async_local(&mut self, node: ast::Local, span: Span) -> hir::Local {
        let id = self.next_index();
        self.node_mapping.insert(node.id, id);

        let pattern = self.lower_pattern(node.pattern);
        let ty = node.ty.map(|n| self.lower_type(n));
        let body = self.lower_expression(
            node.initializer
                .expect("parser guarantees async var has an initializer"),
        );
        let init_span = body.span;
        let def_id = self
            .context
            .allocate_synthetic_id(self.context.package_index());
        let closure = self.mk_expression(
            hir::ExpressionKind::Closure(hir::ClosureExpr {
                def_id,
                params: Vec::new(),
                return_ty: None,
                is_async: true,
                implicit_await: true,
                body,
                snapshot_captures: false,
                span: init_span,
            }),
            span,
        );

        hir::Local {
            id,
            mutability: hir::Mutability::Immutable,
            pattern,
            ty,
            initializer: Some(closure),
            is_async: true,
        }
    }

    fn lower_static_variable(&mut self, node: ast::StaticVariable) -> hir::StaticVariable {
        hir::StaticVariable {
            identifier: node.identifier,
            mutability: node.mutability,
            ty: self.lower_type(node.ty),
            initializer: self.lower_expression(node.initializer),
        }
    }
}

impl Actor<'_, '_> {
    #[track_caller]
    fn convert_resolution_state(&mut self, state: Option<ResolutionState>) -> hir::Resolution {
        let Some(state) = state else {
            return hir::Resolution::Error;
        };

        match state {
            ResolutionState::Complete(resolution) => self.lower_resolution(resolution),
            ResolutionState::Partial { .. } => unreachable!("must provide full resolution"),
        }
    }

    #[track_caller]
    fn lower_resolution(&mut self, res: Resolution) -> hir::Resolution {
        return match res {
            Resolution::PrimaryType(n) => hir::Resolution::PrimaryType(n),
            Resolution::Definition(n, m) => hir::Resolution::Definition(n, m),
            Resolution::SelfTypeAlias(n) => hir::Resolution::SelfTypeAlias(n),
            Resolution::InterfaceSelfTypeParameter(m) => {
                hir::Resolution::InterfaceSelfTypeParameter(m)
            }
            Resolution::FunctionSet(n) => hir::Resolution::FunctionSet(n),
            Resolution::LocalVariable(id) => {
                let id = self.node_mapping.get(&id).expect("Local Mapping");
                hir::Resolution::LocalVariable(*id)
            }
            Resolution::SelfConstructor(n) => hir::Resolution::SelfConstructor(n),
            Resolution::StdItem(n) => hir::Resolution::StdItem(n),
            Resolution::Error => hir::Resolution::Error,
        };
    }

    #[track_caller]
    fn get_resolution(&mut self, id: ast::NodeID) -> hir::Resolution {
        let state = self.resolutions.resolutions.get(&id).cloned();
        let resolution = self.convert_resolution_state(state);
        resolution
    }

    /// Build an explicit foundational factory path for syntax desugaring.
    /// Missing type arguments are inferred from the surrounding expression.
    fn mk_foundation_factory(&mut self, item: StdItem, span: Span) -> Box<hir::Expression> {
        let name = item.name_str().expect("foundation type must have a name");
        let identifier = Identifier::new(self.context.intern_symbol(name), span);
        let path = self.mk_single_segment_resolved_path(identifier, Resolution::StdItem(item));
        let base = self.mk_ty(hir::TypeKind::Nominal(path), span);
        let member = hir::PathSegment {
            id: self.next_index(),
            identifier: Identifier::new(self.context.intern_symbol("new"), span),
            arguments: None,
            span,
            resolution: Resolution::Error,
        };
        let path = hir::ResolvedPath::Relative(base, member);
        self.mk_expression(hir::ExpressionKind::Path(path), span)
    }

    fn mk_single_segment_resolved_path(
        &mut self,
        identifier: Identifier,
        resolution: hir::Resolution,
    ) -> hir::ResolvedPath {
        let segment = hir::PathSegment {
            id: self.next_index(),
            identifier: identifier,
            arguments: None,
            span: identifier.span,
            resolution: resolution.clone(),
        };
        hir::ResolvedPath::Resolved(hir::Path {
            span: identifier.span,
            resolution,
            segments: vec![segment],
        })
    }

    fn lower_identifier_expression_path(
        &mut self,
        id: ast::NodeID,
        identifier: Identifier,
    ) -> hir::ResolvedPath {
        let resolution = self.get_resolution(id);
        let segment = hir::PathSegment {
            id: self.next_index(),
            identifier: identifier,
            arguments: None,
            span: identifier.span,
            resolution: resolution.clone(),
        };
        hir::ResolvedPath::Resolved(hir::Path {
            span: identifier.span,
            resolution,
            segments: vec![segment],
        })
    }
}

impl Actor<'_, '_> {
    fn mk_expression(&mut self, kind: hir::ExpressionKind, span: Span) -> Box<hir::Expression> {
        let expr = hir::Expression {
            id: self.next_index(),
            kind,
            span,
        };

        Box::new(expr)
    }

    fn mk_statement(&mut self, kind: hir::StatementKind, span: Span) -> hir::Statement {
        hir::Statement {
            id: self.next_index(),
            kind,
            span,
        }
    }

    fn mk_block(&mut self, statements: Vec<hir::Statement>, span: Span) -> hir::Block {
        let mut statements = statements;
        let tail = match statements.pop() {
            Some(hir::Statement {
                kind: hir::StatementKind::Expression(expr),
                ..
            }) => Some(expr),
            Some(stmt) => {
                statements.push(stmt);
                None
            }
            None => None,
        };
        hir::Block {
            id: self.next_index(),
            statements,
            tail,
            span,
        }
    }

    fn mk_ty(&mut self, kind: hir::TypeKind, span: Span) -> Box<hir::Type> {
        let ty = hir::Type {
            id: self.next_index(),
            kind,
            span,
        };

        Box::new(ty)
    }
}

#[derive(Clone)]
struct OptionalUnwrapReplacement {
    target_id: ast::NodeID,
    expression: Box<hir::Expression>,
}

impl Actor<'_, '_> {
    fn with_optional_unwrap_replacement<T>(
        &mut self,
        replacement: Option<OptionalUnwrapReplacement>,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let prev = self.optional_unwrap_replacement.take();
        self.optional_unwrap_replacement = replacement;
        let result = f(self);
        self.optional_unwrap_replacement = prev;
        result
    }

    fn lower_optional_expr(
        &mut self,
        expr: &ast::Expression,
        replacement: Option<&OptionalUnwrapReplacement>,
        force_optional: bool,
    ) -> (Box<hir::Expression>, bool) {
        if let Some(replacement) = replacement {
            if replacement.target_id == expr.id {
                if matches!(expr.kind, ast::ExpressionKind::OptionalUnwrap(_)) {
                    return (replacement.expression.clone(), false);
                }
            }
        }

        let skip_id = replacement.map(|r| r.target_id);
        if let Some((unwrap_id, inner_expr)) = self.find_outer_optional_unwrap(expr, skip_id) {
            let (scrutinee, _) = self.lower_optional_expr(inner_expr, replacement, false);

            let binding_ident =
                Identifier::new(self.context.intern_symbol("__optional_val"), expr.span);
            let binding_id = self.next_index();
            let binding_pattern = hir::Pattern {
                id: binding_id,
                span: expr.span,
                kind: hir::PatternKind::Binding {
                    name: binding_ident,
                },
            };

            let some_pattern = hir::Pattern {
                id: self.next_index(),
                span: expr.span,
                kind: hir::PatternKind::PathTuple {
                    path: hir::ConstructorPath::Qualified {
                        path: self.mk_optional_variant_path("some", expr.span),
                    },
                    fields: vec![binding_pattern],
                    field_span: expr.span,
                },
            };

            let none_pattern = hir::Pattern {
                id: self.next_index(),
                span: expr.span,
                kind: hir::PatternKind::Member(hir::ConstructorPath::Qualified {
                    path: self.mk_optional_variant_path("none", expr.span),
                }),
            };

            let binding_ref_path = self.mk_single_segment_resolved_path(
                binding_ident,
                Resolution::LocalVariable(binding_id),
            );
            let binding_ref_expr =
                self.mk_expression(hir::ExpressionKind::Path(binding_ref_path), expr.span);

            let replacement = OptionalUnwrapReplacement {
                target_id: unwrap_id,
                expression: binding_ref_expr,
            };

            let (some_body, _) = self.lower_optional_expr(expr, Some(&replacement), true);
            let none_body = self.wrap_optional_none(expr.span);

            let match_expr = hir::MatchExpression {
                source: hir::MatchSource::desugared(hir::MatchKind::OptionalUnwrap),
                value: scrutinee,
                arms: vec![
                    hir::MatchArm {
                        pattern: some_pattern,
                        body: some_body,
                        guard: None,
                        span: expr.span,
                    },
                    hir::MatchArm {
                        pattern: none_pattern,
                        body: none_body,
                        guard: None,
                        span: expr.span,
                    },
                ],
                kw_span: expr.span,
            };

            let expr = self.mk_expression(hir::ExpressionKind::Match(match_expr), expr.span);
            return (expr, true);
        }

        let lowered = self.with_optional_unwrap_replacement(replacement.cloned(), |this| {
            this.lower_expression(Box::new(expr.clone()))
        });
        let _ = force_optional;
        (lowered, false)
    }

    fn find_outer_optional_unwrap<'a>(
        &self,
        expr: &'a ast::Expression,
        skip_id: Option<ast::NodeID>,
    ) -> Option<(ast::NodeID, &'a ast::Expression)> {
        if let ast::ExpressionKind::OptionalUnwrap(inner) = &expr.kind {
            if Some(expr.id) == skip_id {
                return None;
            }
            return Some((expr.id, inner));
        }

        match &expr.kind {
            ast::ExpressionKind::OptionalEvaluation(_) => None,
            ast::ExpressionKind::Member { target, .. } => {
                self.find_outer_optional_unwrap(target, skip_id)
            }
            ast::ExpressionKind::TupleAccess(target, _) => {
                self.find_outer_optional_unwrap(target, skip_id)
            }
            ast::ExpressionKind::Call(callee, args) => {
                if let Some(found) = self.find_outer_optional_unwrap(callee, skip_id) {
                    return Some(found);
                }
                for arg in args {
                    if let Some(found) = self.find_outer_optional_unwrap(&arg.expression, skip_id) {
                        return Some(found);
                    }
                }
                None
            }
            ast::ExpressionKind::Index { target, index } => self
                .find_outer_optional_unwrap(target, skip_id)
                .or_else(|| {
                    index
                        .iter()
                        .find_map(|arg| self.find_outer_optional_unwrap(&arg.expression, skip_id))
                }),
            ast::ExpressionKind::Specialize { target, index, .. } => self
                .find_outer_optional_unwrap(target, skip_id)
                .or_else(|| {
                    index.as_deref().and_then(|args| {
                        args.iter()
                            .find_map(|arg| self.find_outer_optional_unwrap(&arg.expression, skip_id))
                    })
                }),
            ast::ExpressionKind::Parenthesis(target) => {
                self.find_outer_optional_unwrap(target, skip_id)
            }
            ast::ExpressionKind::Binary(_, lhs, rhs)
            | ast::ExpressionKind::Assign(lhs, rhs)
            | ast::ExpressionKind::AssignOp(_, lhs, rhs)
            | ast::ExpressionKind::AssignOptional(lhs, rhs) => self
                .find_outer_optional_unwrap(lhs, skip_id)
                .or_else(|| self.find_outer_optional_unwrap(rhs, skip_id)),
            ast::ExpressionKind::Unary(_, rhs)
            | ast::ExpressionKind::Spread(rhs)
            | ast::ExpressionKind::Reference(rhs)
            | ast::ExpressionKind::Dereference(rhs)
            | ast::ExpressionKind::Propagate(rhs) => self.find_outer_optional_unwrap(rhs, skip_id),
            ast::ExpressionKind::Range(lhs, rhs, _) => lhs
                .as_deref()
                .and_then(|e| self.find_outer_optional_unwrap(e, skip_id))
                .or_else(|| {
                    rhs.as_deref()
                        .and_then(|e| self.find_outer_optional_unwrap(e, skip_id))
                }),
            ast::ExpressionKind::Array(items) => items
                .iter()
                .find_map(|item| self.find_outer_optional_unwrap(item, skip_id)),
            ast::ExpressionKind::Tuple(items, _) => items
                .iter()
                .find_map(|item| self.find_outer_optional_unwrap(item, skip_id)),
            ast::ExpressionKind::If(node) => self
                .find_outer_optional_unwrap(&node.condition, skip_id)
                .or_else(|| self.find_outer_optional_unwrap(&node.then_block, skip_id))
                .or_else(|| {
                    node.else_block
                        .as_deref()
                        .and_then(|expr| self.find_outer_optional_unwrap(expr, skip_id))
                }),
            ast::ExpressionKind::Match(node) => self
                .find_outer_optional_unwrap(&node.value, skip_id)
                .or_else(|| {
                    node.arms
                        .iter()
                        .find_map(|arm| self.find_outer_optional_unwrap(&arm.body, skip_id))
                }),
            ast::ExpressionKind::StructLiteral(node) => node
                .fields
                .iter()
                .find_map(|field| self.find_outer_optional_unwrap(&field.expression, skip_id))
                .or_else(|| {
                    node.base
                        .as_deref()
                        .and_then(|base| self.find_outer_optional_unwrap(base, skip_id))
                }),
            _ => None,
        }
    }

    fn wrap_optional_none(&mut self, span: Span) -> Box<hir::Expression> {
        let none_path = self.mk_optional_variant_path("none", span);
        self.mk_expression(hir::ExpressionKind::Path(none_path), span)
    }
}

fn convert_ast_literal(
    gcx: GlobalContext<'_>,
    literal: ast::Literal,
) -> Result<hir::Literal, String> {
    match literal {
        ast::Literal::Bool(value) => Ok(hir::Literal::Bool(value)),
        ast::Literal::Rune { value } => {
            let c: char = escape::unescape_char(&value)
                .map_err(|err| format!("malformed rune, {:?}", err))?;
            Ok(hir::Literal::Rune(c))
        }
        ast::Literal::String { value } => Ok(hir::Literal::String(gcx.intern_symbol(&value))),
        ast::Literal::Integer {
            value,
            base,
            suffix,
        } => {
            let content = value.replace("_", "");
            let digits = match base {
                crate::parse::Base::Decimal => content.as_str(),
                crate::parse::Base::Binary => {
                    content.strip_prefix("0b").unwrap_or(content.as_str())
                }
                crate::parse::Base::Octal => content.strip_prefix("0o").unwrap_or(content.as_str()),
                crate::parse::Base::Hexadecimal => {
                    content.strip_prefix("0x").unwrap_or(content.as_str())
                }
            };
            u64::from_str_radix(digits, base.radix())
                .map(|value| hir::Literal::Integer {
                    value: value as i128,
                    suffix,
                })
                .map_err(|err| format!("malformed integer literal: {}", err))
        }
        ast::Literal::Float { value } => {
            match value.parse::<f64>() {
                Ok(v) => return Ok(hir::Literal::Float(v)),
                Err(err) => return Err(format!("malformed floating point, {}", err)),
            };
        }
        ast::Literal::Nil => Ok(hir::Literal::Nil),
    }
}

fn negate_literal(literal: &mut hir::Literal) -> bool {
    match literal {
        hir::Literal::Integer { value, .. } if *value >= 0 => *value = -*value,
        hir::Literal::Float(value) => *value = -*value,
        _ => return false,
    }
    true
}

#[cfg(test)]
mod tests {
    use super::escape::{EscapeError, unescape_char, unescape_str};
    use crate::{
        hir::{DeclarationKind, ExpressionKind, ResolvedPath, StatementKind},
        test_support::analyze_script,
    };

    #[test]
    fn literal_escape_decoding_preserves_unicode_and_ascii_boundaries() {
        for (source, expected) in [
            ("é", 'é'),
            (r"\0", '\0'),
            (r"\n", '\n'),
            (r"\r", '\r'),
            (r"\t", '\t'),
            (r"\\", '\\'),
            (r"\'", '\''),
            (r#"\""#, '"'),
            (r"\x00", '\0'),
            (r"\x7f", '\x7f'),
            (r"\u{000000}", '\0'),
            (r"\u{1_f9_80_}", '🦀'),
            (r"\u{10ffff}", '\u{10ffff}'),
        ] {
            assert_eq!(unescape_char(source), Ok(expected), "{source}");
            assert_eq!(unescape_str(source), Ok(expected.to_string()), "{source}");
        }
        assert_eq!(unescape_str(r"hello\n世界"), Ok("hello\n世界".into()));
    }

    #[test]
    fn malformed_literal_escapes_preserve_diagnostics() {
        use EscapeError::*;
        for (source, expected) in [
            ("\\", LoneSlash),
            (r"\z", InvalidEscape),
            (r"\x", TooShortHexEscape),
            (r"\x1", TooShortHexEscape),
            (r"\xx0", InvalidCharInHexEscape),
            (r"\x0z", InvalidCharInHexEscape),
            (r"\x80", OutOfRangeHexEscape),
            (r"\xff", OutOfRangeHexEscape),
            (r"\u1234", NoBraceInUnicodeEscape),
            (r"\u{", UnclosedUnicodeEscape),
            (r"\u{}", EmptyUnicodeEscape),
            (r"\u{_1}", LeadingUnderscoreUnicodeEscape),
            (r"\u{1", UnclosedUnicodeEscape),
            (r"\u{1z}", InvalidCharInUnicodeEscape),
            (r"\u{0000000}", OverlongUnicodeEscape),
            (r"\u{0000000z}", InvalidCharInUnicodeEscape),
            (r"\u{d800}", LoneSurrogateUnicodeEscape),
            (r"\u{dfff}", LoneSurrogateUnicodeEscape),
            (r"\u{110000}", OutOfRangeUnicodeEscape),
            ("\r", BareCarriageReturn),
        ] {
            assert_eq!(unescape_char(source).unwrap_err(), expected, "{source}");
            assert_eq!(unescape_str(source).unwrap_err(), expected, "{source}");
        }
    }

    #[test]
    fn rune_literals_require_exactly_one_character() {
        assert_eq!(unescape_char(""), Err(EscapeError::ZeroChars));
        assert_eq!(unescape_str(""), Ok(String::new()));
        for source in ["ab", "éa", r"\x01a", r"\u{1}a"] {
            assert_eq!(unescape_char(source), Err(EscapeError::MoreThanOneChar));
        }
        for source in ["\n", "\t", "'"] {
            assert_eq!(unescape_char(source), Err(EscapeError::EscapeOnlyChar));
            assert_eq!(unescape_str(source), Ok(source.to_string()));
        }
    }

    #[test]
    fn resolved_member_chain_keeps_per_segment_resolution() {
        let package = analyze_script(
            "func main() {\n    Foo::bar()\n}\n\nnamespace Foo {\n    func bar() {}\n}\n",
            |package, _| package,
        );

        let main_decl = package
            .root
            .declarations
            .iter()
            .find(|declaration| declaration.identifier.symbol.as_str() == "main")
            .expect("main declaration");
        let DeclarationKind::Function(function) = &main_decl.kind else {
            panic!("main should be a function");
        };
        let block = function.block.as_ref().expect("main body");
        let expression = if let Some(expression) = block.tail.as_ref() {
            expression
        } else {
            let StatementKind::Expression(expression) = &block.statements[0].kind else {
                panic!("first statement should be an expression");
            };
            expression
        };
        let ExpressionKind::Call { callee, .. } = &expression.kind else {
            panic!("statement should lower to a call");
        };
        let ExpressionKind::Path(ResolvedPath::Resolved(path)) = &callee.kind else {
            panic!("callee should lower to a resolved path");
        };

        assert_eq!(path.segments.len(), 2);

        let crate::hir::Resolution::Definition(first_id, first_kind) = &path.segments[0].resolution
        else {
            panic!("first segment should resolve to a definition");
        };
        let crate::hir::Resolution::Definition(second_id, second_kind) =
            &path.segments[1].resolution
        else {
            panic!("second segment should resolve to a definition");
        };

        assert_eq!(*first_kind, crate::hir::DefinitionKind::Namespace);
        assert_ne!(*first_id, *second_id);
        assert_eq!(*second_kind, crate::hir::DefinitionKind::Function);
    }
}
