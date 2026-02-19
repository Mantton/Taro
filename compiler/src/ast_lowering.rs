use crate::{
    ast::{self, Identifier},
    cfg::TargetInfo,
    compile::context::GlobalContext,
    error::CompileResult,
    hir::{self, DefinitionKind, StdType},
    sema::resolve::models::{
        ExpressionResolutionState, Resolution, ResolutionOutput, ResolutionState,
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

pub struct Actor<'a, 'c> {
    pub context: GlobalContext<'c>,
    pub resolutions: &'a ResolutionOutput<'c>,
    pub next_index: u32,
    pub node_mapping: FxHashMap<ast::NodeID, hir::NodeID>,
    optional_unwrap_replacement: Option<OptionalUnwrapReplacement>,
}

impl<'a, 'c> Actor<'a, 'c> {
    fn new(context: GlobalContext<'c>, resolutions: &'a ResolutionOutput<'c>) -> Actor<'a, 'c> {
        Actor {
            context,
            resolutions,
            next_index: 0,
            node_mapping: Default::default(),
            optional_unwrap_replacement: None,
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

impl Actor<'_, '_> {
    fn lower_module(&mut self, module: ast::Module) -> hir::Module {
        let id = self.definition_id(module.id);
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
        }
    }
}

impl Actor<'_, '_> {
    fn lower_declaration(&mut self, node: ast::Declaration) -> Vec<hir::Declaration> {
        // Check @cfg attributes - if any cfg condition fails, skip this declaration
        if !self.should_include_declaration(&node.attributes) {
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

        let kind = match kind {
            ast::DeclarationKind::Interface(node) => {
                hir::DeclarationKind::Interface(self.lower_interface(node))
            }
            ast::DeclarationKind::Struct(node) => {
                hir::DeclarationKind::Struct(self.lower_struct(node))
            }
            ast::DeclarationKind::Enum(node) => hir::DeclarationKind::Enum(self.lower_enum(node)),
            ast::DeclarationKind::TypeAlias(node) => {
                hir::DeclarationKind::TypeAlias(self.lower_alias(node))
            }
            ast::DeclarationKind::Function(node) => {
                let span = node.signature.span;
                hir::DeclarationKind::Function(self.lower_function(node, span))
            }
            ast::DeclarationKind::ExternBlock(node) => {
                return node
                    .declarations
                    .into_iter()
                    .map(|decl| self.lower_extern_declaration(decl, node.abi.clone()))
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
            ast::DeclarationKind::Variable(node) => {
                hir::DeclarationKind::Variable(self.lower_local(node))
            }
            ast::DeclarationKind::Impl(node) => hir::DeclarationKind::Impl(self.lower_impl(node)),
        };

        vec![hir::Declaration {
            id: self.definition_id(id),
            span,
            identifier,
            kind,
            attributes: self.lower_attributes(attributes),
        }]
    }

    /// Check if a declaration should be included based on @cfg attributes.
    /// Returns true if all @cfg conditions pass (or if there are no @cfg attrs).
    fn should_include_declaration(&self, attributes: &ast::AttributeList) -> bool {
        for attr in attributes {
            if self.context.symbol_eq(attr.identifier.symbol.clone(), "cfg") {
                if !self.evaluate_cfg(attr) {
                    return false;
                }
            }
        }
        true
    }

    /// Evaluate a single @cfg attribute.
    /// Returns true if the condition matches, false otherwise.
    fn evaluate_cfg(&self, attr: &ast::Attribute) -> bool {
        // New syntax: @cfg(os("macos") && ...)
        if let Some(cfg_expr) = &attr.cfg_expr {
            return self.evaluate_cfg_expr(cfg_expr);
        }

        // Legacy syntax: @cfg(target_os = "macos")
        let Some(args) = &attr.args else {
            // @cfg without arguments - treat as always true (or error?)
            return true;
        };

        // Get target triple from context
        let triple = self.context.store.target_layout.triple();
        let triple_str = triple.as_str().to_str().unwrap_or("");

        // Parse triple for OS and arch (format: arch-vendor-os or arch-vendor-os-env)
        let parts: Vec<&str> = triple_str.split('-').collect();
        let target_arch = parts.first().cloned().unwrap_or("");
        let target_os = if parts.len() >= 3 { parts[2] } else { "" };

        for arg in &args.items {
            match arg {
                ast::AttributeArg::KeyValue { key, value, .. } => {
                    let key_text = self.context.symbol_text(key.symbol.clone());
                    let key_str = key_text.as_str();
                    let value_str = match value {
                        ast::Literal::String { value } => value.as_str(),
                        _ => continue, // Skip non-string values for now
                    };

                    match key_str {
                        "target_os" => {
                            // Match common OS names
                            let matches = match value_str {
                                "macos" | "darwin" => {
                                    target_os.contains("darwin") || target_os == "macos"
                                }
                                "linux" => target_os == "linux",
                                "windows" => target_os.contains("windows") || target_os == "win32",
                                _ => target_os == value_str,
                            };
                            if !matches {
                                return false;
                            }
                        }
                        "target_arch" => {
                            // Match common arch names
                            let matches = match value_str {
                                "x86_64" | "amd64" => target_arch == "x86_64",
                                "aarch64" | "arm64" => {
                                    target_arch == "aarch64" || target_arch == "arm64"
                                }
                                "arm" => target_arch.starts_with("arm"),
                                _ => target_arch == value_str,
                            };
                            if !matches {
                                return false;
                            }
                        }
                        "target_profile" => {
                            let profile = match self.context.config.profile {
                                crate::compile::config::BuildProfile::Debug => "debug",
                                crate::compile::config::BuildProfile::Release => "release",
                            };

                            if profile != value_str {
                                return false;
                            }
                        }
                        _ => {
                            return false;
                        }
                    }
                }
                ast::AttributeArg::Flag { key, .. } => {
                    // @cfg(debug)
                    let key_text = self.context.symbol_text(key.symbol.clone());
                    let key_str = key_text.as_str();
                    match key_str {
                        "debug" => {
                            if !matches!(
                                self.context.config.profile,
                                crate::compile::config::BuildProfile::Debug
                            ) {
                                return false;
                            }
                        }
                        _ => {
                            // Unknown flag - treat as not matching
                            return false;
                        }
                    }
                }
            }
        }

        true // All conditions passed
    }

    /// Evaluate a CfgExpr (from #cfg(...) expression) against target triple
    fn evaluate_cfg_expr(&self, expr: &ast::CfgExpr) -> bool {
        // Get target triple from TargetLayout (which may be host or cross-compile target)
        let triple = self.context.store.target_layout.triple();
        let triple_str = triple.as_str().to_str().unwrap_or("");
        let mut target = TargetInfo::from_triple(triple_str);
        target.profile = match self.context.config.profile {
            crate::compile::config::BuildProfile::Debug => "debug".to_string(),
            crate::compile::config::BuildProfile::Release => "release".to_string(),
        };
        self.eval_cfg_expr_inner(expr, &target)
    }

    fn eval_cfg_expr_inner(&self, expr: &ast::CfgExpr, target: &TargetInfo) -> bool {
        match expr {
            ast::CfgExpr::Predicate { name, value, .. } => {
                let name_text = self.context.symbol_text(name.symbol.clone());
                let name_str = name_text.as_str();
                let value_text = self.context.symbol_text(value.clone());
                let value_str = value_text.as_str();

                match name_str {
                    "os" => target.matches_os(value_str),
                    "arch" => target.matches_arch(value_str),
                    "family" => target.matches_family(value_str),
                    "profile" => target.matches_profile(value_str),
                    _ => false, // Unknown predicate
                }
            }
            ast::CfgExpr::Not(inner, _) => !self.eval_cfg_expr_inner(inner, target),
            ast::CfgExpr::All(items, _) => {
                items.iter().all(|e| self.eval_cfg_expr_inner(e, target))
            }
            ast::CfgExpr::Any(items, _) => {
                items.iter().any(|e| self.eval_cfg_expr_inner(e, target))
            }
        }
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
                let span = node.signature.span;
                hir::DeclarationKind::Function(self.lower_function(node, span))
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
                let span = node.signature.span;
                hir::DeclarationKind::Function(self.lower_function(node, span))
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
                let span = node.signature.span;
                hir::DeclarationKind::Function(self.lower_function(node, span))
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
            ast::AssociatedDeclarationKind::Constant(node) => {
                hir::AssociatedDeclarationKind::Constant(self.lower_constant(node))
            }
            ast::AssociatedDeclarationKind::Function(node) => {
                let span = node.signature.span;
                hir::AssociatedDeclarationKind::Function(self.lower_function(node, span))
            }
            ast::AssociatedDeclarationKind::AssociatedType(node) => {
                hir::AssociatedDeclarationKind::Type(self.lower_alias(node))
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

    fn lower_struct(&mut self, node: ast::Struct) -> hir::Struct {
        hir::Struct {
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

    fn lower_use_tree(&mut self, _: ast::UseTree) -> hir::UseTree {
        hir::UseTree {}
    }
}

impl Actor<'_, '_> {
    fn lower_function(&mut self, node: ast::Function, span: Span) -> hir::Function {
        let abi = self.lower_abi(node.abi, span);
        hir::Function {
            generics: self.lower_generics(node.generics),
            signature: self.lower_function_signature(node.signature),
            block: node.block.map(|n| self.lower_block(n)),
            abi,
        }
    }

    fn lower_abi(&mut self, abi: Option<Symbol>, span: Span) -> Option<hir::Abi> {
        let Some(abi) = abi else { return None };
        let abi_text = self.context.symbol_text(abi);
        match abi_text.as_str() {
            "C" | "c" => Some(hir::Abi::C),
            "taro_rt" | "rt" => Some(hir::Abi::Runtime),
            "taro_intrinsic" | "intrinsic" => Some(hir::Abi::Intrinsic),
            other => {
                self.context.dcx.emit_error(
                    format!(
                        "unknown ABI \"{}\" (supported: \"C\", \"taro_rt\", \"taro_intrinsic\")",
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
            is_variadic,
            span,
        } = node;
        let id = self.next_index();
        self.node_mapping.insert(node_id, id);
        hir::FunctionParameter {
            id,
            attributes: self.lower_attributes(attributes),
            label,
            name,
            annotated_type: self.lower_type(annotated_type),
            default_value: default_value.map(|n| self.lower_expression(n)),
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
            ast::TypeKind::Reference(ty, mt) => hir::TypeKind::Reference(self.lower_type(ty), mt),
            ast::TypeKind::Parenthesis(ty) => return self.lower_type(ty),
            ast::TypeKind::Tuple(items) => {
                let items = items.into_iter().map(|n| self.lower_type(n)).collect();
                hir::TypeKind::Tuple(items)
            }
            ast::TypeKind::Array { size, element } => hir::TypeKind::Array {
                size: self.lower_anon_const(size),
                element: self.lower_type(element),
            },
            ast::TypeKind::Optional(element) => {
                let inner = self.lower_type(element);
                self.mk_foundation_type(
                    node.span,
                    hir::StdType::Option,
                    vec![hir::TypeArgument::Type(inner)],
                )
            }
            ast::TypeKind::List(element) => {
                let inner = self.lower_type(element);
                self.mk_foundation_type(
                    node.span,
                    hir::StdType::List,
                    vec![hir::TypeArgument::Type(inner)],
                )
            }
            ast::TypeKind::Dictionary { key, value } => {
                let key_ty = self.lower_type(key);
                let value_ty = self.lower_type(value);
                self.mk_foundation_type(
                    node.span,
                    hir::StdType::Dictionary,
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
            ast::TypeKind::ImplicitSelf => {
                let resolution = self.get_resolution(node.id);
                let path = hir::Path {
                    span: node.span,
                    resolution: resolution.clone(),
                    segments: vec![hir::PathSegment {
                        id: self.next_index(),
                        identifier: Identifier {
                            symbol: self.context.intern_symbol("Self"),
                            span: node.span,
                        },
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
        kind: StdType,
        arguments: Vec<hir::TypeArgument>,
    ) -> hir::TypeKind {
        let name = kind.name_str().expect("foundation type must have a name");

        let path = hir::Path {
            span,
            resolution: Resolution::Foundation(kind),
            segments: vec![hir::PathSegment {
                id: self.next_index(),
                identifier: Identifier::new(self.context.intern_symbol(name), span),
                arguments: Some(hir::TypeArguments { span, arguments }),
                span,
                resolution: Resolution::Foundation(kind),
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
                hir::PatternKind::Binding {
                    name: ident,
                    mode: hir::BindingMode::ByValue,
                }
            }
            ast::PatternKind::Tuple(items, span) => hir::PatternKind::Tuple(
                items
                    .into_iter()
                    .map(|node| self.lower_pattern(node))
                    .collect(),
                span,
            ),
            ast::PatternKind::Reference {
                pattern,
                mutability: mutable,
            } => hir::PatternKind::Reference {
                pattern: Box::new(self.lower_pattern(*pattern)),
                mutable,
            },
            ast::PatternKind::Member(pattern_path) => {
                hir::PatternKind::Member(self.lower_pattern_path(node.id, pattern_path))
            }
            ast::PatternKind::PathTuple {
                path,
                fields,
                field_span,
            } => hir::PatternKind::PathTuple {
                path: self.lower_pattern_path(node.id, path),
                fields: fields
                    .into_iter()
                    .map(|field| self.lower_pattern(field))
                    .collect(),
                field_span,
            },
            ast::PatternKind::Or(items, span) => hir::PatternKind::Or(
                items
                    .into_iter()
                    .map(|node| self.lower_pattern(node))
                    .collect(),
                span,
            ),
            ast::PatternKind::Literal(expr) => {
                let value = *expr.value;
                let literal = match value.kind {
                    ast::ExpressionKind::Literal(lit) => {
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
                hir::PatternKind::Literal(literal)
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

        hir::Block {
            id: self.next_index(),
            statements: statements
                .into_iter()
                .map(|n| self.lower_statement(n))
                .collect(),
            tail: tail_expr.map(|expr| self.lower_expression(expr)),
            span: node.span,
        }
    }

    fn lower_statement(&mut self, node: ast::Statement) -> hir::Statement {
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
            ast::StatementKind::Break(..) => hir::StatementKind::Break,
            ast::StatementKind::Continue(..) => hir::StatementKind::Continue,
            ast::StatementKind::Return(node) => {
                hir::StatementKind::Return(node.map(|n| self.lower_expression(n)))
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
                let break_statement = self.mk_statement(hir::StatementKind::Break, node.span);
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
            ast::StatementKind::For(for_stmt) => {
                let stmt_kind = self.lower_for_statement(for_stmt, node.span);
                return self.mk_statement(stmt_kind, node.span);
            }
            ast::StatementKind::Defer(node) => hir::StatementKind::Defer(self.lower_block(node)),
            ast::StatementKind::Guard {
                condition,
                else_block,
            } => hir::StatementKind::Guard {
                condition: self.lower_expression(condition),
                else_block: self.lower_block(else_block),
            },
        };
        hir::Statement {
            id: self.next_index(),
            kind,
            span: node.span,
        }
    }
}

impl Actor<'_, '_> {
    fn lower_for_statement(&mut self, node: ast::ForStatement, span: Span) -> hir::StatementKind {
        /*
        Desugars:
            for pattern in collection { body }
        to:
            {
                var __for_iter = collection.makeIterator();
                loop {
                    var element = __for_iter.next()
                    match element {
                        case Optional.some(pattern) => { body }
                        case Optional.none => break
                    }
                }
            }
        */
        // 1. Lower the iterator expression
        let collection = self.lower_expression(node.iterator);

        // 2. Create local binding: var __for_iter = Iterable.makeIterator(collection)
        let iter_ident = Identifier::new(self.context.intern_symbol("__for_iter"), span);
        let iter_pattern_id = self.next_index();
        let iter_pattern = hir::Pattern {
            id: iter_pattern_id,
            span,
            kind: hir::PatternKind::Binding {
                name: iter_ident.clone(),
                mode: hir::BindingMode::ByValue,
            },
        };

        // Create Iterable.makeIterator(collection) call as UFCS call
        let iterable_id = self
            .context
            .find_std_type("Iterable")
            .expect("std.Iterable not found");
        let iterable_path = hir::ResolvedPath::Resolved(hir::Path {
            span,
            resolution: Resolution::Definition(iterable_id, DefinitionKind::Interface),
            segments: vec![hir::PathSegment {
                id: self.next_index(),
                identifier: Identifier::new(self.context.intern_symbol("Iterable"), span),
                arguments: None,
                span,
                resolution: Resolution::Definition(iterable_id, DefinitionKind::Interface),
            }],
        });

        let iterable_ty = hir::Type {
            id: self.next_index(),
            span,
            kind: hir::TypeKind::Nominal(iterable_path),
        };

        // Resolve 'makeIterator' within Iterable
        let iterable_reqs = self
            .context
            .get_interface_requirements(iterable_id)
            .expect("Iterable interface requirements not found");
        let make_iter_def = iterable_reqs
            .methods
            .iter()
            .find(|m| self.context.symbol_eq(m.name.clone(), "makeIterator"))
            .expect("makeIterator method not found in Iterable");

        let make_iter_id = make_iter_def.id;
        let make_iter_kind = self.context.definition_kind(make_iter_id);

        let make_iter_segment = hir::PathSegment {
            id: self.next_index(),
            identifier: Identifier::new(self.context.intern_symbol("makeIterator"), span),
            arguments: None,
            span,
            resolution: Resolution::Definition(make_iter_id, make_iter_kind),
        };

        let make_iter_fn_path =
            hir::ResolvedPath::Relative(Box::new(iterable_ty), make_iter_segment);
        let make_iter_fn_expr =
            self.mk_expression(hir::ExpressionKind::Path(make_iter_fn_path), span);

        let make_iterator_call = self.mk_expression(
            hir::ExpressionKind::Call {
                callee: make_iter_fn_expr,
                arguments: vec![hir::ExpressionArgument {
                    label: None,
                    expression: collection,
                    span,
                }],
            },
            span,
        );

        let iter_local = hir::Local {
            id: self.next_index(),
            mutability: hir::Mutability::Mutable,
            pattern: iter_pattern,
            ty: None,
            initializer: Some(make_iterator_call),
        };

        // 3. Create Iterator.next(&mut __for_iter) call
        let iter_ref_path = self.mk_single_segment_resolved_path(
            iter_ident,
            Resolution::LocalVariable(iter_pattern_id),
        );
        let iter_ref_expr = self.mk_expression(hir::ExpressionKind::Path(iter_ref_path), span);
        let iter_mut_borrow = self.mk_expression(
            hir::ExpressionKind::Reference(iter_ref_expr, hir::Mutability::Mutable),
            span,
        );

        // Resolve Iterator.next path
        let iterator_id = self
            .context
            .find_std_type("Iterator")
            .expect("std.Iterator not found");
        let iterator_path = hir::ResolvedPath::Resolved(hir::Path {
            span,
            resolution: Resolution::Definition(iterator_id, DefinitionKind::Interface),
            segments: vec![hir::PathSegment {
                id: self.next_index(),
                identifier: Identifier::new(self.context.intern_symbol("Iterator"), span),
                arguments: None,
                span,
                resolution: Resolution::Definition(iterator_id, DefinitionKind::Interface),
            }],
        });

        let iterator_ty = hir::Type {
            id: self.next_index(),
            span,
            kind: hir::TypeKind::Nominal(iterator_path),
        };

        let iterator_reqs = self
            .context
            .get_interface_requirements(iterator_id)
            .expect("Iterator interface requirements not found");
        let next_def = iterator_reqs
            .methods
            .iter()
            .find(|m| self.context.symbol_eq(m.name.clone(), "next"))
            .expect("next method not found in Iterator");

        let next_id = next_def.id;
        let next_kind = self.context.definition_kind(next_id);

        let next_segment = hir::PathSegment {
            id: self.next_index(),
            identifier: Identifier::new(self.context.intern_symbol("next"), span),
            arguments: None,
            span,
            resolution: Resolution::Definition(next_id, next_kind),
        };

        let next_fn_path = hir::ResolvedPath::Relative(Box::new(iterator_ty), next_segment);
        let next_fn_expr = self.mk_expression(hir::ExpressionKind::Path(next_fn_path), span);

        let next_call = self.mk_expression(
            hir::ExpressionKind::Call {
                callee: next_fn_expr,
                arguments: vec![hir::ExpressionArgument {
                    label: None,
                    expression: iter_mut_borrow,
                    span,
                }],
            },
            span,
        );

        // var element = Iterator.next(&mut __for_iter);
        let element_ident = Identifier::new(self.context.intern_symbol("element"), span);
        let element_pattern_id = self.next_index();
        let element_pattern = hir::Pattern {
            id: element_pattern_id,
            span,
            kind: hir::PatternKind::Binding {
                name: element_ident.clone(),
                mode: hir::BindingMode::ByValue,
            },
        };

        let element_local = hir::Local {
            id: self.next_index(),
            mutability: hir::Mutability::Mutable,
            pattern: element_pattern,
            ty: None,
            initializer: Some(next_call),
        };

        // 5. Lower the user's pattern from the for loop
        let user_pattern = self.lower_pattern(node.pattern);

        // 6. Create Optional.some(user_pattern) - FULLY QUALIFIED
        let some_path = self.mk_optional_variant_path("some", span);
        let some_pattern = hir::Pattern {
            id: self.next_index(),
            span,
            kind: hir::PatternKind::PathTuple {
                path: hir::PatternPath::Qualified { path: some_path },
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
            let continue_stmt = self.mk_statement(hir::StatementKind::Continue, span);
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

        // 8. Create Optional.none pattern - FULLY QUALIFIED
        let none_path = self.mk_optional_variant_path("none", span);
        let none_pattern = hir::Pattern {
            id: self.next_index(),
            span,
            kind: hir::PatternKind::Member(hir::PatternPath::Qualified { path: none_path }),
        };

        // Arm 2: case Optional.none => break
        let break_stmt = self.mk_statement(hir::StatementKind::Break, span);
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

        // 11. Create outer block: { var __for_iter = ...; loop { ... } }
        let iter_stmt = self.mk_statement(hir::StatementKind::Variable(iter_local), span);
        let loop_stmt = self.mk_statement(loop_stmt_kind, span);
        let outer_block = self.mk_block(vec![iter_stmt, loop_stmt], span);

        hir::StatementKind::Expression(
            self.mk_expression(hir::ExpressionKind::Block(outer_block), span),
        )
    }
}
impl Actor<'_, '_> {
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
            ast::ExpressionKind::Member { target, name } => {
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
            } => {
                // Convert Specialize into a path with type arguments on the final segment
                match self.lower_specialize_as_path(&target, type_arguments, node.span) {
                    Some(path) => hir::ExpressionKind::Path(path),
                    None => {
                        self.context.dcx.emit_error(
                            "type arguments can only be applied to path-like expressions".into(),
                            Some(node.span),
                        );
                        hir::ExpressionKind::Malformed
                    }
                }
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
            ast::ExpressionKind::Tuple(nodes) => hir::ExpressionKind::Tuple(
                nodes
                    .into_iter()
                    .map(|expr| self.lower_expression(expr))
                    .collect(),
            ),
            ast::ExpressionKind::If(node) => {
                hir::ExpressionKind::If(self.lower_if_expression(node))
            }
            ast::ExpressionKind::Match(node) => {
                hir::ExpressionKind::Match(self.lower_match_expression(node))
            }
            ast::ExpressionKind::Call(node, args) => {
                let callee_state = self
                    .resolutions
                    .expression_resolutions
                    .get(&node.id)
                    .cloned();
                let callee = self.lower_expression(node);
                let args = self.lower_expression_arguments(args);

                let treat_as_method =
                    matches!(
                        callee_state,
                        None | Some(ExpressionResolutionState::DeferredAssociatedValue)
                    ) && matches!(callee.kind, hir::ExpressionKind::Member { .. });

                if treat_as_method {
                    let hir::ExpressionKind::Member { target, name } = callee.kind else {
                        unreachable!()
                    };

                    hir::ExpressionKind::MethodCall {
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
            ast::ExpressionKind::Reference(node, mutability) => {
                hir::ExpressionKind::Reference(self.lower_expression(node), mutability)
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
                hir::ExpressionKind::Unary(op, self.lower_expression(rhs))
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
                hir::ExpressionKind::Assign(self.lower_expression(lhs), self.lower_expression(rhs))
            }
            ast::ExpressionKind::Parenthesis(node) => {
                return self.lower_expression(node);
            }
            ast::ExpressionKind::CastAs(node, ty) => {
                hir::ExpressionKind::CastAs(self.lower_expression(node), self.lower_type(ty))
            }
            ast::ExpressionKind::Pipe(lhs, rhs) => {
                return self.lower_pipe_expression(lhs, rhs, node.span);
            }
            ast::ExpressionKind::PatternBinding(node) => {
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
                // `1..10`
                let foundational = if inclusive {
                    StdType::ClosedRange
                } else {
                    StdType::Range
                };

                let lhs = self.lower_expression(lhs);
                let rhs = self.lower_expression(rhs);
                let identiier = Identifier::new(self.context.intern_symbol("Range"), node.span);
                let range_path = self.mk_single_segment_resolved_path(
                    identiier,
                    Resolution::Foundation(foundational),
                );
                let foo = self.mk_expression(hir::ExpressionKind::Path(range_path), node.span);

                let arguments = vec![lhs, rhs]
                    .into_iter()
                    .map(|node| hir::ExpressionArgument {
                        label: None,
                        span: node.span,
                        expression: node,
                    })
                    .collect();

                let call = self.mk_expression(
                    hir::ExpressionKind::Call {
                        callee: foo,
                        arguments,
                    },
                    node.span,
                );
                return call;
            }
            ast::ExpressionKind::DictionaryLiteral(map_pairs) => {
                // ["foo": "bar"] => { let dictionary = Dictionary(); dictionary.insert("foo", "bar"); dictionary }
                // Initialize the dictionary via a foundational call.
                let ctor_ident =
                    Identifier::new(self.context.intern_symbol("Dictionary"), node.span);
                let ctor_path = self.mk_single_segment_resolved_path(
                    ctor_ident,
                    Resolution::Foundation(hir::StdType::Dictionary),
                );
                let ctor = self.mk_expression(hir::ExpressionKind::Path(ctor_path), node.span);
                let initializer = self.mk_expression(
                    hir::ExpressionKind::Call {
                        callee: ctor,
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
                        name: dictionary_ident.clone(),
                        mode: hir::BindingMode::ByValue,
                    },
                };

                // Store the pattern's ID - this is what THIR uses to register the local binding
                let pattern_id = pattern.id;

                let local = hir::Local {
                    id: self.next_index(),
                    mutability: hir::Mutability::Mutable,
                    pattern,
                    ty: None,
                    initializer: Some(initializer),
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
                        dictionary_ident.clone(),
                        Resolution::LocalVariable(local_id),
                    );
                    let target =
                        self.mk_expression(hir::ExpressionKind::Path(dictionary_path), node.span);
                    let member = self.mk_expression(
                        hir::ExpressionKind::Member {
                            target,
                            name: insert_ident.clone(),
                        },
                        node.span,
                    );

                    let arguments = vec![key, value]
                        .into_iter()
                        .map(|expr| hir::ExpressionArgument {
                            label: None,
                            span: expr.span,
                            expression: expr,
                        })
                        .collect();

                    let call = self.mk_expression(
                        hir::ExpressionKind::MethodCall {
                            receiver: member,
                            name: insert_ident.clone(),
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
                let path = self.lower_path(
                    struct_literal.path.segments[0].id,
                    struct_literal.path.clone(),
                );
                let fields = struct_literal
                    .fields
                    .iter()
                    .map(|f| hir::ExpressionField {
                        label: f.label.clone(),
                        expression: self.lower_expression(f.expression.clone()),
                        span: f.span,
                    })
                    .collect();
                hir::ExpressionKind::StructLiteral(hir::StructLiteral { path, fields })
            }
            ast::ExpressionKind::CfgCheck(cfg_expr) => {
                // Evaluate the cfg expression at compile time
                let result = self.evaluate_cfg_expr(&cfg_expr);
                hir::ExpressionKind::Literal(hir::Literal::Bool(result))
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
        // Only compact purely qualified dotted chains that are fully resolved by the resolver.
        // If any segment is deferred, keep it in expression form so typeck can resolve associated
        // items/types.
        let mut parts: Vec<(ast::NodeID, Identifier)> = Vec::new();
        self.collect_member_chain_parts(target, &mut parts)?;
        parts.push((member_expr_id, name));

        let (base_id, base_ident) = parts.first()?;

        let mut last_resolution = self.get_resolution(*base_id);
        let mut segments = Vec::with_capacity(parts.len());
        segments.push(hir::PathSegment {
            id: self.next_index(),
            identifier: base_ident.clone(),
            arguments: None,
            span: base_ident.span,
            resolution: last_resolution.clone(),
        });

        for (part_id, ident) in parts.into_iter().skip(1) {
            match self
                .resolutions
                .expression_resolutions
                .get(&part_id)
                .cloned()
            {
                Some(ExpressionResolutionState::Resolved(res)) => {
                    last_resolution = self.lower_resolution(res);
                    segments.push(hir::PathSegment {
                        id: self.next_index(),
                        identifier: ident.clone(),
                        arguments: None,
                        span: ident.span,
                        resolution: last_resolution.clone(),
                    });
                }
                Some(ExpressionResolutionState::DeferredAssociatedType)
                | Some(ExpressionResolutionState::DeferredAssociatedValue) => return None,
                None => unreachable!(
                    "ICE: missing expression resolution for member chain segment {part_id:?}"
                ),
            }
        }

        Some(hir::Path {
            span,
            resolution: last_resolution,
            segments,
        })
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

            segs.push(seg_name.clone());
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
                identifier: ident.clone(),
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

    fn collect_member_chain_parts(
        &self,
        expr: &ast::Expression,
        out: &mut Vec<(ast::NodeID, Identifier)>,
    ) -> Option<()> {
        match &expr.kind {
            ast::ExpressionKind::Identifier(ident) => {
                out.push((expr.id, ident.clone()));
                Some(())
            }
            ast::ExpressionKind::Member { target, name } => {
                self.collect_member_chain_parts(target, out)?;
                out.push((expr.id, name.clone()));
                Some(())
            }
            _ => None,
        }
    }

    /// Attempts to convert an AST expression to a resolved path suitable for attaching type arguments.
    /// Returns None if the expression cannot be converted to a path.
    fn try_expr_as_resolved_path(&mut self, expr: &ast::Expression) -> Option<hir::ResolvedPath> {
        match &expr.kind {
            ast::ExpressionKind::Identifier(ident) => {
                let resolved_path = self.lower_identifier_expression_path(expr.id, ident.clone());
                Some(resolved_path)
            }
            ast::ExpressionKind::Member { target, name } => {
                // Check resolution state to determine how to handle
                match self
                    .resolutions
                    .expression_resolutions
                    .get(&expr.id)
                    .cloned()
                {
                    Some(ExpressionResolutionState::Resolved(_)) => {
                        let path = self.try_lower_resolved_member_chain_as_path(
                            expr.id, target, name.clone(), expr.span,
                        )?;
                        Some(hir::ResolvedPath::Resolved(path))
                    }
                    Some(ExpressionResolutionState::DeferredAssociatedType) => {
                        let path =
                            self.lower_deferred_associated_type_member_chain(target.clone(), name.clone());
                        Some(path)
                    }
                    // DeferredAssociatedValue and None cannot be converted to paths for specialization
                    _ => None,
                }
            }
            ast::ExpressionKind::Specialize {
                target,
                type_arguments,
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
            .map(|arg| hir::ExpressionArgument {
                label: arg.label,
                expression: self.lower_expression(arg.expression),
                span: arg.span,
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
                    kind: hir::PatternKind::Binding {
                        name: param.name,
                        mode: hir::BindingMode::ByValue,
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
            body,
            is_move: false, // TODO: Support `move` keyword in parser
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
        // Transform `let x = opt` into `case Optional.some(x) = opt`
        let inner_pattern = self.lower_pattern(node.pattern);
        let some_span = inner_pattern.span;

        let pattern = hir::Pattern {
            id: self.next_index(),
            span: some_span,
            kind: hir::PatternKind::PathTuple {
                path: hir::PatternPath::Qualified {
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
            kind: hir::PatternKind::Binding {
                name: val_ident.clone(),
                mode: hir::BindingMode::ByValue,
            },
        };

        // Create Optional.some(__optional_val) pattern using qualified path
        let some_path = self.mk_optional_variant_path("some", lhs_span);
        let some_pattern = hir::Pattern {
            id: self.next_index(),
            span: lhs_span,
            kind: hir::PatternKind::PathTuple {
                path: hir::PatternPath::Qualified { path: some_path },
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
            kind: hir::PatternKind::Member(hir::PatternPath::Qualified { path: none_path }),
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

    /// Creates a fully resolved path for an Optional variant (e.g., `Optional.some` or `Optional.none`).
    /// Looks up the Optional enum and its variants from the global context to get actual DefinitionIDs.
    fn mk_optional_variant_path(&mut self, variant_name: &str, span: Span) -> hir::ResolvedPath {
        use crate::sema::resolve::models::{DefinitionKind, VariantCtorKind};

        let optional_ident = Identifier::new(self.context.intern_symbol("Optional"), span);
        let variant_ident = Identifier::new(self.context.intern_symbol(variant_name), span);

        // Look up the Optional enum from std library
        let optional_def_id = self
            .context
            .find_std_type("Optional")
            .expect("Optional type must be available from std library");

        // Get the enum definition to find the variant
        let enum_def = self
            .context
            .try_get_enum_definition(optional_def_id)
            .expect("Optional must be an enum");

        // Find the variant by name
        let variant = enum_def
            .variants
            .iter()
            .find(|v| self.context.symbol_eq(v.name.clone(), variant_name))
            .expect("Optional must have this variant");

        // Determine the constructor kind based on variant fields
        let ctor_kind = match variant.kind {
            crate::sema::models::EnumVariantKind::Unit => VariantCtorKind::Constant,
            crate::sema::models::EnumVariantKind::Tuple(_) => VariantCtorKind::Function,
        };

        // Create base segment: Optional (with Definition resolution to the enum)
        let base_segment = hir::PathSegment {
            id: self.next_index(),
            identifier: optional_ident,
            arguments: None,
            span,
            resolution: hir::Resolution::Definition(optional_def_id, DefinitionKind::Enum),
        };

        // Create variant segment with fully resolved DefinitionID
        let variant_segment = hir::PathSegment {
            id: self.next_index(),
            identifier: variant_ident,
            arguments: None,
            span,
            resolution: hir::Resolution::Definition(
                variant.ctor_def_id,
                DefinitionKind::VariantConstructor(ctor_kind),
            ),
        };

        hir::ResolvedPath::Resolved(hir::Path {
            span,
            // The path resolution is the final segment's resolution (the variant constructor)
            resolution: hir::Resolution::Definition(
                variant.ctor_def_id,
                DefinitionKind::VariantConstructor(ctor_kind),
            ),
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

    fn lower_pipe_expression(
        &mut self,
        lhs: Box<ast::Expression>,
        rhs: Box<ast::Expression>,
        span: Span,
    ) -> Box<hir::Expression> {
        let lhs_span = lhs.span;

        match *rhs {
            ast::Expression {
                kind: ast::ExpressionKind::Call(callee, mut args),
                ..
            } => {
                let mut lhs_slot = Some(lhs);

                for arg in args.iter_mut() {
                    if lhs_slot.is_some()
                        && matches!(arg.expression.kind, ast::ExpressionKind::Wildcard)
                    {
                        arg.expression = lhs_slot.take().unwrap();
                        break;
                    }
                }

                if let Some(expr) = lhs_slot {
                    args.insert(
                        0,
                        ast::ExpressionArgument {
                            label: None,
                            expression: expr,
                            span: lhs_span,
                        },
                    );
                }

                let callee_state = self
                    .resolutions
                    .expression_resolutions
                    .get(&callee.id)
                    .cloned();
                let kind = match callee.kind {
                    ast::ExpressionKind::Member { target, name }
                        if matches!(
                            callee_state,
                            None | Some(ExpressionResolutionState::DeferredAssociatedValue)
                        ) =>
                    {
                        hir::ExpressionKind::MethodCall {
                            receiver: self.lower_expression(target),
                            name,
                            arguments: self.lower_expression_arguments(args),
                        }
                    }
                    _ => hir::ExpressionKind::Call {
                        callee: self.lower_expression(callee),
                        arguments: self.lower_expression_arguments(args),
                    },
                };

                self.mk_expression(kind, span)
            }
            rhs_expr => {
                let args = vec![ast::ExpressionArgument {
                    label: None,
                    expression: lhs,
                    span: lhs_span,
                }];

                let kind = hir::ExpressionKind::Call {
                    callee: self.lower_expression(Box::new(rhs_expr)),
                    arguments: self.lower_expression_arguments(args),
                };

                self.mk_expression(kind, span)
            }
        }
    }
}

impl Actor<'_, '_> {
    fn lower_variant(&mut self, node: ast::Variant) -> hir::Variant {
        hir::Variant {
            def_id: self.definition_id(node.id),
            ctor_def_id: self.definition_id(node.ctor_id),
            identifier: node.identifier,
            kind: match node.kind {
                ast::VariantKind::Unit => hir::VariantKind::Unit,
                ast::VariantKind::Tuple(fields) => hir::VariantKind::Tuple(
                    fields
                        .into_iter()
                        .map(|node| self.lower_field_definition(node))
                        .collect(),
                ),
            },
            discriminant: node.discriminant.map(|node| self.lower_anon_const(node)),
            span: node.span,
        }
    }

    fn lower_field_definition(&mut self, node: ast::FieldDefinition) -> hir::FieldDefinition {
        hir::FieldDefinition {
            def_id: self.definition_id(node.id),
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
        let Some(state) = state else { unreachable!() };

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

    fn lower_pattern_path(&mut self, id: ast::NodeID, path: ast::PatternPath) -> hir::PatternPath {
        match path {
            ast::PatternPath::Qualified { path } => {
                let path = self.lower_path(id, path);
                hir::PatternPath::Qualified { path }
            }
            ast::PatternPath::Inferred { name, span } => hir::PatternPath::Inferred { name, span },
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
            Resolution::Foundation(n) => hir::Resolution::Foundation(n),
            Resolution::Error => hir::Resolution::Error,
        };
    }

    #[track_caller]
    fn get_resolution(&mut self, id: ast::NodeID) -> hir::Resolution {
        let state = self.resolutions.resolutions.get(&id).cloned();
        let resolution = self.convert_resolution_state(state);
        resolution
    }

    fn mk_single_segment_resolved_path(
        &mut self,
        identifier: Identifier,
        resolution: hir::Resolution,
    ) -> hir::ResolvedPath {
        let segment = hir::PathSegment {
            id: self.next_index(),
            identifier: identifier.clone(),
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
            identifier: identifier.clone(),
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
                    name: binding_ident.clone(),
                    mode: hir::BindingMode::ByValue,
                },
            };

            let some_pattern = hir::Pattern {
                id: self.next_index(),
                span: expr.span,
                kind: hir::PatternKind::PathTuple {
                    path: hir::PatternPath::Qualified {
                        path: self.mk_optional_variant_path("some", expr.span),
                    },
                    fields: vec![binding_pattern],
                    field_span: expr.span,
                },
            };

            let none_pattern = hir::Pattern {
                id: self.next_index(),
                span: expr.span,
                kind: hir::PatternKind::Member(hir::PatternPath::Qualified {
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
            ast::ExpressionKind::Specialize { target, .. }
            | ast::ExpressionKind::Parenthesis(target) => {
                self.find_outer_optional_unwrap(target, skip_id)
            }
            ast::ExpressionKind::Binary(_, lhs, rhs)
            | ast::ExpressionKind::Assign(lhs, rhs)
            | ast::ExpressionKind::AssignOp(_, lhs, rhs) => self
                .find_outer_optional_unwrap(lhs, skip_id)
                .or_else(|| self.find_outer_optional_unwrap(rhs, skip_id)),
            ast::ExpressionKind::Unary(_, rhs)
            | ast::ExpressionKind::Reference(rhs, _)
            | ast::ExpressionKind::Dereference(rhs) => {
                self.find_outer_optional_unwrap(rhs, skip_id)
            }
            ast::ExpressionKind::Range(lhs, rhs, _) => self
                .find_outer_optional_unwrap(lhs, skip_id)
                .or_else(|| self.find_outer_optional_unwrap(rhs, skip_id)),
            ast::ExpressionKind::Array(items) => items
                .iter()
                .find_map(|item| self.find_outer_optional_unwrap(item, skip_id)),
            ast::ExpressionKind::Tuple(items) => items
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
                .find_map(|field| self.find_outer_optional_unwrap(&field.expression, skip_id)),
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
        ast::Literal::String { value } => {
            let value = escape::unescape_str(&value)
                .map_err(|err| format!("malformed string, {:?}", err))?;
            Ok(hir::Literal::String(gcx.intern_symbol(&value)))
        }
        ast::Literal::Integer { value, base } => {
            let content = value.replace("_", "");
            let digits = match base {
                crate::parse::Base::Decimal => content.as_str(),
                crate::parse::Base::Binary => content.strip_prefix("0b").unwrap_or(content.as_str()),
                crate::parse::Base::Octal => content.strip_prefix("0o").unwrap_or(content.as_str()),
                crate::parse::Base::Hexadecimal => {
                    content.strip_prefix("0x").unwrap_or(content.as_str())
                }
            };
            u64::from_str_radix(digits, base.radix())
                .map(|i| hir::Literal::Integer(i))
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

mod escape {
    /// Errors and warnings that can occur during string unescaping. They mostly
    /// relate to malformed escape sequences, but there are a few that are about
    /// other problems.
    #[derive(Debug, PartialEq, Eq)]
    #[allow(unused)]
    pub enum EscapeError {
        /// Expected 1 char, but 0 were found.
        ZeroChars,
        /// Expected 1 char, but more than 1 were found.
        MoreThanOneChar,

        /// Escaped '\' character without continuation.
        LoneSlash,
        /// Invalid escape character (e.g. '\z').
        InvalidEscape,
        /// Raw '\r' encountered.
        BareCarriageReturn,
        /// Raw '\r' encountered in raw string.
        BareCarriageReturnInRawString,
        /// Unescaped character that was expected to be escaped (e.g. raw '\t').
        EscapeOnlyChar,

        /// Numeric character escape is too short (e.g. '\x1').
        TooShortHexEscape,
        /// Invalid character in numeric escape (e.g. '\xz')
        InvalidCharInHexEscape,
        /// Character code in numeric escape is non-ascii (e.g. '\xFF').
        OutOfRangeHexEscape,

        /// '\u' not followed by '{'.
        NoBraceInUnicodeEscape,
        /// Non-hexadecimal value in '\u{..}'.
        InvalidCharInUnicodeEscape,
        /// '\u{}'
        EmptyUnicodeEscape,
        /// No closing brace in '\u{..}', e.g. '\u{12'.
        UnclosedUnicodeEscape,
        /// '\u{_12}'
        LeadingUnderscoreUnicodeEscape,
        /// More than 6 characters in '\u{..}', e.g. '\u{10FFFF_FF}'
        OverlongUnicodeEscape,
        /// Invalid in-bound unicode character code, e.g. '\u{DFFF}'.
        LoneSurrogateUnicodeEscape,
        /// Out of bounds unicode character code, e.g. '\u{FFFFFF}'.
        OutOfRangeUnicodeEscape,

        /// Unicode escape code in byte literal.
        UnicodeEscapeInByte,
        /// Non-ascii character in byte literal, byte string literal, or raw byte string literal.
        NonAsciiCharInByte,

        // `\0` in a C string literal.
        NulInCStr,

        /// After a line ending with '\', the next line contains whitespace
        /// characters that are not skipped.
        UnskippedWhitespaceWarning,

        /// After a line ending with '\', multiple lines are skipped.
        MultipleSkippedLinesWarning,
    }

    impl EscapeError {
        /// Returns true for actual errors, as opposed to warnings.
        pub fn _is_fatal(&self) -> bool {
            !matches!(
                self,
                EscapeError::UnskippedWhitespaceWarning | EscapeError::MultipleSkippedLinesWarning
            )
        }
    }

    /// Takes a contents of a char literal (without quotes), and returns an
    /// unescaped char or an error.
    pub fn unescape_char(src: &str) -> Result<char, EscapeError> {
        unescape_char_or_byte(&mut src.chars(), Mode::Char)
    }

    /// Takes a contents of a string literal (without quotes), and returns the
    /// unescaped string or an error.
    pub fn unescape_str(src: &str) -> Result<String, EscapeError> {
        let mut out = String::with_capacity(src.len());
        let mut chars = src.chars();
        while let Some(c) = chars.next() {
            let c = match c {
                '\\' => scan_escape(&mut chars, Mode::Str)?,
                '\r' => return Err(EscapeError::BareCarriageReturn),
                _ => ascii_check(c, Mode::Str.allow_unicode_chars())?,
            };
            out.push(c);
        }
        Ok(out)
    }

    /// What kind of literal do we parse.
    #[derive(Debug, Clone, Copy, PartialEq)]
    #[allow(unused)]
    pub enum Mode {
        Char,

        Byte,

        Str,
        RawStr,

        ByteStr,
        RawByteStr,

        CStr,
        RawCStr,
    }

    #[allow(unused)]
    impl Mode {
        pub fn in_double_quotes(self) -> bool {
            use Mode::*;
            match self {
                Str | RawStr | ByteStr | RawByteStr | CStr | RawCStr => true,
                Char | Byte => false,
            }
        }

        /// Are `\x80`..`\xff` allowed?
        fn allow_high_bytes(self) -> bool {
            use Mode::*;
            match self {
                Char | Str => false,
                Byte | ByteStr | CStr => true,
                RawStr | RawByteStr | RawCStr => unreachable!(),
            }
        }

        /// Are unicode (non-ASCII) chars allowed?
        #[inline]
        fn allow_unicode_chars(self) -> bool {
            use Mode::*;
            match self {
                Byte | ByteStr | RawByteStr => false,
                Char | Str | RawStr | CStr | RawCStr => true,
            }
        }

        /// Are unicode escapes (`\u`) allowed?
        fn allow_unicode_escapes(self) -> bool {
            use Mode::*;

            match self {
                Byte | ByteStr => false,
                Char | Str | CStr => true,
                RawByteStr | RawStr | RawCStr => unreachable!(),
            }
        }

        pub fn prefix_noraw(self) -> &'static str {
            use Mode::*;
            match self {
                Char | Str | RawStr => "",
                Byte | ByteStr | RawByteStr => "b",
                CStr | RawCStr => "c",
            }
        }
    }

    fn scan_escape<T: From<char> + From<u8>>(
        chars: &mut std::str::Chars<'_>,
        mode: Mode,
    ) -> Result<T, EscapeError> {
        // Previous character was '\\', unescape what follows.
        let res: char = match chars.next().ok_or(EscapeError::LoneSlash)? {
            '"' => '"',
            'n' => '\n',
            'r' => '\r',
            't' => '\t',
            '\\' => '\\',
            '\'' => '\'',
            '0' => '\0',
            'x' => {
                // Parse hexadecimal character code.

                let hi = chars.next().ok_or(EscapeError::TooShortHexEscape)?;
                let hi = hi.to_digit(16).ok_or(EscapeError::InvalidCharInHexEscape)?;

                let lo = chars.next().ok_or(EscapeError::TooShortHexEscape)?;
                let lo = lo.to_digit(16).ok_or(EscapeError::InvalidCharInHexEscape)?;

                let value = (hi * 16 + lo) as u8;

                return if !mode.allow_high_bytes() && !value.is_ascii() {
                    Err(EscapeError::OutOfRangeHexEscape)
                } else {
                    // This may be a high byte, but that will only happen if `T` is
                    // `MixedUnit`, because of the `allow_high_bytes` check above.
                    Ok(T::from(value))
                };
            }
            'u' => return scan_unicode(chars, mode.allow_unicode_escapes()).map(T::from),
            _ => return Err(EscapeError::InvalidEscape),
        };
        Ok(T::from(res))
    }

    fn scan_unicode(
        chars: &mut std::str::Chars<'_>,
        allow_unicode_escapes: bool,
    ) -> Result<char, EscapeError> {
        // We've parsed '\u', now we have to parse '{..}'.

        if chars.next() != Some('{') {
            return Err(EscapeError::NoBraceInUnicodeEscape);
        }

        // First character must be a hexadecimal digit.
        let mut n_digits = 1;
        let mut value: u32 = match chars.next().ok_or(EscapeError::UnclosedUnicodeEscape)? {
            '_' => return Err(EscapeError::LeadingUnderscoreUnicodeEscape),
            '}' => return Err(EscapeError::EmptyUnicodeEscape),
            c => c
                .to_digit(16)
                .ok_or(EscapeError::InvalidCharInUnicodeEscape)?,
        };

        // First character is valid, now parse the rest of the number
        // and closing brace.
        loop {
            match chars.next() {
                None => return Err(EscapeError::UnclosedUnicodeEscape),
                Some('_') => continue,
                Some('}') => {
                    if n_digits > 6 {
                        return Err(EscapeError::OverlongUnicodeEscape);
                    }

                    // Incorrect syntax has higher priority for error reporting
                    // than unallowed value for a literal.
                    if !allow_unicode_escapes {
                        return Err(EscapeError::UnicodeEscapeInByte);
                    }

                    break std::char::from_u32(value).ok_or({
                        if value > 0x10FFFF {
                            EscapeError::OutOfRangeUnicodeEscape
                        } else {
                            EscapeError::LoneSurrogateUnicodeEscape
                        }
                    });
                }
                Some(c) => {
                    let digit: u32 = c
                        .to_digit(16)
                        .ok_or(EscapeError::InvalidCharInUnicodeEscape)?;
                    n_digits += 1;
                    if n_digits > 6 {
                        // Stop updating value since we're sure that it's incorrect already.
                        continue;
                    }
                    value = value * 16 + digit;
                }
            };
        }
    }

    #[inline]
    fn ascii_check(c: char, allow_unicode_chars: bool) -> Result<char, EscapeError> {
        if allow_unicode_chars || c.is_ascii() {
            Ok(c)
        } else {
            Err(EscapeError::NonAsciiCharInByte)
        }
    }

    fn unescape_char_or_byte(
        chars: &mut std::str::Chars<'_>,
        mode: Mode,
    ) -> Result<char, EscapeError> {
        let c = chars.next().ok_or(EscapeError::ZeroChars)?;
        let res = match c {
            '\\' => scan_escape(chars, mode),
            '\n' | '\t' | '\'' => Err(EscapeError::EscapeOnlyChar),
            '\r' => Err(EscapeError::BareCarriageReturn),
            _ => ascii_check(c, mode.allow_unicode_chars()),
        }?;
        if chars.next().is_some() {
            return Err(EscapeError::MoreThanOneChar);
        }
        Ok(res)
    }
}
