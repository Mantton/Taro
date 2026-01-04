use crate::{
    ast::{self, Identifier},
    compile::context::GlobalContext,
    error::CompileResult,
    hir::{self, StdType},
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
}

impl<'a, 'c> Actor<'a, 'c> {
    fn new(context: GlobalContext<'c>, resolutions: &'a ResolutionOutput<'c>) -> Actor<'a, 'c> {
        Actor {
            context,
            resolutions,
            next_index: 0,
            node_mapping: Default::default(),
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
            })
            .collect()
    }
}

impl Actor<'_, '_> {
    fn lower_declaration(&mut self, node: ast::Declaration) -> Vec<hir::Declaration> {
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
                    .map(|decl| self.lower_extern_declaration(decl))
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
            ast::DeclarationKind::Extension(node) => {
                hir::DeclarationKind::Extension(self.lower_extension(node))
            }
            ast::DeclarationKind::Operator(..) => unreachable!(),
        };

        vec![hir::Declaration {
            id: self.definition_id(id),
            span,
            identifier,
            kind,
            attributes: self.lower_attributes(attributes),
        }]
    }

    fn lower_extern_declaration(&mut self, node: ast::ExternDeclaration) -> hir::Declaration {
        let ast::Declaration {
            id,
            kind,
            span,
            identifier,
            attributes,
            ..
        } = node;

        let kind = match kind {
            ast::ExternDeclarationKind::Function(node) => {
                let span = node.signature.span;
                hir::DeclarationKind::Function(self.lower_function(node, span))
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
            ast::AssociatedDeclarationKind::Operator(node) => {
                hir::AssociatedDeclarationKind::Operator(self.lower_operator(node))
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
    fn lower_operator(&mut self, node: ast::Operator) -> hir::Operator {
        let span = node.function.signature.span;
        hir::Operator {
            function: self.lower_function(node.function, span),
            kind: node.kind,
        }
    }

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
        match abi.as_str() {
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
    fn lower_extension(&mut self, node: ast::Extension) -> hir::Extension {
        hir::Extension {
            ty: self.lower_type(node.ty),
            generics: self.lower_generics(node.generics),
            conformances: node.conformances.map(|n| self.lower_conformances(n)),
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
                            symbol: Symbol::new("Self"),
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
                identifier: Identifier::new(Symbol::new(name), span),
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
                    ast::ExpressionKind::Literal(lit) => match convert_ast_literal(lit) {
                        Ok(lit) => lit,
                        Err(err) => {
                            self.context.dcx.emit_error(err.into(), Some(value.span));
                            hir::Literal::Nil
                        }
                    },
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
            ast::StatementKind::For(..) => todo!(),
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
    fn lower_expression(&mut self, node: Box<ast::Expression>) -> Box<hir::Expression> {
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
                hir::ExpressionKind::PatternBinding(self.lower_pattern_binding_condition(node))
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
            ast::ExpressionKind::Range(lhs, rhs, inclusive) => {
                // `1..10`
                let foundational = if inclusive {
                    StdType::ClosedRange
                } else {
                    StdType::Range
                };

                let lhs = self.lower_expression(lhs);
                let rhs = self.lower_expression(rhs);
                let identiier = Identifier::new(Symbol::new("Range"), node.span);
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
                let ctor_ident = Identifier::new(Symbol::new("Dictionary"), node.span);
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
                let dictionary_ident = Identifier::new(Symbol::new("__dictionary"), node.span);
                let pattern = hir::Pattern {
                    id: self.next_index(),
                    span: node.span,
                    kind: hir::PatternKind::Binding {
                        name: dictionary_ident,
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

                let insert_ident = Identifier::new(Symbol::new("insert"), node.span);
                for pair in map_pairs {
                    let key = self.lower_expression(pair.key);
                    let value = self.lower_expression(pair.value);

                    let dictionary_path = self.mk_single_segment_resolved_path(
                        dictionary_ident,
                        Resolution::LocalVariable(local_id),
                    );
                    let target =
                        self.mk_expression(hir::ExpressionKind::Path(dictionary_path), node.span);
                    let member = self.mk_expression(
                        hir::ExpressionKind::Member {
                            target,
                            name: insert_ident,
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
            ast::ExpressionKind::Closure(_) => todo!("closures!"),
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

        let (base_id, base_ident) = *parts.first()?;

        let mut last_resolution = self.get_resolution(base_id);
        let mut segments = Vec::with_capacity(parts.len());
        segments.push(hir::PathSegment {
            id: self.next_index(),
            identifier: base_ident,
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
                        identifier: ident,
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

    fn collect_member_chain_parts(
        &self,
        expr: &ast::Expression,
        out: &mut Vec<(ast::NodeID, Identifier)>,
    ) -> Option<()> {
        match &expr.kind {
            ast::ExpressionKind::Identifier(ident) => {
                out.push((expr.id, *ident));
                Some(())
            }
            ast::ExpressionKind::Member { target, name } => {
                self.collect_member_chain_parts(target, out)?;
                out.push((expr.id, *name));
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
                let resolved_path = self.lower_identifier_expression_path(expr.id, *ident);
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
        let result = convert_ast_literal(node);

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
            source: hir::MatchSource::Match,
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

    fn lower_pattern_binding_condition(
        &mut self,
        node: ast::PatternBindingCondition,
    ) -> hir::PatternBindingCondition {
        hir::PatternBindingCondition {
            pattern: self.lower_pattern(node.pattern),
            expression: self.lower_expression(node.expression),
            span: node.span,
        }
    }

    fn lower_optional_pattern_binding(
        &mut self,
        node: ast::PatternBindingCondition,
    ) -> hir::PatternBindingCondition {
        // Transform `let x = opt` into `case .some(x) = opt`
        let inner_pattern = self.lower_pattern(node.pattern);
        let some_ident = Identifier::new(Symbol::new("some"), inner_pattern.span);
        // Create `.some(inner_pattern)`
        let pattern = hir::Pattern {
            id: self.next_index(),
            span: inner_pattern.span,
            kind: hir::PatternKind::PathTuple {
                path: hir::PatternPath::Inferred {
                    name: some_ident,
                    span: inner_pattern.span,
                },
                fields: vec![inner_pattern.clone()],
                field_span: inner_pattern.span,
            },
        };

        hir::PatternBindingCondition {
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
        // case .some(val) => val
        let val_ident = Identifier::new(Symbol::new("val"), span); // synthesized variable
        let val_pattern = hir::Pattern {
            id: self.next_index(),
            span,
            kind: hir::PatternKind::Binding {
                name: val_ident,
                mode: hir::BindingMode::ByValue,
            },
        };
        let some_ident = Identifier::new(Symbol::new("some"), span);
        let some_pattern = hir::Pattern {
            id: self.next_index(),
            span,
            kind: hir::PatternKind::PathTuple {
                path: hir::PatternPath::Inferred {
                    name: some_ident,
                    span,
                },
                fields: vec![val_pattern.clone()],
                field_span: span,
            },
        };

        let val_expr_path = hir::ResolvedPath::Resolved(hir::Path {
            span,
            resolution: Resolution::LocalVariable(val_pattern.id), // Resolves to the binding
            segments: vec![hir::PathSegment {
                id: self.next_index(),
                identifier: val_ident,
                arguments: None,
                span,
                resolution: Resolution::LocalVariable(val_pattern.id),
            }],
        });
        let val_expr = Box::new(hir::Expression {
            id: self.next_index(),
            kind: hir::ExpressionKind::Path(val_expr_path),
            span,
        });

        let some_arm = hir::MatchArm {
            pattern: some_pattern,
            body: val_expr,
            guard: None,
            span,
        };

        // case .none => rhs
        let none_ident = Identifier::new(Symbol::new("none"), span);
        let none_pattern = hir::Pattern {
            id: self.next_index(),
            span,
            kind: hir::PatternKind::Member(hir::PatternPath::Inferred {
                name: none_ident,
                span,
            }),
        };

        let rhs_expr = self.lower_expression(rhs);
        let none_arm = hir::MatchArm {
            pattern: none_pattern,
            body: rhs_expr,
            guard: None,
            span,
        };

        hir::MatchExpression {
            source: hir::MatchSource::OptionalDefault,
            value: lhs,
            arms: vec![some_arm, none_arm],
            kw_span: span,
        }
    }

    fn lower_optional_evaluation(
        &mut self,
        expr: Box<ast::Expression>,
        span: Span,
    ) -> hir::ExpressionKind {
        // Deconstruct the expression to find the `OptionalUnwrap` target.
        // Currently supporting basic `Member` access, e.g., `target?.member`.
        // AST structure: Member { target: OptionalUnwrap(inner_target), name }

        // We need to recursively unwrap to find the `OptionalUnwrap` node if it's nested
        // (e.g. `foo()?.bar`). But `OptionalUnwrap` is essentially a marker that applies to the
        // IMMEDIATE operand's type.

        // For `a?.b`:
        // Expr: Member(target=OptionalUnwrap(a), b)
        // Lower to: match a { .some(tmp) => tmp.b, .none => .none }

        let (target, continuation) = match expr.kind {
            ast::ExpressionKind::Member { target, name } => match target.kind {
                ast::ExpressionKind::OptionalUnwrap(inner) => (
                    inner,
                    Box::new(move |_this: &mut Self, tmp: Box<hir::Expression>| {
                        hir::ExpressionKind::Member { target: tmp, name }
                    })
                        as Box<dyn FnOnce(&mut Self, Box<hir::Expression>) -> hir::ExpressionKind>,
                ),

                _ => {
                    self.context.dcx.emit_error(
                        "optional evaluation expected an optional unwrap".into(),
                        Some(expr.span),
                    );
                    return hir::ExpressionKind::Malformed;
                }
            },
            ast::ExpressionKind::Call(callee, args) => match callee.kind {
                ast::ExpressionKind::OptionalUnwrap(inner) => (
                    inner,
                    Box::new(move |_this: &mut Self, tmp: Box<hir::Expression>| {
                        let lowered_args = _this.lower_expression_arguments(args);
                        hir::ExpressionKind::Call {
                            callee: tmp,
                            arguments: lowered_args,
                        }
                    })
                        as Box<dyn FnOnce(&mut Self, Box<hir::Expression>) -> hir::ExpressionKind>,
                ),
                _ => {
                    self.context.dcx.emit_error(
                        "optional evaluation expected an optional unwrap".into(),
                        Some(expr.span),
                    );
                    return hir::ExpressionKind::Malformed;
                }
            },
            _ => {
                // Fallback for cases we don't support deeply yet or aren't structured as expected.
                // Ideally recursive, but for now simple support.
                self.context.dcx.emit_error(
                    "unsupported expression in optional chain".into(),
                    Some(expr.span),
                );
                return hir::ExpressionKind::Malformed;
            }
        };

        let target_expr = self.lower_expression(target);

        // case .some(tmp)
        let tmp_ident = Identifier::new(Symbol::new("tmp"), span);
        let tmp_pattern = hir::Pattern {
            id: self.next_index(),
            span,
            kind: hir::PatternKind::Binding {
                name: tmp_ident,
                mode: hir::BindingMode::ByValue,
            },
        };
        let some_ident = Identifier::new(Symbol::new("some"), span);
        let tmp_id = tmp_pattern.id;
        let some_pattern = hir::Pattern {
            id: self.next_index(),
            span,
            kind: hir::PatternKind::PathTuple {
                path: hir::PatternPath::Inferred {
                    name: some_ident,
                    span,
                },
                fields: vec![tmp_pattern],
                field_span: span,
            },
        };

        // tmp expr to be used in continuation
        let tmp_expr_path = hir::ResolvedPath::Resolved(hir::Path {
            span,
            resolution: Resolution::LocalVariable(tmp_id),
            segments: vec![hir::PathSegment {
                id: self.next_index(),
                identifier: tmp_ident,
                arguments: None,
                span,
                resolution: Resolution::LocalVariable(tmp_id),
            }],
        });
        let tmp_expr = Box::new(hir::Expression {
            id: self.next_index(),
            kind: hir::ExpressionKind::Path(tmp_expr_path),
            span,
        });

        // Apply continuation to create the specific operation (Member, Call, etc.)
        let continuation_kind = continuation(self, tmp_expr);
        let continuation_expr = Box::new(hir::Expression {
            id: self.next_index(),
            kind: continuation_kind,
            span, // This span might need to be more precise
        });

        let some_arm = hir::MatchArm {
            pattern: some_pattern,
            body: continuation_expr,
            guard: None,
            span,
        };

        // case .none => .none
        let none_ident = Identifier::new(Symbol::new("none"), span);
        let none_pattern = hir::Pattern {
            id: self.next_index(),
            span,
            kind: hir::PatternKind::Member(hir::PatternPath::Inferred {
                name: none_ident,
                span,
            }),
        };
        // Result is .none (inferred)
        let option_ident = Identifier::new(Symbol::new("Option"), span);
        let option_path = hir::Path {
            span,
            resolution: Resolution::Foundation(hir::StdType::Option),
            segments: vec![hir::PathSegment {
                id: self.next_index(),
                identifier: option_ident,
                arguments: None,
                span,
                resolution: Resolution::Foundation(hir::StdType::Option),
            }],
        };
        let option_expr = Box::new(hir::Expression {
            id: self.next_index(), // We need ID for expression
            kind: hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(option_path)),
            span,
        });

        let result_none_expr = Box::new(hir::Expression {
            id: self.next_index(),
            kind: hir::ExpressionKind::Member {
                target: option_expr,
                name: none_ident,
            },
            span,
        });

        let none_arm = hir::MatchArm {
            pattern: none_pattern,
            body: result_none_expr,
            guard: None,
            span,
        };

        hir::ExpressionKind::Match(hir::MatchExpression {
            source: hir::MatchSource::OptionalUnwrap,
            value: target_expr,
            arms: vec![some_arm, none_arm],
            kw_span: span,
        })
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
            identifier,
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
            identifier,
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

fn convert_ast_literal(literal: ast::Literal) -> Result<hir::Literal, String> {
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
            Ok(hir::Literal::String(Symbol::new(&value)))
        }
        ast::Literal::Integer { value, base } => {
            let content = value.replace("_", "");
            u64::from_str_radix(&content, base.radix())
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
