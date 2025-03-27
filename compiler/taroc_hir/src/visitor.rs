use crate::{
    AnonConst, Attribute, BindingPattern, BindingPatternKind, Block, ClosureExpression,
    Declaration, DeclarationKind, Expression, ExpressionArgument, ExpressionKind, FieldDefinition,
    File, Function, FunctionParameter, FunctionPrototype, FunctionSignature, Generics, Label,
    Local, MatchingPattern, MatchingPatternKind, MethodCall, Module, Package, Path, PathSegment,
    Statement, StatementKind, Type, TypeArguments, TypeKind, TypeParameter, TypeParameterKind,
    TypeParameters, Variant, VariantKind,
};
use std::ops::ControlFlow;
use taroc_span::Identifier;

use super::{
    ComputedProperty, DeclarationContext, GenericBound, GenericBounds, GenericRequirement,
    GenericRequirementList, GenericWhereClause, NodeID, PathTree,
};

pub trait VisitorResult {
    type Residual;
    fn output() -> Self;
    fn from_residual(residual: Self::Residual) -> Self;
    fn from_branch(b: ControlFlow<Self::Residual>) -> Self;
    fn branch(self) -> ControlFlow<Self::Residual>;
}

impl VisitorResult for () {
    #[cfg(feature = "nightly")]
    type Residual = !;

    #[cfg(not(feature = "nightly"))]
    type Residual = core::convert::Infallible;

    fn output() -> Self {}
    fn from_residual(_: Self::Residual) -> Self {}
    fn from_branch(_: ControlFlow<Self::Residual>) -> Self {}
    fn branch(self) -> ControlFlow<Self::Residual> {
        ControlFlow::Continue(())
    }
}

#[macro_export]
macro_rules! try_visit {
    ($e:expr) => {
        match $crate::visitor::VisitorResult::branch($e) {
            core::ops::ControlFlow::Continue(()) => (),
            #[allow(unreachable_code)]
            core::ops::ControlFlow::Break(r) => {
                return $crate::visitor::VisitorResult::from_residual(r);
            }
        }
    };
}

#[macro_export]
macro_rules! visit_optional {
    ($visitor: expr, $method: ident, $opt: expr $(, $($extra_args: expr),* )?) => {
        if let Some(x) = $opt {
            $crate::try_visit!($visitor.$method(x $(, $($extra_args,)* )?));
        }
    }
}

#[macro_export]
macro_rules! walk_list {
    ($visitor: expr, $method: ident, $list: expr $(, $($extra_args: expr),* )?) => {
        for elem in $list {
            $crate::try_visit!($visitor.$method(elem $(, $($extra_args,)* )?));
        }
    }
}

#[macro_export]
macro_rules! walk_visitable_list {
    ($visitor: expr, $list: expr $(, $($extra_args: expr),* )?) => {
        for elem in $list {
            $crate::try_visit!(elem.visit_with($visitor $(, $($extra_args,)* )?));
        }
    }
}

impl<T> VisitorResult for ControlFlow<T> {
    type Residual = T;

    fn output() -> Self {
        ControlFlow::Continue(())
    }
    fn from_residual(residual: Self::Residual) -> Self {
        ControlFlow::Break(residual)
    }
    fn from_branch(b: Self) -> Self {
        b
    }
    fn branch(self) -> Self {
        self
    }
}

pub trait HirVisitor: Sized {
    type Result: VisitorResult = ();
    fn visit_ident(&mut self, _: &Identifier) -> Self::Result {
        Self::Result::output()
    }
    fn visit_package(&mut self, p: &Package) -> Self::Result {
        walk_package(self, p)
    }
    fn visit_module(&mut self, m: &Module) -> Self::Result {
        walk_module(self, m)
    }
    fn visit_file(&mut self, file: &File) -> Self::Result {
        walk_file(self, file)
    }

    fn visit_declaration(&mut self, d: &Declaration, c: DeclarationContext) -> Self::Result {
        walk_declaration(self, d, c)
    }

    fn visit_statement(&mut self, s: &Statement) -> Self::Result {
        walk_statement(self, s)
    }
    fn visit_expression(&mut self, e: &Expression) -> Self::Result {
        walk_expression(self, e)
    }
    fn visit_type(&mut self, ty: &Type) -> Self::Result {
        walk_type(self, ty)
    }

    fn visit_matching_pattern(&mut self, p: &MatchingPattern) -> Self::Result {
        walk_matching_pattern(self, p)
    }
    fn visit_binding_pattern(&mut self, p: &BindingPattern) -> Self::Result {
        walk_binding_pattern(self, p)
    }

    fn visit_import(&mut self, i: &PathTree, id: NodeID) -> Self::Result {
        walk_import(self, i, id)
    }

    fn visit_export(&mut self, i: &PathTree, id: NodeID) -> Self::Result {
        walk_export(self, i, id)
    }

    fn visit_path_tree(
        &mut self,
        node: &PathTree,
        id: NodeID,
        _is_nested: bool,
        is_import: bool,
    ) -> Self::Result {
        walk_path_tree(self, node, id, is_import)
    }

    fn visit_attribute(&mut self, attr: &Attribute) -> Self::Result {
        walk_attribute(self, attr)
    }

    fn visit_generics(&mut self, g: &Generics) -> Self::Result {
        walk_generics(self, g)
    }
    fn visit_type_parameters(&mut self, t: &TypeParameters) -> Self::Result {
        walk_type_parameters(self, t)
    }
    fn visit_type_parameter(&mut self, t: &TypeParameter) -> Self::Result {
        walk_type_parameter(self, t)
    }
    fn visit_type_parameter_bounds(&mut self, t: &Vec<Path>) -> Self::Result {
        walk_type_parameter_bounds(self, t)
    }
    fn visit_label(&mut self, l: &Label) -> Self::Result {
        walk_label(self, l)
    }

    fn visit_function(&mut self, f: &Function) -> Self::Result {
        walk_function(self, f)
    }

    fn visit_function_signature(&mut self, f: &FunctionSignature) -> Self::Result {
        walk_function_signature(self, f)
    }

    fn visit_function_prototype(&mut self, f: &FunctionPrototype) -> Self::Result {
        walk_function_prototype(self, f)
    }

    fn visit_closure(&mut self, _c: &ClosureExpression) -> Self::Result {
        Self::Result::output()
    }
    fn visit_function_parameter(&mut self, f: &FunctionParameter) -> Self::Result {
        walk_function_parameter(self, f)
    }
    fn visit_local(&mut self, l: &Local) -> Self::Result {
        walk_local(self, l)
    }
    fn visit_block(&mut self, b: &Block) -> Self::Result {
        walk_block(self, b)
    }
    fn visit_anon_const(&mut self, c: &AnonConst) -> Self::Result {
        walk_anon_const(self, c)
    }

    fn visit_field_definition(&mut self, f: &FieldDefinition) -> Self::Result {
        walk_field_definition(self, f)
    }
    fn visit_variant(&mut self, v: &Variant) -> Self::Result {
        walk_variant(self, v)
    }
    fn visit_variant_kind(&mut self, k: &VariantKind) -> Self::Result {
        walk_variant_kind(self, k)
    }

    fn visit_path(&mut self, p: &Path) -> Self::Result {
        walk_path(self, p)
    }
    fn visit_path_segment(&mut self, p: &PathSegment) -> Self::Result {
        walk_path_segment(self, p)
    }

    fn visit_type_arguments(&mut self, t: &TypeArguments) -> Self::Result {
        walk_type_arguments(self, t)
    }

    fn visit_expression_argument(&mut self, e: &ExpressionArgument) -> Self::Result {
        walk_expression_argument(self, e)
    }

    fn visit_generic_where_clause(&mut self, n: &GenericWhereClause) -> Self::Result {
        walk_generic_where_clause(self, n)
    }

    fn visit_generic_requirement_list(&mut self, n: &GenericRequirementList) -> Self::Result {
        walk_generic_requirement_list(self, n)
    }

    fn visit_generic_requirement(&mut self, n: &GenericRequirement) -> Self::Result {
        walk_generic_requirement(self, n)
    }

    fn visit_generic_bounds(&mut self, n: &GenericBounds) -> Self::Result {
        walk_generic_bounds(self, n)
    }

    fn visit_generic_bound(&mut self, n: &GenericBound) -> Self::Result {
        walk_generic_bound(self, n)
    }

    fn visit_computed_property(&mut self, n: &ComputedProperty) -> Self::Result {
        walk_computed_property(self, n)
    }
}

pub fn walk_package<V: HirVisitor>(visitor: &mut V, package: &Package) -> V::Result {
    visitor.visit_module(&package.root)
}

pub fn walk_module<V: HirVisitor>(visitor: &mut V, module: &Module) -> V::Result {
    let Module {
        files, submodules, ..
    } = module;
    walk_list!(visitor, visit_module, submodules);
    walk_list!(visitor, visit_file, files);
    V::Result::output()
}

pub fn walk_file<V: HirVisitor>(visitor: &mut V, file: &File) -> V::Result {
    let File { declarations, .. } = file;
    walk_list!(
        visitor,
        visit_declaration,
        declarations,
        DeclarationContext::Module
    );
    V::Result::output()
}

pub fn walk_declaration<V: HirVisitor>(
    visitor: &mut V,
    declaration: &Declaration,
    _context: DeclarationContext,
) -> V::Result {
    walk_list!(visitor, visit_attribute, &declaration.attributes);
    visitor.visit_ident(&declaration.identifier);

    match &declaration.kind {
        DeclarationKind::Function(f) => {
            try_visit!(visitor.visit_function(f));
        }
        DeclarationKind::Constructor(function, _) => {
            try_visit!(visitor.visit_function(function));
        }
        DeclarationKind::Operator(_, function) => {
            try_visit!(visitor.visit_function(function));
        }
        DeclarationKind::Variable(decl) => {
            try_visit!(visitor.visit_local(decl))
        }
        DeclarationKind::Import(i) => {
            try_visit!(visitor.visit_import(i, declaration.id));
        }
        DeclarationKind::Export(i) => {
            try_visit!(visitor.visit_export(i, declaration.id));
        }
        DeclarationKind::Extend(extension) => {
            try_visit!(visitor.visit_path(&extension.ty.path));
            walk_list!(
                visitor,
                visit_declaration,
                &extension.declarations,
                DeclarationContext::Extend
            )
        }
        DeclarationKind::TypeAlias(ty) => {
            try_visit!(visitor.visit_generics(&ty.generics));
            visit_optional!(visitor, visit_type, &ty.ty);
        }
        DeclarationKind::Extern(node) => {
            walk_list!(
                visitor,
                visit_declaration,
                &node.declarations,
                DeclarationContext::Extern
            )
        }
        DeclarationKind::Namespace(node) => {
            walk_list!(
                visitor,
                visit_declaration,
                &node.declarations,
                DeclarationContext::Namespace
            )
        }
        DeclarationKind::Bridge(_) => todo!(),
        DeclarationKind::Computed(node) => {
            try_visit!(visitor.visit_computed_property(node))
        }
        DeclarationKind::AssociatedType => {}
        DeclarationKind::Constant(..) => todo!(),
        DeclarationKind::EnumCase(node) => {
            walk_list!(visitor, visit_variant, &node.members)
        }
        DeclarationKind::DefinedType(node) => {
            try_visit!(visitor.visit_generics(&node.generics));
            let ctx = match &node.kind {
                crate::DefinedTypeKind::Struct => DeclarationContext::Struct,
                crate::DefinedTypeKind::Enum => DeclarationContext::Enum,
                crate::DefinedTypeKind::Interface => DeclarationContext::Interface,
            };
            walk_list!(visitor, visit_declaration, &node.declarations, ctx)
        }
    }

    V::Result::output()
}

pub fn walk_statement<V: HirVisitor>(visitor: &mut V, s: &Statement) -> V::Result {
    match &s.kind {
        StatementKind::Declaration(decl) => {
            try_visit!(visitor.visit_declaration(decl, DeclarationContext::Statement));
        }
        StatementKind::Expression(expr) => {
            try_visit!(visitor.visit_expression(expr))
        }
        StatementKind::Variable(local) => {
            try_visit!(visitor.visit_local(local))
        }
        StatementKind::Break(label) => {
            visit_optional!(visitor, visit_ident, label);
        }
        StatementKind::Continue(label) => {
            visit_optional!(visitor, visit_ident, label);
        }
        StatementKind::Return(expr) => {
            visit_optional!(visitor, visit_expression, expr);
        }
        StatementKind::Loop(label, block) => {
            visit_optional!(visitor, visit_label, label);
            try_visit!(visitor.visit_block(block));
        }
        StatementKind::Defer(block) => {
            try_visit!(visitor.visit_block(block));
        }
    }

    V::Result::output()
}
pub fn walk_expression<V: HirVisitor>(visitor: &mut V, expr: &Expression) -> V::Result {
    match &expr.kind {
        ExpressionKind::Path(path) => {
            try_visit!(visitor.visit_path(path))
        }
        ExpressionKind::Array(expressions) => {
            walk_list!(visitor, visit_expression, expressions)
        }
        ExpressionKind::Tuple(expressions) => {
            walk_list!(visitor, visit_expression, expressions)
        }
        ExpressionKind::If(..) => {
            // try_visit!(visitor.visit_if_chain(if_chain));
        }
        ExpressionKind::FunctionCall(caller, args) => {
            try_visit!(visitor.visit_expression(caller));
            walk_list!(visitor, visit_expression_argument, args);
        }
        ExpressionKind::MethodCall(method_call) => {
            let MethodCall {
                receiver,
                method,
                arguments,
                ..
            } = method_call;
            try_visit!(visitor.visit_expression(receiver));
            try_visit!(visitor.visit_path_segment(method));
            walk_list!(visitor, visit_expression_argument, arguments);
        }
        ExpressionKind::Binary(_, lhs, rhs) => {
            try_visit!(visitor.visit_expression(lhs));
            try_visit!(visitor.visit_expression(rhs));
        }
        ExpressionKind::Unary(_, expression) => {
            try_visit!(visitor.visit_expression(expression));
        }
        ExpressionKind::FieldAccess(expr, field) => {
            try_visit!(visitor.visit_expression(expr));
            try_visit!(visitor.visit_path_segment(field));
        }
        ExpressionKind::TupleAccess(expr, _) => {
            try_visit!(visitor.visit_expression(expr));
        }
        ExpressionKind::Subscript(invoker, args) => {
            try_visit!(visitor.visit_expression(invoker));
            walk_list!(visitor, visit_expression_argument, args);
        }
        ExpressionKind::AssignOp(_, lhs, rhs) => {
            try_visit!(visitor.visit_expression(lhs));
            try_visit!(visitor.visit_expression(rhs));
        }
        ExpressionKind::CastAs(expr, ty) => {
            try_visit!(visitor.visit_expression(expr));
            try_visit!(visitor.visit_type(ty));
        }
        ExpressionKind::Assign(lhs, rhs) => {
            try_visit!(visitor.visit_expression(lhs));
            try_visit!(visitor.visit_expression(rhs));
        }
        ExpressionKind::Literal(_) => {}
        ExpressionKind::Await(expr) => {
            try_visit!(visitor.visit_expression(expr));
        }

        ExpressionKind::Closure(func) => {
            try_visit!(visitor.visit_closure(func))
        }
        ExpressionKind::MatchBinding(..) => todo!(),
        ExpressionKind::Malformed => {}
        ExpressionKind::InferMemberPath(_) => todo!(),
        ExpressionKind::Block(block) => {
            try_visit!(visitor.visit_block(block));
        }
    }
    V::Result::output()
}
pub fn walk_type<V: HirVisitor>(visitor: &mut V, ty: &Type) -> V::Result {
    let Type { kind, .. } = ty;
    match kind {
        TypeKind::Pointer(ty, _) => {
            try_visit!(visitor.visit_type(ty));
        }
        TypeKind::Reference(ty, _) => {
            try_visit!(visitor.visit_type(ty));
        }
        TypeKind::Tuple(tys) => {
            walk_list!(visitor, visit_type, tys);
        }
        TypeKind::Path(path) => {
            try_visit!(visitor.visit_path(path));
        }
        TypeKind::Array { element, .. } => {
            try_visit!(visitor.visit_type(element));
        }
        TypeKind::Function { inputs, output, .. } => {
            walk_list!(visitor, visit_type, inputs);
            visit_optional!(visitor, visit_type, output);
        }
        TypeKind::ImplicitSelf => {}
        TypeKind::InferedClosureParameter => {}
        TypeKind::SomeOrAny(_, ty) => {
            try_visit!(visitor.visit_type(ty));
        }
        TypeKind::Composite(items) => {
            walk_list!(visitor, visit_type, items);
        }
    }
    V::Result::output()
}
pub fn walk_matching_pattern<V: HirVisitor>(
    visitor: &mut V,
    pattern: &MatchingPattern,
) -> V::Result {
    match &pattern.kind {
        MatchingPatternKind::Literal(lit) => {
            try_visit!(visitor.visit_anon_const(lit));
        }
        MatchingPatternKind::Binding(ident) => {
            try_visit!(visitor.visit_ident(ident));
        }
        MatchingPatternKind::Wildcard => {}
        MatchingPatternKind::Path(path) => {
            try_visit!(visitor.visit_path(path));
        }
        MatchingPatternKind::Tuple(pats, _) => {
            walk_list!(visitor, visit_matching_pattern, pats);
        }
        MatchingPatternKind::Or(pats, _) => {
            walk_list!(visitor, visit_matching_pattern, pats);
        }
        MatchingPatternKind::Rest => todo!(),
        MatchingPatternKind::PathTuple(..) => todo!(),
        MatchingPatternKind::PathStruct(..) => todo!(),
    }

    V::Result::output()
}
pub fn walk_binding_pattern<V: HirVisitor>(visitor: &mut V, pattern: &BindingPattern) -> V::Result {
    match &pattern.kind {
        BindingPatternKind::Wildcard => {}
        BindingPatternKind::Identifier(ident) => {
            try_visit!(visitor.visit_ident(ident));
        }
        BindingPatternKind::Tuple(pats) => {
            walk_list!(visitor, visit_binding_pattern, pats);
        }
    }

    V::Result::output()
}
pub fn walk_import<V: HirVisitor>(visitor: &mut V, tree: &PathTree, id: NodeID) -> V::Result {
    try_visit!(visitor.visit_path_tree(tree, id, false, true));
    V::Result::output()
}

pub fn walk_export<V: HirVisitor>(visitor: &mut V, tree: &PathTree, id: NodeID) -> V::Result {
    try_visit!(visitor.visit_path_tree(tree, id, false, false));
    V::Result::output()
}

pub fn walk_path_tree<V: HirVisitor>(
    visitor: &mut V,
    tree: &PathTree,
    _id: NodeID,
    is_import: bool,
) -> V::Result {
    try_visit!(visitor.visit_path(&tree.root));
    match &tree.node {
        super::PathTreeNode::Glob => {}
        super::PathTreeNode::Simple { .. } => {}
        super::PathTreeNode::Nested { nodes, .. } => {
            for (node, id) in nodes {
                try_visit!(visitor.visit_path_tree(node, *id, true, is_import))
            }
        }
    }
    V::Result::output()
}
pub fn walk_attribute<V: HirVisitor>(_visitor: &mut V, _attribute: &Attribute) -> V::Result {
    V::Result::output()
}
pub fn walk_type_parameters<V: HirVisitor>(
    visitor: &mut V,
    parameters: &TypeParameters,
) -> V::Result {
    walk_list!(visitor, visit_type_parameter, &parameters.parameters);
    V::Result::output()
}
pub fn walk_type_parameter<V: HirVisitor>(visitor: &mut V, parameter: &TypeParameter) -> V::Result {
    try_visit!(visitor.visit_ident(&parameter.identifier));
    match &parameter.kind {
        TypeParameterKind::Constant { default, ty } => {
            try_visit!(visitor.visit_type(ty));
            visit_optional!(visitor, visit_anon_const, default);
        }
        TypeParameterKind::Type { default } => {
            visit_optional!(visitor, visit_type, default);
        }
    }
    V::Result::output()
}
pub fn walk_type_parameter_bounds<V: HirVisitor>(visitor: &mut V, bounds: &Vec<Path>) -> V::Result {
    walk_list!(visitor, visit_path, bounds);
    V::Result::output()
}
pub fn walk_label<V: HirVisitor>(visitor: &mut V, label: &Label) -> V::Result {
    try_visit!(visitor.visit_ident(&label.identifier));
    V::Result::output()
}

pub fn walk_closure<V: HirVisitor>(_visitor: &mut V) {
    todo!()
}
pub fn walk_function_parameter<V: HirVisitor>(
    visitor: &mut V,
    parameter: &FunctionParameter,
) -> V::Result {
    let FunctionParameter {
        name,
        annotated_type,
        default_value,
        ..
    } = parameter;

    try_visit!(visitor.visit_ident(name));
    try_visit!(visitor.visit_type(annotated_type));
    visit_optional!(visitor, visit_expression, default_value);
    V::Result::output()
}
pub fn walk_local<V: HirVisitor>(visitor: &mut V, local: &Local) -> V::Result {
    try_visit!(visitor.visit_binding_pattern(&local.pattern));
    visit_optional!(visitor, visit_type, &local.ty);
    visit_optional!(visitor, visit_expression, &local.initializer);
    V::Result::output()
}

pub fn walk_block<V: HirVisitor>(visitor: &mut V, block: &Block) -> V::Result {
    walk_list!(visitor, visit_statement, &block.statements);
    V::Result::output()
}
pub fn walk_anon_const<V: HirVisitor>(visitor: &mut V, anon_const: &AnonConst) -> V::Result {
    try_visit!(visitor.visit_expression(&anon_const.value));
    V::Result::output()
}
pub fn walk_field_definition<V: HirVisitor>(
    visitor: &mut V,
    field_definition: &FieldDefinition,
) -> V::Result {
    try_visit!(visitor.visit_ident(&field_definition.identifier));
    try_visit!(visitor.visit_type(&field_definition.ty));
    V::Result::output()
}
pub fn walk_variant<V: HirVisitor>(visitor: &mut V, variant: &Variant) -> V::Result {
    try_visit!(visitor.visit_ident(&variant.identifier));
    try_visit!(visitor.visit_variant_kind(&variant.kind));
    visit_optional!(visitor, visit_anon_const, &variant.discriminant);
    V::Result::output()
}
pub fn walk_variant_kind<V: HirVisitor>(visitor: &mut V, variant_kind: &VariantKind) -> V::Result {
    match variant_kind {
        VariantKind::Tuple(_, fields) => {
            walk_list!(visitor, visit_field_definition, fields);
        }
        VariantKind::Struct(_, fields) => {
            walk_list!(visitor, visit_field_definition, fields);
        }
        _ => {}
    }
    V::Result::output()
}

pub fn walk_path<V: HirVisitor>(visitor: &mut V, path: &Path) -> V::Result {
    walk_list!(visitor, visit_path_segment, &path.segments);
    V::Result::output()
}

pub fn walk_path_segment<V: HirVisitor>(visitor: &mut V, path_segment: &PathSegment) -> V::Result {
    try_visit!(visitor.visit_ident(&path_segment.identifier));
    visit_optional!(visitor, visit_type_arguments, &path_segment.arguments);
    V::Result::output()
}

pub fn walk_type_arguments<V: HirVisitor>(visitor: &mut V, arguments: &TypeArguments) -> V::Result {
    let tys = &arguments.arguments;
    walk_list!(visitor, visit_type, tys);
    V::Result::output()
}

pub fn walk_expression_argument<V: HirVisitor>(
    visitor: &mut V,
    arg: &ExpressionArgument,
) -> V::Result {
    visit_optional!(visitor, visit_label, &arg.label);
    try_visit!(visitor.visit_expression(&arg.expression));
    V::Result::output()
}

pub fn walk_function<V: HirVisitor>(visitor: &mut V, function: &Function) -> V::Result {
    try_visit!(visitor.visit_generics(&function.generics));
    try_visit!(visitor.visit_function_signature(&function.signature));
    visit_optional!(visitor, visit_block, &function.block);
    V::Result::output()
}

pub fn walk_function_signature<V: HirVisitor>(
    visitor: &mut V,
    signature: &FunctionSignature,
) -> V::Result {
    try_visit!(visitor.visit_function_prototype(&signature.prototype));
    V::Result::output()
}

pub fn walk_function_prototype<V: HirVisitor>(
    visitor: &mut V,
    func: &FunctionPrototype,
) -> V::Result {
    walk_list!(visitor, visit_function_parameter, &func.inputs);
    visit_optional!(visitor, visit_type, &func.output);
    V::Result::output()
}

pub fn walk_generics<V: HirVisitor>(visitor: &mut V, node: &Generics) -> V::Result {
    visit_optional!(visitor, visit_type_parameters, &node.type_parameters);
    visit_optional!(visitor, visit_generic_where_clause, &node.where_clause);
    V::Result::output()
}

pub fn walk_generic_where_clause<V: HirVisitor>(
    visitor: &mut V,
    node: &GenericWhereClause,
) -> V::Result {
    try_visit!(visitor.visit_generic_requirement_list(&node.requirements));
    V::Result::output()
}

pub fn walk_generic_requirement_list<V: HirVisitor>(
    visitor: &mut V,
    node: &GenericRequirementList,
) -> V::Result {
    walk_list!(visitor, visit_generic_requirement, node);
    V::Result::output()
}

pub fn walk_generic_requirement<V: HirVisitor>(
    visitor: &mut V,
    node: &GenericRequirement,
) -> V::Result {
    match &node {
        GenericRequirement::SameTypeRequirement(c) => {
            try_visit!(visitor.visit_path(&c.bounded_type.path));
            try_visit!(visitor.visit_type(&c.bound));
        }
        GenericRequirement::ConformanceRequirement(c) => {
            try_visit!(visitor.visit_path(&c.bounded_type.path));
            try_visit!(visitor.visit_generic_bounds(&c.bounds));
        }
    }
    V::Result::output()
}

pub fn walk_generic_bounds<V: HirVisitor>(visitor: &mut V, node: &GenericBounds) -> V::Result {
    walk_list!(visitor, visit_generic_bound, node);
    V::Result::output()
}

pub fn walk_generic_bound<V: HirVisitor>(visitor: &mut V, node: &GenericBound) -> V::Result {
    try_visit!(visitor.visit_path(&node.path.path));
    V::Result::output()
}

pub fn walk_computed_property<V: HirVisitor>(
    visitor: &mut V,
    node: &ComputedProperty,
) -> V::Result {
    try_visit!(visitor.visit_type(&node.ty));
    try_visit!(visitor.visit_block(&node.block));
    V::Result::output()
}
