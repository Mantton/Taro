use super::{
    GenericBound, GenericBounds, GenericRequirement, GenericRequirementList, GenericWhereClause,
    NodeID, PathTree,
};
use crate::{
    AnonConst, AssociatedDeclaration, Attribute, Block, ClosureExpression, Declaration,
    DeclarationKind, EnumDefinition, Expression, ExpressionArgument, ExpressionField,
    ExpressionKind, FieldDefinition, File, ForeignDeclaration, Function, FunctionDeclaration,
    FunctionDeclarationKind, FunctionParameter, FunctionPrototype, FunctionSignature, Generics,
    Inheritance, Label, Local, MatchArm, MethodCall, Module, Package, Path, PathSegment, Pattern,
    PatternField, PatternKind, Statement, StatementKind, TaggedPath, Type, TypeArgument,
    TypeArguments, TypeKind, TypeParameter, TypeParameterKind, TypeParameters, Variant,
    VariantKind,
};
use std::ops::ControlFlow;
use taroc_ast_ir::OperatorKind;
use taroc_span::Identifier;

pub enum FunctionContext {
    Free,
    Foreign,
    Assoc(AssocContext),
    AssocOperand(AssocContext, OperatorKind),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AssocContext {
    Interface(NodeID),
    Extend(NodeID),
}

impl AssocContext {
    pub fn node_id(self) -> NodeID {
        match self {
            AssocContext::Interface(node_id) => node_id,
            AssocContext::Extend(node_id) => node_id,
        }
    }
}

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

    fn visit_declaration(&mut self, d: &Declaration) -> Self::Result {
        walk_declaration(self, d)
    }

    fn visit_assoc_declaration(
        &mut self,
        declaration: &AssociatedDeclaration,
        context: AssocContext,
    ) -> Self::Result {
        walk_assoc_declaration(self, declaration, context)
    }

    fn visit_foreign_declaration(&mut self, d: &ForeignDeclaration) -> Self::Result {
        walk_foreign_declaration(self, d)
    }

    fn visit_function_declaration(&mut self, d: &FunctionDeclaration) -> Self::Result {
        walk_function_declaration(self, d)
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

    fn visit_pattern(&mut self, p: &Pattern) -> Self::Result {
        walk_pattern(self, p)
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

    fn visit_function(&mut self, id: NodeID, f: &Function, c: FunctionContext) -> Self::Result {
        walk_function(self, id, f, c)
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
    fn visit_expression_field(&mut self, k: &ExpressionField) -> Self::Result {
        walk_expr_field(self, k)
    }

    fn visit_pattern_field(&mut self, k: &PatternField) -> Self::Result {
        walk_pat_field(self, k)
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

    fn visit_type_argument(&mut self, t: &TypeArgument) -> Self::Result {
        walk_type_argument(self, t)
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

    fn visit_inheritance(&mut self, n: &Inheritance) -> Self::Result {
        walk_inheritance(self, n)
    }

    fn visit_tagged_path(&mut self, node: &TaggedPath) -> Self::Result {
        walk_tagged_path(self, node)
    }

    fn visit_enum_def(&mut self, node: &EnumDefinition) -> Self::Result {
        walk_enum_def(self, node)
    }

    fn visit_match_arm(&mut self, node: &MatchArm) -> Self::Result {
        walk_match_arm(self, node)
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
    walk_list!(visitor, visit_declaration, declarations);
    V::Result::output()
}

pub fn walk_declaration<V: HirVisitor>(visitor: &mut V, declaration: &Declaration) -> V::Result {
    walk_list!(visitor, visit_attribute, &declaration.attributes);
    visitor.visit_ident(&declaration.identifier);

    match &declaration.kind {
        DeclarationKind::Interface(node) => {
            try_visit!(visitor.visit_generics(&node.generics));
            walk_list!(
                visitor,
                visit_assoc_declaration,
                &node.declarations,
                AssocContext::Interface(declaration.id)
            );
        }
        DeclarationKind::Struct(node) => {
            try_visit!(visitor.visit_generics(&node.generics));
            try_visit!(visitor.visit_variant_kind(&node.variant))
        }
        DeclarationKind::Enum(node) => {
            try_visit!(visitor.visit_generics(&node.generics));
            try_visit!(visitor.visit_enum_def(&node))
        }
        DeclarationKind::Function(node) => {
            try_visit!(visitor.visit_function(declaration.id, node, FunctionContext::Free));
        }
        DeclarationKind::Static(node) => {
            try_visit!(visitor.visit_ident(&node.identifier));
            try_visit!(visitor.visit_type(&node.ty));
            visit_optional!(visitor, visit_expression, &node.expr);
        }
        DeclarationKind::Constant(node) => {
            try_visit!(visitor.visit_type(&node.ty));
            visit_optional!(visitor, visit_expression, &node.expr);
        }
        DeclarationKind::Import(node) => {
            try_visit!(visitor.visit_export(node, declaration.id));
        }
        DeclarationKind::Export(node) => {
            try_visit!(visitor.visit_export(node, declaration.id));
        }
        DeclarationKind::TypeAlias(node) => {
            try_visit!(visitor.visit_generics(&node.generics));
            visit_optional!(visitor, visit_type, &node.ty);
        }
        DeclarationKind::Extend(node) => {
            try_visit!(visitor.visit_type(&node.ty));
            try_visit!(visitor.visit_generics(&node.generics));
            walk_list!(
                visitor,
                visit_assoc_declaration,
                &node.declarations,
                AssocContext::Extend(declaration.id)
            );
        }
        DeclarationKind::Namespace(node) => {
            walk_list!(visitor, visit_declaration, &node.declarations)
        }
        DeclarationKind::Extern(node) => {
            walk_list!(visitor, visit_foreign_declaration, &node.declarations,);
        }
        DeclarationKind::Malformed => unreachable!(),
    }

    V::Result::output()
}

pub fn walk_assoc_declaration<V: HirVisitor>(
    visitor: &mut V,
    declaration: &AssociatedDeclaration,
    context: AssocContext,
) -> V::Result {
    walk_list!(visitor, visit_attribute, &declaration.attributes);
    visitor.visit_ident(&declaration.identifier);

    match &declaration.kind {
        crate::AssociatedDeclarationKind::Constant(node) => {
            try_visit!(visitor.visit_type(&node.ty));
            visit_optional!(visitor, visit_expression, &node.expr);
        }
        crate::AssociatedDeclarationKind::Function(node) => {
            try_visit!(visitor.visit_function(
                declaration.id,
                node,
                FunctionContext::Assoc(context)
            ));
        }
        crate::AssociatedDeclarationKind::Type(node) => {
            try_visit!(visitor.visit_generics(&node.generics));
            visit_optional!(visitor, visit_type, &node.ty);
        }
        crate::AssociatedDeclarationKind::Operator(operator_kind, function) => {
            let ctx = FunctionContext::AssocOperand(context, *operator_kind);
            try_visit!(visitor.visit_function(declaration.id, function, ctx));
        }
    }

    V::Result::output()
}

pub fn walk_foreign_declaration<V: HirVisitor>(
    visitor: &mut V,
    declaration: &ForeignDeclaration,
) -> V::Result {
    walk_list!(visitor, visit_attribute, &declaration.attributes);
    visitor.visit_ident(&declaration.identifier);

    match &declaration.kind {
        crate::ForeignDeclarationKind::Function(function) => {
            try_visit!(visitor.visit_function(declaration.id, function, FunctionContext::Foreign));
        }
        crate::ForeignDeclarationKind::Type(node) => {
            try_visit!(visitor.visit_generics(&node.generics));
            visit_optional!(visitor, visit_type, &node.ty);
        }
    }

    V::Result::output()
}

pub fn walk_function_declaration<V: HirVisitor>(
    visitor: &mut V,
    declaration: &FunctionDeclaration,
) -> V::Result {
    walk_list!(visitor, visit_attribute, &declaration.attributes);
    visitor.visit_ident(&declaration.identifier);

    match &declaration.kind {
        FunctionDeclarationKind::Struct(node) => {
            try_visit!(visitor.visit_generics(&node.generics));
            try_visit!(visitor.visit_variant_kind(&node.variant))
        }
        FunctionDeclarationKind::Enum(node) => {
            try_visit!(visitor.visit_generics(&node.generics));
            try_visit!(visitor.visit_enum_def(&node))
        }
        FunctionDeclarationKind::Function(node) => {
            try_visit!(visitor.visit_function(declaration.id, node, FunctionContext::Free));
        }
        FunctionDeclarationKind::Constant(node) => {
            try_visit!(visitor.visit_type(&node.ty));
            visit_optional!(visitor, visit_expression, &node.expr);
        }
        FunctionDeclarationKind::TypeAlias(node) => {
            try_visit!(visitor.visit_generics(&node.generics));
            visit_optional!(visitor, visit_type, &node.ty);
        }
    }

    V::Result::output()
}

pub fn walk_statement<V: HirVisitor>(visitor: &mut V, s: &Statement) -> V::Result {
    match &s.kind {
        StatementKind::Declaration(decl) => {
            try_visit!(visitor.visit_function_declaration(decl));
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
        ExpressionKind::StructLiteral(node) => {
            try_visit!(visitor.visit_path(&node.path));
            walk_list!(visitor, visit_expression_field, &node.fields);
        }
        ExpressionKind::ArrayLiteral(expressions) => {
            walk_list!(visitor, visit_expression, expressions)
        }
        ExpressionKind::Tuple(expressions) => {
            walk_list!(visitor, visit_expression, expressions)
        }
        ExpressionKind::Reference(expression, _) => {
            try_visit!(visitor.visit_expression(expression));
        }
        ExpressionKind::Dereference(expression) => {
            try_visit!(visitor.visit_expression(expression));
        }
        ExpressionKind::If(node) => {
            try_visit!(visitor.visit_expression(&node.condition));
            try_visit!(visitor.visit_expression(&node.then_block));
            visit_optional!(visitor, visit_expression, &node.else_block);
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
        ExpressionKind::Closure(func) => {
            try_visit!(visitor.visit_closure(func))
        }
        ExpressionKind::PatternBinding(..) => todo!(),
        ExpressionKind::Malformed => {}
        ExpressionKind::Block(block) => {
            try_visit!(visitor.visit_block(block));
        }
        ExpressionKind::Await(expression) => {
            try_visit!(visitor.visit_expression(expression));
        }
        ExpressionKind::Match(node) => {
            try_visit!(visitor.visit_expression(&node.value));
            walk_list!(visitor, visit_match_arm, &node.arms);
        }
    }
    V::Result::output()
}
pub fn walk_type<V: HirVisitor>(visitor: &mut V, ty: &Type) -> V::Result {
    let Type { kind, .. } = ty;
    match kind {
        TypeKind::Tuple(tys) => {
            walk_list!(visitor, visit_type, tys);
        }
        TypeKind::Path(path) => {
            try_visit!(visitor.visit_path(path));
        }
        TypeKind::Function { inputs, output, .. } => {
            walk_list!(visitor, visit_type, inputs);
            try_visit!(visitor.visit_type(output));
        }
        TypeKind::Opaque(items) => {
            walk_list!(visitor, visit_tagged_path, items);
        }
        TypeKind::Exisitential(items) => {
            walk_list!(visitor, visit_tagged_path, items);
        }
        TypeKind::Infer => {}
        TypeKind::AnonStruct { fields } => {
            walk_list!(visitor, visit_field_definition, fields);
        }
        TypeKind::Malformed => unreachable!(),
    }
    V::Result::output()
}
pub fn walk_pattern<V: HirVisitor>(visitor: &mut V, pattern: &Pattern) -> V::Result {
    match &pattern.kind {
        PatternKind::Expression(k) => match k {
            crate::PatternExpressionKind::Path(path) => try_visit!(visitor.visit_path(path)),
            crate::PatternExpressionKind::AnonConst(expression) => {
                try_visit!(visitor.visit_expression(expression));
            }
        },
        PatternKind::Identifier(ident) => {
            try_visit!(visitor.visit_ident(ident));
        }
        PatternKind::Wildcard => {}

        PatternKind::Tuple(pats, _) => {
            walk_list!(visitor, visit_pattern, pats);
        }
        PatternKind::Or(pats, _) => {
            walk_list!(visitor, visit_pattern, pats);
        }
        PatternKind::PathTuple(path, pat, _) => {
            try_visit!(visitor.visit_path(path));
            walk_list!(visitor, visit_pattern, pat);
        }
        PatternKind::PathStruct(path, fields, ..) => {
            try_visit!(visitor.visit_path(path));
            walk_list!(visitor, visit_pattern_field, fields);
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

    visit_optional!(visitor, visit_generic_bounds, &parameter.bounds);
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
    try_visit!(visitor.visit_pattern(&local.pattern));
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
        VariantKind::Struct(fields) => {
            walk_list!(visitor, visit_field_definition, fields);
        }
        _ => {}
    }
    V::Result::output()
}

pub fn walk_expr_field<V: HirVisitor>(visitor: &mut V, field: &ExpressionField) -> V::Result {
    try_visit!(visitor.visit_expression(&field.expression));
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
    walk_list!(visitor, visit_type_argument, tys);
    V::Result::output()
}

pub fn walk_type_argument<V: HirVisitor>(visitor: &mut V, argument: &TypeArgument) -> V::Result {
    match argument {
        TypeArgument::Type(ty) => try_visit!(visitor.visit_type(ty)),
        TypeArgument::Const(anon_const) => try_visit!(visitor.visit_anon_const(anon_const)),
    }
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

pub fn walk_function<V: HirVisitor>(
    visitor: &mut V,
    _: NodeID,
    function: &Function,
    _: FunctionContext,
) -> V::Result {
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
    visit_optional!(visitor, visit_inheritance, &node.conformance);
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
            try_visit!(visitor.visit_type(&c.bounded_type));
            try_visit!(visitor.visit_type(&c.bound));
        }
        GenericRequirement::ConformanceRequirement(c) => {
            try_visit!(visitor.visit_type(&c.bounded_type));
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

pub fn walk_inheritance<V: HirVisitor>(visitor: &mut V, node: &Inheritance) -> V::Result {
    walk_list!(visitor, visit_tagged_path, &node.interfaces);
    V::Result::output()
}

pub fn walk_tagged_path<V: HirVisitor>(visitor: &mut V, node: &TaggedPath) -> V::Result {
    try_visit!(visitor.visit_path(&node.path));
    V::Result::output()
}

pub fn walk_enum_def<V: HirVisitor>(visitor: &mut V, node: &EnumDefinition) -> V::Result {
    walk_list!(visitor, visit_variant, &node.variants);
    V::Result::output()
}

pub fn walk_pat_field<V: HirVisitor>(visitor: &mut V, node: &PatternField) -> V::Result {
    try_visit!(visitor.visit_ident(&node.identifier));
    try_visit!(visitor.visit_pattern(&node.pattern));
    V::Result::output()
}

pub fn walk_match_arm<V: HirVisitor>(visitor: &mut V, node: &MatchArm) -> V::Result {
    try_visit!(visitor.visit_pattern(&node.pattern));
    visit_optional!(visitor, visit_expression, &node.guard);
    try_visit!(visitor.visit_expression(&node.body));

    V::Result::output()
}
