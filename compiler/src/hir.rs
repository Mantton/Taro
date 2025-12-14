pub use crate::ast::BinaryOperator;
pub use crate::ast::Label;
pub use crate::ast::Mutability;
pub use crate::ast::OperatorKind;
pub use crate::ast::UnaryOperator;
use crate::ast::VisitorResult;
use crate::span::{Identifier, Span, Symbol};
use crate::try_visit;
use crate::visit_optional;
use crate::walk_list;

pub type Resolution = crate::sema::resolve::models::Resolution<NodeID>;
pub type DefinitionID = crate::sema::resolve::models::DefinitionID;
pub type DefinitionKind = crate::sema::resolve::models::DefinitionKind;

index_vec::define_index_type! {
    pub struct NodeID = u32;
}

#[derive(Debug, Clone)]
pub struct Package {
    pub root: Module,
}

#[derive(Debug, Clone)]
pub struct Module {
    pub id: DefinitionID,
    pub name: Symbol,
    pub declarations: Vec<Declaration>,
    pub submodules: Vec<Module>,
}

#[derive(Debug, Clone)]
pub struct Attribute {
    pub identifier: Identifier,
}

pub type AttributeList = Vec<Attribute>;

#[derive(Debug, Clone)]
pub struct Declaration<K = DeclarationKind> {
    pub id: DefinitionID,
    pub span: Span,
    pub identifier: Identifier,
    pub kind: K,
    pub attributes: AttributeList,
}

#[derive(Debug, Clone)]
pub enum DeclarationKind {
    Interface(Interface),
    Struct(Struct),
    Enum(Enum),
    Function(Function),
    TypeAlias(TypeAlias),
    Constant(Constant),
    Variable(Local),
    Import(UseTree),
    Export(UseTree),
    Namespace(Namespace),
    Extension(Extension),
    Malformed,
}

pub type AssociatedDeclaration = Declaration<AssociatedDeclarationKind>;
#[derive(Debug, Clone)]
pub enum AssociatedDeclarationKind {
    Constant(Constant),
    Function(Function),
    Type(TypeAlias),
    Operator(Operator),
    Initializer(Initializer),
}

#[derive(Debug, Clone)]
pub struct Interface {
    pub generics: Generics,
    pub declarations: Vec<AssociatedDeclaration>,
    pub conformances: Option<Conformances>,
}

#[derive(Debug, Clone)]
pub struct Struct {
    pub generics: Generics,
    pub fields: Vec<FieldDefinition>,
}

#[derive(Debug, Clone)]
pub struct Enum {
    pub generics: Generics,
    pub variants: Vec<Variant>,
}

#[derive(Debug, Clone)]
pub struct TypeAlias {
    pub generics: Generics,
    pub ty: Option<Box<Type>>,
    pub bounds: Option<GenericBounds>,
}

#[derive(Debug, Clone)]
pub struct Namespace {
    pub declarations: Vec<Declaration>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Abi {
    C,
    Intrinsic,
}

#[derive(Debug, Clone)]
pub struct Function {
    pub generics: Generics,
    pub signature: FunctionSignature,
    pub block: Option<Block>,
    pub abi: Option<Abi>,
}

/// AST Representation of a function parameter
///
/// ```text
/// name: String
/// name: String = "Default Value"
/// @attribute name: String
///
/// ```
#[derive(Debug, Clone)]
pub struct FunctionParameter {
    pub id: NodeID,
    pub attributes: AttributeList,
    pub label: Option<Label>,
    pub name: Identifier,
    pub annotated_type: Box<Type>,
    pub default_value: Option<Box<Expression>>,
    pub is_variadic: bool,
    pub span: Span,
}

/// AST representation of the function prototype, with its inputs and outputs
///
/// `(name: string) -> int`
/// `(name: string) -> void` // defaults to void if not provided
#[derive(Debug, Clone)]
pub struct FunctionPrototype {
    pub inputs: Vec<FunctionParameter>,
    pub output: Option<Box<Type>>,
}

#[derive(Debug, Clone)]
pub struct FunctionSignature {
    pub span: Span,
    pub prototype: FunctionPrototype,
}

#[derive(Debug, Clone)]
pub struct Operator {
    pub function: Function,
    pub kind: OperatorKind,
}

#[derive(Debug, Clone)]
pub struct Initializer {
    pub function: Function,
}

#[derive(Debug, Clone)]
pub struct UseTree {}

#[derive(Debug, Clone)]
pub struct Constant {
    pub identifier: Identifier,
    pub ty: Box<Type>,
    pub expr: Option<Box<Expression>>,
}

#[derive(Debug, Clone)]
pub struct Extension {
    pub ty: Box<Type>,
    pub generics: Generics,
    pub conformances: Option<Conformances>,
    pub declarations: Vec<AssociatedDeclaration>,
}

//
#[derive(Debug, Clone)]
pub struct Path {
    pub span: Span,
    pub resolution: Resolution,
    pub segments: Vec<PathSegment>,
}

#[derive(Debug, Clone)]
pub struct PathSegment {
    pub id: NodeID,
    pub identifier: Identifier,
    pub arguments: Option<TypeArguments>,
    pub span: Span,
    pub resolution: Resolution,
}

#[derive(Debug, Clone)]
pub struct PathNode {
    pub id: NodeID,
    pub path: ResolvedPath,
}

#[derive(Debug, Clone)]
pub enum ResolvedPath {
    Resolved(Path),
    Relative(Box<Type>, PathSegment),
}

#[derive(Debug, Clone)]
pub struct AnonConst {
    pub value: Box<Expression>,
}

#[derive(Debug, Clone)]
pub struct Type {
    pub id: NodeID,
    pub span: Span,
    pub kind: TypeKind,
}

#[derive(Debug, Clone)]
pub enum TypeKind {
    /// `Foo` | `Foo[T]` | Foo.Bar | `Foo.Bar[T]`
    Nominal(ResolvedPath),
    /// Pointer Type
    ///
    /// `*T` | `*const T`
    Pointer(Box<Type>, Mutability),
    /// Reference Type
    ///
    /// `&T` | `&const T`
    Reference(Box<Type>, Mutability),
    /// Tuple Type
    ///
    /// `(T, V)`
    Tuple(Vec<Box<Type>>),
    /// An Array with a fixed size `N`
    ///
    /// `[T;N]`
    Array { size: AnonConst, element: Box<Type> },
    /// (T, V) -> X
    Function {
        inputs: Vec<Box<Type>>,
        output: Box<Type>,
    },
    /// any T
    BoxedExistential { interfaces: Vec<PathNode> },
    /// _
    Infer,
}

#[derive(Debug, Clone)]
pub struct TypeParameters {
    pub span: Span,
    pub parameters: Vec<TypeParameter>,
}

#[derive(Debug, Clone)]
pub struct TypeParameter {
    pub id: NodeID,
    pub span: Span,
    pub identifier: Identifier,
    pub bounds: Option<GenericBounds>,
    pub kind: TypeParameterKind,
}

#[derive(Debug, Clone)]
pub enum TypeParameterKind {
    Type {
        default: Option<Box<Type>>,
    },
    Constant {
        ty: Box<Type>,
        default: Option<AnonConst>,
    },
}

#[derive(Debug, Clone)]
pub struct TypeArguments {
    pub span: Span,
    pub arguments: Vec<TypeArgument>,
}

#[derive(Debug, Clone)]
pub enum TypeArgument {
    Type(Box<Type>),
    Const(AnonConst),
}

/// `where T: X & Y`
#[derive(Debug, Clone)]
pub struct GenericWhereClause {
    pub requirements: GenericRequirementList,
    pub span: Span,
}

/// `T: X & Y, V == T`
pub type GenericRequirementList = Vec<GenericRequirement>;

#[derive(Debug, Clone)]
pub enum GenericRequirement {
    /// `Foo == Bar`
    SameTypeRequirement(RequiredTypeConstraint),
    /// `Foo: Hashable`
    ConformanceRequirement(ConformanceConstraint),
}

/// `Foo == Bar`
#[derive(Debug, Clone)]
pub struct RequiredTypeConstraint {
    pub bounded_type: Box<Type>,
    pub bound: Box<Type>,
    pub span: Span,
}

/// `Foo: Hashable`
#[derive(Debug, Clone)]
pub struct ConformanceConstraint {
    pub bounded_type: Box<Type>,
    pub bounds: GenericBounds,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct GenericBound {
    pub path: PathNode,
}

pub type GenericBounds = Vec<GenericBound>;

#[derive(Debug, Clone)]
pub struct Conformances {
    pub bounds: Vec<PathNode>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Generics {
    pub type_parameters: Option<TypeParameters>,
    pub where_clause: Option<GenericWhereClause>,
}

// Variants
#[derive(Debug, Clone)]
pub struct Variant {
    pub id: NodeID,
    pub ctor_id: NodeID,
    pub identifier: Identifier,
    pub kind: VariantKind,
    pub discriminant: Option<AnonConst>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum VariantKind {
    Unit,
    Tuple(Vec<FieldDefinition>),
}

#[derive(Debug, Clone)]
pub struct FieldDefinition {
    pub id: NodeID,
    pub mutability: Mutability,
    pub label: Option<Label>,
    pub identifier: Identifier,
    pub ty: Box<Type>,
    pub span: Span,
}

// Statement
#[derive(Debug, Clone)]
pub struct Statement {
    pub id: NodeID,
    pub kind: StatementKind,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum StatementKind {
    Declaration(Declaration),
    Expression(Box<Expression>),
    Variable(Local),
    Break,
    Continue,
    Return(Option<Box<Expression>>),
    Loop {
        label: Option<Label>,
        block: Block,
    },
    Defer(Block),
    Guard {
        condition: Box<Expression>,
        else_block: Block,
    },
}

#[derive(Debug, Clone)]
pub struct Local {
    pub id: NodeID,
    pub mutability: Mutability,
    pub pattern: Pattern,
    pub ty: Option<Box<Type>>,
    pub initializer: Option<Box<Expression>>,
}

#[derive(Debug, Clone)]
pub struct Block {
    pub id: NodeID,
    pub statements: Vec<Statement>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Expression {
    pub id: NodeID,
    pub kind: ExpressionKind,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum ExpressionKind {
    /// Runes, Bools, Integers, Floats, Strings
    Literal(Literal),

    /// A qualified path in expression position.
    ///
    /// This is used for both fully-resolved names (e.g. module paths, functions, constructors,
    /// locals) and type-relative unresolved accesses that need typechecking (via
    /// [`ResolvedPath::Relative`]).
    Path(ResolvedPath),

    /// `foo.bar` (instance member access only; type-relative access uses `ExpressionKind::Path`)
    Member {
        target: Box<Expression>,
        name: Identifier,
    },
    /// A[T]
    Specialize {
        target: Box<Expression>,
        type_arguments: TypeArguments,
    },
    /// `[a, b, c]`
    Array(Vec<Box<Expression>>),
    /// `(a, b, c)`
    Tuple(Vec<Box<Expression>>),
    /// `if foo { } else { }`
    If(IfExpression),
    /// `match foo {
    ///     case <pattern> => ...
    /// }`
    Match(MatchExpression),
    /// `main()`
    Call {
        callee: Box<Expression>,
        arguments: Vec<ExpressionArgument>,
    },
    /// `receiver.method(...)`
    MethodCall {
        receiver: Box<Expression>,
        name: Identifier,
        arguments: Vec<ExpressionArgument>,
    },
    /// &a | &const T
    Reference(Box<Expression>, Mutability),
    /// *a
    Dereference(Box<Expression>),
    /// `a + b`
    Binary(BinaryOperator, Box<Expression>, Box<Expression>),
    /// `!a` | '-a' | '~a'
    Unary(UnaryOperator, Box<Expression>),
    /// `a.1`
    TupleAccess(Box<Expression>, AnonConst),
    ///` a += b`
    AssignOp(BinaryOperator, Box<Expression>, Box<Expression>),
    ///` a = b`
    Assign(Box<Expression>, Box<Expression>),
    /// `a as int`
    CastAs(Box<Expression>, Box<Type>),
    /// A Binding Condition used for Tagged Unions
    ///
    /// `if let .some(value) = foo {}`
    ///
    /// `guard let .some(value) = foo else { return }`
    ///
    /// `while let .some(value) = foo {}`
    PatternBinding(PatternBindingCondition),
    /// { }
    Block(Block),
    Malformed,
}

#[derive(Debug, Clone)]
pub enum Literal {
    Bool(bool),
    Rune(char),
    String(Symbol),
    Integer(u64),
    Float(f64),
    Nil,
}

#[derive(Debug, Clone)]
pub struct MatchExpression {
    pub value: Box<Expression>,
    pub arms: Vec<MatchArm>,
    pub kw_span: Span,
}

#[derive(Debug, Clone)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub body: Box<Expression>,
    pub guard: Option<Box<Expression>>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct ExpressionArgument {
    pub label: Option<Label>,
    pub expression: Box<Expression>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct IfExpression {
    pub condition: Box<Expression>,
    pub then_block: Box<Expression>,
    pub else_block: Option<Box<Expression>>,
}

#[derive(Debug, Clone)]
pub struct PatternBindingCondition {
    pub pattern: Pattern,
    pub expression: Box<Expression>,
    pub span: Span,
}

// Pattern
// Patterns
#[derive(Debug, Clone)]

pub struct Pattern {
    pub id: NodeID,
    pub span: Span,
    pub kind: PatternKind,
}

#[derive(Debug, Clone)]
pub enum PatternKind {
    /// _
    Wildcard,
    /// ..
    Rest,
    // `foo`
    Identifier(Identifier),
    // (a, b)
    Tuple(Vec<Pattern>, Span),
    // Foo.Bar
    Member(PatternPath),
    // Foo.Bar(a, b)
    PathTuple {
        path: PatternPath,
        fields: Vec<Pattern>,
        field_span: Span,
    },
    // Foo | Bar
    Or(Vec<Pattern>, Span),
    // Bool, Rune, String, Integer & Float Literals
    Literal(AnonConst),
}

#[derive(Debug, Clone)]
pub enum PatternPath {
    Qualified { path: ResolvedPath },          // A.B.C
    Inferred { name: Identifier, span: Span }, // .B
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FoundationDecl {
    /// Option Type
    Option,
    /// List Type
    List,
    /// Dictionary Type
    Dictionary,
    /// Range Type
    Range,
    /// Closed Range Type (Inclusive Range)
    ClosedRange,
}

// MARK - Visitor
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AssocContext {
    Interface(DefinitionID),
    Extension(DefinitionID),
}

impl AssocContext {
    pub fn def_id(self) -> DefinitionID {
        match self {
            AssocContext::Interface(id) => id,
            AssocContext::Extension(id) => id,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UseTreeContext {
    Import(DefinitionID),
    Export(DefinitionID),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FunctionContext {
    Free,
    Assoc(AssocContext),
    Initializer,
    Operator,
    Nested,
}

pub fn is_expression_bodied(block: &Block) -> Option<&Expression> {
    match block.statements.as_slice() {
        [
            Statement {
                kind: StatementKind::Expression(expr),
                ..
            },
        ] => {
            Some(expr) // exactly one expression stmt → expr-bodied
        }
        _ => None, // otherwise treat as regular block
    }
}

pub trait HirVisitor: Sized {
    type Result: VisitorResult = ();

    fn visit_package(&mut self, node: &Package) -> Self::Result {
        walk_package(self, node)
    }

    fn visit_module(&mut self, node: &Module, is_root: bool) -> Self::Result {
        walk_module(self, node, is_root)
    }

    fn visit_attribute(&mut self, node: &Attribute) -> Self::Result {
        walk_attribute(self, node)
    }

    fn visit_declaration(&mut self, node: &Declaration) -> Self::Result {
        walk_declaration(self, node)
    }

    fn visit_assoc_declaration(
        &mut self,
        node: &AssociatedDeclaration,
        context: AssocContext,
    ) -> Self::Result {
        walk_assoc_declaration(self, node, context)
    }

    fn visit_interface(&mut self, node: &Interface, id: DefinitionID) -> Self::Result {
        walk_interface(self, node, id)
    }

    fn visit_struct(&mut self, node: &Struct) -> Self::Result {
        walk_struct(self, node)
    }

    fn visit_enum(&mut self, node: &Enum) -> Self::Result {
        walk_enum(self, node)
    }

    fn visit_variant(&mut self, node: &Variant) -> Self::Result {
        walk_variant(self, node)
    }

    fn visit_field_definition(&mut self, node: &FieldDefinition) -> Self::Result {
        walk_field_definition(self, node)
    }

    fn visit_function(
        &mut self,
        id: DefinitionID,
        node: &Function,
        c: FunctionContext,
    ) -> Self::Result {
        walk_function(self, id, node, c)
    }

    fn visit_function_signature(&mut self, node: &FunctionSignature) -> Self::Result {
        walk_function_signature(self, node)
    }

    fn visit_function_prototype(&mut self, node: &FunctionPrototype) -> Self::Result {
        walk_function_prototype(self, node)
    }

    fn visit_function_parameter(&mut self, node: &FunctionParameter) -> Self::Result {
        walk_function_parameter(self, node)
    }

    fn visit_initializer(&mut self, node: &Initializer, id: DefinitionID) -> Self::Result {
        walk_initializer(self, node, id)
    }

    fn visit_operator(&mut self, node: &Operator, id: DefinitionID) -> Self::Result {
        walk_operator(self, node, id)
    }

    fn visit_type_alias(&mut self, node: &TypeAlias) -> Self::Result {
        walk_type_alias(self, node)
    }

    fn visit_constant(&mut self, node: &Constant) -> Self::Result {
        walk_constant(self, node)
    }

    fn visit_namespace(&mut self, node: &Namespace) -> Self::Result {
        walk_namespace(self, node)
    }

    fn visit_extension(&mut self, node: &Extension, id: DefinitionID) -> Self::Result {
        walk_extension(self, node, id)
    }

    fn visit_use_tree(&mut self, node: &UseTree, context: UseTreeContext) -> Self::Result {
        walk_use_tree(self, node, context)
    }

    fn visit_type(&mut self, node: &Type) -> Self::Result {
        walk_type(self, node)
    }

    fn visit_type_arguments(&mut self, node: &TypeArguments) -> Self::Result {
        walk_type_arguments(self, node)
    }

    fn visit_type_argument(&mut self, node: &TypeArgument) -> Self::Result {
        walk_type_argument(self, node)
    }

    fn visit_generics(&mut self, node: &Generics) -> Self::Result {
        walk_generics(self, node)
    }

    fn visit_type_parameters(&mut self, node: &TypeParameters) -> Self::Result {
        walk_type_parameters(self, node)
    }

    fn visit_type_parameter(&mut self, node: &TypeParameter) -> Self::Result {
        walk_type_parameter(self, node)
    }

    fn visit_generic_bounds(&mut self, node: &GenericBounds) -> Self::Result {
        walk_generic_bounds(self, node)
    }

    fn visit_generic_bound(&mut self, node: &GenericBound) -> Self::Result {
        walk_generic_bound(self, node)
    }

    fn visit_generic_where_clause(&mut self, node: &GenericWhereClause) -> Self::Result {
        walk_generic_where_clause(self, node)
    }

    fn visit_generic_requirement_list(&mut self, node: &GenericRequirementList) -> Self::Result {
        walk_generic_requirement_list(self, node)
    }

    fn visit_generic_requirement(&mut self, node: &GenericRequirement) -> Self::Result {
        walk_generic_requirement(self, node)
    }

    fn visit_required_type_constraint(&mut self, node: &RequiredTypeConstraint) -> Self::Result {
        walk_required_type_constraint(self, node)
    }

    fn visit_conformance_constraint(&mut self, node: &ConformanceConstraint) -> Self::Result {
        walk_conformance_constraint(self, node)
    }

    fn visit_conformances(&mut self, node: &Conformances) -> Self::Result {
        walk_conformances(self, node)
    }

    fn visit_path(&mut self, node: &Path) -> Self::Result {
        walk_path(self, node)
    }

    fn visit_path_node(&mut self, node: &PathNode) -> Self::Result {
        walk_path_node(self, node)
    }

    fn visit_resolved_path(&mut self, node: &ResolvedPath) -> Self::Result {
        walk_resolved_path(self, node)
    }

    fn visit_path_segment(&mut self, node: &PathSegment) -> Self::Result {
        walk_path_segment(self, node)
    }

    fn visit_statement(&mut self, node: &Statement) -> Self::Result {
        walk_statement(self, node)
    }

    fn visit_block(&mut self, node: &Block) -> Self::Result {
        walk_block(self, node)
    }

    fn visit_local(&mut self, node: &Local) -> Self::Result {
        walk_local(self, node)
    }

    fn visit_expression(&mut self, node: &Expression) -> Self::Result {
        walk_expression(self, node)
    }

    fn visit_expression_argument(&mut self, node: &ExpressionArgument) -> Self::Result {
        walk_expression_argument(self, node)
    }

    fn visit_if_expression(&mut self, node: &IfExpression) -> Self::Result {
        walk_if_expression(self, node)
    }

    fn visit_match_expression(&mut self, node: &MatchExpression) -> Self::Result {
        walk_match_expression(self, node)
    }

    fn visit_match_arm(&mut self, node: &MatchArm) -> Self::Result {
        walk_match_arm(self, node)
    }

    fn visit_anon_const(&mut self, node: &AnonConst) -> Self::Result {
        walk_anon_const(self, node)
    }

    fn visit_pattern_binding_condition(&mut self, node: &PatternBindingCondition) -> Self::Result {
        walk_pattern_binding_condition(self, node)
    }

    fn visit_pattern(&mut self, node: &Pattern) -> Self::Result {
        walk_pattern(self, node)
    }

    fn visit_pattern_path(&mut self, node: &PatternPath) -> Self::Result {
        walk_pattern_path(self, node)
    }

    fn visit_identifier(&mut self, _node: &Identifier) -> Self::Result {
        Self::Result::output()
    }

    fn visit_label(&mut self, node: &Label) -> Self::Result {
        self.visit_identifier(&node.identifier)
    }
}

pub fn walk_package<V: HirVisitor>(visitor: &mut V, package: &Package) -> V::Result {
    visitor.visit_module(&package.root, true)
}

pub fn walk_module<V: HirVisitor>(visitor: &mut V, module: &Module, is_root: bool) -> V::Result {
    let _ = is_root;
    walk_list!(visitor, visit_module, &module.submodules, false);
    walk_list!(visitor, visit_declaration, &module.declarations);
    V::Result::output()
}

pub fn walk_attribute<V: HirVisitor>(visitor: &mut V, attribute: &Attribute) -> V::Result {
    visitor.visit_identifier(&attribute.identifier);
    V::Result::output()
}

pub fn walk_declaration<V: HirVisitor>(visitor: &mut V, declaration: &Declaration) -> V::Result {
    walk_list!(visitor, visit_attribute, &declaration.attributes);

    match &declaration.kind {
        DeclarationKind::Interface(node) => {
            try_visit!(visitor.visit_interface(node, declaration.id));
        }
        DeclarationKind::Struct(node) => {
            try_visit!(visitor.visit_struct(node));
        }
        DeclarationKind::Enum(node) => {
            try_visit!(visitor.visit_enum(node));
        }
        DeclarationKind::Function(node) => {
            try_visit!(visitor.visit_function(declaration.id, node, FunctionContext::Free));
        }
        DeclarationKind::TypeAlias(node) => {
            try_visit!(visitor.visit_type_alias(node));
        }
        DeclarationKind::Constant(node) => {
            try_visit!(visitor.visit_constant(node));
        }
        DeclarationKind::Variable(..) => {}
        DeclarationKind::Import(node) => {
            try_visit!(visitor.visit_use_tree(node, UseTreeContext::Import(declaration.id)));
        }
        DeclarationKind::Export(node) => {
            try_visit!(visitor.visit_use_tree(node, UseTreeContext::Export(declaration.id)));
        }
        DeclarationKind::Namespace(node) => {
            try_visit!(visitor.visit_namespace(node));
        }
        DeclarationKind::Extension(node) => {
            try_visit!(visitor.visit_extension(node, declaration.id));
        }
        DeclarationKind::Malformed => {}
    }

    V::Result::output()
}

pub fn walk_assoc_declaration<V: HirVisitor>(
    visitor: &mut V,
    declaration: &AssociatedDeclaration,
    context: AssocContext,
) -> V::Result {
    walk_list!(visitor, visit_attribute, &declaration.attributes);

    match &declaration.kind {
        AssociatedDeclarationKind::Constant(node) => {
            try_visit!(visitor.visit_constant(node));
        }
        AssociatedDeclarationKind::Function(node) => {
            try_visit!(visitor.visit_function(
                declaration.id,
                node,
                FunctionContext::Assoc(context)
            ));
        }
        AssociatedDeclarationKind::Type(node) => {
            try_visit!(visitor.visit_type_alias(node));
        }
        AssociatedDeclarationKind::Operator(node) => {
            try_visit!(visitor.visit_operator(node, declaration.id));
        }
        AssociatedDeclarationKind::Initializer(node) => {
            try_visit!(visitor.visit_initializer(node, declaration.id));
        }
    }

    V::Result::output()
}

pub fn walk_interface<V: HirVisitor>(
    visitor: &mut V,
    node: &Interface,
    id: DefinitionID,
) -> V::Result {
    try_visit!(visitor.visit_generics(&node.generics));
    visit_optional!(visitor, visit_conformances, &node.conformances);
    walk_list!(
        visitor,
        visit_assoc_declaration,
        &node.declarations,
        AssocContext::Interface(id)
    );
    V::Result::output()
}

pub fn walk_struct<V: HirVisitor>(visitor: &mut V, node: &Struct) -> V::Result {
    try_visit!(visitor.visit_generics(&node.generics));
    walk_list!(visitor, visit_field_definition, &node.fields);
    V::Result::output()
}

pub fn walk_enum<V: HirVisitor>(visitor: &mut V, node: &Enum) -> V::Result {
    try_visit!(visitor.visit_generics(&node.generics));
    walk_list!(visitor, visit_variant, &node.variants);
    V::Result::output()
}

pub fn walk_variant<V: HirVisitor>(visitor: &mut V, node: &Variant) -> V::Result {
    visitor.visit_identifier(&node.identifier);
    visit_optional!(visitor, visit_anon_const, &node.discriminant);
    match &node.kind {
        VariantKind::Unit => {}
        VariantKind::Tuple(fields) => walk_list!(visitor, visit_field_definition, fields),
    }
    V::Result::output()
}

pub fn walk_field_definition<V: HirVisitor>(visitor: &mut V, node: &FieldDefinition) -> V::Result {
    visit_optional!(visitor, visit_label, &node.label);
    visitor.visit_identifier(&node.identifier);
    try_visit!(visitor.visit_type(&node.ty));
    V::Result::output()
}

pub fn walk_function<V: HirVisitor>(
    visitor: &mut V,
    id: DefinitionID,
    node: &Function,
    c: FunctionContext,
) -> V::Result {
    try_visit!(visitor.visit_generics(&node.generics));
    try_visit!(visitor.visit_function_signature(&node.signature));
    visit_optional!(visitor, visit_block, &node.block);
    let _ = (id, c);
    V::Result::output()
}

pub fn walk_function_signature<V: HirVisitor>(
    visitor: &mut V,
    node: &FunctionSignature,
) -> V::Result {
    try_visit!(visitor.visit_function_prototype(&node.prototype));
    V::Result::output()
}

pub fn walk_function_prototype<V: HirVisitor>(
    visitor: &mut V,
    node: &FunctionPrototype,
) -> V::Result {
    walk_list!(visitor, visit_function_parameter, &node.inputs);
    visit_optional!(visitor, visit_type, &node.output);
    V::Result::output()
}

pub fn walk_function_parameter<V: HirVisitor>(
    visitor: &mut V,
    node: &FunctionParameter,
) -> V::Result {
    walk_list!(visitor, visit_attribute, &node.attributes);
    visit_optional!(visitor, visit_label, &node.label);
    visitor.visit_identifier(&node.name);
    try_visit!(visitor.visit_type(&node.annotated_type));
    visit_optional!(visitor, visit_expression, &node.default_value);
    V::Result::output()
}

pub fn walk_initializer<V: HirVisitor>(
    visitor: &mut V,
    node: &Initializer,
    id: DefinitionID,
) -> V::Result {
    try_visit!(visitor.visit_function(id, &node.function, FunctionContext::Initializer));
    V::Result::output()
}

pub fn walk_operator<V: HirVisitor>(
    visitor: &mut V,
    node: &Operator,
    id: DefinitionID,
) -> V::Result {
    try_visit!(visitor.visit_function(id, &node.function, FunctionContext::Operator));
    V::Result::output()
}

pub fn walk_type_alias<V: HirVisitor>(visitor: &mut V, node: &TypeAlias) -> V::Result {
    try_visit!(visitor.visit_generics(&node.generics));
    visit_optional!(visitor, visit_type, &node.ty);
    visit_optional!(visitor, visit_generic_bounds, &node.bounds);
    V::Result::output()
}

pub fn walk_constant<V: HirVisitor>(visitor: &mut V, node: &Constant) -> V::Result {
    visitor.visit_identifier(&node.identifier);
    try_visit!(visitor.visit_type(&node.ty));
    visit_optional!(visitor, visit_expression, &node.expr);
    V::Result::output()
}

pub fn walk_namespace<V: HirVisitor>(visitor: &mut V, node: &Namespace) -> V::Result {
    walk_list!(visitor, visit_declaration, &node.declarations);
    V::Result::output()
}

pub fn walk_extension<V: HirVisitor>(
    visitor: &mut V,
    node: &Extension,
    id: DefinitionID,
) -> V::Result {
    try_visit!(visitor.visit_generics(&node.generics));
    try_visit!(visitor.visit_type(&node.ty));
    visit_optional!(visitor, visit_conformances, &node.conformances);
    walk_list!(
        visitor,
        visit_assoc_declaration,
        &node.declarations,
        AssocContext::Extension(id)
    );
    V::Result::output()
}

pub fn walk_use_tree<V: HirVisitor>(
    _visitor: &mut V,
    _node: &UseTree,
    _context: UseTreeContext,
) -> V::Result {
    V::Result::output()
}

pub fn walk_type<V: HirVisitor>(visitor: &mut V, ty: &Type) -> V::Result {
    match &ty.kind {
        TypeKind::Nominal(path) => {
            try_visit!(visitor.visit_resolved_path(path));
        }
        TypeKind::Pointer(internal, _) | TypeKind::Reference(internal, _) => {
            try_visit!(visitor.visit_type(internal));
        }
        TypeKind::Tuple(elems) => {
            walk_list!(visitor, visit_type, elems);
        }
        TypeKind::Array { size, element } => {
            try_visit!(visitor.visit_anon_const(size));
            try_visit!(visitor.visit_type(element));
        }
        TypeKind::Function { inputs, output } => {
            walk_list!(visitor, visit_type, inputs);
            try_visit!(visitor.visit_type(output));
        }
        TypeKind::BoxedExistential { interfaces } => {
            walk_list!(visitor, visit_path_node, interfaces);
        }
        TypeKind::Infer => {}
    }
    V::Result::output()
}

pub fn walk_type_arguments<V: HirVisitor>(visitor: &mut V, node: &TypeArguments) -> V::Result {
    walk_list!(visitor, visit_type_argument, &node.arguments);
    V::Result::output()
}

pub fn walk_type_argument<V: HirVisitor>(visitor: &mut V, node: &TypeArgument) -> V::Result {
    match node {
        TypeArgument::Type(ty) => try_visit!(visitor.visit_type(ty)),
        TypeArgument::Const(c) => try_visit!(visitor.visit_anon_const(c)),
    }
    V::Result::output()
}

pub fn walk_generics<V: HirVisitor>(visitor: &mut V, node: &Generics) -> V::Result {
    visit_optional!(visitor, visit_type_parameters, &node.type_parameters);
    visit_optional!(visitor, visit_generic_where_clause, &node.where_clause);
    V::Result::output()
}

pub fn walk_type_parameters<V: HirVisitor>(visitor: &mut V, node: &TypeParameters) -> V::Result {
    walk_list!(visitor, visit_type_parameter, &node.parameters);
    V::Result::output()
}

pub fn walk_type_parameter<V: HirVisitor>(visitor: &mut V, node: &TypeParameter) -> V::Result {
    visitor.visit_identifier(&node.identifier);
    match &node.kind {
        TypeParameterKind::Type { default } => {
            visit_optional!(visitor, visit_type, default);
        }
        TypeParameterKind::Constant { ty, default } => {
            try_visit!(visitor.visit_type(ty));
            visit_optional!(visitor, visit_anon_const, default);
        }
    }
    visit_optional!(visitor, visit_generic_bounds, &node.bounds);
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
    match node {
        GenericRequirement::SameTypeRequirement(req) => {
            try_visit!(visitor.visit_required_type_constraint(req));
        }
        GenericRequirement::ConformanceRequirement(req) => {
            try_visit!(visitor.visit_conformance_constraint(req));
        }
    }
    V::Result::output()
}

pub fn walk_required_type_constraint<V: HirVisitor>(
    visitor: &mut V,
    node: &RequiredTypeConstraint,
) -> V::Result {
    try_visit!(visitor.visit_type(&node.bounded_type));
    try_visit!(visitor.visit_type(&node.bound));
    V::Result::output()
}

pub fn walk_conformance_constraint<V: HirVisitor>(
    visitor: &mut V,
    node: &ConformanceConstraint,
) -> V::Result {
    try_visit!(visitor.visit_type(&node.bounded_type));
    try_visit!(visitor.visit_generic_bounds(&node.bounds));
    V::Result::output()
}

pub fn walk_generic_bounds<V: HirVisitor>(visitor: &mut V, node: &GenericBounds) -> V::Result {
    walk_list!(visitor, visit_generic_bound, node);
    V::Result::output()
}

pub fn walk_generic_bound<V: HirVisitor>(visitor: &mut V, node: &GenericBound) -> V::Result {
    try_visit!(visitor.visit_path_node(&node.path));
    V::Result::output()
}

pub fn walk_conformances<V: HirVisitor>(visitor: &mut V, node: &Conformances) -> V::Result {
    walk_list!(visitor, visit_path_node, &node.bounds);
    V::Result::output()
}

pub fn walk_path<V: HirVisitor>(visitor: &mut V, path: &Path) -> V::Result {
    walk_list!(visitor, visit_path_segment, &path.segments);
    V::Result::output()
}

pub fn walk_path_node<V: HirVisitor>(visitor: &mut V, node: &PathNode) -> V::Result {
    try_visit!(visitor.visit_resolved_path(&node.path));
    V::Result::output()
}

pub fn walk_resolved_path<V: HirVisitor>(visitor: &mut V, path: &ResolvedPath) -> V::Result {
    match path {
        ResolvedPath::Resolved(path) => {
            try_visit!(visitor.visit_path(path));
        }
        ResolvedPath::Relative(ty, segment) => {
            try_visit!(visitor.visit_type(ty));
            try_visit!(visitor.visit_path_segment(segment));
        }
    }
    V::Result::output()
}

pub fn walk_path_segment<V: HirVisitor>(visitor: &mut V, path_segment: &PathSegment) -> V::Result {
    visitor.visit_identifier(&path_segment.identifier);
    visit_optional!(visitor, visit_type_arguments, &path_segment.arguments);
    V::Result::output()
}

pub fn walk_statement<V: HirVisitor>(visitor: &mut V, s: &Statement) -> V::Result {
    match &s.kind {
        StatementKind::Declaration(decl) => {
            try_visit!(visitor.visit_declaration(decl));
        }
        StatementKind::Expression(expr) => {
            try_visit!(visitor.visit_expression(expr));
        }
        StatementKind::Variable(local) => {
            try_visit!(visitor.visit_local(local));
        }
        StatementKind::Break | StatementKind::Continue => {}
        StatementKind::Return(expr) => {
            visit_optional!(visitor, visit_expression, expr);
        }
        StatementKind::Loop { label, block } => {
            visit_optional!(visitor, visit_label, label);
            try_visit!(visitor.visit_block(block));
        }
        StatementKind::Defer(block) => {
            try_visit!(visitor.visit_block(block));
        }
        StatementKind::Guard {
            condition,
            else_block,
        } => {
            try_visit!(visitor.visit_expression(condition));
            try_visit!(visitor.visit_block(else_block));
        }
    }
    V::Result::output()
}

pub fn walk_block<V: HirVisitor>(visitor: &mut V, block: &Block) -> V::Result {
    walk_list!(visitor, visit_statement, &block.statements);
    V::Result::output()
}

pub fn walk_local<V: HirVisitor>(visitor: &mut V, node: &Local) -> V::Result {
    try_visit!(visitor.visit_pattern(&node.pattern));
    visit_optional!(visitor, visit_type, &node.ty);
    visit_optional!(visitor, visit_expression, &node.initializer);
    V::Result::output()
}

pub fn walk_expression<V: HirVisitor>(visitor: &mut V, node: &Expression) -> V::Result {
    match &node.kind {
        ExpressionKind::Literal(_) => {}
        ExpressionKind::Path(path) => {
            try_visit!(visitor.visit_resolved_path(path));
        }
        ExpressionKind::Member { target, name } => {
            try_visit!(visitor.visit_expression(target));
            try_visit!(visitor.visit_identifier(name));
        }
        ExpressionKind::Specialize {
            target,
            type_arguments,
        } => {
            try_visit!(visitor.visit_expression(target));
            try_visit!(visitor.visit_type_arguments(type_arguments));
        }
        ExpressionKind::Array(expressions) => {
            walk_list!(visitor, visit_expression, expressions);
        }
        ExpressionKind::Tuple(expressions) => {
            walk_list!(visitor, visit_expression, expressions);
        }
        ExpressionKind::If(expr) => {
            try_visit!(visitor.visit_if_expression(expr));
        }
        ExpressionKind::Match(expr) => {
            try_visit!(visitor.visit_match_expression(expr));
        }
        ExpressionKind::Call { callee, arguments } => {
            try_visit!(visitor.visit_expression(callee));
            walk_list!(visitor, visit_expression_argument, arguments);
        }
        ExpressionKind::MethodCall {
            receiver,
            arguments,
            ..
        } => {
            try_visit!(visitor.visit_expression(receiver));
            walk_list!(visitor, visit_expression_argument, arguments);
        }
        ExpressionKind::Reference(expression, _) => {
            try_visit!(visitor.visit_expression(expression));
        }
        ExpressionKind::Dereference(expression) => {
            try_visit!(visitor.visit_expression(expression));
        }
        ExpressionKind::Binary(_, lhs, rhs) => {
            try_visit!(visitor.visit_expression(lhs));
            try_visit!(visitor.visit_expression(rhs));
        }
        ExpressionKind::Unary(_, expression) => {
            try_visit!(visitor.visit_expression(expression));
        }
        ExpressionKind::TupleAccess(expression, anon_const) => {
            try_visit!(visitor.visit_expression(expression));
            try_visit!(visitor.visit_anon_const(anon_const));
        }
        ExpressionKind::AssignOp(_, lhs, rhs) => {
            try_visit!(visitor.visit_expression(lhs));
            try_visit!(visitor.visit_expression(rhs));
        }
        ExpressionKind::Assign(lhs, rhs) => {
            try_visit!(visitor.visit_expression(lhs));
            try_visit!(visitor.visit_expression(rhs));
        }
        ExpressionKind::CastAs(expression, ty) => {
            try_visit!(visitor.visit_expression(expression));
            try_visit!(visitor.visit_type(ty));
        }
        ExpressionKind::PatternBinding(condition) => {
            try_visit!(visitor.visit_pattern_binding_condition(condition));
        }
        ExpressionKind::Block(block) => {
            try_visit!(visitor.visit_block(block));
        }
        ExpressionKind::Malformed => {}
    };

    V::Result::output()
}

pub fn walk_expression_argument<V: HirVisitor>(
    visitor: &mut V,
    node: &ExpressionArgument,
) -> V::Result {
    visit_optional!(visitor, visit_label, &node.label);
    try_visit!(visitor.visit_expression(&node.expression));
    V::Result::output()
}

pub fn walk_if_expression<V: HirVisitor>(visitor: &mut V, node: &IfExpression) -> V::Result {
    try_visit!(visitor.visit_expression(&node.condition));
    try_visit!(visitor.visit_expression(&node.then_block));
    visit_optional!(visitor, visit_expression, &node.else_block);
    V::Result::output()
}

pub fn walk_match_expression<V: HirVisitor>(visitor: &mut V, node: &MatchExpression) -> V::Result {
    try_visit!(visitor.visit_expression(&node.value));
    walk_list!(visitor, visit_match_arm, &node.arms);
    V::Result::output()
}

pub fn walk_match_arm<V: HirVisitor>(visitor: &mut V, node: &MatchArm) -> V::Result {
    try_visit!(visitor.visit_pattern(&node.pattern));
    try_visit!(visitor.visit_expression(&node.body));
    visit_optional!(visitor, visit_expression, &node.guard);
    V::Result::output()
}

pub fn walk_anon_const<V: HirVisitor>(visitor: &mut V, anon_const: &AnonConst) -> V::Result {
    try_visit!(visitor.visit_expression(&anon_const.value));
    V::Result::output()
}

pub fn walk_pattern_binding_condition<V: HirVisitor>(
    visitor: &mut V,
    node: &PatternBindingCondition,
) -> V::Result {
    try_visit!(visitor.visit_pattern(&node.pattern));
    try_visit!(visitor.visit_expression(&node.expression));
    V::Result::output()
}

pub fn walk_pattern<V: HirVisitor>(visitor: &mut V, pattern: &Pattern) -> V::Result {
    match &pattern.kind {
        PatternKind::Wildcard | PatternKind::Rest => {}
        PatternKind::Identifier(identifier) => {
            try_visit!(visitor.visit_identifier(identifier));
        }
        PatternKind::Tuple(patterns, _) => {
            walk_list!(visitor, visit_pattern, patterns);
        }
        PatternKind::Member(pattern_path) => {
            try_visit!(visitor.visit_pattern_path(pattern_path));
        }
        PatternKind::PathTuple { path, fields, .. } => {
            try_visit!(visitor.visit_pattern_path(path));
            walk_list!(visitor, visit_pattern, fields);
        }
        PatternKind::Or(patterns, _) => {
            walk_list!(visitor, visit_pattern, patterns);
        }
        PatternKind::Literal(anon_const) => {
            try_visit!(visitor.visit_anon_const(anon_const));
        }
    }

    V::Result::output()
}

pub fn walk_pattern_path<V: HirVisitor>(visitor: &mut V, node: &PatternPath) -> V::Result {
    match node {
        PatternPath::Qualified { path } => {
            try_visit!(visitor.visit_resolved_path(path));
        }
        PatternPath::Inferred { name, .. } => {
            try_visit!(visitor.visit_identifier(name));
        }
    }
    V::Result::output()
}
