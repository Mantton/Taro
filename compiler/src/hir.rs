pub use crate::ast::BinaryOperator;
pub use crate::ast::Label;
pub use crate::ast::Mutability;
pub use crate::ast::OperatorKind;
pub use crate::ast::UnaryOperator;
use crate::span::{Identifier, Span, Symbol};

index_vec::define_index_type! {
    pub struct NodeID = u32;
}

#[derive(Debug, Clone)]
pub struct Package {
    pub root: Module,
}

#[derive(Debug, Clone)]
pub struct Module {
    pub id: NodeID,
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
    pub id: NodeID,
    pub span: Span,
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
    Variable(()),
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

#[derive(Debug, Clone)]
pub struct Function {
    pub generics: Generics,
    pub signature: FunctionSignature,
    pub block: Option<Block>,
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
    pub is_async: bool,
}

#[derive(Debug, Clone)]
pub enum FunctionReceiverKind {
    Use, // Copy or Move
    Reference(Mutability),
    Pointer(Mutability),
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
pub struct Path {}

#[derive(Debug, Clone)]
pub struct PathNode {
    pub id: NodeID,
    pub path: Path,
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
    Path(Path),
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
    BoxedExistential { interfaces: Vec<Path> },
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
    Struct(Vec<FieldDefinition>),
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

    /// `foo`
    Identifier(Identifier),

    /// `foo.bar`
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
    Call(Box<Expression>, Vec<ExpressionArgument>),
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
pub struct MapPair {
    pub key: Box<Expression>,
    pub value: Box<Expression>,
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
    pub shorthand: bool,
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
    // Foo.Bar { a, b, .. }
    PathStruct {
        path: PatternPath,
        fields: Vec<PatternField>,
        field_span: Span,
        ignore_rest: bool,
    },
    // Foo | Bar
    Or(Vec<Pattern>, Span),
    // Bool, Rune, String, Integer & Float Literals
    Literal(AnonConst),
}

#[derive(Debug, Clone)]
pub enum PatternPath {
    Qualified { path: Path },                  // A.B.C
    Inferred { name: Identifier, span: Span }, // .B
}

#[derive(Debug, Clone)]
pub struct PatternField {
    pub id: NodeID,
    pub identifier: Identifier,
    pub pattern: Pattern,
    pub span: Span,
}
