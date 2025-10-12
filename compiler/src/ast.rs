use crate::{
    parse::Base,
    span::{FileID, Span},
};
use ecow::EcoString;

#[derive(Debug)]
pub struct Package {
    pub root: Module,
}

#[derive(Debug)]
pub struct Module {
    pub name: EcoString,
    pub files: Vec<File>,
    pub submodules: Vec<Module>,
}

#[derive(Debug)]
pub struct File {
    pub id: FileID,
    pub declarations: Vec<Declaration>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Mutability {
    Mutable,
    Immutable,
}

#[derive(Debug, Clone)]
pub struct Identifier {
    pub span: Span,
    pub symbol: EcoString,
}

impl Identifier {
    pub fn emtpy(file: FileID) -> Self {
        Identifier {
            span: Span::empty(file),
            symbol: "".into(),
        }
    }

    pub fn new(symbol: EcoString, span: Span) -> Self {
        Identifier { span, symbol }
    }
}

#[derive(Debug, Clone)]
pub struct Label {
    pub identifier: Identifier,
    pub span: Span,
}

#[derive(Debug, Clone, Copy)]
pub struct Visibility {
    pub span: Span,
    pub level: VisibilityLevel,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VisibilityLevel {
    Public,
    Protected,
    FilePrivate,
    Private,
    Inherent,
}

#[derive(Debug)]
pub struct Attribute {
    pub identifier: Identifier,
}

pub type AttributeList = Vec<Attribute>;

#[derive(Debug)]
pub struct Declaration<K = DeclarationKind> {
    pub kind: K,
    pub span: Span,
    pub visibility: Visibility,
    pub identifier: Identifier,
    pub attributes: AttributeList,
}

#[derive(Debug)]
pub enum DeclarationKind {
    Interface(Interface),
    Struct(Struct),
    Enum(Enum),
    Function(Function),
    Variable(Local),
    Constant(Constant),
    Import(UseTree),
    Export(UseTree),
    Extend(Extension),
    TypeAlias(TypeAlias),
    Namespace(Namespace),
    Initializer(Initializer),
}

// Function Declarations
pub type FunctionDeclaration = Declaration<FunctionDeclarationKind>;
#[derive(Debug)]
pub enum FunctionDeclarationKind {
    Struct(Struct),
    Enum(Enum),
    Function(Function),
    Constant(Constant),
    TypeAlias(TypeAlias),
}

// Namespace Declarations
pub type NamespaceDeclaration = Declaration<NamespaceDeclarationKind>;
#[derive(Debug)]
pub enum NamespaceDeclarationKind {
    Struct(Struct),
    Enum(Enum),
    Function(Function),
    Constant(Constant),
    TypeAlias(TypeAlias),
    Namespace(Namespace),
    Interface(Interface),
}

// Extensions & Interface Declarations
pub type AssociatedDeclaration = Declaration<AssociatedDeclarationKind>;
#[derive(Debug)]
pub enum AssociatedDeclarationKind {
    Constant(Constant),
    Function(Function),
    Initializer(Initializer),
}

#[derive(Debug)]
pub struct Interface {
    pub generics: Generics,
    pub declarations: Vec<AssociatedDeclaration>,
}

#[derive(Debug)]
pub struct Struct {
    pub generics: Generics,
    pub fields: Vec<FieldDefinition>,
}

#[derive(Debug)]
pub struct Enum {
    pub generics: Generics,
    pub cases: Vec<EnumCase>,
}

#[derive(Debug)]
pub struct Function {
    pub generics: Generics,
    pub signature: FunctionSignature,
    pub block: Option<Block>,
}

#[derive(Debug)]
pub struct Initializer {
    pub function: Function,
}

#[derive(Debug)]
pub struct Local {
    pub mutability: Mutability,
    pub pattern: Pattern,
    pub ty: Option<Box<Type>>,
    pub initializer: Option<Box<Expression>>,
    pub is_shorthand: bool,
}

#[derive(Debug)]
pub struct Constant {
    pub identifier: Identifier,
    pub ty: Box<Type>,
    pub expr: Option<Box<Expression>>,
}

#[derive(Debug)]
pub struct TypeAlias {
    pub generics: Generics,
    pub ty: Option<Box<Type>>,
}

#[derive(Debug)]
pub struct Namespace {
    pub declarations: Option<Vec<NamespaceDeclaration>>,
}

#[derive(Debug)]
pub struct Extension {
    pub ty: Box<Type>,
    pub generics: Generics,
    pub declarations: Vec<AssociatedDeclaration>,
}

#[derive(Debug)]
pub struct UseTree {
    pub span: Span,
    pub path: UseTreePath,
    pub kind: UseTreeKind,
}

#[derive(Debug)]
pub struct UseTreePath {
    pub span: Span,
    pub nodes: Vec<Identifier>,
}

#[derive(Debug)]
pub enum UseTreeKind {
    Glob,
    Simple {
        alias: Option<Identifier>,
    },
    Nested {
        nodes: Vec<(Identifier, Option<Identifier>)>,
        span: Span,
    },
}

// Statements

#[derive(Debug)]
pub struct Statement {
    pub kind: StatementKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum StatementKind {
    Declaration(FunctionDeclaration),
    Expression(Box<Expression>),
    Variable(Local),
    Break(Option<Identifier>),
    Continue(Option<Identifier>),
    Return(Option<Box<Expression>>),
    Loop {
        label: Option<Label>,
        block: Block,
    },
    While {
        label: Option<Label>,
        condition: Box<Expression>,
        block: Block,
    },
    For(ForStatement),
    Defer(Block),
    Guard {
        condition: Box<Expression>,
        block: Block,
    },
}

#[derive(Debug)]
pub struct ForStatement {
    pub label: Option<Label>,
    pub pattern: Pattern,
    pub iterator: Box<Expression>,
    pub clause: Option<Box<Expression>>,
    pub block: Block,
}

#[derive(Debug)]
pub struct Block {
    pub statements: Vec<Statement>,
    pub has_declarations: bool,
    pub span: Span,
}

// Expressions
#[derive(Debug)]
pub struct Expression {
    pub kind: ExpressionKind,
    pub span: Span,
}

#[derive(Debug)]
pub struct AnonConst {
    pub value: Box<Expression>,
}

#[derive(Debug)]
pub enum ExpressionKind {
    Malformed,
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
    /// `["a" : 100]`
    DictionaryLiteral(Vec<MapPair>),
    /// `if foo { } else { }`
    If(IfExpression),
    /// `match foo {
    ///     case <pattern> => ...
    /// }`
    Match(MatchExpression),
    /// `main()`
    FunctionCall(Box<Expression>, Vec<ExpressionArgument>),
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
    /// `(a)`
    Parenthesis(Box<Expression>),
    /// `a as int`
    CastAs(Box<Expression>, Box<Type>),
    /// `a ? b : c`
    Ternary(Box<Expression>, Box<Expression>, Box<Expression>),

    /// `a |> b`
    Pipe(Box<Expression>, Box<Expression>),
    /// A Binding Condition used for Tagged Unions
    ///
    /// `if let .some(value) = foo {}`
    ///
    /// `guard let .some(value) = foo else { return }`
    ///
    /// `while let .some(value) = foo {}`
    PatternBinding(PatternBindingCondition),
    /// `a ?? b`
    OptionalDefault(Box<Expression>, Box<Expression>),
    /// lhs..rhs | lhs..=rhs, bool indicates inclusiveness
    Range(Box<Expression>, Box<Expression>, bool),
    /// `_`
    Wildcard,
    /// |a, b| a + b
    Closure(ClosureExpression),
    /// { }
    Block(Block),
    /// `a!`
    ForceUnwrap(Box<Expression>),
    /// `a?`
    OptionalUnwrap(Box<Expression>),
    ///
    OptionalEvaluation(Box<Expression>),
}

#[derive(Debug)]
pub enum Literal {
    Bool(bool),
    Rune { value: EcoString },
    String { value: EcoString },
    Integer { value: EcoString, base: Base },
    Float { value: EcoString, base: Base },
    Nil,
}

#[derive(Debug)]
pub struct MapPair {
    pub key: Box<Expression>,
    pub value: Box<Expression>,
}

#[derive(Debug)]
pub struct MatchExpression {
    pub value: Option<Box<Expression>>,
    pub arms: Vec<MatchArm>,
    pub kw_span: Span,
}

#[derive(Debug)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub body: Box<Expression>,
    pub guard: Option<Box<Expression>>,
    pub span: Span,
}

#[derive(Debug)]
pub struct ExpressionArgument {
    pub label: Option<Label>,
    pub expression: Box<Expression>,
    pub span: Span,
}

#[derive(Debug)]
pub struct IfExpression {
    pub condition: Box<Expression>,
    pub body: Block,
    pub else_block: Option<Box<Expression>>,
}

#[derive(Debug)]
pub struct PatternBindingCondition {
    pub pattern: Pattern,
    pub expression: Box<Expression>,
    pub shorthand: bool,
    pub span: Span,
}

#[derive(Debug)]
pub struct ClosureExpression {
    pub signature: FunctionSignature,
    pub body: Block,
    pub span: Span,
}

// Type
#[derive(Debug)]
pub struct Type {
    pub span: Span,
    pub kind: TypeKind,
}

#[derive(Debug)]
pub enum TypeKind {
    /// `Foo` | `Foo[T]`
    Nominal {
        name: Identifier,
        type_arguments: Option<TypeArguments>,
    },
    /// Foo.Bar | `Foo.Bar[T]`
    Member {
        target: Box<Type>,
        name: Identifier,
        type_arguments: Option<TypeArguments>,
    },
    /// Pointer Type
    ///
    /// `*T` | `*const T`
    Pointer(Box<Type>, Mutability),
    /// Reference Type
    ///
    /// `&T` | `&const T`
    Reference(Box<Type>, Mutability),
    /// Paren type
    /// `(T)`
    Parenthesis(Box<Type>),
    /// Tuple Type
    ///
    /// `(T, V)`
    Tuple(Vec<Box<Type>>),
    /// Optional Type
    ///
    /// `T?`
    Optional(Box<Type>),
    /// `~T` -> Option<&T> | `~const T` -> Option<&const T>
    OptionalReference(Box<Type>, Mutability),
    /// An Array with a fixed size `N`
    ///
    /// `[T;N]`
    Array {
        size: AnonConst,
        element: Box<Type>,
    },
    /// A Dynamic, growable array
    ///
    /// `[T]`
    List(Box<Type>),
    /// A hash-map
    ///
    /// `[T:V]`
    Dictionary {
        key: Box<Type>,
        value: Box<Type>,
    },

    /// (T, V) -> X
    Function {
        inputs: Vec<Box<Type>>,
        output: Box<Type>,
    },
    /// Ty of, self, &self, &const self
    ImplicitSelf,
    // |a, b| a + b
    InferedClosureParameter,
    /// _
    Infer,
}

// Patterns
#[derive(Debug)]
pub struct Pattern {
    pub span: Span,
    pub kind: PatternKind,
}

#[derive(Debug)]
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
    Member(PatternPathHead),
    // Foo.Bar(a, b)
    PathTuple(PatternPathHead, Vec<Pattern>, Span),
    // Foo.Bar { a, b, .. }
    PathStruct(PatternPathHead, Vec<PatternField>, Span, bool),
    // Foo | Bar
    Or(Vec<Pattern>, Span),
    // Bool, Rune, String, Integer & Float Literals
    Literal(AnonConst),
}

#[derive(Debug)]
pub enum PatternPathHeadKind {
    Ident(Identifier), // A
    Member {
        target: Box<PatternPathHeadKind>,
        name: Identifier,
    }, // A.B
}

#[derive(Debug)]
pub enum PatternPathHead {
    Full(PatternPathHeadKind),                  // A.Bar
    Shorthand { case: Identifier, span: Span }, // `.Case`
}

#[derive(Debug)]
pub struct PatternField {
    pub identifier: Identifier,
    pub pattern: Pattern,
    pub span: Span,
}

// Generics

/// Represents the 'T: Foo' in Option<T: Foo>
#[derive(Debug)]
pub struct TypeParameter {
    pub span: Span,
    pub identifier: Identifier,
    pub bounds: Option<GenericBounds>,
    pub kind: TypeParameterKind,
}

#[derive(Debug)]
pub enum TypeParameterKind {
    Type {
        default: Option<Box<Type>>,
    },
    Constant {
        ty: Box<Type>,
        default: Option<AnonConst>,
    },
}

#[derive(Debug)]
pub struct TypeParameters {
    pub span: Span,
    pub parameters: Vec<TypeParameter>,
}

#[derive(Debug)]
pub struct TypeArguments {
    pub span: Span,
    pub arguments: Vec<TypeArgument>,
}

#[derive(Debug)]
pub enum TypeArgument {
    Type(Box<Type>),
    Const(AnonConst),
}

#[derive(Debug)]
pub struct Generics {
    pub type_parameters: Option<TypeParameters>,
    pub where_clause: Option<GenericWhereClause>,
    pub conformances: Option<Conformances>,
}

/// `where T: X & Y`
#[derive(Debug)]
pub struct GenericWhereClause {
    pub requirements: GenericRequirementList,
    pub span: Span,
}

/// `T: X & Y, V == T`
pub type GenericRequirementList = Vec<GenericRequirement>;

#[derive(Debug)]
pub enum GenericRequirement {
    /// `Foo == Bar`
    SameTypeRequirement(RequiredTypeConstraint),
    /// `T: Hashable`
    ConformanceRequirement(ConformanceConstraint),
}

/// `Foo == Bar`
#[derive(Debug)]
pub struct RequiredTypeConstraint {
    pub bounded_type: Box<Type>,
    pub bound: Box<Type>,
    pub span: Span,
}

/// `T: Hashable`
#[derive(Debug)]
pub struct ConformanceConstraint {
    pub bounded_type: Box<Type>,
    pub bounds: GenericBounds,
    pub span: Span,
}

#[derive(Debug)]
pub struct GenericBound {
    pub path: Box<Type>,
}

pub type GenericBounds = Vec<GenericBound>;

#[derive(Debug)]
pub struct Conformances {
    pub interfaces: Vec<Box<Type>>,
}

// ADT
#[derive(Debug)]
pub struct EnumCase {
    pub span: Span,
    pub variants: Vec<Variant>,
}

#[derive(Debug)]
pub struct Variant {
    pub identifier: Identifier,
    pub kind: VariantKind,
    pub discriminant: Option<AnonConst>,
    pub span: Span,
}

#[derive(Debug)]
pub enum VariantKind {
    Unit,
    Tuple(Vec<FieldDefinition>),
    Struct(Vec<FieldDefinition>),
}

#[derive(Debug)]
pub struct FieldDefinition {
    pub visibility: Visibility,
    pub mutability: Mutability,
    pub label: Option<Label>,
    pub identifier: Identifier,
    pub ty: Box<Type>,
    pub span: Span,
}

// Functions

/// AST Representation of a function parameter
///
/// ```text
/// name: String
/// name: String = "Default Value"
/// @attribute name: String
/// ```
#[derive(Debug)]
pub struct FunctionParameter {
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
#[derive(Debug)]
pub struct FunctionPrototype {
    pub inputs: Vec<FunctionParameter>,
    pub output: Option<Box<Type>>,
}

#[derive(Debug)]
pub struct FunctionSignature {
    pub span: Span,
    pub prototype: FunctionPrototype,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SelfKind {
    Copy,
    Reference,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum BinaryOperator {
    /// `+`
    Add,
    /// `-`
    Sub,
    /// `*`
    Mul,
    /// `/`
    Div,
    /// `%`
    Rem,
    /// `&&`
    BoolAnd,
    /// `||`
    BoolOr,
    /// `&`
    BitAnd,
    /// `|`
    BitOr,
    /// `^`
    BitXor,
    /// `<<`
    BitShl,
    /// `>>`
    BitShr,
    /// `==`
    Eql,
    /// `<`
    Lt,
    /// `>`
    Gt,
    /// `<=`
    Leq,
    /// `>=`
    Geq,
    /// `!=`
    Neq,
    /// Pointer Equality
    /// `===`
    PtrEq,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum UnaryOperator {
    // !
    LogicalNot,
    // -
    Negate,
    // ~
    BitwiseNot,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OperatorKind {
    Add,
    Sub,
    Div,
    Mul,
    Rem,

    BitShl,
    BitShr,
    BitAnd,
    BitOr,
    BitXor,

    Neg,
    Not,
    BitwiseNot,

    AddAssign,
    SubAssign,
    DivAssign,
    MulAssign,
    RemAssign,

    BitShlAssign,
    BitShrAssign,
    BitAndAssign,
    BitOrAssign,
    BitXorAssign,

    BoolAnd,
    BoolOr,

    Lt,
    Gt,
    Leq,
    Geq,
    Eq,
    Neq,
}

impl TryFrom<DeclarationKind> for AssociatedDeclarationKind {
    type Error = DeclarationKind;

    fn try_from(kind: DeclarationKind) -> Result<AssociatedDeclarationKind, DeclarationKind> {
        Ok(match kind {
            DeclarationKind::Constant(node) => AssociatedDeclarationKind::Constant(node),
            DeclarationKind::Function(node) => AssociatedDeclarationKind::Function(node),
            DeclarationKind::Initializer(node) => AssociatedDeclarationKind::Initializer(node),
            _ => return Err(kind),
        })
    }
}

impl TryFrom<DeclarationKind> for FunctionDeclarationKind {
    type Error = DeclarationKind;

    fn try_from(kind: DeclarationKind) -> Result<FunctionDeclarationKind, DeclarationKind> {
        Ok(match kind {
            DeclarationKind::Function(node) => FunctionDeclarationKind::Function(node),
            DeclarationKind::Struct(node) => FunctionDeclarationKind::Struct(node),
            DeclarationKind::Enum(node) => FunctionDeclarationKind::Enum(node),
            DeclarationKind::Constant(node) => FunctionDeclarationKind::Constant(node),
            DeclarationKind::TypeAlias(node) => FunctionDeclarationKind::TypeAlias(node),
            _ => return Err(kind),
        })
    }
}

impl TryFrom<DeclarationKind> for NamespaceDeclarationKind {
    type Error = DeclarationKind;

    fn try_from(kind: DeclarationKind) -> Result<NamespaceDeclarationKind, DeclarationKind> {
        Ok(match kind {
            DeclarationKind::Function(node) => NamespaceDeclarationKind::Function(node),
            DeclarationKind::Struct(node) => NamespaceDeclarationKind::Struct(node),
            DeclarationKind::Enum(node) => NamespaceDeclarationKind::Enum(node),
            DeclarationKind::Constant(node) => NamespaceDeclarationKind::Constant(node),
            DeclarationKind::TypeAlias(node) => NamespaceDeclarationKind::TypeAlias(node),
            DeclarationKind::Namespace(node) => NamespaceDeclarationKind::Namespace(node),
            DeclarationKind::Interface(node) => NamespaceDeclarationKind::Interface(node),
            _ => return Err(kind),
        })
    }
}
