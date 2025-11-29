use crate::{
    parse::Base,
    span::{FileID, Span, Symbol},
};
use index_vec::define_index_type;
use std::ops::ControlFlow;

define_index_type! {
    pub struct NodeID = u32;
}

#[derive(Debug)]
pub struct Package {
    pub root: Module,
}

#[derive(Debug)]
pub struct Module {
    pub id: NodeID,
    pub name: Symbol,
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

pub use crate::span::Identifier;

#[derive(Debug, Clone, Copy)]
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
    pub id: NodeID,
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
    Extension(Extension),
    TypeAlias(TypeAlias),
    Namespace(Namespace),
    Initializer(Initializer),
    Operator(Operator),
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
    Import(UseTree),
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
    Import(UseTree),
    Export(UseTree),
}

// Impls & Interface Declarations
pub type AssociatedDeclaration = Declaration<AssociatedDeclarationKind>;
#[derive(Debug)]
pub enum AssociatedDeclarationKind {
    Constant(Constant),
    Function(Function),
    AssociatedType(TypeAlias),
    Initializer(Initializer),
    Operator(Operator),
}

#[derive(Debug)]
pub struct Interface {
    pub generics: Generics,
    pub declarations: Vec<AssociatedDeclaration>,
    pub conformances: Option<Conformances>,
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
    pub is_static: bool,
}

#[derive(Debug)]
pub struct Initializer {
    pub function: Function,
}

#[derive(Debug)]
pub struct Operator {
    pub kind: OperatorKind,
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
    pub bounds: Option<GenericBounds>,
}

#[derive(Debug)]
pub struct Namespace {
    pub declarations: Vec<NamespaceDeclaration>,
}

#[derive(Debug)]
pub struct Extension {
    pub ty: Box<Type>,
    pub generics: Generics,
    pub conformances: Option<Conformances>,
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
        nodes: Vec<UseTreeNestedItem>,
        span: Span,
    },
}

#[derive(Debug)]
pub struct UseTreeNestedItem {
    pub id: NodeID,
    pub name: Identifier,
    pub alias: Option<Identifier>,
}

// Statements

#[derive(Debug)]
pub struct Statement {
    pub id: NodeID,
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
        else_block: Block,
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
    pub id: NodeID,
    pub statements: Vec<Statement>,
    pub has_declarations: bool,
    pub span: Span,
}

// Expressions
#[derive(Debug)]
pub struct Expression {
    pub id: NodeID,
    pub kind: ExpressionKind,
    pub span: Span,
}

#[derive(Debug)]
pub struct AnonConst {
    pub value: Box<Expression>,
}

#[derive(Debug)]
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
    /// `["a" : 100]`
    DictionaryLiteral(Vec<MapPair>),
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
    /// `if case .some(value) = foo {}`
    ///
    /// `guard case .some(value) = foo else { return }`
    ///
    /// `while case .some(value) = foo {}`
    PatternBinding(PatternBindingCondition),
    /// A Shorthand binding condition for optionals
    ///
    /// `if let foo = foo {}`
    ///
    /// `guard let foo else { return }`
    ///
    /// `while let foo = bar {}`
    OptionalPatternBinding(PatternBindingCondition),
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
    /// `a?`
    OptionalUnwrap(Box<Expression>),
    ///
    OptionalEvaluation(Box<Expression>),
}

#[derive(Debug)]
pub enum Literal {
    Bool(bool),
    Rune { value: String },
    String { value: String },
    Integer { value: String, base: Base },
    Float { value: String },
    Nil,
}

#[derive(Debug)]
pub struct MapPair {
    pub key: Box<Expression>,
    pub value: Box<Expression>,
}

#[derive(Debug)]
pub struct MatchExpression {
    pub value: Box<Expression>,
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
    pub then_block: Box<Expression>,
    pub else_block: Option<Box<Expression>>,
}

#[derive(Debug)]
pub struct PatternBindingCondition {
    pub pattern: Pattern,
    pub expression: Box<Expression>,
    pub span: Span,
}

#[derive(Debug)]
pub struct ClosureExpression {
    pub signature: FunctionSignature,
    pub body: Box<Expression>,
    pub span: Span,
}

#[derive(Debug)]
pub struct Path {
    pub span: Span,
    pub segments: Vec<PathSegment>,
}

#[derive(Debug)]
pub struct PathSegment {
    pub id: NodeID,
    pub identifier: Identifier,
    pub arguments: Option<TypeArguments>,
    pub span: Span,
}

#[derive(Debug)]
pub struct PathNode {
    pub id: NodeID,
    pub path: Path,
}

// Type
#[derive(Debug)]
pub struct Type {
    pub id: NodeID,
    pub span: Span,
    pub kind: TypeKind,
}

#[derive(Debug)]
pub enum TypeKind {
    /// `Foo` | `Foo[T]` | Foo.Bar | `Foo.Bar[T]`
    Nominal(Path),
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
    /// An Array with a fixed size `N`
    ///
    /// `[T;N]`
    Array { size: AnonConst, element: Box<Type> },
    /// A Dynamic, growable array
    ///
    /// `[T]`
    List(Box<Type>),
    /// A hash-map
    ///
    /// `[T:V]`
    Dictionary { key: Box<Type>, value: Box<Type> },

    /// (T, V) -> X
    Function {
        inputs: Vec<Box<Type>>,
        output: Box<Type>,
    },
    /// Ty of, self, &self, &const self
    ImplicitSelf,
    /// |a, b| a + b
    InferedClosureParameter,
    /// any T
    BoxedExistential { interfaces: Vec<PathNode> },
    /// _
    Infer,
}

// Patterns
#[derive(Debug)]
pub struct Pattern {
    pub id: NodeID,
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

#[derive(Debug)]
pub enum PatternPath {
    Qualified { path: Path },                  // A.B.C
    Inferred { name: Identifier, span: Span }, // .B
}

#[derive(Debug)]
pub struct PatternField {
    pub id: NodeID,
    pub identifier: Identifier,
    pub pattern: Pattern,
    pub span: Span,
}

// Generics

/// Represents the 'T: Foo' in Option<T: Foo>
#[derive(Debug)]
pub struct TypeParameter {
    pub id: NodeID,
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
    pub path: PathNode,
}

pub type GenericBounds = Vec<GenericBound>;

#[derive(Debug)]
pub struct Conformances {
    pub bounds: Vec<PathNode>,
    pub span: Span,
}

// ADT
#[derive(Debug)]
pub struct EnumCase {
    pub span: Span,
    pub variants: Vec<Variant>,
}

#[derive(Debug)]
pub struct Variant {
    pub id: NodeID,
    pub ctor_id: NodeID,
    pub identifier: Identifier,
    pub kind: VariantKind,
    pub discriminant: Option<AnonConst>,
    pub span: Span,
}

#[derive(Debug)]
pub enum VariantKind {
    Unit,
    Tuple(Vec<FieldDefinition>),
}

#[derive(Debug)]
pub struct FieldDefinition {
    pub id: NodeID,
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

    Index,
    IndexAssign,
}

impl TryFrom<DeclarationKind> for AssociatedDeclarationKind {
    type Error = DeclarationKind;

    fn try_from(kind: DeclarationKind) -> Result<AssociatedDeclarationKind, DeclarationKind> {
        Ok(match kind {
            DeclarationKind::Constant(node) => AssociatedDeclarationKind::Constant(node),
            DeclarationKind::Function(node) => AssociatedDeclarationKind::Function(node),
            DeclarationKind::Initializer(node) => AssociatedDeclarationKind::Initializer(node),
            DeclarationKind::Operator(node) => AssociatedDeclarationKind::Operator(node),
            DeclarationKind::TypeAlias(node) => AssociatedDeclarationKind::AssociatedType(node),
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
            DeclarationKind::Import(node) => FunctionDeclarationKind::Import(node),
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
            DeclarationKind::Import(node) => NamespaceDeclarationKind::Import(node),
            DeclarationKind::Export(node) => NamespaceDeclarationKind::Export(node),
            _ => return Err(kind),
        })
    }
}

// MARK - Visitor
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
        match VisitorResult::branch($e) {
            core::ops::ControlFlow::Continue(()) => (),
            #[allow(unreachable_code)]
            core::ops::ControlFlow::Break(r) => {
                return VisitorResult::from_residual(r);
            }
        }
    };
}

#[macro_export]
macro_rules! visit_optional {
    ($visitor: expr, $method: ident, $opt: expr $(, $($extra_args: expr),* )?) => {
        if let Some(x) = $opt {
            try_visit!($visitor.$method(x $(, $($extra_args,)* )?));
        }
    }
}

#[macro_export]
macro_rules! walk_list {
    ($visitor: expr, $method: ident, $list: expr $(, $($extra_args: expr),* )?) => {
        for elem in $list {
            try_visit!($visitor.$method(elem $(, $($extra_args,)* )?));
        }
    }
}

#[macro_export]
macro_rules! walk_visitable_list {
    ($visitor: expr, $list: expr $(, $($extra_args: expr),* )?) => {
        for elem in $list {
            try_visit!(elem.visit_with($visitor $(, $($extra_args,)* )?));
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AssocContext {
    Interface(NodeID),
    Extension(NodeID),
}

impl AssocContext {
    pub fn node_id(self) -> NodeID {
        match self {
            AssocContext::Interface(id) => id,
            AssocContext::Extension(id) => id,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UseTreeContext {
    Import(NodeID),
    Export(NodeID),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FunctionContext {
    Free,
    Foreign,
    Assoc(AssocContext),
    Initializer,
    Operator,
    Nested,
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

pub trait AstVisitor: Sized {
    type Result: VisitorResult = ();

    fn visit_package(&mut self, node: &Package) -> Self::Result {
        walk_package(self, node)
    }

    fn visit_module(&mut self, node: &Module, is_root: bool) -> Self::Result {
        walk_module(self, node)
    }

    fn visit_file(&mut self, node: &File) -> Self::Result {
        walk_file(self, node)
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

    fn visit_function_declaration(&mut self, node: &FunctionDeclaration) -> Self::Result {
        walk_function_declaration(self, node)
    }

    fn visit_namespace_declaration(&mut self, node: &NamespaceDeclaration) -> Self::Result {
        walk_namespace_declaration(self, node)
    }

    fn visit_statement(&mut self, node: &Statement) -> Self::Result {
        walk_statement(self, node)
    }
    fn visit_expression(&mut self, node: &Expression) -> Self::Result {
        walk_expression(self, node)
    }
    fn visit_type(&mut self, node: &Type) -> Self::Result {
        walk_type(self, node)
    }

    fn visit_pattern(&mut self, node: &Pattern) -> Self::Result {
        walk_pattern(self, node)
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

    fn visit_generic_where_clause(&mut self, node: &GenericWhereClause) -> Self::Result {
        walk_generic_where_clause(self, node)
    }

    fn visit_generic_requirement_list(&mut self, node: &GenericRequirementList) -> Self::Result {
        walk_generic_requirement_list(self, node)
    }

    fn visit_generic_requirement(&mut self, node: &GenericRequirement) -> Self::Result {
        walk_generic_requirement(self, node)
    }

    fn visit_generic_bounds(&mut self, node: &GenericBounds) -> Self::Result {
        walk_generic_bounds(self, node)
    }

    fn visit_generic_bound(&mut self, node: &GenericBound) -> Self::Result {
        walk_generic_bound(self, node)
    }

    fn visit_use_tree(&mut self, node: &UseTree, context: UseTreeContext) -> Self::Result {
        walk_use_tree(self, node, context)
    }

    fn visit_local(&mut self, node: &Local) -> Self::Result {
        walk_local(self, node)
    }

    fn visit_function(&mut self, id: NodeID, node: &Function, c: FunctionContext) -> Self::Result {
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

    fn visit_block(&mut self, node: &Block) -> Self::Result {
        walk_block(self, node)
    }
    fn visit_label(&mut self, node: &Label) -> Self::Result {
        walk_label(self, node)
    }

    fn visit_struct_definition(&mut self, node: &Struct) -> Self::Result {
        walk_struct_definition(self, node)
    }

    fn visit_enum_definition(&mut self, node: &Enum) -> Self::Result {
        walk_enum_definition(self, node)
    }
    fn visit_field_definition(&mut self, node: &FieldDefinition) -> Self::Result {
        walk_field_definition(self, node)
    }

    fn visit_enum_variant(&mut self, node: &Variant) -> Self::Result {
        walk_enum_variant(self, node)
    }

    fn visit_constant(&mut self, node: &Constant) -> Self::Result {
        walk_constant(self, node)
    }

    fn visit_initializer(&mut self, node: &Initializer, id: NodeID) -> Self::Result {
        walk_initializer(self, node, id)
    }

    fn visit_operator(&mut self, node: &Operator, id: NodeID) -> Self::Result {
        walk_operator(self, node, id)
    }

    fn visit_alias(&mut self, node: &TypeAlias) -> Self::Result {
        walk_alias(self, node)
    }

    fn visit_path(&mut self, p: &Path) -> Self::Result {
        walk_path(self, p)
    }
    fn visit_path_segment(&mut self, p: &PathSegment) -> Self::Result {
        walk_path_segment(self, p)
    }

    fn visit_type_arguments(&mut self, node: &TypeArguments) -> Self::Result {
        walk_type_arguments(self, node)
    }

    fn visit_type_argument(&mut self, node: &TypeArgument) -> Self::Result {
        walk_type_argument(self, node)
    }

    fn visit_pattern_field(&mut self, node: &PatternField) -> Self::Result {
        walk_pattern_field(self, node)
    }

    fn visit_pattern_path(&mut self, node: &PatternPath) -> Self::Result {
        walk_pattern_path(self, node)
    }

    fn visit_identifier(&mut self, node: &Identifier) -> Self::Result {
        Self::Result::output()
    }

    fn visit_anon_constant(&mut self, node: &AnonConst) -> Self::Result {
        walk_anon_const(self, node)
    }

    fn visit_attribute(&mut self, node: &Attribute) -> Self::Result {
        walk_attribute(self, node)
    }

    fn visit_expression_argument(&mut self, node: &ExpressionArgument) -> Self::Result {
        walk_expression_argument(self, node)
    }

    fn visit_map_pair(&mut self, node: &MapPair) -> Self::Result {
        walk_map_pair(self, node)
    }

    fn visit_match_arm(&mut self, node: &MatchArm) -> Self::Result {
        walk_match_arm(self, node)
    }

    fn visit_conformance(&mut self, node: &Conformances) -> Self::Result {
        walk_conformance(self, node)
    }

    fn visit_path_node(&mut self, node: &PathNode) -> Self::Result {
        walk_path_node(self, node)
    }
}

pub fn walk_package<V: AstVisitor>(visitor: &mut V, package: &Package) -> V::Result {
    visitor.visit_module(&package.root, true)
}

pub fn walk_module<V: AstVisitor>(visitor: &mut V, module: &Module) -> V::Result {
    let Module {
        files, submodules, ..
    } = module;
    walk_list!(visitor, visit_module, submodules, false);
    walk_list!(visitor, visit_file, files);
    V::Result::output()
}

pub fn walk_file<V: AstVisitor>(visitor: &mut V, file: &File) -> V::Result {
    let File { declarations, .. } = file;
    walk_list!(visitor, visit_declaration, declarations);
    V::Result::output()
}

pub fn walk_attribute<V: AstVisitor>(_visitor: &mut V, _attribute: &Attribute) -> V::Result {
    V::Result::output()
}

pub fn walk_declaration<V: AstVisitor>(visitor: &mut V, declaration: &Declaration) -> V::Result {
    walk_list!(visitor, visit_attribute, &declaration.attributes);
    visitor.visit_identifier(&declaration.identifier);

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
            try_visit!(visitor.visit_struct_definition(&node));
        }
        DeclarationKind::Enum(node) => {
            try_visit!(visitor.visit_enum_definition(&node));
        }
        DeclarationKind::Function(node) => {
            try_visit!(visitor.visit_function(declaration.id, node, FunctionContext::Free));
        }
        DeclarationKind::Variable(node) => {
            try_visit!(visitor.visit_local(&node));
        }
        DeclarationKind::Constant(node) => {
            try_visit!(visitor.visit_constant(&node));
        }
        DeclarationKind::Import(node) => {
            try_visit!(visitor.visit_use_tree(node, UseTreeContext::Import(declaration.id)))
        }
        DeclarationKind::Export(node) => {
            try_visit!(visitor.visit_use_tree(node, UseTreeContext::Export(declaration.id)))
        }
        DeclarationKind::Extension(node) => {
            try_visit!(visitor.visit_generics(&node.generics));
            try_visit!(visitor.visit_type(&node.ty));

            walk_list!(
                visitor,
                visit_assoc_declaration,
                &node.declarations,
                AssocContext::Extension(declaration.id)
            );
        }
        DeclarationKind::TypeAlias(node) => {
            try_visit!(visitor.visit_alias(&node));
        }
        DeclarationKind::Namespace(node) => {
            walk_list!(visitor, visit_namespace_declaration, &node.declarations);
        }
        DeclarationKind::Initializer(..) | DeclarationKind::Operator(..) => {
            unreachable!()
        }
    }

    V::Result::output()
}

pub fn walk_assoc_declaration<V: AstVisitor>(
    visitor: &mut V,
    declaration: &AssociatedDeclaration,
    context: AssocContext,
) -> V::Result {
    walk_list!(visitor, visit_attribute, &declaration.attributes);
    visitor.visit_identifier(&declaration.identifier);

    match &declaration.kind {
        AssociatedDeclarationKind::Constant(node) => {
            try_visit!(visitor.visit_constant(&node));
        }
        AssociatedDeclarationKind::Function(node) => {
            try_visit!(visitor.visit_function(
                declaration.id,
                node,
                FunctionContext::Assoc(context)
            ));
        }
        AssociatedDeclarationKind::Initializer(node) => {
            try_visit!(visitor.visit_initializer(&node, declaration.id));
        }
        AssociatedDeclarationKind::AssociatedType(node) => {
            try_visit!(visitor.visit_alias(&node));
        }
        AssociatedDeclarationKind::Operator(node) => {
            try_visit!(visitor.visit_operator(&node, declaration.id));
        }
    }

    V::Result::output()
}

pub fn walk_function_declaration<V: AstVisitor>(
    visitor: &mut V,
    declaration: &FunctionDeclaration,
) -> V::Result {
    walk_list!(visitor, visit_attribute, &declaration.attributes);
    visitor.visit_identifier(&declaration.identifier);

    match &declaration.kind {
        FunctionDeclarationKind::Struct(node) => {
            try_visit!(visitor.visit_struct_definition(node))
        }
        FunctionDeclarationKind::Enum(node) => {
            try_visit!(visitor.visit_enum_definition(node))
        }
        FunctionDeclarationKind::Function(node) => {
            try_visit!(visitor.visit_function(declaration.id, node, FunctionContext::Nested))
        }
        FunctionDeclarationKind::Constant(node) => {
            try_visit!(visitor.visit_constant(node))
        }
        FunctionDeclarationKind::TypeAlias(node) => {
            try_visit!(visitor.visit_alias(node))
        }
        FunctionDeclarationKind::Import(node) => {
            try_visit!(visitor.visit_use_tree(node, UseTreeContext::Import(declaration.id)))
        }
    }

    V::Result::output()
}

pub fn walk_namespace_declaration<V: AstVisitor>(
    visitor: &mut V,
    declaration: &NamespaceDeclaration,
) -> V::Result {
    walk_list!(visitor, visit_attribute, &declaration.attributes);
    visitor.visit_identifier(&declaration.identifier);
    match &declaration.kind {
        NamespaceDeclarationKind::Struct(node) => {
            try_visit!(visitor.visit_struct_definition(node))
        }
        NamespaceDeclarationKind::Enum(node) => {
            try_visit!(visitor.visit_enum_definition(node))
        }
        NamespaceDeclarationKind::Function(node) => {
            try_visit!(visitor.visit_function(declaration.id, node, FunctionContext::Free))
        }
        NamespaceDeclarationKind::Constant(node) => {
            try_visit!(visitor.visit_constant(node))
        }
        NamespaceDeclarationKind::TypeAlias(node) => {
            try_visit!(visitor.visit_alias(node))
        }
        NamespaceDeclarationKind::Namespace(node) => {
            walk_list!(visitor, visit_namespace_declaration, &node.declarations);
        }
        NamespaceDeclarationKind::Interface(node) => {
            try_visit!(visitor.visit_generics(&node.generics));
            walk_list!(
                visitor,
                visit_assoc_declaration,
                &node.declarations,
                AssocContext::Interface(declaration.id)
            );
        }
        NamespaceDeclarationKind::Import(node) => {
            try_visit!(visitor.visit_use_tree(node, UseTreeContext::Import(declaration.id)))
        }
        NamespaceDeclarationKind::Export(node) => {
            try_visit!(visitor.visit_use_tree(node, UseTreeContext::Export(declaration.id)))
        }
    }
    V::Result::output()
}

pub fn walk_statement<V: AstVisitor>(visitor: &mut V, s: &Statement) -> V::Result {
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
            visit_optional!(visitor, visit_identifier, label);
        }
        StatementKind::Continue(label) => {
            visit_optional!(visitor, visit_identifier, label);
        }
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
        StatementKind::While {
            label,
            condition,
            block,
        } => {
            visit_optional!(visitor, visit_label, label);
            try_visit!(visitor.visit_expression(condition));
            try_visit!(visitor.visit_block(block));
        }
        StatementKind::For(node) => {
            visit_optional!(visitor, visit_label, &node.label);
            try_visit!(visitor.visit_pattern(&node.pattern));
            try_visit!(visitor.visit_expression(&node.iterator));
            visit_optional!(visitor, visit_expression, &node.clause);
            try_visit!(visitor.visit_block(&node.block));
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

pub fn walk_expression<V: AstVisitor>(visitor: &mut V, node: &Expression) -> V::Result {
    match &node.kind {
        ExpressionKind::Wildcard | ExpressionKind::Literal(_) => {}
        ExpressionKind::Identifier(node) => {
            try_visit!(visitor.visit_identifier(node))
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
            walk_list!(visitor, visit_expression, expressions)
        }
        ExpressionKind::Tuple(expressions) => {
            walk_list!(visitor, visit_expression, expressions)
        }
        ExpressionKind::DictionaryLiteral(pairs) => {
            walk_list!(visitor, visit_map_pair, pairs)
        }
        ExpressionKind::If(node) => {
            try_visit!(visitor.visit_expression(&node.condition));
            try_visit!(visitor.visit_expression(&node.then_block));
            visit_optional!(visitor, visit_expression, &node.else_block);
        }
        ExpressionKind::Match(node) => {
            try_visit!(visitor.visit_expression(&node.value));
            walk_list!(visitor, visit_match_arm, &node.arms);
        }
        ExpressionKind::Call(expression, arguments) => {
            try_visit!(visitor.visit_expression(expression));
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
        ExpressionKind::TupleAccess(expression, _) => {
            try_visit!(visitor.visit_expression(expression));
        }
        ExpressionKind::AssignOp(_, lhs, rhs) => {
            try_visit!(visitor.visit_expression(lhs));
            try_visit!(visitor.visit_expression(rhs));
        }
        ExpressionKind::Assign(lhs, rhs) => {
            try_visit!(visitor.visit_expression(lhs));
            try_visit!(visitor.visit_expression(rhs));
        }
        ExpressionKind::Parenthesis(expression) => {
            try_visit!(visitor.visit_expression(expression));
        }
        ExpressionKind::CastAs(expression, ty) => {
            try_visit!(visitor.visit_expression(expression));
            try_visit!(visitor.visit_type(ty));
        }
        ExpressionKind::Ternary(lhs, mid, rhs) => {
            try_visit!(visitor.visit_expression(lhs));
            try_visit!(visitor.visit_expression(mid));
            try_visit!(visitor.visit_expression(rhs));
        }
        ExpressionKind::Pipe(lhs, rhs) => {
            try_visit!(visitor.visit_expression(lhs));
            try_visit!(visitor.visit_expression(rhs));
        }
        ExpressionKind::PatternBinding(condition) => {
            try_visit!(visitor.visit_pattern(&condition.pattern));
            try_visit!(visitor.visit_expression(&condition.expression));
        }
        ExpressionKind::OptionalPatternBinding(condition) => {
            try_visit!(visitor.visit_pattern(&condition.pattern));
            try_visit!(visitor.visit_expression(&condition.expression));
        }
        ExpressionKind::OptionalDefault(lhs, rhs) => {
            try_visit!(visitor.visit_expression(lhs));
            try_visit!(visitor.visit_expression(rhs));
        }
        ExpressionKind::Range(lhs, rhs, _) => {
            try_visit!(visitor.visit_expression(lhs));
            try_visit!(visitor.visit_expression(rhs));
        }
        ExpressionKind::Closure(expression) => {
            try_visit!(visitor.visit_function_signature(&expression.signature));
            try_visit!(visitor.visit_expression(&expression.body))
        }
        ExpressionKind::Block(block) => {
            try_visit!(visitor.visit_block(block));
        }
        ExpressionKind::OptionalUnwrap(expression) => {
            try_visit!(visitor.visit_expression(expression));
        }
        ExpressionKind::OptionalEvaluation(expression) => {
            try_visit!(visitor.visit_expression(expression));
        }
    };

    V::Result::output()
}

pub fn walk_type<V: AstVisitor>(visitor: &mut V, ty: &Type) -> V::Result {
    let Type { kind, .. } = ty;
    match kind {
        TypeKind::Nominal(path) => {
            try_visit!(visitor.visit_path(path));
        }
        TypeKind::Pointer(internal, _) => {
            try_visit!(visitor.visit_type(internal))
        }
        TypeKind::Reference(internal, _) => {
            try_visit!(visitor.visit_type(internal))
        }
        TypeKind::Parenthesis(internal) => {
            try_visit!(visitor.visit_type(internal))
        }
        TypeKind::Tuple(elems) => {
            walk_list!(visitor, visit_type, elems);
        }
        TypeKind::Optional(internal) => {
            try_visit!(visitor.visit_type(internal));
        }
        TypeKind::Array { size, element } => {
            try_visit!(visitor.visit_anon_constant(size));
            try_visit!(visitor.visit_type(element));
        }
        TypeKind::List(element) => {
            try_visit!(visitor.visit_type(element));
        }
        TypeKind::Dictionary { key, value } => {
            try_visit!(visitor.visit_type(key));
            try_visit!(visitor.visit_type(value));
        }
        TypeKind::Function { inputs, output } => {
            walk_list!(visitor, visit_type, inputs);
            try_visit!(visitor.visit_type(output));
        }
        TypeKind::BoxedExistential { interfaces } => {
            walk_list!(visitor, visit_path_node, interfaces);
        }
        TypeKind::ImplicitSelf => {}
        TypeKind::InferedClosureParameter => {}
        TypeKind::Infer => {}
    }
    V::Result::output()
}

pub fn walk_pattern<V: AstVisitor>(visitor: &mut V, pattern: &Pattern) -> V::Result {
    match &pattern.kind {
        PatternKind::Rest | PatternKind::Wildcard => {}
        PatternKind::Identifier(identifier) => {
            try_visit!(visitor.visit_identifier(identifier))
        }
        PatternKind::Member(pattern_path_head) => {}
        PatternKind::PathTuple { fields, .. } => {
            walk_list!(visitor, visit_pattern, fields);
        }
        PatternKind::PathStruct { fields, .. } => {
            walk_list!(visitor, visit_pattern_field, fields);
        }
        PatternKind::Tuple(patterns, _) => {
            walk_list!(visitor, visit_pattern, patterns);
        }
        PatternKind::Or(patterns, _) => {
            walk_list!(visitor, visit_pattern, patterns);
        }
        PatternKind::Literal(anon_const) => {
            try_visit!(visitor.visit_anon_constant(anon_const))
        }
    }

    V::Result::output()
}

pub fn walk_generics<V: AstVisitor>(visitor: &mut V, node: &Generics) -> V::Result {
    visit_optional!(visitor, visit_type_parameters, &node.type_parameters);
    visit_optional!(visitor, visit_generic_where_clause, &node.where_clause);
    V::Result::output()
}

pub fn walk_type_parameter<V: AstVisitor>(visitor: &mut V, parameter: &TypeParameter) -> V::Result {
    try_visit!(visitor.visit_identifier(&parameter.identifier));
    match &parameter.kind {
        TypeParameterKind::Constant { default, ty } => {
            try_visit!(visitor.visit_type(ty));
            visit_optional!(visitor, visit_anon_constant, default);
        }
        TypeParameterKind::Type { default } => {
            visit_optional!(visitor, visit_type, default);
        }
    }

    visit_optional!(visitor, visit_generic_bounds, &parameter.bounds);
    V::Result::output()
}

pub fn walk_type_parameters<V: AstVisitor>(
    visitor: &mut V,
    parameters: &TypeParameters,
) -> V::Result {
    walk_list!(visitor, visit_type_parameter, &parameters.parameters);
    V::Result::output()
}

pub fn walk_use_tree<V: AstVisitor>(
    visitor: &mut V,
    tree: &UseTree,
    context: UseTreeContext,
) -> V::Result {
    V::Result::output()
}

pub fn walk_local<V: AstVisitor>(visitor: &mut V, node: &Local) -> V::Result {
    try_visit!(visitor.visit_pattern(&node.pattern));
    visit_optional!(visitor, visit_type, &node.ty);
    visit_optional!(visitor, visit_expression, &node.initializer);
    V::Result::output()
}

pub fn walk_function<V: AstVisitor>(
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

pub fn walk_function_signature<V: AstVisitor>(
    visitor: &mut V,
    signature: &FunctionSignature,
) -> V::Result {
    try_visit!(visitor.visit_function_prototype(&signature.prototype));
    V::Result::output()
}

pub fn walk_function_prototype<V: AstVisitor>(
    visitor: &mut V,
    func: &FunctionPrototype,
) -> V::Result {
    walk_list!(visitor, visit_function_parameter, &func.inputs);
    visit_optional!(visitor, visit_type, &func.output);
    V::Result::output()
}

pub fn walk_function_parameter<V: AstVisitor>(
    visitor: &mut V,
    parameter: &FunctionParameter,
) -> V::Result {
    let FunctionParameter {
        name,
        annotated_type,
        default_value,
        ..
    } = parameter;

    try_visit!(visitor.visit_identifier(name));
    try_visit!(visitor.visit_type(annotated_type));
    visit_optional!(visitor, visit_expression, default_value);
    V::Result::output()
}

#[inline]
pub fn walk_block<V: AstVisitor>(visitor: &mut V, block: &Block) -> V::Result {
    walk_list!(visitor, visit_statement, &block.statements);
    V::Result::output()
}

#[inline]
pub fn walk_struct_definition<V: AstVisitor>(visitor: &mut V, node: &Struct) -> V::Result {
    try_visit!(visitor.visit_generics(&node.generics));
    walk_list!(visitor, visit_field_definition, &node.fields);
    V::Result::output()
}
#[inline]
pub fn walk_enum_definition<V: AstVisitor>(visitor: &mut V, node: &Enum) -> V::Result {
    try_visit!(visitor.visit_generics(&node.generics));
    let variants: Vec<&Variant> = node.cases.iter().flat_map(|v| &v.variants).collect();
    walk_list!(visitor, visit_enum_variant, variants);
    V::Result::output()
}

#[inline]
pub fn walk_enum_variant<V: AstVisitor>(visitor: &mut V, node: &Variant) -> V::Result {
    try_visit!(visitor.visit_identifier(&node.identifier));
    match &node.kind {
        VariantKind::Tuple(fields) => {
            walk_list!(visitor, visit_field_definition, fields);
        }
        _ => {}
    }
    visit_optional!(visitor, visit_anon_constant, &node.discriminant);
    V::Result::output()
}

#[inline]
pub fn walk_field_definition<V: AstVisitor>(
    visitor: &mut V,
    field_definition: &FieldDefinition,
) -> V::Result {
    try_visit!(visitor.visit_identifier(&field_definition.identifier));
    try_visit!(visitor.visit_type(&field_definition.ty));
    V::Result::output()
}

#[inline]
pub fn walk_anon_const<V: AstVisitor>(visitor: &mut V, anon_const: &AnonConst) -> V::Result {
    try_visit!(visitor.visit_expression(&anon_const.value));
    V::Result::output()
}

#[inline]
pub fn walk_constant<V: AstVisitor>(visitor: &mut V, node: &Constant) -> V::Result {
    try_visit!(visitor.visit_type(&node.ty));
    visit_optional!(visitor, visit_expression, &node.expr);
    V::Result::output()
}

#[inline]
pub fn walk_initializer<V: AstVisitor>(
    visitor: &mut V,
    node: &Initializer,
    id: NodeID,
) -> V::Result {
    try_visit!(visitor.visit_function(id, &node.function, FunctionContext::Initializer));
    V::Result::output()
}

#[inline]
pub fn walk_operator<V: AstVisitor>(visitor: &mut V, node: &Operator, id: NodeID) -> V::Result {
    try_visit!(visitor.visit_function(id, &node.function, FunctionContext::Operator));
    V::Result::output()
}

#[inline]
pub fn walk_alias<V: AstVisitor>(visitor: &mut V, node: &TypeAlias) -> V::Result {
    try_visit!(visitor.visit_generics(&node.generics));
    visit_optional!(visitor, visit_type, &node.ty);
    visit_optional!(visitor, visit_generic_bounds, &node.bounds);
    V::Result::output()
}

pub fn walk_label<V: AstVisitor>(visitor: &mut V, label: &Label) -> V::Result {
    try_visit!(visitor.visit_identifier(&label.identifier));
    V::Result::output()
}

pub fn walk_type_arguments<V: AstVisitor>(visitor: &mut V, arguments: &TypeArguments) -> V::Result {
    let tys = &arguments.arguments;
    walk_list!(visitor, visit_type_argument, tys);
    V::Result::output()
}

pub fn walk_type_argument<V: AstVisitor>(visitor: &mut V, argument: &TypeArgument) -> V::Result {
    match argument {
        TypeArgument::Type(ty) => try_visit!(visitor.visit_type(ty)),
        TypeArgument::Const(anon_const) => try_visit!(visitor.visit_anon_constant(anon_const)),
    }
    V::Result::output()
}

pub fn walk_generic_where_clause<V: AstVisitor>(
    visitor: &mut V,
    node: &GenericWhereClause,
) -> V::Result {
    try_visit!(visitor.visit_generic_requirement_list(&node.requirements));
    V::Result::output()
}

pub fn walk_generic_requirement_list<V: AstVisitor>(
    visitor: &mut V,
    node: &GenericRequirementList,
) -> V::Result {
    walk_list!(visitor, visit_generic_requirement, node);
    V::Result::output()
}

pub fn walk_generic_requirement<V: AstVisitor>(
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

pub fn walk_generic_bounds<V: AstVisitor>(visitor: &mut V, node: &GenericBounds) -> V::Result {
    walk_list!(visitor, visit_generic_bound, node);
    V::Result::output()
}

pub fn walk_generic_bound<V: AstVisitor>(visitor: &mut V, node: &GenericBound) -> V::Result {
    try_visit!(visitor.visit_path(&node.path.path));
    V::Result::output()
}

pub fn walk_pattern_field<V: AstVisitor>(visitor: &mut V, node: &PatternField) -> V::Result {
    try_visit!(visitor.visit_identifier(&node.identifier));
    try_visit!(visitor.visit_pattern(&node.pattern));
    V::Result::output()
}

pub fn walk_pattern_path<V: AstVisitor>(visitor: &mut V, node: &PatternPath) -> V::Result {
    match node {
        PatternPath::Qualified { path, .. } => {
            todo!()
        }
        PatternPath::Inferred { name, .. } => {
            try_visit!(visitor.visit_identifier(&name));
        }
    }
    V::Result::output()
}

pub fn walk_path<V: AstVisitor>(visitor: &mut V, path: &Path) -> V::Result {
    walk_list!(visitor, visit_path_segment, &path.segments);
    V::Result::output()
}

pub fn walk_path_segment<V: AstVisitor>(visitor: &mut V, path_segment: &PathSegment) -> V::Result {
    try_visit!(visitor.visit_identifier(&path_segment.identifier));
    visit_optional!(visitor, visit_type_arguments, &path_segment.arguments);
    V::Result::output()
}

pub fn walk_expression_argument<V: AstVisitor>(
    visitor: &mut V,
    arg: &ExpressionArgument,
) -> V::Result {
    visit_optional!(visitor, visit_label, &arg.label);
    try_visit!(visitor.visit_expression(&arg.expression));
    V::Result::output()
}

pub fn walk_map_pair<V: AstVisitor>(visitor: &mut V, node: &MapPair) -> V::Result {
    try_visit!(visitor.visit_expression(&node.key));
    try_visit!(visitor.visit_expression(&node.value));
    V::Result::output()
}

pub fn walk_match_arm<V: AstVisitor>(visitor: &mut V, node: &MatchArm) -> V::Result {
    try_visit!(visitor.visit_pattern(&node.pattern));
    visit_optional!(visitor, visit_expression, &node.guard);
    try_visit!(visitor.visit_expression(&node.body));

    V::Result::output()
}

pub fn walk_conformance<V: AstVisitor>(visitor: &mut V, node: &Conformances) -> V::Result {
    walk_list!(visitor, visit_path_node, &node.bounds);
    V::Result::output()
}

pub fn walk_path_node<V: AstVisitor>(visitor: &mut V, node: &PathNode) -> V::Result {
    try_visit!(visitor.visit_path(&node.path));
    V::Result::output()
}

impl Pattern {
    pub fn walk(&self, action: &mut impl FnMut(&Pattern) -> bool) {
        if !action(self) {
            return;
        }

        match &self.kind {
            PatternKind::Wildcard
            | PatternKind::Rest
            | PatternKind::Literal(..)
            | PatternKind::Identifier(..)
            | PatternKind::Member(..) => {}
            PatternKind::PathStruct { fields, .. } => {
                fields.iter().for_each(|f| f.pattern.walk(action))
            }
            PatternKind::Tuple(sub_pats, ..)
            | PatternKind::PathTuple {
                fields: sub_pats, ..
            }
            | PatternKind::Or(sub_pats, _) => {
                sub_pats.iter().for_each(|p| p.walk(action));
            }
        }
    }
}
