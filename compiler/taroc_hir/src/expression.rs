use super::{
    NodeID,
    block::Block,
    function::FunctionPrototype,
    label::Label,
    literal::Literal,
    path::{Path, PathSegment},
    pattern::Pattern,
    ty::Type,
};
use taroc_ast_ir::{BinaryOperator, Mutability, UnaryOperator};
use taroc_span::{Identifier, Span};

#[derive(Debug, Clone)]
pub struct Expression {
    pub id: NodeID,
    pub kind: ExpressionKind,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum ExpressionKind {
    Malformed,
    Literal(Literal),
    // foo | foo::bar | foo::bar<baz>
    Path(Path),
    /// Foo::Bar { a: 10, b: 20 }
    StructLiteral(StructLiteral),
    /// `[a, b, c]`
    ArrayLiteral(Vec<Box<Expression>>),
    /// `(a, b, c)`
    Tuple(Vec<Box<Expression>>),
    /// `if foo { } else { }`
    If(IfExpression),
    Match(MatchExpression),
    /// `main()`
    FunctionCall(Box<Expression>, Vec<ExpressionArgument>),
    /// `foo.bar()`
    MethodCall(MethodCall),
    /// &a | &const T
    Reference(Box<Expression>, Mutability),
    /// *a
    Dereference(Box<Expression>),
    /// `a + b`
    Binary(BinaryOperator, Box<Expression>, Box<Expression>),
    // !a
    // &a
    // *a
    // -a
    // ~a
    Unary(UnaryOperator, Box<Expression>),
    /// `a.b`
    FieldAccess(Box<Expression>, PathSegment),
    /// `a.1`
    TupleAccess(Box<Expression>, AnonConst),
    /// `a[b]`
    Subscript(Box<Expression>, Vec<ExpressionArgument>),
    ///` a += b`
    AssignOp(BinaryOperator, Box<Expression>, Box<Expression>),
    ///` a = b`
    Assign(Box<Expression>, Box<Expression>),
    /// `a as int`
    CastAs(Box<Expression>, Box<Type>),
    /// A Binding Condition used for Tagged Unions
    ///
    /// `if let Some(value) = foo {}`
    PatternBinding(PatternBinding),
    /// |a, b| { a + b }
    Closure(ClosureExpression),
    /// { <stmt_list> }
    Block(Block),
    /// await foo.bar()
    Await(Box<Expression>),
}

#[derive(Debug, Clone)]
pub struct AnonConst {
    pub value: Box<Expression>,
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
pub struct MethodCall {
    pub receiver: Box<Expression>,
    pub method: PathSegment,
    pub arguments: Vec<ExpressionArgument>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct PatternBinding {
    pub expression: Box<Expression>,
    pub pattern: Pattern,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct ClosureExpression {
    pub prototype: FunctionPrototype,
    pub body: Block,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct ExpressionField {
    pub label: Identifier,
    pub expression: Box<Expression>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct StructLiteral {
    pub path: Path,
    pub fields: Vec<ExpressionField>,
}

#[derive(Debug, Clone)]
pub struct MatchExpression {
    pub value: Box<Expression>,
    pub arms: Vec<MatchArm>,
}

#[derive(Debug, Clone)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub body: Box<Expression>,
    pub guard: Option<Box<Expression>>,
    pub span: Span,
}
