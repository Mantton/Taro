use super::{
    NodeID,
    block::Block,
    function::FunctionPrototype,
    label::Label,
    literal::Literal,
    path::{Path, PathSegment},
    pattern::MatchingPattern,
    ty::Type,
};
use taroc_ast_ir::{BinaryOperator, UnaryOperator};
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
    When(WhenExpression),
    /// `main()`
    FunctionCall(Box<Expression>, Vec<ExpressionArgument>),
    /// `foo.bar()`
    MethodCall(MethodCall),
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
    /// `if match Some(value) = foo {}`
    MatchBinding(PatternBindingCondition),
    /// |a, b| { a + b }
    Closure(ClosureExpression),
    /// { <stmt_list> }
    Block(Block),
    /// await foo.bar()
    Await(Box<Expression>),
    // Lowered away

    // `(a)`
    // Parenthesis(Box<Expression>),
    // `a ? b : c`
    // Ternary(Box<Expression>, Box<Expression>, Box<Expression>),
    // `a!`
    // ForceUnwrap(Box<Expression>),
    // `a?`
    // OptionalUnwrap(Box<Expression>),
    //
    // OptionalEvaluation(Box<Expression>),
    // `a |> b`
    // Pipe(Box<Expression>, Box<Expression>),
    // `a ?? b`
    // OptionalDefault(Box<Expression>, Box<Expression>),
    //
    // An ensure statement offers a cleaner way to deal with the `Result<T, E>` type.
    //
    // `let foo = ensure bar()` // `foo` will be of type `T` or the function will return `Result.Failure(E)`
    //
    // `let foo = ensure? bar()` // `foo` will be of type `Optional<T>`, the function will not return early, rather the error value will be discarded
    //
    // `let foo = ensure! bar()` // `foo` will be of type `T` if the result expects Result<Option<T>>, the function will not return early, rather the error value will be discarded
    // Ensure(EnsureMode, Box<Expression>),
    // `["a" : 100]`
    // Dictionary(Vec<MapPair>),
    // A Binding Condition used to unwrap an optional value, conditions may only appear `if`, `guard` & `while` conditions

    // `if let foo {}`

    // `if let foo = bar {}`

    // `guard let foo else { return }`

    // `guard let foo = bar else { return }`

    // `while let foo {}`

    // `while let foo = bar {}`
    // OptionalBinding(OptionalBindingCondition),
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
pub struct PatternBindingCondition {
    pub expression: Box<Expression>,
    pub pattern: MatchingPattern,
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
pub struct WhenExpression {
    pub value: Box<Expression>,
    pub arms: Vec<WhenArm>,
    pub kind: WhenExpressionKind,
}

#[derive(Debug, Clone, Copy)]
pub enum WhenExpressionKind {
    Expression,
    Pattern,
}

#[derive(Debug, Clone)]
pub struct WhenArm {
    pub kind: WhenArmKind,
    pub body: Box<Expression>,
    pub guard: Option<Box<Expression>>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum WhenArmKind {
    // is <Pat> =>
    Pattern(MatchingPattern),
    // <expr> =>
    Expression(Vec<Box<Expression>>),

    Default,
}
