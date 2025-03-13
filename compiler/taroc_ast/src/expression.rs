use super::{
    Block, FunctionSignature, Label, Literal, MatchingPattern, Mutability, Path, PathSegment,
    StatementConditionList, Type,
};
use taroc_span::{Identifier, Span};
use taroc_token::{BinaryOperator, UnaryOperator};

#[derive(Debug)]
pub struct Expression {
    pub kind: ExpressionKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum ExpressionKind {
    Literal(Literal),
    // foo | foo::bar | foo::bar<baz>
    Path(Path),
    /// `[a, b, c]`
    Array(Vec<Box<Expression>>),
    /// `(a, b, c)`
    Tuple(Vec<Box<Expression>>),
    /// `["a" : 100]`
    Dictionary(Vec<MapPair>),
    /// `if foo { } else { }`
    If(IfExpression),
    /// `when foo {
    ///     _ => ...
    ///     <expr> => ...
    ///     is <pattern> => ...
    /// }`
    When(WhenExpression),
    /// `main()`
    FunctionCall(Box<Expression>, Vec<ExpressionArgument>),
    /// `foo.bar()`
    MethodCall(MethodCall),
    /// `a + b`
    Binary(BinaryOperator, Box<Expression>, Box<Expression>),
    /// `!a`
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
    /// `(a)`
    Parenthesis(Box<Expression>),
    /// `a as int`
    CastAs(Box<Expression>, Box<Type>),
    /// `a ? b : c`
    Ternary(Box<Expression>, Box<Expression>, Box<Expression>),
    /// `a!`
    ForceUnwrap(Box<Expression>),
    /// `a?`
    OptionalUnwrap(Box<Expression>),
    ///
    OptionalEvaluation(Box<Expression>),
    /// `a |> b`
    Pipe(Box<Expression>, Box<Expression>),
    /// A Binding Condition used to unwrap an optional value, conditions may only appear `if`, `guard` & `while` conditions
    ///
    /// `if let foo {}`
    ///
    /// `if let foo = bar {}`
    ///
    /// `guard let foo else { return }`
    ///
    /// `guard let foo = bar else { return }`
    ///
    /// `while let foo {}`
    ///
    /// `while let foo = bar {}`
    OptionalBinding(OptionalBindingCondition),
    /// A Binding Condition used for Tagged Unions
    ///
    /// `if match Option::Some(value) = foo {}`
    ///
    /// `guard match Option::Some(value) = foo else { return }`
    ///
    /// `while match Option::Some(value) = foo {}`
    MatchBinding(PatternBindingCondition),
    /// `a ?? b`
    OptionalDefault(Box<Expression>, Box<Expression>),
    /// An ensure statement offers a cleaner way to deal with the `Result<T, E>` type.
    ///
    /// `let foo = ensure bar()` // `foo` will be of type `T` or the function will return `Result.Failure(E)`
    ///
    /// `let foo = ensure? bar()` // `foo` will be of type `Optional<T>`, the function will not return early, rather the error value will be discarded
    ///
    /// `let foo = ensure! bar()` // `foo` will be of type `T` if the result expects Result<Option<T>>, the function will not return early, rather the error value will be discarded
    Ensure(EnsureMode, Box<Expression>),
    /// lhs..rhs | lhs..=rhs, bool indicates inclusiveness
    Range(Box<Expression>, Box<Expression>, bool),
    /// `_`
    Wildcard,
    /// { a, b in a + b }
    Closure(ClosureExpression),
    /// await foo.bar()
    Await(Box<Expression>),
    /// unsafe {}
    Unsafe(Block),
    /// { }, only used by when expression atm
    Block(Block),
    /// Trailing closure
    TrailingClosure(Box<Expression>, Box<Expression>),
    /// ::Foo
    InferMember(Path),
}

#[derive(Debug)]
pub struct AnonConst {
    pub value: Box<Expression>,
}

#[derive(Debug)]
pub struct MapPair {
    pub key: Box<Expression>,
    pub value: Box<Expression>,
}

#[derive(Debug)]
pub struct WhenExpression {
    pub value: Option<Box<Expression>>,
    pub arms: Vec<WhenArm>,
}

#[derive(Debug)]
pub struct WhenArm {
    pub kind: WhenArmKind,
    pub body: Box<Expression>,
    pub span: Span,
}

#[derive(Debug)]
pub enum WhenArmKind {
    // is <Pat> =>
    Pattern(MatchingPattern),
    // <expr> =>
    Expression(StatementConditionList),
}

#[derive(Debug)]
pub struct ExpressionArgument {
    pub label: Option<Label>,
    pub expression: Box<Expression>,
    pub span: Span,
}

#[derive(Debug)]
pub enum EnsureMode {
    Full,     // !
    Partial,  // ?
    Inherent, //
}

#[derive(Debug)]
pub struct IfExpression {
    pub conditions: StatementConditionList,
    pub body: Block,
    pub else_block: Option<Box<Expression>>,
}

#[derive(Debug)]
pub struct MethodCall {
    pub receiver: Box<Expression>,
    pub method: PathSegment,
    pub arguments: Vec<ExpressionArgument>,
    pub span: Span,
}

#[derive(Debug)]
pub struct OptionalBindingCondition {
    pub is_shorthand: bool,
    pub identifier: Identifier,
    pub expression: Option<Box<Expression>>,
    pub mutability: Mutability,
    pub span: Span,
}

#[derive(Debug)]
pub struct PatternBindingCondition {
    pub pattern: MatchingPattern,
    pub expression: Box<Expression>,
    pub span: Span,
}

#[derive(Debug)]
pub struct ClosureExpression {
    pub signature: FunctionSignature,
    pub body: Block,
    pub span: Span,
}
