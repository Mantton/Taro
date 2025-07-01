use super::{
    Block, FunctionSignature, Label, Literal, Path, PathSegment, Pattern, StatementConditionList,
    Type,
};
use taroc_ast_ir::{BinaryOperator, UnaryOperator};
use taroc_span::Span;

#[derive(Debug)]
pub struct Expression {
    pub kind: ExpressionKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum ExpressionKind {
    Malformed,
    Literal(Literal),
    // foo | foo::bar | foo::bar<baz>
    Path(Path),
    /// Foo::Bar { a: 10, b: 20 }
    StructLiteral(StructLiteral),
    /// `[a, b, c]`
    Array(Vec<Box<Expression>>),
    /// `(a, b, c)`
    Tuple(Vec<Box<Expression>>),
    /// `["a" : 100]`
    DictionaryLiteral(Vec<MapPair>),
    /// `if foo { } else { }`
    If(IfExpression),
    /// `when foo {
    ///     <pattern> => ...
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
    /// A Binding Condition used for Tagged Unions
    ///
    /// `if let Option::Some(value) = foo {}`
    ///
    /// `guard let Option::Some(value) = foo else { return }`
    ///
    /// `while let Option::Some(value) = foo {}`
    PatternBinding(PatternBindingCondition),
    /// `a ?? b`
    OptionalDefault(Box<Expression>, Box<Expression>),
    /// An ensure statement offers a cleaner way to deal with the `Result<T, E>` or `Option<T>` type.
    ///
    /// `let foo = ensure bar()` // `foo` will be of type `T` or the function will return `Result.Failure(E)` | Option.None
    Ensure(Box<Expression>),
    /// lhs..rhs | lhs..=rhs, bool indicates inclusiveness
    Range(Box<Expression>, Box<Expression>, bool),
    /// `_`
    Wildcard,
    /// |a, b| a + b
    Closure(ClosureExpression),
    /// await foo.bar()
    Await(Box<Expression>),
    /// { }
    Block(Block),
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
    pub kw_span: Span,
}

#[derive(Debug)]
pub struct WhenArm {
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

#[derive(Debug)]
pub struct ExpressionField {
    pub is_shorthand: bool,
    pub label: Option<Label>,
    pub expression: Box<Expression>,
    pub span: Span,
}

#[derive(Debug)]
pub struct StructLiteral {
    pub path: Path,
    pub fields: Vec<ExpressionField>,
}
