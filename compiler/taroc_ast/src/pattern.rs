use super::{AnonConst, Path};
use taroc_ast_ir::BindingMode;
use taroc_span::{Identifier, Span};

#[derive(Debug)]
pub struct MatchingPattern {
    pub span: Span,
    pub kind: MatchingPatternKind,
}

#[derive(Debug)]
pub enum MatchingPatternKind {
    /// _
    Wildcard,
    /// ..
    Rest,
    // foo | var foo
    Binding(BindingMode, Identifier),
    // (a, b)
    Tuple(Vec<MatchingPattern>, Span),
    // Foo::Bar
    Path(Path),
    // Foo::Bar(a, b)
    PathTuple(Path, Vec<MatchingPattern>, Span),
    // Foo::Bar { a, b, .. }
    PathStruct(Path, Vec<PatternField>, Span, bool),
    // Foo | Bar
    Or(Vec<MatchingPattern>, Span),
    // Anon Consts in Pattern Type
    Literal(AnonConst),
}

#[derive(Debug)]
pub struct BindingPattern {
    pub span: Span,
    pub kind: BindingPatternKind,
}

#[derive(Debug)]
pub enum BindingPatternKind {
    Wildcard,
    Identifier(Identifier),
    Tuple(Vec<BindingPattern>),
}

#[derive(Debug)]
pub struct PatternField {
    pub identifier: Identifier,
    pub pattern: Option<MatchingPattern>,
    pub span: Span,
}
