use super::{AnonConst, Path};
use taroc_span::{Identifier, Span};

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
    // foo
    Identifier(Identifier),
    // (a, b)
    Tuple(Vec<Pattern>, Span),
    // Foo::Bar
    Path(Path),
    // Foo::Bar(a, b)
    PathTuple(Path, Vec<Pattern>, Span),
    // Foo::Bar { a, b, .. }
    PathStruct(Path, Vec<PatternField>, Span, bool),
    // Foo | Bar
    Or(Vec<Pattern>, Span),
    // Anon Consts in Pattern Type
    Literal(AnonConst),
}

#[derive(Debug)]
pub struct PatternField {
    pub identifier: Identifier,
    pub pattern: Pattern,
    pub span: Span,
}
