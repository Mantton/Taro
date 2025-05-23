use super::{NodeID, expression::AnonConst, path::Path};
use taroc_ast_ir::BindingMode;
use taroc_span::{Identifier, Span};

#[derive(Debug, Clone)]
pub struct MatchingPattern {
    pub id: NodeID,
    pub span: Span,
    pub kind: MatchingPatternKind,
}

#[derive(Debug, Clone)]
pub enum MatchingPatternKind {
    /// _
    Wildcard,
    /// ..
    Rest,
    // foo | var foo
    Binding(BindingMode, Identifier),
    // (a, b)
    Tuple(Vec<MatchingPattern>, Span),
    // Foo::Bar(a, b)
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

#[derive(Debug, Clone)]
pub struct BindingPattern {
    pub id: NodeID,
    pub span: Span,
    pub kind: BindingPatternKind,
}

#[derive(Debug, Clone)]
pub enum BindingPatternKind {
    Wildcard,
    Identifier(Identifier),
    Tuple(Vec<BindingPattern>),
}

#[derive(Debug, Clone)]
pub struct PatternField {
    pub id: NodeID,
    pub identifier: Identifier,
    pub pattern: Option<MatchingPattern>,
    pub span: Span,
}
