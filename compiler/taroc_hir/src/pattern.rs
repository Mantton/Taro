use taroc_ast::Mutability;
use taroc_span::{Identifier, Span};

use super::{Label, NodeID, expression::AnonConst, path::Path};
#[derive(Debug, Clone)]
pub struct MatchingPattern {
    pub id: NodeID,
    pub span: Span,
    pub kind: MatchingPatternKind,
}

#[derive(Debug, Clone)]
pub struct BindingMode(pub Mutability);
#[derive(Debug, Clone)]
pub enum MatchingPatternKind {
    /// _
    Wildcard,
    /// ..
    Rest,
    // foo | var foo
    Binding(Identifier),
    // (a, b)
    Tuple(Vec<MatchingPattern>, Span),
    // Foo::Bar(a, b)
    Path(Path),
    // Foo::Bar(a, b)
    PathTuple(Path, Vec<LabeledMatchingPattern>, Span),
    // Foo::Bar { a, b, .. }
    PathStruct(Path, Vec<PatternField>, Span, bool),
    // Foo | Bar
    Or(Vec<MatchingPattern>, Span),
    // Anon Consts in Pattern Type
    Literal(AnonConst),
}

#[derive(Debug, Clone)]
pub struct LabeledMatchingPattern {
    pub label: Option<Label>,
    pub pattern: MatchingPattern,
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
