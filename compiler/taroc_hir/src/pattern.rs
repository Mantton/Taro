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
    pub pattern: MatchingPattern,
    pub span: Span,
}

impl MatchingPattern {
    pub fn walk(&self, action: &mut impl FnMut(&MatchingPattern) -> bool) {
        if !action(self) {
            return;
        }

        match &self.kind {
            MatchingPatternKind::Wildcard
            | MatchingPatternKind::Literal(..)
            | MatchingPatternKind::Binding(..)
            | MatchingPatternKind::Path(..) => {}
            MatchingPatternKind::PathStruct(_, fields, ..) => {
                fields.iter().for_each(|f| f.pattern.walk(action))
            }
            MatchingPatternKind::Tuple(sub_pats, ..)
            | MatchingPatternKind::PathTuple(_, sub_pats, _)
            | MatchingPatternKind::Or(sub_pats, _) => {
                sub_pats.iter().for_each(|p| p.walk(action));
            }
        }
    }
}
