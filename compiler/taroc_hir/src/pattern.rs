use super::{NodeID, expression::AnonConst, path::Path};
use taroc_span::{Identifier, Span};

#[derive(Debug, Clone)]
pub struct Pattern {
    pub id: NodeID,
    pub span: Span,
    pub kind: PatternKind,
}

#[derive(Debug, Clone)]
pub enum PatternKind {
    /// _
    Wildcard,
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

#[derive(Debug, Clone)]
pub struct PatternField {
    pub id: NodeID,
    pub identifier: Identifier,
    pub pattern: Pattern,
    pub span: Span,
}

impl Pattern {
    pub fn walk(&self, action: &mut impl FnMut(&Pattern) -> bool) {
        if !action(self) {
            return;
        }

        match &self.kind {
            PatternKind::Wildcard
            | PatternKind::Literal(..)
            | PatternKind::Identifier(..)
            | PatternKind::Path(..) => {}
            PatternKind::PathStruct(_, fields, ..) => {
                fields.iter().for_each(|f| f.pattern.walk(action))
            }
            PatternKind::Tuple(sub_pats, ..)
            | PatternKind::PathTuple(_, sub_pats, _)
            | PatternKind::Or(sub_pats, _) => {
                sub_pats.iter().for_each(|p| p.walk(action));
            }
        }
    }
}

use std::hash::{Hash, Hasher};

impl PartialEq for Pattern {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for Pattern {}

impl Hash for Pattern {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}
