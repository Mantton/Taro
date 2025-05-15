use taroc_span::{Identifier, Span};

use super::{NodeID, generics::TypeArguments};

#[derive(Debug, Clone)]
pub struct Path {
    pub span: Span,
    pub segments: Vec<PathSegment>,
}

#[derive(Debug, Clone)]
pub struct PathSegment {
    pub id: NodeID,
    pub identifier: Identifier,
    pub arguments: Option<TypeArguments>,
    pub span: Span,
}
