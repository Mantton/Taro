use taroc_span::{Identifier, Span};

use super::{NodeID, generics::TypeArguments};

#[derive(Debug)]
pub struct Path {
    pub span: Span,
    pub segments: Vec<PathSegment>,
}

#[derive(Debug)]
pub struct PathSegment {
    pub id: NodeID,
    pub identifier: Identifier,
    pub arguments: Option<TypeArguments>,
}
