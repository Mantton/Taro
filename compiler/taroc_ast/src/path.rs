use super::generics::TypeArguments;
use taroc_span::{Identifier, Span};

#[derive(Debug)]
pub struct Path {
    pub span: Span,
    pub segments: Vec<PathSegment>,
}

#[derive(Debug)]
pub struct PathSegment {
    pub identifier: Identifier,
    pub arguments: Option<TypeArguments>,
    pub span: Span,
}
