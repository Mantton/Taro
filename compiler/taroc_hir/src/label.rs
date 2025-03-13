use taroc_span::{Identifier, Span};

#[derive(Debug, Clone)]
pub struct Label {
    pub identifier: Identifier,
    pub span: Span,
}
