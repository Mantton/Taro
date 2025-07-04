use taroc_span::{Identifier, Span};

#[derive(Debug, Clone, Copy)]
pub struct Label {
    pub identifier: Identifier,
    pub span: Span,
}
