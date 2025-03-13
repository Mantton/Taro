use taroc_span::Span;

#[derive(Debug, Clone, Copy)]
pub struct Visibility {
    pub span: Span,
    pub level: VisibilityLevel,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VisibilityLevel {
    Public,
    Inherent,
}
