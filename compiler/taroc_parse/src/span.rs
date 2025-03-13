use taroc_span::Span;

use super::package::Parser;

impl Parser {
    pub fn lo_span(&self) -> Span {
        self.current()
            .map(|token| token.span)
            .unwrap_or(Span::empty(self.file.file))
    }

    pub fn hi_span(&self) -> Span {
        self.previous()
            .map(|token| token.span)
            .unwrap_or(Span::empty(self.file.file))
    }
}
