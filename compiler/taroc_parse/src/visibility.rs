use super::package::{Parser, R};
use taroc_ast::{Visibility, VisibilityLevel};
use taroc_token::TokenKind;

impl Parser {
    pub fn parse_visibility(&mut self) -> R<Visibility> {
        let lo = self.lo_span();
        let level = if self.eat(TokenKind::Public) {
            VisibilityLevel::Public
        } else {
            VisibilityLevel::Inherent
        };

        Ok(Visibility {
            span: lo.to(self.hi_span()),
            level,
        })
    }
}
