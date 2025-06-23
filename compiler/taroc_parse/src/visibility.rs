use super::package::{Parser, R};
use taroc_ast::{Visibility, VisibilityLevel};
use taroc_token::TokenKind;

impl Parser {
    pub fn parse_visibility(&mut self) -> R<Visibility> {
        let lo = self.lo_span();
        let level = if self.eat(TokenKind::Public) {
            VisibilityLevel::Public
        } else if self.eat(TokenKind::Private) {
            VisibilityLevel::Private
        } else {
            VisibilityLevel::Inherent
        };

        Ok(Visibility {
            span: lo.to(self.hi_span()),
            level,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::make_parser;
    use taroc_span::session_test;

    #[test]
    fn test_public_visibility() {
        session_test!({
            let mut parser = make_parser!("public");
            let vis = parser.parse_visibility().expect("visibility");
            assert_eq!(vis.level, VisibilityLevel::Public);
        });
    }

    #[test]
    fn test_private_visibility() {
        session_test!({
            let mut parser = make_parser!("private");
            let vis = parser.parse_visibility().expect("visibility");
            assert_eq!(vis.level, VisibilityLevel::Private);
        });
    }

    #[test]
    fn test_default_visibility() {
        session_test!({
            let mut parser = make_parser!("");
            let vis = parser.parse_visibility().expect("visibility");
            assert_eq!(vis.level, VisibilityLevel::Inherent);
        });
    }
}
