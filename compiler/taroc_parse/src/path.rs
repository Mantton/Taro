use super::package::{Parser, R};
use taroc_ast::{Path, PathSegment};
use taroc_token::TokenKind;

impl Parser {
    pub fn parse_path(&mut self) -> R<Path> {
        let start_span = self.lo_span();

        let mut segments = Vec::new();
        loop {
            let segment = self.parse_path_segment(true)?;
            segments.push(segment);

            if self.eat(TokenKind::Scope) {
                self.consume_new_lines();
                continue;
            } else {
                break;
            }
        }

        let p = Path {
            segments,
            span: start_span.to(self.hi_span()),
        };

        Ok(p)
    }

    pub fn parse_path_segment(&mut self, allow_generics: bool) -> R<PathSegment> {
        let lo = self.lo_span();
        let identifier = self.parse_identifier()?;
        let arguments = if allow_generics
            && self.matches(TokenKind::LChevron)
            && self.can_parse_type_arguments()
        {
            Some(self.parse_type_arguments()?)
        } else {
            None
        };

        let segment = PathSegment {
            identifier,
            arguments,
            span: lo.to(self.hi_span()),
        };

        Ok(segment)
    }
}

impl Parser {
    pub fn parse_module_path(&mut self) -> R<Path> {
        let start_span = self.lo_span();

        let mut segments = Vec::new();
        loop {
            let segment = self.parse_path_segment(true)?;
            segments.push(segment);
            let is_import_coupler = self.matches(TokenKind::Scope)
                && (self.next_matches(1, TokenKind::LBrace)
                    || self.next_matches(1, TokenKind::Star));
            if is_import_coupler || !self.eat(TokenKind::Scope) {
                break;
            } else {
            }
        }

        let p = Path {
            segments,
            span: start_span.to(self.hi_span()),
        };

        Ok(p)
    }
}

#[cfg(test)]
mod test {
    use crate::make_parser;
    use taroc_span::session_test;

    #[test]
    fn test_simple_path() {
        session_test!({
            let mut parser = make_parser!("foo::bar");
            let path = parser.parse_path().expect("path");
            assert_eq!(path.segments.len(), 2);
            assert_eq!(path.segments[0].identifier.symbol.as_str(), "foo");
            assert_eq!(path.segments[1].identifier.symbol.as_str(), "bar");
        });
    }
}
