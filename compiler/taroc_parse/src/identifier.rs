use super::package::{Parser, R};
use taroc_span::{Identifier, SpannedMessage};
use taroc_token::TokenKind;

impl Parser {
    pub fn parse_identifier(&mut self) -> R<Identifier> {
        let Some(current) = self.current() else {
            return Err(SpannedMessage::new(
                "expected identifier".to_string(),
                self.lo_span(),
            ));
        };

        match current.kind {
            TokenKind::Identifier => {
                let symbol = self.symbol_from(current.content)?;

                let v = Identifier {
                    span: current.span,
                    symbol,
                };

                self.bump();
                return Ok(v);
            }
            _ => {
                let msg = format!("expected identifier, got '{}'", self.current_content());
                return Err(SpannedMessage::new(msg, current.span));
            }
        };
    }

    pub fn parse_optional_ident(&mut self) -> R<Option<Identifier>> {
        if self.matches(TokenKind::Identifier) {
            return Ok(Some(self.parse_identifier()?));
        } else {
            return Ok(None);
        }
    }
}

#[cfg(test)]
mod test {
    use crate::make_parser;
    use taroc_span::session_test;

    #[test]
    fn test_identifier() {
        session_test!({
            let mut parser = make_parser!("foo");
            let ident = parser.parse_identifier().expect("identifier");
            assert_eq!(ident.symbol.as_str(), "foo");
        });
    }
}
