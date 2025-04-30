use super::package::{Parser, R};
use taroc_ast::{Attribute, AttributeList};
use taroc_token::TokenKind;

impl Parser {
    pub fn parse_attributes(&mut self) -> R<AttributeList> {
        let mut attrs = vec![];
        while !self.is_at_end() {
            let Some(attr) = self.parse_attribute()? else {
                break;
            };

            attrs.push(attr);
        }
        self.consume_comments_and_new_lines();
        Ok(attrs)
    }

    pub fn parse_attribute(&mut self) -> R<Option<Attribute>> {
        if !self.eat(TokenKind::At) {
            return Ok(None);
        };

        let identifier = self.parse_identifier()?;

        // TODO, nested e.g: @available("Platform-iOS")

        let attr = Attribute { identifier };

        return Ok(Some(attr));
    }
}

#[cfg(test)]
mod test {
    use taroc_span::create_session_globals_then;

    use crate::make_parser;

    #[test]
    fn test_plain_attribute() {
        create_session_globals_then(|| {
            let mut parser = make_parser!("@foo");
            let attribute = parser.parse_attribute();

            // assert_eq!(attribute.identifier.symbol.as_str(), "foo");
        });
    }
}
