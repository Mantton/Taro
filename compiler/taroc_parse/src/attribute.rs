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
    use crate::make_parser;
    use taroc_span::session_test;

    #[test]
    fn test_plain_attribute() {
        session_test!({
            let mut parser = make_parser!("@foo");
            let attribute = parser.parse_attribute().expect("").expect("");
            assert_eq!(attribute.identifier.symbol.as_str(), "foo");
        });
    }
}
