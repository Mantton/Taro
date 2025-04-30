use super::package::{Parser, R};
use taroc_ast::{FieldDefinition, Mutability, Variant, VariantKind};
use taroc_span::Identifier;
use taroc_token::{Delimiter, TokenKind};

impl Parser {
    pub fn parse_field_definition(&mut self) -> R<FieldDefinition> {
        let lo = self.lo_span();
        let visibility = self.parse_visibility()?;
        let mutability = if self.eat(TokenKind::Const) {
            Mutability::Immutable
        } else {
            Mutability::Mutable
        };

        let identifier = self.parse_identifier()?;
        self.expect(TokenKind::Colon)?;

        let ty = self.parse_type()?;

        let fd = FieldDefinition {
            visibility,
            label: None,
            identifier,
            ty,
            mutability,
            span: lo.to(self.hi_span()),
        };

        Ok(fd)
    }

    pub fn parse_field_definitions(&mut self, delim: Delimiter) -> R<Vec<FieldDefinition>> {
        self.parse_delimiter_sequence(delim, TokenKind::Comma, true, |p| {
            p.parse_field_definition()
        })
    }
}

impl Parser {
    pub fn parse_enum_variant(&mut self) -> R<Variant> {
        let lo = self.lo_span();
        let identifier = self.parse_identifier()?;
        let kind = self.parse_variant_kind()?;
        let discriminant = if self.eat(TokenKind::Assign) {
            Some(self.parse_anon_const()?)
        } else {
            None
        };

        let v = Variant {
            identifier,
            kind,
            discriminant,
            span: lo.to(self.hi_span()),
        };

        Ok(v)
    }

    pub fn parse_variant_kind(&mut self) -> R<VariantKind> {
        match self.current_kind() {
            TokenKind::LParen => self.parse_tuple_variant(),
            TokenKind::LBrace => self.parse_struct_variant(),
            _ => Ok(VariantKind::Unit),
        }
    }

    fn parse_tuple_variant(&mut self) -> R<VariantKind> {
        let fields =
            self.parse_delimiter_sequence(Delimiter::Parenthesis, TokenKind::Comma, false, |p| {
                p.parse_tuple_variant_field()
            })?;

        let k = VariantKind::Tuple(fields);
        Ok(k)
    }

    fn parse_struct_variant(&mut self) -> R<VariantKind> {
        let fields = self.parse_field_definitions(Delimiter::Brace)?;
        Ok(VariantKind::Struct(fields))
    }

    fn parse_tuple_variant_field(&mut self) -> R<FieldDefinition> {
        let lo = self.lo_span();
        let vis = self.parse_visibility()?;
        let label = self.parse_label()?;
        let ty = self.parse_type()?;

        let def = FieldDefinition {
            visibility: vis,
            label,
            mutability: Mutability::Mutable,
            identifier: Identifier::emtpy(self.file.file),
            ty,
            span: lo.to(self.hi_span()),
        };

        Ok(def)
    }
}

#[cfg(test)]
mod test {
    use taroc_ast::{Mutability, TypeKind, VisibilityLevel};
    use taroc_token::Delimiter;

    use crate::make_parser;

    #[test]
    fn test_field_definition() {
        let mut parser = make_parser!("foo:bar");
        let field = parser.parse_field_definition().expect("field definition");
        // assert_eq!(field.identifier.name, "foo");
        assert_eq!(field.mutability, Mutability::Mutable);
        assert_eq!(field.visibility.level, VisibilityLevel::Inherent);
        assert!(matches!(field.ty.kind, TypeKind::Path(_)));

        let mut parser = make_parser!("public const foo:bar");
        let field = parser.parse_field_definition().expect("field definition");
        // assert_eq!(field.identifier.name, "foo");
        assert_eq!(field.mutability, Mutability::Immutable);
        assert_eq!(field.visibility.level, VisibilityLevel::Public);
        assert!(matches!(field.ty.kind, TypeKind::Path(_)))
    }

    #[test]
    fn test_field_definition_sequence() {
        let input = r#"{
            foo:T,
            public const bar: T,
            public baz: T,
            const foobar: T
        }"#;

        let mut parser = make_parser!(input);
        let fields = parser
            .parse_field_definitions(Delimiter::Brace)
            .expect("definitions");
        assert_eq!(4, fields.len());
        assert_eq!(
            vec!["foo", "bar", "baz", "foobar"],
            fields
                .iter()
                .map(|f| f.identifier.symbol.as_str())
                .collect::<Vec<&str>>()
        )
    }
}
