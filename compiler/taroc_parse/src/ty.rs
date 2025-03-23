use taroc_ast::{InterfaceType, Mutability, Type, TypeKind};
use taroc_span::SpannedMessage;
use taroc_token::{Delimiter, TokenKind};

use super::package::{Parser, R};

impl Parser {
    pub fn parse_type(&mut self) -> R<Box<Type>> {
        let lo = self.lo_span();
        let k = self.parse_type_kind()?;
        let hi = self.hi_span();
        let ty = Type {
            span: lo.to(hi),
            kind: k,
        };

        // optional type : T?
        if self.matches(TokenKind::Question) {
            let k = self.parse_optional_type(ty)?;
            let hi = self.hi_span();
            let ty = Type {
                span: lo.to(hi),
                kind: k,
            };
            return Ok(Box::new(ty));
        }

        Ok(Box::new(ty))
    }

    fn parse_type_kind(&mut self) -> R<TypeKind> {
        let res = match self.current_kind() {
            TokenKind::Star | TokenKind::Amp => self.parse_pointer_type(self.current_kind()),
            TokenKind::Identifier => self.parse_path_type(),
            TokenKind::LParen => self.parse_tuple_type(),
            TokenKind::LBracket => self.parse_collection_type(),
            TokenKind::Struct => self.parse_anon_struct_type(),
            TokenKind::Function => self.parse_function_type(),
            TokenKind::Tilde => {
                self.bump();
                let mutability = if self.eat(TokenKind::Const) {
                    Mutability::Immutable
                } else {
                    Mutability::Mutable
                };
                Ok(TypeKind::OptionalReference(self.parse_type()?, mutability))
            }
            TokenKind::Some | TokenKind::Any => self.parse_interface_type(),
            _ => {
                let msg = format!("expected type found {}", self.current_kind());
                let err = SpannedMessage::new(msg, self.current_token_span());
                return Err(err);
            }
        };

        res
    }

    fn parse_type_mutability(&mut self) -> Mutability {
        if self.eat(TokenKind::Const) {
            Mutability::Immutable
        } else {
            Mutability::Mutable
        }
    }

    fn parse_interface_type(&mut self) -> R<TypeKind> {
        debug_assert!(matches!(
            self.current_kind(),
            TokenKind::Some | TokenKind::Any
        ));

        let is_static = self.current_kind() == TokenKind::Some;
        self.bump();

        let ty = self.parse_type()?;

        let k = if is_static {
            InterfaceType::Some
        } else {
            InterfaceType::Any
        };

        Ok(TypeKind::SomeOrAny(k, ty))
    }

    fn parse_pointer_type(&mut self, k: TokenKind) -> R<TypeKind> {
        self.expect(k)?; // eat '*' OR '&' symbol
        debug_assert!(matches!(k, TokenKind::Star | TokenKind::Amp));

        let is_pointer = matches!(k, TokenKind::Star);
        let mutability = self.parse_type_mutability();
        let ty = self.parse_type()?;

        let kind = if is_pointer {
            TypeKind::Pointer(ty, mutability)
        } else {
            TypeKind::Reference(ty, mutability)
        };

        Ok(kind)
    }

    fn parse_path_type(&mut self) -> R<TypeKind> {
        let path = self.parse_path()?;
        let kind = TypeKind::Path(path);

        Ok(kind)
    }

    fn parse_tuple_type(&mut self) -> R<TypeKind> {
        let lo = self.lo_span();
        let elements =
            self.parse_delimiter_sequence(Delimiter::Parenthesis, TokenKind::Comma, false, |p| {
                p.parse_type()
            })?;

        if elements.is_empty() {
            let msg = "expected 1 or more elements in tuple type";
            let err = SpannedMessage::new(msg.to_string(), lo.to(self.hi_span()));
            return Err(err);
        }

        if elements.len() == 1 {
            let first = elements.into_iter().next().unwrap();
            return Ok(TypeKind::Parenthesis(first));
        }

        Ok(TypeKind::Tuple(elements))
    }

    fn parse_collection_type(&mut self) -> R<TypeKind> {
        // Parses []T, [N]T, [T:V]
        // eat opening bracket
        self.expect(TokenKind::LBracket)?;

        // expecting a list type: []T
        if self.eat(TokenKind::RBracket) {
            let ty = self.parse_type()?;
            return Ok(TypeKind::List(ty));
        }

        self.drop_anchor();
        match self.parse_array_type() {
            Ok(k) => return Ok(k),
            Err(_) if self.matches(TokenKind::Colon) => {
                self.raise_anchor();
                return self.parse_dictionary_type();
            }
            Err(err) => return Err(err),
        }
    }

    fn parse_array_type(&mut self) -> R<TypeKind> {
        let size = self.parse_anon_const()?;
        self.expect(TokenKind::RBracket)?;
        let element = self.parse_type()?;
        return Ok(TypeKind::Array { size, element });
    }

    fn parse_dictionary_type(&mut self) -> R<TypeKind> {
        let key = self.parse_type()?;
        self.expect(TokenKind::Colon)?;
        let value = self.parse_type()?;
        self.expect(TokenKind::RBracket)?;
        return Ok(TypeKind::Dictionary { key, value });
    }

    fn parse_anon_struct_type(&mut self) -> R<TypeKind> {
        self.expect(TokenKind::Struct)?; // eat keyword
        let fields = self.parse_field_definitions(Delimiter::Brace)?;
        Ok(TypeKind::AnonStruct { fields })
    }

    fn parse_optional_type(&mut self, ty: Type) -> R<TypeKind> {
        self.expect(TokenKind::Question)?;
        let k = TypeKind::Optional(Box::new(ty));
        Ok(k)
    }

    fn parse_function_type(&mut self) -> R<TypeKind> {
        // func (T, V) async -> V
        self.expect(TokenKind::Function)?;

        let inputs = self.parse_delimiter_sequence(
            Delimiter::Parenthesis,
            TokenKind::Semicolon,
            false,
            |p| p.parse_type(),
        )?;

        let is_async = self.eat(TokenKind::Async);

        let output = if self.eat(TokenKind::RArrow) {
            Some(self.parse_type()?)
        } else {
            None
        };

        let kind = TypeKind::Function {
            inputs,
            output,
            is_async,
        };
        Ok(kind)
    }
}
