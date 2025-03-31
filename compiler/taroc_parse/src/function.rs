use super::package::{Parser, R};
use taroc_ast::{
    DeclarationKind, Function, FunctionParameter, FunctionPrototype, FunctionReciever,
    FunctionSignature, Generics, Label, Mutability,
};
use taroc_span::{Identifier, SpannedMessage};
use taroc_token::{Delimiter, OperatorKind, TokenKind};

impl Parser {
    pub fn parse_function(&mut self) -> R<(Identifier, DeclarationKind)> {
        // func <name> <type_parameters>? (<parameter list>) <async?> -> <return_type>? <where_clause>?
        self.expect(TokenKind::Function)?;
        let identifier = self.parse_identifier()?;
        let func = self.parse_fn()?;
        Ok((identifier, DeclarationKind::Function(func)))
    }

    pub fn parse_constructor(&mut self) -> R<DeclarationKind> {
        self.expect(TokenKind::Init)?;
        let is_optional = self.eat(TokenKind::Question);
        let func = self.parse_fn()?;
        Ok(DeclarationKind::Constructor(func, is_optional))
    }

    pub fn parse_operator(&mut self) -> R<DeclarationKind> {
        self.expect(TokenKind::Operator)?;
        let operator = self.parse_operator_from_token()?;
        let func = self.parse_fn()?;
        Ok(DeclarationKind::Operator(operator, func))
    }

    fn parse_fn(&mut self) -> R<Function> {
        let lo = self.lo_span();
        let type_parameters = self.parse_type_parameters()?;
        let parameters = self.parse_function_parameters()?;

        let reciever = if self.eat(TokenKind::Const) {
            Some(FunctionReciever::Reference(Mutability::Immutable))
        } else if self.eat(TokenKind::Mut) {
            Some(FunctionReciever::Reference(Mutability::Mutable))
        } else {
            None
        };

        let is_async = self.eat(TokenKind::Async);
        if is_async && self.matches_any(&[TokenKind::Mut, TokenKind::Const]) {
            self.emit_error(
                "receiver must appear before async modifier".into(),
                self.current_token_span(),
            );
        }

        let return_type = if self.eat(TokenKind::RArrow) {
            Some(self.parse_type()?)
        } else {
            None
        };

        let where_clause = self.parse_generic_where_clause()?;

        let prototype = FunctionPrototype {
            inputs: parameters,
            output: return_type,
        };

        let signature = FunctionSignature {
            span: lo.to(self.hi_span()),
            prototype,
            is_async,
        };

        let block = if self.matches(TokenKind::LBrace) {
            Some(self.parse_block()?)
        } else {
            self.expect_line_break_or_semi()?;
            None
        };

        let generics = Generics {
            type_parameters,
            where_clause,
            inheritance: None,
        };

        let func = Function {
            reciever,
            signature,
            block,
            generics,
        };

        Ok(func)
    }

    fn parse_function_parameters(&mut self) -> R<Vec<FunctionParameter>> {
        self.parse_delimiter_sequence(Delimiter::Parenthesis, TokenKind::Comma, false, |p| {
            p.parse_function_parameter()
        })
    }

    fn parse_function_parameter(&mut self) -> R<FunctionParameter> {
        let lo = self.lo_span();

        // @attribute label name: type
        let attributes = self.parse_attributes()?;

        let mut underscore_label = false;
        let label = if self.matches(TokenKind::Identifier) {
            Some(self.parse_identifier()?)
        } else if self.matches(TokenKind::Underscore) {
            underscore_label = true;
            self.bump();
            None
        } else {
            let msg = "expected parameter name or label".to_string();
            let err = SpannedMessage::new(msg, self.current_token_span());
            return Err(err);
        };

        let name = if self.matches(TokenKind::Identifier) {
            self.parse_identifier()?
        } else if let Some(label) = label.clone() {
            label
        } else if underscore_label {
            Identifier::emtpy(self.file.file)
        } else {
            let msg = "expected parameter name".to_string();
            let err = SpannedMessage::new(msg, self.current_token_span());
            return Err(err);
        };

        self.expect(TokenKind::Colon)?;
        let label = if let Some(label) = label {
            Some(Label {
                span: label.span.to(self.hi_span()),
                identifier: label,
            })
        } else {
            None
        };

        let ty = self.parse_type()?;

        let is_variadic = self.eat(TokenKind::Ellipsis);

        let default_value = if self.eat(TokenKind::Assign) {
            let expr = self.parse_expression()?;
            Some(expr)
        } else {
            None
        };

        let param = FunctionParameter {
            attributes,
            label,
            name,
            annotated_type: ty,
            default_value,
            is_variadic,
            span: lo.to(self.hi_span()),
        };

        Ok(param)
    }
}

impl Parser {
    fn parse_operator_from_token(&mut self) -> R<OperatorKind> {
        let kind = match self.current_kind() {
            TokenKind::Plus => Some(OperatorKind::Add),
            TokenKind::Minus => Some(OperatorKind::Sub),
            TokenKind::Star => Some(OperatorKind::Mul),
            TokenKind::Quotient => Some(OperatorKind::Div),
            TokenKind::Modulus => Some(OperatorKind::Rem),

            TokenKind::AmpAmp => Some(OperatorKind::BoolAnd),
            TokenKind::BarBar => Some(OperatorKind::BoolOr),

            TokenKind::Amp => Some(OperatorKind::BitAnd),
            TokenKind::Bar => Some(OperatorKind::BitOr),
            TokenKind::Caret => Some(OperatorKind::BitXor),

            TokenKind::Shl => Some(OperatorKind::BitShl),
            TokenKind::Shr => Some(OperatorKind::BitShr),

            TokenKind::Eql => Some(OperatorKind::Eq),
            TokenKind::Neq => Some(OperatorKind::Neq),
            TokenKind::Geq => Some(OperatorKind::Geq),
            TokenKind::Leq => Some(OperatorKind::Leq),
            TokenKind::Teq => Some(OperatorKind::ExprMatch),

            TokenKind::RChevron => Some(OperatorKind::Gt),
            TokenKind::LChevron => Some(OperatorKind::Lt),

            TokenKind::PlusEq => Some(OperatorKind::Add),
            TokenKind::MinusEq => Some(OperatorKind::Sub),
            TokenKind::MulEq => Some(OperatorKind::Mul),
            TokenKind::DivEq => Some(OperatorKind::Div),
            TokenKind::RemEq => Some(OperatorKind::Rem),

            TokenKind::AmpEq => Some(OperatorKind::BitAnd),
            TokenKind::BarEq => Some(OperatorKind::BitOr),
            TokenKind::CaretEq => Some(OperatorKind::BitXor),

            TokenKind::ShlEq => Some(OperatorKind::BitShl),
            TokenKind::ShrEq => Some(OperatorKind::BitShr),
            _ => None,
        };

        if let Some(kind) = kind {
            self.bump();
            return Ok(kind);
        }

        if self.matches(TokenKind::LBracket) && self.next_matches(1, TokenKind::RBracket) {
            self.bump();
            self.bump();
            return Ok(OperatorKind::Index);
        }

        let err = SpannedMessage::new(format!("invalid operator"), self.current_token_span());
        Err(err)
    }
}
