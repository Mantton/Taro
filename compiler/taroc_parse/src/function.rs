use super::package::{Parser, R};
use crate::declaration::FnParseMode;
use taroc_ast::{
    BinaryOperator, DeclarationKind, Function, FunctionParameter, FunctionPrototype,
    FunctionSignature, Generics, Label, Mutability, OperatorKind, SelfKind, Type, TypeKind,
};
use taroc_span::{Identifier, SpannedMessage, Symbol};
use taroc_token::{Delimiter, TokenKind};

impl Parser {
    pub fn parse_function(&mut self, mode: FnParseMode) -> R<(Identifier, DeclarationKind)> {
        // func <name> <type_parameters>? (<parameter list>) <async?> -> <return_type>? <where_clause>?
        self.expect(TokenKind::Function)?;
        let identifier = self.parse_identifier()?;
        let func = self.parse_fn(mode)?;
        Ok((identifier, DeclarationKind::Function(func)))
    }

    pub fn parse_operator(&mut self, mode: FnParseMode) -> R<(Identifier, DeclarationKind)> {
        self.expect(TokenKind::Operator)?;
        let lo = self.lo_span();
        let operator = self.parse_operator_from_token()?;
        let span = lo.to(self.hi_span());
        let func = self.parse_fn(mode)?;
        Ok((
            Identifier::new(Symbol::with(""), span),
            DeclarationKind::Operator(operator, func),
        ))
    }

    fn parse_fn(&mut self, mode: FnParseMode) -> R<Function> {
        let lo = self.lo_span();
        let type_parameters = self.parse_type_parameters()?;
        let parameters = self.parse_function_parameters()?;

        let is_async = self.eat(TokenKind::Async);

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
            if mode.req_body {
                self.emit_error(
                    "function requires body".into(),
                    self.previous().unwrap().span,
                );
            }
            self.expect_line_break_or_semi()?;
            None
        };

        let generics = Generics {
            type_parameters,
            where_clause,
            conformances: None,
        };

        let func = Function {
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
        if let Some(self_param) = self.parse_self_parameter()? {
            return Ok(self_param);
        }

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

    fn parse_self_parameter(&mut self) -> R<Option<FunctionParameter>> {
        let lo = self.lo_span();
        let attributes = self.parse_attributes()?;

        let (kind, mutability, ident) = match self.current_kind() {
            TokenKind::Identifier => {
                let anchor = self.cursor;
                let ident = self.parse_identifier()?;

                if ident.symbol == Symbol::with("self") {
                    (SelfKind::Copy, Mutability::Immutable, ident)
                } else {
                    self.cursor = anchor;
                    return Ok(None);
                }
            }
            TokenKind::Amp => {
                self.bump();
                let mutability = self.parse_mutability();
                (SelfKind::Reference, mutability, self.parse_self()?)
            }
            _ => return Ok(None),
        };

        let self_ty = Type {
            span: ident.span,
            kind: TypeKind::ImplicitSelf,
        };

        let ty = match kind {
            SelfKind::Copy => self_ty,
            SelfKind::Reference => Type {
                span: ident.span,
                kind: TypeKind::Reference(Box::new(self_ty), mutability),
            },
        };

        Ok(Some(FunctionParameter {
            attributes,
            label: None,
            name: ident,
            annotated_type: Box::new(ty),
            default_value: None,
            is_variadic: false,
            span: lo.to(self.hi_span()),
        }))
    }

    fn parse_self(&mut self) -> R<Identifier> {
        let ident = self.parse_identifier()?;

        if ident.symbol != Symbol::with("self") {
            let msg = format!(
                "expected 'self' paremeter, found '{}' instead",
                ident.symbol
            );
            let err = SpannedMessage::new(msg.to_string(), ident.span);
            return Err(err);
        }

        return Ok(ident);
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

            TokenKind::RChevron => Some(OperatorKind::Gt),
            TokenKind::LChevron => Some(OperatorKind::Lt),

            TokenKind::PlusEq => Some(OperatorKind::AddAssign),
            TokenKind::MinusEq => Some(OperatorKind::SubAssign),
            TokenKind::MulEq => Some(OperatorKind::MulAssign),
            TokenKind::DivEq => Some(OperatorKind::DivAssign),
            TokenKind::RemEq => Some(OperatorKind::RemAssign),

            TokenKind::AmpEq => Some(OperatorKind::BitAndAssign),
            TokenKind::BarEq => Some(OperatorKind::BitOrAssign),
            TokenKind::CaretEq => Some(OperatorKind::BitXorAssign),

            TokenKind::ShlEq => Some(OperatorKind::BitShlAssign),
            TokenKind::ShrEq => Some(OperatorKind::BitShrAssign),
            TokenKind::Bang => Some(OperatorKind::Not),
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

        if self.matches(TokenKind::Underscore) && self.next_matches(1, TokenKind::Minus) {
            self.bump();
            self.bump();
            return Ok(OperatorKind::Neg);
        }

        let err = SpannedMessage::new(format!("invalid operator"), self.current_token_span());
        Err(err)
    }
}

impl Parser {
    pub fn bin_op_non_assign(k: TokenKind) -> Option<BinaryOperator> {
        match k {
            TokenKind::Plus => Some(BinaryOperator::Add),
            TokenKind::Minus => Some(BinaryOperator::Sub),
            TokenKind::Star => Some(BinaryOperator::Mul),
            TokenKind::Quotient => Some(BinaryOperator::Div),
            TokenKind::Modulus => Some(BinaryOperator::Rem),

            TokenKind::AmpAmp => Some(BinaryOperator::BoolAnd),
            TokenKind::BarBar => Some(BinaryOperator::BoolOr),

            TokenKind::Amp => Some(BinaryOperator::BitAnd),
            TokenKind::Bar => Some(BinaryOperator::BitOr),
            TokenKind::Caret => Some(BinaryOperator::BitXor),

            TokenKind::Shl => Some(BinaryOperator::BitShl),
            TokenKind::Shr => Some(BinaryOperator::BitShr),

            TokenKind::Eql => Some(BinaryOperator::Eql),
            TokenKind::Neq => Some(BinaryOperator::Neq),
            TokenKind::Geq => Some(BinaryOperator::Geq),
            TokenKind::Leq => Some(BinaryOperator::Leq),

            TokenKind::RChevron => Some(BinaryOperator::Gt),
            TokenKind::LChevron => Some(BinaryOperator::Lt),
            TokenKind::PtrEq => Some(BinaryOperator::PtrEq),
            _ => None,
        }
    }

    pub fn bin_op_assign(k: TokenKind) -> Option<BinaryOperator> {
        match k {
            TokenKind::PlusEq => Some(BinaryOperator::Add),
            TokenKind::MinusEq => Some(BinaryOperator::Sub),
            TokenKind::MulEq => Some(BinaryOperator::Mul),
            TokenKind::DivEq => Some(BinaryOperator::Div),
            TokenKind::RemEq => Some(BinaryOperator::Rem),

            TokenKind::AmpEq => Some(BinaryOperator::BitAnd),
            TokenKind::BarEq => Some(BinaryOperator::BitOr),
            TokenKind::CaretEq => Some(BinaryOperator::BitXor),

            TokenKind::ShlEq => Some(BinaryOperator::BitShl),
            TokenKind::ShrEq => Some(BinaryOperator::BitShr),
            _ => None,
        }
    }
}
