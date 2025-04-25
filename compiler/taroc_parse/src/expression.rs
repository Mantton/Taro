use super::package::{Parser, R};
use crate::restrictions::Restrictions;
use taroc_ast::{
    AnonConst, Block, ClosureExpression, EnsureMode, Expression, ExpressionArgument,
    ExpressionKind, FunctionParameter, FunctionPrototype, FunctionSignature, IfExpression, Literal,
    LiteralKind, MapPair, MethodCall, Mutability, OptionalBindingCondition,
    PatternBindingCondition, Type, TypeKind, UnaryOperator, WhenArm, WhenArmKind, WhenExpression,
};
use taroc_span::{Span, SpannedMessage};
use taroc_token::{Base, Delimiter, TokenKind};

impl Parser {
    pub fn parse_expression(&mut self) -> R<Box<Expression>> {
        self.parse_assignment_expr()
    }

    pub fn parse_anon_const(&mut self) -> R<AnonConst> {
        let value = self.parse_expression()?;
        let a = AnonConst { value };
        Ok(a)
    }
}

impl Parser {
    pub fn build_expr(&mut self, kind: ExpressionKind, span: Span) -> Box<Expression> {
        Box::new(Expression { kind, span })
    }
}

impl Parser {
    fn parse_assignment_expr(&mut self) -> R<Box<Expression>> {
        let mut expr = self.parse_non_assignment_expr()?;

        use TokenKind as T;

        if self.eat(TokenKind::Assign) {
            let value = self.parse_non_assignment_expr()?;
            let span = expr.span.to(value.span);
            let kind = ExpressionKind::Assign(expr, value);
            expr = self.build_expr(kind, span);
        } else if matches!(
            self.current_kind(),
            T::PlusEq
                | T::MinusEq
                | T::MulEq
                | T::DivEq
                | T::RemEq
                | T::AmpEq
                | T::BarEq
                | T::CaretEq
                | T::ShlEq
                | T::ShrEq
        ) {
            let op = Self::bin_op_assign(self.current_kind()).unwrap();
            self.bump();

            let value = self.parse_non_assignment_expr()?;
            let span = expr.span.to(value.span);
            let kind = ExpressionKind::AssignOp(op, expr, value);
            expr = self.build_expr(kind, span);
        }

        Ok(expr)
    }
}

impl Parser {
    pub fn parse_non_assignment_expr(&mut self) -> R<Box<Expression>> {
        self.parse_pipe_expr()
    }

    fn parse_pipe_expr(&mut self) -> R<Box<Expression>> {
        let mut expr = self.parse_ternary_expr()?;

        while matches!(self.current_kind(), TokenKind::Pipe) {
            self.bump();
            let right = self.parse_ternary_expr()?;

            let span = expr.span.to(right.span);
            let kind = ExpressionKind::Pipe(expr, right);
            expr = self.build_expr(kind, span);
        }

        Ok(expr)
    }

    fn parse_ternary_expr(&mut self) -> R<Box<Expression>> {
        let mut expr = self.parse_optional_default_expr()?;

        while self.eat(TokenKind::Question) {
            let middle = self.parse_ternary_expr()?;

            self.expect(TokenKind::Colon)?;

            let right = self.parse_ternary_expr()?;

            let span = expr.span.to(right.span);
            let kind = ExpressionKind::Ternary(expr, middle, right);
            expr = self.build_expr(kind, span);
        }

        Ok(expr)
    }
}

impl Parser {
    fn parse_optional_default_expr(&mut self) -> R<Box<Expression>> {
        let mut expr = self.parse_range_expr()?;
        while matches!(self.current_kind(), TokenKind::QuestionQuestion) {
            self.bump();
            let right = self.parse_range_expr()?;

            let span = expr.span.to(right.span);
            let kind = ExpressionKind::OptionalDefault(expr, right);
            expr = self.build_expr(kind, span);
        }
        Ok(expr)
    }
}

impl Parser {
    fn parse_range_expr(&mut self) -> R<Box<Expression>> {
        let mut expr = self.parse_bool_or_expr()?;
        let is_inclusive = if self.eat(TokenKind::DotDot) {
            false
        } else if self.eat(TokenKind::DotDotEq) {
            true
        } else {
            return Ok(expr);
        };

        let rhs = self.parse_bool_or_expr()?;

        let span = expr.span.to(rhs.span);
        let kind = ExpressionKind::Range(expr, rhs, is_inclusive);

        expr = self.build_expr(kind, span);
        Ok(expr)
    }
}

impl Parser {
    fn parse_bool_or_expr(&mut self) -> R<Box<Expression>> {
        // a || b
        let mut expr = self.parse_bool_and_expr()?;

        while matches!(self.current_kind(), TokenKind::BarBar) {
            expr = self.build_binary_expr(expr, |p| p.parse_bool_and_expr())?;
        }

        Ok(expr)
    }
    fn parse_bool_and_expr(&mut self) -> R<Box<Expression>> {
        // a && b
        let mut expr = self.parse_comparison_expr()?;

        while matches!(self.current_kind(), TokenKind::AmpAmp) {
            expr = self.build_binary_expr(expr, |p| p.parse_comparison_expr())?;
        }

        Ok(expr)
    }

    fn parse_comparison_expr(&mut self) -> R<Box<Expression>> {
        let mut expr = self.parse_bit_or_expr()?;

        while matches!(
            self.current_kind(),
            TokenKind::LChevron
                | TokenKind::RChevron
                | TokenKind::Geq
                | TokenKind::Leq
                | TokenKind::Neq
                | TokenKind::Eql
                | TokenKind::Teq
                | TokenKind::PtrEq
        ) {
            expr = self.build_binary_expr(expr, |p| p.parse_bit_or_expr())?;
        }

        Ok(expr)
    }
    fn parse_bit_or_expr(&mut self) -> R<Box<Expression>> {
        // a | b
        let mut expr = self.parse_bit_xor_expr()?;

        while matches!(self.current_kind(), TokenKind::Bar) {
            expr = self.build_binary_expr(expr, |p| p.parse_bit_xor_expr())?;
        }

        Ok(expr)
    }
    fn parse_bit_xor_expr(&mut self) -> R<Box<Expression>> {
        // boolean [a ^ b]

        let mut expr = self.parse_bit_and_expr()?;

        while matches!(self.current_kind(), TokenKind::Caret) {
            expr = self.build_binary_expr(expr, |p| p.parse_bit_and_expr())?;
        }

        Ok(expr)
    }
    fn parse_bit_and_expr(&mut self) -> R<Box<Expression>> {
        // boolean [&]

        let mut expr = self.parse_bit_shift_expr()?;

        while matches!(self.current_kind(), TokenKind::Amp) {
            expr = self.build_binary_expr(expr, |p| p.parse_bit_shift_expr())?;
        }

        Ok(expr)
    }
    fn parse_bit_shift_expr(&mut self) -> R<Box<Expression>> {
        // boolean [<< , >> ]
        let mut expr = self.parse_term_expr()?;

        while matches!(self.current_kind(), TokenKind::Shl | TokenKind::Shr) {
            expr = self.build_binary_expr(expr, |p| p.parse_term_expr())?;
        }

        Ok(expr)
    }

    fn parse_term_expr(&mut self) -> R<Box<Expression>> {
        // boolean [ + - ]
        let mut expr = self.parse_factor_expr()?;

        while matches!(self.current_kind(), TokenKind::Minus | TokenKind::Plus) {
            expr = self.build_binary_expr(expr, |p| p.parse_factor_expr())?;
        }

        Ok(expr)
    }

    fn parse_factor_expr(&mut self) -> R<Box<Expression>> {
        // boolean [ * , / , %]

        let mut expr = self.parse_cast_expr()?;

        while matches!(
            self.current_kind(),
            TokenKind::Quotient | TokenKind::Star | TokenKind::Modulus
        ) {
            expr = self.build_binary_expr(expr, |p| p.parse_cast_expr())?;
        }

        Ok(expr)
    }

    fn build_binary_expr<F>(&mut self, lhs: Box<Expression>, mut action: F) -> R<Box<Expression>>
    where
        F: FnMut(&mut Parser) -> R<Box<Expression>>,
    {
        let op = Self::bin_op_non_assign(self.current_kind());

        let Some(op) = op else {
            let msg = format!("unknown binary operator {}", self.current_kind());
            return Err(SpannedMessage::new(msg, self.current_token_span()));
        };

        self.bump(); // eat operator

        let rhs = action(self)?;
        let span = lhs.span.clone().to(rhs.span.clone());
        let kind = ExpressionKind::Binary(op, lhs, rhs);
        let expr = self.build_expr(kind, span);

        Ok(expr)
    }
}

impl Parser {
    fn parse_cast_expr(&mut self) -> R<Box<Expression>> {
        let mut expr = self.parse_kw_prefix_expr()?;

        while self.eat(TokenKind::As) {
            let ty = self.parse_type()?;

            let span = expr.span.clone().to(ty.span.clone());
            let kind = ExpressionKind::CastAs(expr, ty);
            expr = self.build_expr(kind, span)
        }

        return Ok(expr);
    }
}

impl Parser {
    fn parse_kw_prefix_expr(&mut self) -> R<Box<Expression>> {
        let lo = self.lo_span();

        // ensure <! | ?>?  <expr>
        if self.eat(TokenKind::Ensure) {
            let mode = if self.eat(TokenKind::Bang) {
                EnsureMode::Full
            } else if self.eat(TokenKind::Question) {
                EnsureMode::Partial
            } else {
                EnsureMode::Inherent
            };

            let mut expr = self.parse_prefix_expr()?;

            let kind = ExpressionKind::Ensure(mode, expr);
            let span = lo.to(self.hi_span());
            expr = self.build_expr(kind, span);
            return Ok(expr);
        }

        if self.eat(TokenKind::Await) {
            let mut expr = self.parse_prefix_expr()?;
            let kind = ExpressionKind::Await(expr);
            let span = lo.to(self.hi_span());
            expr = self.build_expr(kind, span);
            return Ok(expr);
        }

        return self.parse_prefix_expr();
    }
}

impl Parser {
    fn parse_prefix_expr(&mut self) -> R<Box<Expression>> {
        let lo = self.lo_span();
        // Expression Statements
        if (self.matches(TokenKind::If) || self.matches(TokenKind::When))
            && !self
                .restrictions
                .contains(Restrictions::ALLOW_BINDING_CONDITION)
        {
            return self.parse_stmt_expr();
        }

        let operator = match self.current_kind() {
            TokenKind::Bang => {
                self.bump();
                UnaryOperator::LogicalNot
            }
            TokenKind::Tilde => {
                self.bump();
                UnaryOperator::BitwiseNot
            }
            TokenKind::Star => {
                self.bump();
                UnaryOperator::Dereference
            }
            TokenKind::Amp => {
                self.bump();
                UnaryOperator::Reference(matches!(self.parse_mutability(), Mutability::Mutable))
            }
            TokenKind::Minus => {
                self.bump();
                UnaryOperator::Negate
            }
            _ => return self.parse_postfix_expr(),
        };

        let mut expr = self.parse_prefix_expr()?;
        let kind = ExpressionKind::Unary(operator, expr);
        let span = lo.to(self.hi_span());
        expr = self.build_expr(kind, span);
        return Ok(expr);
    }
}

impl Parser {
    fn parse_postfix_expr_suffix(
        &mut self,
        mut expr: Box<Expression>,
        is_optional_chain: &mut bool,
    ) -> R<Box<Expression>> {
        let mut pre_consumed_dot = false;

        loop {
            let mut lo = self.lo_span();

            if pre_consumed_dot {
                lo = self.previous().unwrap().span;
            }

            // parsing dot expr: `foo.<expr>`
            if self.eat(TokenKind::Dot) || pre_consumed_dot {
                pre_consumed_dot = false; // reset for next iter
                self.consume_new_lines();

                // parsing tuple index: `foo.<integer>`
                if self.current_kind() == TokenKind::Integer(Base::Decimal) {
                    let c = self.parse_anon_const()?;
                    let k = ExpressionKind::TupleAccess(expr, c);
                    let span = lo.to(self.hi_span());
                    expr = self.build_expr(k, span);
                    continue;
                }

                // field access: `foo.<ident>`
                let segment = self.parse_path_segment(true)?;
                let span = expr.span.to(self.hi_span());
                let kind = ExpressionKind::FieldAccess(expr, segment);
                expr = self.build_expr(kind, span);
                continue;
            }

            // parsing call expr: `foo(<expr_arguments>)`
            if self.matches(TokenKind::LParen) {
                expr = self.parse_call_expr(expr)?;
                continue;
            }

            // parsing index/subscript expr: `foo[<expr_arguments>]`
            if self.matches(TokenKind::LBracket) {
                let arguments = self.parse_expression_argument_list(Delimiter::Bracket)?;
                let span = expr.span.to(self.hi_span());
                let node = ExpressionKind::Subscript(expr, arguments);
                expr = self.build_expr(node, span);
                continue;
            }

            // parsing optional access: `foo ?. <integer_literal> | <ident>`
            if self.eat(TokenKind::QuestionDot) {
                *is_optional_chain = true;
                let span = expr.span.to(self.hi_span());

                let kind = ExpressionKind::OptionalUnwrap(expr);
                expr = self.build_expr(kind, lo.to(span));
                pre_consumed_dot = self.current_kind() == TokenKind::Identifier
                    || self.matches(TokenKind::Integer(Base::Decimal));
                continue;
            }

            // parsing force unwrap: `foo!`
            if self.eat(TokenKind::Bang) {
                let span = expr.span.to(self.hi_span());
                let kind = ExpressionKind::ForceUnwrap(expr);
                expr = self.build_expr(kind, span);
                continue;
            }

            // Parsing Closure: foo {}
            if self.matches(TokenKind::LBrace)
                && !self
                    .restrictions
                    .contains(Restrictions::NO_TRAILING_CLOSURES)
            {
                let closure = self.parse_closure_expression()?;
                let span = expr.span.to(self.hi_span());
                let kind = ExpressionKind::TrailingClosure(expr, closure);
                expr = self.build_expr(kind, span);
                continue;
            }

            break;
        }
        Ok(expr)
    }

    fn parse_postfix_expr(&mut self) -> R<Box<Expression>> {
        let mut expr = self.parse_primary_expr()?;

        let mut has_optional_chain = false;

        expr = self.parse_postfix_expr_suffix(expr, &mut has_optional_chain)?;

        if has_optional_chain {
            let span = expr.span.clone();
            let node = ExpressionKind::OptionalEvaluation(expr);
            expr = self.build_expr(node, span);
        }

        Ok(expr)
    }
}

impl Parser {
    fn parse_optional_binding_condition(&mut self) -> R<Box<Expression>> {
        if !self
            .restrictions
            .contains(Restrictions::ALLOW_BINDING_CONDITION)
        {
            let msg = "cannot use a binding condition here".to_string();
            return Err(SpannedMessage::new(msg, self.current_token_span()));
        }

        // let foo = bar | let foo
        let lo = self.lo_span();

        let mutability = if self.eat(TokenKind::Let) {
            Mutability::Immutable
        } else if self.eat(TokenKind::Var) {
            Mutability::Mutable
        } else {
            unreachable!("expected token to be validated as either let or var")
        };

        let identifier = self.parse_identifier()?;

        let expression = if self.eat(TokenKind::Assign) {
            let binding_cond_res = Restrictions::empty();
            let value = self.with_restrictions(binding_cond_res, |p| p.parse_expression())?;
            Some(value)
        } else {
            None
        };

        let span = lo.to(self.hi_span());
        let binding = OptionalBindingCondition {
            is_shorthand: match expression {
                None => true,
                _ => false,
            },
            identifier,
            expression,
            mutability,
            span: span.clone(),
        };

        let kind = ExpressionKind::OptionalBinding(binding);
        let expr = self.build_expr(kind, span);
        Ok(expr)
    }

    fn parse_pattern_binding_condition(&mut self) -> R<Box<Expression>> {
        let lo = self.lo_span();
        // match <matching_pattern> = <expr>
        self.expect(TokenKind::Match)?;
        let pattern = self.parse_match_pat()?;
        self.expect(TokenKind::Assign)?;

        let mut binding_cond_res = Restrictions::empty();
        binding_cond_res.insert(Restrictions::NO_TRAILING_CLOSURES);
        let expression = self.with_restrictions(binding_cond_res, |p| p.parse_expression())?;
        let span = lo.to(self.hi_span());

        let p = PatternBindingCondition {
            expression,
            pattern,
            span: span.clone(),
        };

        let kind = ExpressionKind::MatchBinding(p);
        let expr = self.build_expr(kind, span);
        Ok(expr)
    }
}

impl Parser {
    fn parse_call_expr(&mut self, expr: Box<Expression>) -> R<Box<Expression>> {
        let args = self.parse_expression_argument_list(Delimiter::Parenthesis)?;

        match expr.kind {
            ExpressionKind::FieldAccess(e, p) => {
                let s = p.identifier.span;
                // if is field access expression, convert to method call expression
                let call = MethodCall {
                    receiver: e,
                    method: p,
                    arguments: args,
                    span: s.to(self.hi_span()),
                };
                let k = ExpressionKind::MethodCall(call);
                return Ok(self.build_expr(k, expr.span.to(self.hi_span())));
            }
            _ => {
                let s = expr.span.clone();
                let k = ExpressionKind::FunctionCall(expr, args);
                return Ok(self.build_expr(k, s.to(self.hi_span())));
            }
        }
    }
}

impl Parser {
    fn parse_closure_expression(&mut self) -> R<Box<Expression>> {
        // { a, b in a + b }

        let lo = self.lo_span();
        self.expect(TokenKind::LBrace)?;

        let signature = {
            self.drop_anchor();
            let can_parse = self.can_parse_closure_signature();
            self.raise_anchor();
            let signature = if can_parse {
                self.parse_closure_signature()?
            } else {
                FunctionSignature {
                    prototype: FunctionPrototype {
                        inputs: vec![],
                        output: None,
                    },
                    span: Span::empty(self.file.file),
                    is_async: false,
                    is_static: false,
                }
            };
            signature
        };

        let b_lo = self.lo_span();
        let statements = self.parse_brace_sequence(false, |p| p.parse_statement())?;
        let body = Block {
            statements,
            has_declarations: false,
            span: b_lo.to(self.hi_span()),
        };
        let c = ClosureExpression {
            signature,
            body,
            span: lo.to(self.hi_span()),
        };

        let kind = ExpressionKind::Closure(c);
        Ok(self.build_expr(kind, lo.to(self.hi_span())))
    }

    fn can_parse_closure_signature(&mut self) -> bool {
        // if next token could not start signature
        // { (...) -> ... in }
        if !self.matches_any(&[
            TokenKind::LParen,
            TokenKind::Identifier,
            TokenKind::Underscore,
        ]) {
            return false;
        }

        // Parsing Possible Closure paramters
        if self.eat(TokenKind::LParen) {
            // Skip until Closing Paren / end of paramter list
            while !self.matches(TokenKind::RParen) && !self.matches(TokenKind::Eof) {
                self.bump();
            }

            // Eat Closing Paren
            if self.eat(TokenKind::RParen) {
                if self.eat(TokenKind::RArrow) {
                    if self.parse_type().is_err() {
                        return false;
                    }
                }
            }
        } else if self.matches_any(&[TokenKind::Identifier, TokenKind::Underscore]) {
            self.bump(); // Consume First Parameter
            while self.eat(TokenKind::Comma) {
                // if we see another parameter bump
                if self.matches_any(&[TokenKind::Identifier, TokenKind::Underscore]) {
                    self.bump();
                    continue;
                }

                // Is not parameter token, (ident | underscore)
                return false;
            }

            // Parse Signature Return Type
            if self.eat(TokenKind::RArrow) {
                if self.parse_type().is_err() {
                    return false;
                }
            }
        }

        // Parse In Keyword
        if !self.matches(TokenKind::In) {
            return false;
        }

        // We have a valid signature
        //
        return true;
    }

    fn parse_closure_signature(&mut self) -> R<FunctionSignature> {
        let lo = self.lo_span();

        let params = if self.matches(TokenKind::LParen) {
            self.parse_delimiter_sequence(Delimiter::Parenthesis, TokenKind::Comma, false, |p| {
                p.parse_closure_param(true)
            })?
        } else {
            let mut has_next = true;
            let mut params = vec![];
            while has_next {
                let param = self.parse_closure_param(false)?;
                params.push(param);
                has_next = self.eat(TokenKind::Comma)
            }
            params
        };

        let return_type = if self.eat(TokenKind::RArrow) {
            Some(self.parse_type()?)
        } else {
            None
        };

        self.expect(TokenKind::In)?;

        let pt = FunctionPrototype {
            inputs: params,
            output: return_type,
        };

        let sg = FunctionSignature {
            span: lo.to(self.hi_span()),
            prototype: pt,
            is_async: false,
            is_static: false,
        };

        Ok(sg)
    }

    fn parse_closure_param(&mut self, strict: bool) -> R<FunctionParameter> {
        let lo = self.lo_span();
        let attributes = self.parse_attributes()?;

        let ident = self.parse_identifier()?;
        let mut is_variadic = false;
        let ty = if !strict && self.eat(TokenKind::Colon) {
            let t = self.parse_type()?;
            is_variadic = self.eat(TokenKind::Ellipsis);
            t
        } else {
            Box::new(Type {
                span: ident.span.clone(),
                kind: TypeKind::InferedClosureParameter,
            })
        };

        let param = FunctionParameter {
            attributes,
            label: None,
            name: ident,
            annotated_type: ty,
            default_value: None,
            is_variadic,
            span: lo.to(self.hi_span()),
        };

        Ok(param)
    }
}

impl Parser {
    fn parse_path_expression(&mut self) -> R<Box<Expression>> {
        let lo = self.lo_span();
        let path = self.parse_path()?;

        let kind = ExpressionKind::Path(path);
        let expr = self.build_expr(kind, lo.to(self.hi_span()));
        return Ok(expr);
    }
}

impl Parser {
    fn parse_tuple_expr(&mut self) -> R<Box<Expression>> {
        let lo = self.lo_span();

        let items =
            self.parse_delimiter_sequence(Delimiter::Parenthesis, TokenKind::Comma, false, |p| {
                p.parse_expression()
            })?;

        let span = lo.to(self.hi_span());
        if items.is_empty() {
            let msg = "expected at least 1 element in a tuple/paren expression".to_string();
            return Err(SpannedMessage::new(msg, span));
        }

        let kind = if items.len() == 1 {
            ExpressionKind::Parenthesis(items.into_iter().next().unwrap())
        } else {
            ExpressionKind::Tuple(items)
        };

        let expr = self.build_expr(kind, span);
        Ok(expr)
    }
}

impl Parser {
    fn parse_collection_expr(&mut self) -> R<Box<Expression>> {
        let lo = self.lo_span();
        self.expect(TokenKind::LBracket)?;

        // early return, []
        if self.eat(TokenKind::RBracket) {
            let kind = ExpressionKind::Array(vec![]);
            let expr = self.build_expr(kind, lo.to(self.hi_span()));
            return Ok(expr);
        }

        // early return, [:]
        if self.matches(TokenKind::Colon) && self.next_matches(1, TokenKind::RBracket) {
            self.bump(); // eat colon
            self.bump(); // eat rbracket

            let kind = ExpressionKind::Dictionary(vec![]);
            let expr = self.build_expr(kind, lo.to(self.hi_span()));
            return Ok(expr);
        }

        let mut map_pairs = vec![];
        let mut array_elements = vec![];

        #[derive(Debug, PartialEq)]
        enum SS {
            Dict,
            Array,
            Infer,
        }

        let mut state = SS::Infer;

        let mut parser = |p: &mut Parser| -> R<()> {
            let k = p.parse_expression()?;

            // check if sequence is denoted as a map
            if state == SS::Infer {
                state = if p.eat(TokenKind::Colon) {
                    SS::Dict
                } else {
                    SS::Array
                };
            }

            // is an array
            if state == SS::Array {
                array_elements.push(k);
                return Ok(());
            }

            // is a dictionary
            p.expect(TokenKind::Colon)?;

            let v = p.parse_expression()?;
            let pair = MapPair { key: k, value: v };
            map_pairs.push(pair);
            return Ok(());
        };

        let _ =
            self.parse_sequence_until(&[TokenKind::RBracket], TokenKind::Comma, false, |p| {
                parser(p)
            })?;
        self.expect(TokenKind::RBracket)?;

        let kind = match state {
            SS::Dict => ExpressionKind::Dictionary(map_pairs),
            SS::Array => ExpressionKind::Array(array_elements),
            SS::Infer => {
                let msg = "unable to infer content of sequence (array or dictionary)".to_string();
                return Err(SpannedMessage::new(msg, lo.to(self.hi_span())));
            }
        };

        let expr = self.build_expr(kind, lo.to(self.hi_span()));
        return Ok(expr);
    }
}

impl Parser {
    fn parse_primary_expr(&mut self) -> R<Box<Expression>> {
        match self.current_kind() {
            TokenKind::Integer(_)
            | TokenKind::Float(_)
            | TokenKind::String
            | TokenKind::Rune
            | TokenKind::True
            | TokenKind::False
            | TokenKind::Nil
            | TokenKind::Void => {
                let lit_kind = match self.current_kind() {
                    TokenKind::Integer(base) => LiteralKind::Integer(base),
                    TokenKind::Float(_) => LiteralKind::Float,
                    TokenKind::String => LiteralKind::String,
                    TokenKind::Rune => LiteralKind::Rune,
                    TokenKind::True => LiteralKind::Bool(true),
                    TokenKind::False => LiteralKind::Bool(false),
                    TokenKind::Nil => LiteralKind::Nil,
                    TokenKind::Void => LiteralKind::Void,
                    _ => unreachable!(),
                };

                let lit = Literal {
                    kind: lit_kind,
                    content: self.symbol_from(self.current().unwrap().content)?,
                };

                let k = ExpressionKind::Literal(lit);
                let expr = self.build_expr(k, self.current_token_span());
                self.bump(); // consume token
                Ok(expr)
            }
            TokenKind::Identifier => self.parse_path_expression(),
            TokenKind::LParen => self.parse_tuple_expr(),
            TokenKind::LBracket => self.parse_collection_expr(),
            TokenKind::Let | TokenKind::Var => self.parse_optional_binding_condition(),
            TokenKind::Match => self.parse_pattern_binding_condition(),
            TokenKind::LBrace => {
                if self
                    .restrictions
                    .contains(Restrictions::ALLOW_BLOCK_EXPRESSION)
                {
                    let block = self.parse_block()?;
                    let span = block.span;
                    let kind = ExpressionKind::Block(block);
                    Ok(self.build_expr(kind, span))
                } else {
                    self.parse_closure_expression()
                }
            }
            TokenKind::Unsafe => {
                let lo = self.lo_span();
                self.bump();
                let block = self.parse_block()?;
                let kind = ExpressionKind::Unsafe(block);
                Ok(self.build_expr(kind, lo.to(self.hi_span())))
            }
            TokenKind::Underscore => {
                if !self.restrictions.contains(Restrictions::ALLOW_WILDCARD) {
                    let msg = format!("wildcard expressions are not permitted here");
                    self.emit_error(msg, self.current_token_span());
                }

                let lo = self.lo_span();
                let kind = ExpressionKind::Wildcard;
                self.bump();
                Ok(self.build_expr(kind, lo.to(self.hi_span())))
            }
            TokenKind::Scope => {
                let lo = self.lo_span();
                let kind = self.parse_inferred_member_expression()?;
                Ok(self.build_expr(kind, lo.to(self.hi_span())))
            }
            _ => {
                let msg = format!("expected expression found {} instead", self.current_kind());
                let span = self.current_token_span();
                Err(SpannedMessage::new(msg, span))
            }
        }
    }
}

impl Parser {
    fn parse_expression_argument_list(&mut self, delim: Delimiter) -> R<Vec<ExpressionArgument>> {
        self.parse_delimiter_sequence(delim, TokenKind::Comma, false, |p| {
            p.parse_expression_argument()
        })
    }

    fn parse_expression_argument(&mut self) -> R<ExpressionArgument> {
        let lo = self.lo_span();
        let label = self.parse_label()?;
        let expression = self.parse_non_assignment_expr()?;
        let span = lo.to(self.hi_span());
        let arg = ExpressionArgument {
            label,
            expression,
            span,
        };

        Ok(arg)
    }
}
impl Parser {
    fn parse_stmt_expr(&mut self) -> R<Box<Expression>> {
        match self.current_kind() {
            TokenKind::If => self.parse_if_expr(),
            TokenKind::When => self.parse_when_expression(),
            _ => unreachable!("must manually check for token kind matching if | switch | match"),
        }
    }
}

impl Parser {
    fn parse_if_expr(&mut self) -> R<Box<Expression>> {
        let lo = self.lo_span();

        self.expect(TokenKind::If)?;

        // Conditions
        let mut if_restrictions = Restrictions::empty();
        if_restrictions.set(Restrictions::ALLOW_BINDING_CONDITION, true);
        if_restrictions.set(Restrictions::NO_TRAILING_CLOSURES, true);
        let conditions = self.with_restrictions(if_restrictions, |p| {
            p.parse_statement_condition_list(TokenKind::LBrace)
        })?;

        // Then - Block
        let body = self.parse_block()?;

        // Else - Block
        let else_block = if self.eat(TokenKind::Else) {
            let else_block = if self.matches(TokenKind::If) {
                self.parse_if_expr()?
            } else {
                let block = self.parse_block()?;
                let span = block.span;
                self.build_expr(ExpressionKind::Block(block), span)
            };

            Some(else_block)
        } else {
            None
        };

        let node = IfExpression {
            conditions,
            body,
            else_block,
        };

        let k = ExpressionKind::If(node);
        Ok(self.build_expr(k, lo.to(self.hi_span())))
    }
}

impl Parser {
    pub fn parse_when_expression(&mut self) -> R<Box<Expression>> {
        let lo = self.lo_span();

        self.expect(TokenKind::When)?;

        let value = if !self.matches(TokenKind::LBrace) {
            let mut res = Restrictions::empty();
            res.set(Restrictions::NO_TRAILING_CLOSURES, true);
            let value = self.with_restrictions(res, |p| p.parse_expression())?;
            Some(value)
        } else {
            None
        };

        self.expect(TokenKind::LBrace)?;
        self.consume_comments_and_new_lines();
        let mut arms = vec![];

        while !self.matches(TokenKind::RBrace) && !self.is_at_end() {
            self.consume_comments_and_new_lines();
            if self.matches(TokenKind::RBrace) {
                break;
            }

            let item = self.parse_when_arm()?;
            arms.push(item);

            if self.matches(TokenKind::RBrace) {
                break;
            }

            self.expect(TokenKind::Newline)?;
        }

        self.expect(TokenKind::RBrace)?;

        let node = WhenExpression { arms, value };
        let k = ExpressionKind::When(node);
        Ok(self.build_expr(k, lo.to(self.hi_span())))
    }

    fn parse_when_arm(&mut self) -> R<WhenArm> {
        let lo = self.lo_span();
        let kind = if self.eat(TokenKind::Is) {
            let pat = self.parse_match_case_pat()?;
            WhenArmKind::Pattern(pat)
        } else {
            let mut when_restrictions = Restrictions::empty();
            when_restrictions.insert(Restrictions::ALLOW_WILDCARD);
            when_restrictions.insert(Restrictions::NO_TRAILING_CLOSURES);
            let cases = self.with_restrictions(when_restrictions, |p| {
                p.parse_statement_condition_list(TokenKind::Colon)
            })?;
            WhenArmKind::Expression(cases)
        };

        self.expect(TokenKind::EqArrow)?;
        let mut body_restrictions = Restrictions::empty();
        body_restrictions.set(Restrictions::ALLOW_BLOCK_EXPRESSION, true);
        let body = self.with_restrictions(body_restrictions, |p| p.parse_expression())?;

        let arm = WhenArm {
            kind,
            body,
            span: lo.to(self.hi_span()),
        };

        Ok(arm)
    }
}

impl Parser {
    fn parse_inferred_member_expression(&mut self) -> R<ExpressionKind> {
        self.expect(TokenKind::Scope)?;
        let path = self.parse_path()?;
        return Ok(ExpressionKind::InferMember(path));
    }
}
