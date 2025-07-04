use super::package::{Parser, R};
use crate::restrictions::Restrictions;
use taroc_ast::{
    AnonConst, ClosureExpression, Expression, ExpressionArgument, ExpressionField, ExpressionKind,
    FunctionParameter, FunctionPrototype, FunctionSignature, IfExpression, Literal, LiteralKind,
    MapPair, MatchArm, MatchExpression, MethodCall, Path, PathSegment, PatternBindingCondition,
    PatternKind, StructLiteral, Type, TypeKind, UnaryOperator,
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

    fn malformed_expr(&mut self, span: Span) -> Box<Expression> {
        self.build_expr(ExpressionKind::Malformed, span)
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

        // ensure <expr>
        if self.eat(TokenKind::Ensure) {
            let mut expr = self.parse_prefix_expr()?;
            let kind = ExpressionKind::Ensure(expr);
            let span = lo.to(self.hi_span());
            expr = self.build_expr(kind, span);
            return Ok(expr);
        }

        // await <expr>
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
        if (self.matches(TokenKind::If) || self.matches(TokenKind::Match))
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
                UnaryOperator::Reference(self.parse_mutability())
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
                    let c = self.parse_literal()?;
                    let k = ExpressionKind::TupleAccess(expr, AnonConst { value: c });
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
    fn parse_pattern_binding_condition(&mut self) -> R<Box<Expression>> {
        if !self
            .restrictions
            .contains(Restrictions::ALLOW_BINDING_CONDITION)
        {
            let msg = "cannot use a binding condition here".to_string();
            return Err(SpannedMessage::new(msg, self.current_token_span()));
        }

        let lo = self.lo_span();
        // match let <pattern> = <expr>
        self.expect(TokenKind::Let)?;
        let pattern = self.parse_pattern()?;
        let mut shorthand = false;
        let expression = if !self.matches(TokenKind::Assign)
            && matches!(pattern.kind, PatternKind::Identifier(..))
        {
            shorthand = true;
            let ident = match &pattern.kind {
                PatternKind::Identifier(ident) => *ident,
                _ => unreachable!(),
            };

            self.build_expr(
                ExpressionKind::Path(Path {
                    span: ident.span,
                    segments: vec![PathSegment {
                        identifier: ident,
                        arguments: None,
                        span: ident.span,
                    }],
                }),
                ident.span,
            )
        } else {
            self.expect(TokenKind::Assign)?;
            let mut binding_cond_res = Restrictions::empty();
            binding_cond_res.insert(Restrictions::NO_STRUCT_LITERALS);
            let expression = self.with_restrictions(binding_cond_res, |p| p.parse_expression())?;
            expression
        };

        let span = lo.to(self.hi_span());

        let p = PatternBindingCondition {
            expression,
            pattern,
            span,
            shorthand,
        };

        let kind = ExpressionKind::PatternBinding(p);
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
        // |a| {} | || -> int {} | async || await ok()
        let lo = self.lo_span();
        let (is_async, prototype) = self.parse_closure_prototype()?;
        let signature = FunctionSignature {
            is_async,
            prototype,
            span: lo.to(self.hi_span()),
        };

        let body = self.parse_block()?;

        let closure = ClosureExpression {
            signature,
            body,
            span: lo.to(self.hi_span()),
        };

        let kind = ExpressionKind::Closure(closure);
        let expr = self.build_expr(kind, lo);
        Ok(expr)
    }

    fn parse_closure_prototype(&mut self) -> R<(bool, FunctionPrototype)> {
        let is_async = self.eat(TokenKind::Async);
        let inputs = if self.eat(TokenKind::BarBar) {
            Vec::new()
        } else {
            self.parse_delimiter_sequence(Delimiter::Parenthesis, TokenKind::Comma, true, |p| {
                p.parse_closure_parameter()
            })?
        };

        let output = if self.eat(TokenKind::RArrow) {
            Some(self.parse_type()?)
        } else {
            None
        };
        let proto = FunctionPrototype { inputs, output };
        Ok((is_async, proto))
    }

    fn parse_closure_parameter(&mut self) -> R<FunctionParameter> {
        let lo = self.lo_span();
        let attributes = self.parse_attributes()?;

        let ident = self.parse_identifier()?;
        let mut is_variadic = false;
        let ty = if self.eat(TokenKind::Colon) {
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

        // struct literal: <Path> {}
        if self.matches(TokenKind::LBrace)
            && !self.restrictions.contains(Restrictions::NO_STRUCT_LITERALS)
        {
            return self.parse_struct_literal(path, lo);
        }

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

            let kind = ExpressionKind::DictionaryLiteral(vec![]);
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
            SS::Dict => ExpressionKind::DictionaryLiteral(map_pairs),
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
            | TokenKind::Nil => self.parse_literal(),
            TokenKind::Identifier => self.parse_path_expression(),
            TokenKind::LParen => self.parse_tuple_expr(),
            TokenKind::LBracket => self.parse_collection_expr(),
            TokenKind::Let => self.parse_pattern_binding_condition(),
            TokenKind::LBrace => self.parse_block_expression(),
            TokenKind::Async | TokenKind::Bar | TokenKind::BarBar => {
                self.parse_closure_expression()
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
            _ => {
                let msg = format!("expected expression, found {}", self.current_kind());
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
            TokenKind::Match => self.parse_match_expression(),
            _ => unreachable!("must manually check for token kind matching if | switch | match"),
        }
    }

    fn parse_block_expression(&mut self) -> R<Box<Expression>> {
        let block = self.parse_block()?;
        let span = block.span;
        let kind = ExpressionKind::Block(block);
        Ok(self.build_expr(kind, span))
    }
}

impl Parser {
    fn parse_if_expr(&mut self) -> R<Box<Expression>> {
        let lo = self.lo_span();

        self.expect(TokenKind::If)?;

        // Conditions
        let mut if_restrictions = Restrictions::empty();
        if_restrictions.set(Restrictions::ALLOW_BINDING_CONDITION, true);
        if_restrictions.set(Restrictions::NO_STRUCT_LITERALS, true);
        let conditions = self.with_restrictions(if_restrictions, |p| {
            p.parse_statement_condition_list(TokenKind::LBrace)
        })?;

        // Then - Block
        let body = self.parse_block()?;

        // Else - Block
        let else_block = if self.eat(TokenKind::Else) {
            let else_block = if self.matches(TokenKind::If) {
                self.parse_if_expr()?
            } else if self.matches(TokenKind::LBrace) {
                self.parse_block_expression()?
            } else {
                self.emit_error("expected block".into(), self.current_token_span());
                self.malformed_expr(self.current_token_span())
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
    pub fn parse_match_expression(&mut self) -> R<Box<Expression>> {
        let lo = self.lo_span();

        self.expect(TokenKind::Match)?;

        let kw_span = self.previous().unwrap().span;

        let value = if !self.matches(TokenKind::LBrace) {
            let mut res = Restrictions::empty();
            res.set(Restrictions::NO_STRUCT_LITERALS, true);
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

            let item = self.parse_match_arm()?;
            let _ = matches!(item.body.kind, ExpressionKind::Block(..));
            arms.push(item);

            if self.matches(TokenKind::RBrace) {
                break;
            }

            self.eat(TokenKind::Comma);

            self.expect(TokenKind::Newline)?;
        }

        self.expect(TokenKind::RBrace)?;

        let node = MatchExpression {
            arms,
            value,
            kw_span,
        };
        let k = ExpressionKind::Match(node);
        Ok(self.build_expr(k, lo.to(self.hi_span())))
    }

    fn parse_match_arm(&mut self) -> R<MatchArm> {
        let lo = self.lo_span();
        self.expect(TokenKind::Case)?;
        let pattern = self.parse_match_arm_pattern()?;
        let guard = if self.eat(TokenKind::If) {
            Some(self.parse_expression()?)
        } else {
            None
        };

        self.expect(TokenKind::EqArrow)?;
        let body = self.parse_expression()?;
        let arm = MatchArm {
            pattern,
            body,
            guard,
            span: lo.to(self.hi_span()),
        };
        Ok(arm)
    }
}
impl Parser {
    fn parse_literal(&mut self) -> R<Box<Expression>> {
        let lit_kind = match self.current_kind() {
            TokenKind::Integer(base) => LiteralKind::Integer(base),
            TokenKind::Float(_) => LiteralKind::Float,
            TokenKind::String => LiteralKind::String,
            TokenKind::Rune => LiteralKind::Rune,
            TokenKind::True => LiteralKind::Bool(true),
            TokenKind::False => LiteralKind::Bool(false),
            TokenKind::Nil => LiteralKind::Nil,
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
}

impl Parser {
    fn parse_struct_literal(&mut self, path: Path, span: Span) -> R<Box<Expression>> {
        let fields = self.parse_expression_field_list()?;
        let literal = StructLiteral { path, fields };
        let kind = ExpressionKind::StructLiteral(literal);
        let span = span.to(self.hi_span());
        Ok(self.build_expr(kind, span))
    }

    fn parse_expression_field_list(&mut self) -> R<Vec<ExpressionField>> {
        self.parse_delimiter_sequence(Delimiter::Brace, TokenKind::Comma, true, |p| {
            p.parse_expression_field()
        })
    }

    fn parse_expression_field(&mut self) -> R<ExpressionField> {
        let lo = self.lo_span();
        let label = self.parse_label()?;

        let expr = self.parse_expression()?;
        let field = ExpressionField {
            is_shorthand: label.is_none(),
            label,
            expression: expr,
            span: lo.to(self.hi_span()),
        };

        Ok(field)
    }
}
