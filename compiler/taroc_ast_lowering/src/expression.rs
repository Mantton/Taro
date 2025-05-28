use super::package::Actor;
use crate::literal::convert_ast_literal;
use taroc_ast::{self, BinaryOperator};
use taroc_span::Span;

impl Actor<'_> {
    pub fn lower_expression(
        &mut self,
        expression: Box<taroc_ast::Expression>,
    ) -> Box<taroc_hir::Expression> {
        let expr = taroc_hir::Expression {
            id: self.next(),
            kind: self.lower_expression_kind(expression.kind, expression.span),
            span: expression.span,
        };

        Box::new(expr)
    }

    pub fn lower_expression_kind(
        &mut self,
        kind: taroc_ast::ExpressionKind,
        span: Span,
    ) -> taroc_hir::ExpressionKind {
        match kind {
            taroc_ast::ExpressionKind::Literal(literal) => self.lower_literal(literal, span),
            taroc_ast::ExpressionKind::Path(path) => {
                taroc_hir::ExpressionKind::Path(self.lower_path(path))
            }
            taroc_ast::ExpressionKind::StructLiteral(literal) => {
                taroc_hir::ExpressionKind::StructLiteral(self.lower_struct_literal(literal))
            }
            taroc_ast::ExpressionKind::Tuple(vec) => taroc_hir::ExpressionKind::Tuple(
                self.lower_sequence(vec, |a, e| a.lower_expression(e)),
            ),
            taroc_ast::ExpressionKind::Array(vec) => taroc_hir::ExpressionKind::ArrayLiteral(
                self.lower_sequence(vec, |a, e| a.lower_expression(e)),
            ),
            taroc_ast::ExpressionKind::Binary(binary_operator, lhs, rhs) => {
                taroc_hir::ExpressionKind::Binary(
                    binary_operator,
                    self.lower_expression(lhs),
                    self.lower_expression(rhs),
                )
            }
            taroc_ast::ExpressionKind::Parenthesis(expression) => {
                (self.lower_expression(expression)).kind
            }
            taroc_ast::ExpressionKind::FunctionCall(expression, vec) => {
                taroc_hir::ExpressionKind::FunctionCall(
                    self.lower_expression(expression),
                    self.lower_sequence(vec, |a, arg| a.lower_expression_argument(arg)),
                )
            }
            taroc_ast::ExpressionKind::MethodCall(m) => {
                taroc_hir::ExpressionKind::MethodCall(taroc_hir::MethodCall {
                    receiver: self.lower_expression(m.receiver),
                    method: self.lower_path_segment(m.method),
                    arguments: self
                        .lower_sequence(m.arguments, |a, arg| a.lower_expression_argument(arg)),
                    span: m.span,
                })
            }
            taroc_ast::ExpressionKind::Unary(op, expr) => {
                taroc_hir::ExpressionKind::Unary(op, self.lower_expression(expr))
            }
            taroc_ast::ExpressionKind::FieldAccess(expression, path_segment) => {
                taroc_hir::ExpressionKind::FieldAccess(
                    self.lower_expression(expression),
                    self.lower_path_segment(path_segment),
                )
            }
            taroc_ast::ExpressionKind::TupleAccess(expression, anon_const) => {
                taroc_hir::ExpressionKind::TupleAccess(
                    self.lower_expression(expression),
                    self.lower_anon_const(anon_const),
                )
            }
            taroc_ast::ExpressionKind::Subscript(expression, vec) => {
                taroc_hir::ExpressionKind::Subscript(
                    self.lower_expression(expression),
                    self.lower_sequence(vec, |a, arg| a.lower_expression_argument(arg)),
                )
            }
            taroc_ast::ExpressionKind::CastAs(expression, ty) => taroc_hir::ExpressionKind::CastAs(
                self.lower_expression(expression),
                self.lower_type(ty),
            ),
            taroc_ast::ExpressionKind::AssignOp(binary_operator, lhs, rhs) => {
                taroc_hir::ExpressionKind::AssignOp(
                    binary_operator,
                    self.lower_expression(lhs),
                    self.lower_expression(rhs),
                )
            }
            taroc_ast::ExpressionKind::Assign(lhs, rhs) => taroc_hir::ExpressionKind::Assign(
                self.lower_expression(lhs),
                self.lower_expression(rhs),
            ),
            taroc_ast::ExpressionKind::If(e) => {
                taroc_hir::ExpressionKind::If(self.lower_if_expression(e))
            }
            taroc_ast::ExpressionKind::Block(b) => {
                taroc_hir::ExpressionKind::Block(self.lower_block(b))
            }
            taroc_ast::ExpressionKind::Await(expression) => {
                (self.lower_expression(expression)).kind
            }
            taroc_ast::ExpressionKind::When(node) => {
                taroc_hir::ExpressionKind::When(self.lower_when_expression(node))
            }
            taroc_ast::ExpressionKind::Ternary(condition, then_expr, else_expr) => {
                self.lower_ternary_expression(condition, then_expr, else_expr)
            }
            taroc_ast::ExpressionKind::DictionaryLiteral(..) => todo!(),
            taroc_ast::ExpressionKind::ForceUnwrap(..) => todo!(),
            taroc_ast::ExpressionKind::OptionalUnwrap(..) => todo!(),
            taroc_ast::ExpressionKind::OptionalEvaluation(..) => todo!(),
            taroc_ast::ExpressionKind::Pipe(..) => todo!(),
            taroc_ast::ExpressionKind::OptionalBinding(..) => todo!(),
            taroc_ast::ExpressionKind::MatchBinding(..) => todo!(),
            taroc_ast::ExpressionKind::OptionalDefault(..) => todo!(),
            taroc_ast::ExpressionKind::Ensure(..) => todo!(),
            taroc_ast::ExpressionKind::Range(..) => todo!(),
            taroc_ast::ExpressionKind::Wildcard => todo!(),
            taroc_ast::ExpressionKind::Closure(..) => todo!(),
            taroc_ast::ExpressionKind::Unsafe(..) => todo!(),
            taroc_ast::ExpressionKind::Malformed => todo!(),
        }
    }
}

impl Actor<'_> {
    fn lower_expression_argument(
        &mut self,
        arg: taroc_ast::ExpressionArgument,
    ) -> taroc_hir::ExpressionArgument {
        taroc_hir::ExpressionArgument {
            label: self.lower_optional(arg.label, |a, l| a.lower_label(l)),
            expression: self.lower_expression(arg.expression),
            span: arg.span,
        }
    }
}

impl Actor<'_> {
    fn lower_literal(
        &mut self,
        literal: taroc_ast::Literal,
        span: Span,
    ) -> taroc_hir::ExpressionKind {
        let result = convert_ast_literal(literal);

        let literal = match result {
            Ok(lit) => lit,
            Err(msg) => {
                self.context.diagnostics.error(msg, span);
                return taroc_hir::ExpressionKind::Malformed;
            }
        };

        taroc_hir::ExpressionKind::Literal(literal)
    }
}

impl Actor<'_> {
    pub fn lower_anon_const(&mut self, an: taroc_ast::AnonConst) -> taroc_hir::AnonConst {
        taroc_hir::AnonConst {
            value: self.lower_expression(an.value),
        }
    }
}

impl Actor<'_> {
    pub fn lower_if_expression(
        &mut self,
        expr: taroc_ast::IfExpression,
    ) -> taroc_hir::IfExpression {
        let condition = self.lower_statement_conditions(expr.conditions);
        let else_block =
            self.lower_optional(expr.else_block, |this, expr| this.lower_expression(expr));
        taroc_hir::IfExpression {
            condition,
            then_block: self.lower_block_to_expression(expr.body),
            else_block,
        }
    }

    pub fn lower_statement_conditions(
        &mut self,
        node: taroc_ast::StatementConditionList,
    ) -> Box<taroc_hir::Expression> {
        let mut iter = node.conditions.into_iter();
        let first = iter.next().unwrap_or_else(|| {
            unreachable!("statement conditions must have at least one condition")
        });

        let first = self.lower_expression(first);

        let result = iter.fold(first, |lhs, next| {
            let span = lhs.span.to(next.span);
            let rhs = self.lower_expression(next);
            let expr = taroc_hir::Expression {
                id: self.next(),
                kind: taroc_hir::ExpressionKind::Binary(BinaryOperator::BoolAnd, lhs, rhs),
                span,
            };
            Box::new(expr)
        });

        result
    }
}

impl Actor<'_> {
    fn lower_struct_literal(&mut self, node: taroc_ast::StructLiteral) -> taroc_hir::StructLiteral {
        taroc_hir::StructLiteral {
            path: self.lower_path(node.path),
            fields: self.lower_sequence(node.fields, |this, field| {
                this.lower_expression_field(field)
            }),
        }
    }

    fn lower_expression_field(
        &mut self,
        node: taroc_ast::ExpressionField,
    ) -> taroc_hir::ExpressionField {
        taroc_hir::ExpressionField {
            is_shorthand: node.is_shorthand,
            span: node.span,
            label: self.lower_optional(node.label, |this, label| this.lower_label(label)),
            expression: self.lower_expression(node.expression),
        }
    }
}

impl Actor<'_> {
    fn lower_when_expression(
        &mut self,
        node: taroc_ast::WhenExpression,
    ) -> taroc_hir::WhenExpression {
        taroc_hir::WhenExpression {
            value: self.lower_optional(node.value, |this, value| this.lower_expression(value)),
            arms: self.lower_sequence(node.arms, |this, arm| this.lower_when_arm(arm)),
        }
    }

    fn lower_when_arm(&mut self, node: taroc_ast::WhenArm) -> taroc_hir::WhenArm {
        let kind = match node.kind {
            taroc_ast::WhenArmKind::Pattern(node) => {
                taroc_hir::WhenArmKind::Pattern(self.lower_matching_pattern(node))
            }
            taroc_ast::WhenArmKind::Expression(nodes) => taroc_hir::WhenArmKind::Expression(
                self.lower_sequence(nodes.conditions, |this, node| this.lower_expression(node)),
            ),
            taroc_ast::WhenArmKind::Default => taroc_hir::WhenArmKind::Default,
        };

        taroc_hir::WhenArm {
            kind,
            span: node.span,
            body: self.lower_expression(node.body),
        }
    }
}

impl Actor<'_> {
    pub fn lower_block_to_expression(
        &mut self,
        block: taroc_ast::Block,
    ) -> Box<taroc_hir::Expression> {
        let block = self.lower_block(block);
        let span = block.span;
        Box::new(taroc_hir::Expression {
            id: block.id,
            kind: taroc_hir::ExpressionKind::Block(block),
            span: span,
        })
    }
}

impl Actor<'_> {
    fn lower_ternary_expression(
        &mut self,
        condition: Box<taroc_ast::Expression>,
        then_expr: Box<taroc_ast::Expression>,
        else_expr: Box<taroc_ast::Expression>,
    ) -> taroc_hir::ExpressionKind {
        /*
        --- ast ---
        a ? b : c

        --- hir ---
        if a { b } else { c }
        */

        // - condition
        let condition = self.lower_expression(condition);

        // - then
        let then_block = {
            let then_span = then_expr.span;
            let then_expr = self.lower_expression(then_expr);
            let then_stmt =
                self.mk_statement(taroc_hir::StatementKind::Expression(then_expr), then_span);
            let then_block = self.mk_block(vec![then_stmt], then_span);
            self.mk_expression(taroc_hir::ExpressionKind::Block(then_block), then_span)
        };

        // - else
        let else_block = {
            let else_span = else_expr.span;
            let else_expr = self.lower_expression(else_expr);
            let else_stmt =
                self.mk_statement(taroc_hir::StatementKind::Expression(else_expr), else_span);
            let else_block = self.mk_block(vec![else_stmt], else_span);
            self.mk_expression(taroc_hir::ExpressionKind::Block(else_block), else_span)
        };

        let if_node = taroc_hir::IfExpression {
            condition,
            then_block,
            else_block: Some(else_block),
        };

        taroc_hir::ExpressionKind::If(if_node)
    }
}

impl Actor<'_> {
    pub fn mk_expression(
        &mut self,
        kind: taroc_hir::ExpressionKind,
        span: Span,
    ) -> Box<taroc_hir::Expression> {
        let expr = taroc_hir::Expression {
            id: self.next(),
            kind,
            span,
        };

        Box::new(expr)
    }
}
