use crate::{
    compile::context::GlobalContext,
    hir,
    sema::models::ConstValue,
    span::Span,
};

pub fn eval_const_expression<'ctx>(
    gcx: GlobalContext<'ctx>,
    expression: &hir::Expression,
) -> Option<ConstValue> {
    match &expression.kind {
        hir::ExpressionKind::Literal(lit) => eval_const_literal(gcx, lit, expression.span),
        hir::ExpressionKind::Unary(op, expr)
            if matches!(op, hir::UnaryOperator::Negate | hir::UnaryOperator::LogicalNot) =>
        {
            let value = eval_const_expression(gcx, expr)?;
            eval_const_unary(gcx, *op, value, expression.span)
        }
        _ => {
            gcx.dcx().emit_error(
                "constant initializer must be a literal or unary operator".into(),
                Some(expression.span),
            );
            None
        }
    }
}

fn eval_const_literal<'ctx>(
    gcx: GlobalContext<'ctx>,
    lit: &hir::Literal,
    span: Span,
) -> Option<ConstValue> {
    Some(match lit {
        hir::Literal::Bool(b) => ConstValue::Bool(*b),
        hir::Literal::Rune(r) => ConstValue::Rune(*r),
        hir::Literal::String(s) => ConstValue::String(*s),
        hir::Literal::Integer(i) => ConstValue::Integer(*i as i128),
        hir::Literal::Float(f) => ConstValue::Float(*f),
        hir::Literal::Nil => {
            gcx.dcx()
                .emit_error("nil is not allowed in constants".into(), Some(span));
            return None;
        }
    })
}

fn eval_const_unary<'ctx>(
    gcx: GlobalContext<'ctx>,
    op: hir::UnaryOperator,
    value: ConstValue,
    span: Span,
) -> Option<ConstValue> {
    match (op, value) {
        (hir::UnaryOperator::LogicalNot, ConstValue::Bool(b)) => Some(ConstValue::Bool(!b)),
        (hir::UnaryOperator::Negate, ConstValue::Integer(i)) => {
            i.checked_neg().map(ConstValue::Integer).or_else(|| {
                gcx.dcx().emit_error("constant overflow".into(), Some(span));
                None
            })
        }
        (hir::UnaryOperator::Negate, ConstValue::Float(f)) => Some(ConstValue::Float(-f)),
        _ => {
            gcx.dcx().emit_error(
                "constant initializer must be a literal or unary operator".into(),
                Some(span),
            );
            None
        }
    }
}
