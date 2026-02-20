use crate::{
    compile::context::GlobalContext,
    hir,
    sema::{
        models::{ConstKind, ConstValue},
        resolve::models::DefinitionKind,
    },
    span::Span,
};

pub fn eval_const_expression<'ctx>(
    gcx: GlobalContext<'ctx>,
    expression: &hir::Expression,
) -> Option<ConstValue> {
    match &expression.kind {
        hir::ExpressionKind::Literal(lit) => eval_const_literal(gcx, lit, expression.span),
        hir::ExpressionKind::Unary(op, expr)
            if matches!(
                op,
                hir::UnaryOperator::Negate
                    | hir::UnaryOperator::LogicalNot
                    | hir::UnaryOperator::BitwiseNot
            ) =>
        {
            let value = eval_const_expression(gcx, expr)?;
            eval_const_unary(gcx, *op, value, expression.span)
        }
        hir::ExpressionKind::Binary(op, lhs, rhs) => {
            let lhs = eval_const_expression(gcx, lhs)?;
            let rhs = eval_const_expression(gcx, rhs)?;
            eval_const_binary(gcx, *op, lhs, rhs, expression.span)
        }
        hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path)) => {
            eval_const_path(gcx, path, expression.span)
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
        hir::Literal::String(s) => ConstValue::String(s.clone()),
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
        (hir::UnaryOperator::BitwiseNot, ConstValue::Integer(i)) => {
            Some(ConstValue::Integer(!i))
        }
        _ => {
            gcx.dcx().emit_error(
                "constant initializer must be a literal or unary operator".into(),
                Some(span),
            );
            None
        }
    }
}

fn eval_const_path<'ctx>(
    gcx: GlobalContext<'ctx>,
    path: &hir::Path,
    span: Span,
) -> Option<ConstValue> {
    match path.resolution {
        hir::Resolution::Definition(def_id, kind)
            if matches!(kind, DefinitionKind::Constant | DefinitionKind::AssociatedConstant) =>
        {
            let Some(value) = gcx.try_get_const(def_id) else {
                let ident = gcx.definition_ident(def_id);
                let name = gcx.symbol_text(ident.symbol);
                gcx.dcx().emit_error(
                    format!("constant '{}' is not yet available for const evaluation", name),
                    Some(span),
                );
                return None;
            };

            match value.kind {
                ConstKind::Value(value) => Some(value),
                _ => {
                    gcx.dcx().emit_error(
                        "constant initializer must resolve to a concrete constant value".into(),
                        Some(span),
                    );
                    None
                }
            }
        }
        _ => {
            gcx.dcx().emit_error(
                "constant initializer must be a literal or unary operator".into(),
                Some(span),
            );
            None
        }
    }
}

fn eval_const_binary<'ctx>(
    gcx: GlobalContext<'ctx>,
    op: hir::BinaryOperator,
    lhs: ConstValue,
    rhs: ConstValue,
    span: Span,
) -> Option<ConstValue> {
    use crate::hir::BinaryOperator as BinOp;

    let type_error = || {
        gcx.dcx()
            .emit_error("unsupported binary operator in constant expression".into(), Some(span));
        None
    };

    let overflow_error = || {
        gcx.dcx().emit_error("constant overflow".into(), Some(span));
        None
    };

    let div_zero_error = || {
        gcx.dcx()
            .emit_error("division by zero in constant expression".into(), Some(span));
        None
    };

    match op {
        BinOp::Add => match (lhs, rhs) {
            (ConstValue::Integer(a), ConstValue::Integer(b)) => {
                a.checked_add(b).map(ConstValue::Integer).or_else(overflow_error)
            }
            (ConstValue::Float(a), ConstValue::Float(b)) => Some(ConstValue::Float(a + b)),
            _ => type_error(),
        },
        BinOp::Sub => match (lhs, rhs) {
            (ConstValue::Integer(a), ConstValue::Integer(b)) => {
                a.checked_sub(b).map(ConstValue::Integer).or_else(overflow_error)
            }
            (ConstValue::Float(a), ConstValue::Float(b)) => Some(ConstValue::Float(a - b)),
            _ => type_error(),
        },
        BinOp::Mul => match (lhs, rhs) {
            (ConstValue::Integer(a), ConstValue::Integer(b)) => {
                a.checked_mul(b).map(ConstValue::Integer).or_else(overflow_error)
            }
            (ConstValue::Float(a), ConstValue::Float(b)) => Some(ConstValue::Float(a * b)),
            _ => type_error(),
        },
        BinOp::Div => match (lhs, rhs) {
            (ConstValue::Integer(_), ConstValue::Integer(0)) => div_zero_error(),
            (ConstValue::Integer(a), ConstValue::Integer(b)) => {
                a.checked_div(b).map(ConstValue::Integer).or_else(overflow_error)
            }
            (ConstValue::Float(_), ConstValue::Float(b)) if b == 0.0 => div_zero_error(),
            (ConstValue::Float(a), ConstValue::Float(b)) => Some(ConstValue::Float(a / b)),
            _ => type_error(),
        },
        BinOp::Rem => match (lhs, rhs) {
            (ConstValue::Integer(_), ConstValue::Integer(0)) => div_zero_error(),
            (ConstValue::Integer(a), ConstValue::Integer(b)) => {
                a.checked_rem(b).map(ConstValue::Integer).or_else(overflow_error)
            }
            _ => type_error(),
        },
        BinOp::BoolAnd => match (lhs, rhs) {
            (ConstValue::Bool(a), ConstValue::Bool(b)) => Some(ConstValue::Bool(a && b)),
            _ => type_error(),
        },
        BinOp::BoolOr => match (lhs, rhs) {
            (ConstValue::Bool(a), ConstValue::Bool(b)) => Some(ConstValue::Bool(a || b)),
            _ => type_error(),
        },
        BinOp::BitAnd => match (lhs, rhs) {
            (ConstValue::Integer(a), ConstValue::Integer(b)) => Some(ConstValue::Integer(a & b)),
            _ => type_error(),
        },
        BinOp::BitOr => match (lhs, rhs) {
            (ConstValue::Integer(a), ConstValue::Integer(b)) => Some(ConstValue::Integer(a | b)),
            _ => type_error(),
        },
        BinOp::BitXor => match (lhs, rhs) {
            (ConstValue::Integer(a), ConstValue::Integer(b)) => Some(ConstValue::Integer(a ^ b)),
            _ => type_error(),
        },
        BinOp::BitShl => match (lhs, rhs) {
            (ConstValue::Integer(a), ConstValue::Integer(b)) if b >= 0 => {
                let shift = b as u128;
                if shift > u32::MAX as u128 {
                    return overflow_error();
                }
                a.checked_shl(shift as u32)
                    .map(ConstValue::Integer)
                    .or_else(overflow_error)
            }
            _ => type_error(),
        },
        BinOp::BitShr => match (lhs, rhs) {
            (ConstValue::Integer(a), ConstValue::Integer(b)) if b >= 0 => {
                let shift = b as u128;
                if shift > u32::MAX as u128 {
                    return overflow_error();
                }
                a.checked_shr(shift as u32)
                    .map(ConstValue::Integer)
                    .or_else(overflow_error)
            }
            _ => type_error(),
        },
        BinOp::Eql => Some(ConstValue::Bool(lhs == rhs)),
        BinOp::Neq => Some(ConstValue::Bool(lhs != rhs)),
        BinOp::Lt => match (lhs, rhs) {
            (ConstValue::Integer(a), ConstValue::Integer(b)) => Some(ConstValue::Bool(a < b)),
            (ConstValue::Float(a), ConstValue::Float(b)) => Some(ConstValue::Bool(a < b)),
            (ConstValue::Rune(a), ConstValue::Rune(b)) => Some(ConstValue::Bool(a < b)),
            _ => type_error(),
        },
        BinOp::Gt => match (lhs, rhs) {
            (ConstValue::Integer(a), ConstValue::Integer(b)) => Some(ConstValue::Bool(a > b)),
            (ConstValue::Float(a), ConstValue::Float(b)) => Some(ConstValue::Bool(a > b)),
            (ConstValue::Rune(a), ConstValue::Rune(b)) => Some(ConstValue::Bool(a > b)),
            _ => type_error(),
        },
        BinOp::Leq => match (lhs, rhs) {
            (ConstValue::Integer(a), ConstValue::Integer(b)) => Some(ConstValue::Bool(a <= b)),
            (ConstValue::Float(a), ConstValue::Float(b)) => Some(ConstValue::Bool(a <= b)),
            (ConstValue::Rune(a), ConstValue::Rune(b)) => Some(ConstValue::Bool(a <= b)),
            _ => type_error(),
        },
        BinOp::Geq => match (lhs, rhs) {
            (ConstValue::Integer(a), ConstValue::Integer(b)) => Some(ConstValue::Bool(a >= b)),
            (ConstValue::Float(a), ConstValue::Float(b)) => Some(ConstValue::Bool(a >= b)),
            (ConstValue::Rune(a), ConstValue::Rune(b)) => Some(ConstValue::Bool(a >= b)),
            _ => type_error(),
        },
    }
}
