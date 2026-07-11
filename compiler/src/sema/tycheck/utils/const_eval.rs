use crate::{
    compile::context::{ConstEvaluationState, GlobalContext},
    hir,
    sema::{
        models::{ConstKind, ConstValue},
        resolve::models::{DefinitionKind, VariantCtorKind},
    },
    span::Span,
};

pub fn register_const_definition<'ctx>(
    gcx: GlobalContext<'ctx>,
    id: hir::DefinitionID,
    expression: &hir::Expression,
) {
    gcx.register_const_value_expression(id, expression);
}

pub fn eval_const_definition<'ctx>(
    gcx: GlobalContext<'ctx>,
    id: hir::DefinitionID,
    span: Span,
) -> Option<ConstValue> {
    if let Some(value) = gcx.try_get_const(id) {
        return match value.kind {
            ConstKind::Value(value) => Some(value),
            _ => {
                gcx.dcx().emit_error(
                    "constant initializer must resolve to a concrete constant value".into(),
                    Some(span),
                );
                None
            }
        };
    }

    match gcx.const_evaluation_state(id) {
        Some(ConstEvaluationState::Evaluated(value)) => return Some(value),
        Some(ConstEvaluationState::Failed) => return None,
        Some(ConstEvaluationState::Evaluating) => {
            let mut cycle = gcx.constant_evaluation_cycle(id);
            cycle.push(id);

            let cycle_names = cycle
                .iter()
                .map(|definition| {
                    gcx.symbol_text(gcx.definition_ident(*definition).symbol)
                        .to_string()
                })
                .collect::<Vec<_>>();
            gcx.dcx().emit_error(
                format!(
                    "circular constant dependency\n\tcycle: {}",
                    cycle_names.join(" -> ")
                ),
                Some(span),
            );

            for definition in cycle.into_iter().take(cycle_names.len().saturating_sub(1)) {
                gcx.set_const_evaluation_state(definition, ConstEvaluationState::Failed);
            }
            return None;
        }
        None => {}
    }

    let Some(expression) = gcx.const_value_expression(id) else {
        let ident = gcx.definition_ident(id);
        let name = gcx.symbol_text(ident.symbol);
        gcx.dcx().emit_error(
            format!(
                "constant '{}' does not have a value available for constant evaluation",
                name
            ),
            Some(span),
        );
        gcx.set_const_evaluation_state(id, ConstEvaluationState::Failed);
        return None;
    };

    gcx.set_const_evaluation_state(id, ConstEvaluationState::Evaluating);
    gcx.push_const_evaluation(id);
    let evaluated = eval_const_expression(gcx, expression);
    gcx.pop_const_evaluation(id);

    if matches!(
        gcx.const_evaluation_state(id),
        Some(ConstEvaluationState::Failed)
    ) {
        return None;
    }

    match evaluated {
        Some(value) => {
            gcx.set_const_evaluation_state(id, ConstEvaluationState::Evaluated(value));
            Some(value)
        }
        None => {
            gcx.set_const_evaluation_state(id, ConstEvaluationState::Failed);
            None
        }
    }
}

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
                "initializer must be a constant expression".into(),
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
        hir::Literal::Integer { value, .. } => ConstValue::Integer(*value as i128),
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
        (hir::UnaryOperator::BitwiseNot, ConstValue::Integer(i)) => Some(ConstValue::Integer(!i)),
        _ => {
            gcx.dcx().emit_error(
                "initializer must be a constant expression".into(),
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
        hir::Resolution::StdItem(hir::StdItem::OptionalNoneCtor)
        | hir::Resolution::StdItem(hir::StdItem::OptionalNoneVariant) => {
            let Some(ctor_id) = gcx.std_item_def(hir::StdItem::OptionalNoneCtor) else {
                gcx.dcx().emit_error(
                    "unable to resolve Optional.none for constant evaluation".into(),
                    Some(span),
                );
                return None;
            };
            Some(ConstValue::EnumUnitVariant(ctor_id))
        }
        hir::Resolution::Definition(def_id, kind)
            if matches!(
                kind,
                DefinitionKind::Constant | DefinitionKind::AssociatedConstant
            ) =>
        {
            eval_const_definition(gcx, def_id, span)
        }
        hir::Resolution::Definition(_, DefinitionKind::ModuleVariable) => {
            gcx.dcx().emit_error(
                "static initializers cannot reference static variables".into(),
                Some(span),
            );
            None
        }
        hir::Resolution::Definition(
            ctor_id,
            DefinitionKind::VariantConstructor(VariantCtorKind::Constant),
        ) => Some(ConstValue::EnumUnitVariant(ctor_id)),
        _ => {
            gcx.dcx().emit_error(
                "initializer must be a constant expression".into(),
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
        gcx.dcx().emit_error(
            "unsupported binary operator in constant expression".into(),
            Some(span),
        );
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
            (ConstValue::Integer(a), ConstValue::Integer(b)) => a
                .checked_add(b)
                .map(ConstValue::Integer)
                .or_else(overflow_error),
            (ConstValue::Float(a), ConstValue::Float(b)) => Some(ConstValue::Float(a + b)),
            _ => type_error(),
        },
        BinOp::Sub => match (lhs, rhs) {
            (ConstValue::Integer(a), ConstValue::Integer(b)) => a
                .checked_sub(b)
                .map(ConstValue::Integer)
                .or_else(overflow_error),
            (ConstValue::Float(a), ConstValue::Float(b)) => Some(ConstValue::Float(a - b)),
            _ => type_error(),
        },
        BinOp::Mul => match (lhs, rhs) {
            (ConstValue::Integer(a), ConstValue::Integer(b)) => a
                .checked_mul(b)
                .map(ConstValue::Integer)
                .or_else(overflow_error),
            (ConstValue::Float(a), ConstValue::Float(b)) => Some(ConstValue::Float(a * b)),
            _ => type_error(),
        },
        BinOp::Div => match (lhs, rhs) {
            (ConstValue::Integer(_), ConstValue::Integer(0)) => div_zero_error(),
            (ConstValue::Integer(a), ConstValue::Integer(b)) => a
                .checked_div(b)
                .map(ConstValue::Integer)
                .or_else(overflow_error),
            (ConstValue::Float(_), ConstValue::Float(b)) if b == 0.0 => div_zero_error(),
            (ConstValue::Float(a), ConstValue::Float(b)) => Some(ConstValue::Float(a / b)),
            _ => type_error(),
        },
        BinOp::Rem => match (lhs, rhs) {
            (ConstValue::Integer(_), ConstValue::Integer(0)) => div_zero_error(),
            (ConstValue::Integer(a), ConstValue::Integer(b)) => a
                .checked_rem(b)
                .map(ConstValue::Integer)
                .or_else(overflow_error),
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

#[cfg(test)]
mod tests {
    use crate::sema::tycheck::test_support::{
        analyze_package_diagnostics, analyze_script_diagnostics,
    };

    #[test]
    fn forward_constant_dependencies_are_order_independent() {
        let diagnostics = analyze_script_diagnostics(
            r#"
const RESULT: int32 = BASE + 2
const BASE: int32 = 40

func main() {
    let _: int32 = RESULT
}
"#,
        );

        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }

    #[test]
    fn forward_constant_dependencies_work_across_files() {
        let diagnostics = analyze_package_diagnostics(&[
            (
                "consumer.tr",
                "const RESULT: int32 = BASE + 2\nfunc useResult() -> int32 { RESULT }\n",
            ),
            ("provider.tr", "const BASE: int32 = 40\n"),
        ]);

        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }

    #[test]
    fn forward_constants_work_in_early_compile_time_contexts() {
        let diagnostics = analyze_script_diagnostics(
            r#"
struct Buffer[const Size: usize = DEFAULT_SIZE] {
    bytes: [uint8; Size]
}

struct Header {
    bytes: [uint8; HEADER_SIZE]
}

const DEFAULT_SIZE: usize = 4
const HEADER_SIZE: usize = 2

func main() {}
"#,
        );

        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }

    #[test]
    fn constant_dependency_cycles_report_the_full_cycle_once() {
        let diagnostics = analyze_script_diagnostics(
            r#"
const A: int32 = B + 1
const B: int32 = C + 1
const C: int32 = A + 1

func main() {}
"#,
        );

        assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
        assert_eq!(
            diagnostics[0].message,
            "circular constant dependency\n\tcycle: A -> B -> C -> A"
        );
    }

    #[test]
    fn direct_constant_dependency_cycles_are_reported_once() {
        let diagnostics = analyze_script_diagnostics(
            r#"
const VALUE: int32 = VALUE + 1

func main() {}
"#,
        );

        assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
        assert_eq!(
            diagnostics[0].message,
            "circular constant dependency\n\tcycle: VALUE -> VALUE"
        );
    }
}
