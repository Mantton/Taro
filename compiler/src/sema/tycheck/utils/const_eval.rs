use crate::{
    compile::context::{ConstEvaluationState, GlobalContext},
    hir,
    sema::{
        models::{ConstKind, ConstValue, FloatTy, IntTy, InterfaceReference, Ty, TyKind, UIntTy},
        resolve::models::{DefinitionKind, VariantCtorKind},
        tycheck::{
            lower::{DefTyLoweringCtx, TypeLowerer},
            results::TypeCheckResults,
            utils::normalize_aliases,
        },
    },
    span::Span,
};

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

    let Some((node, expression)) = gcx
        .const_definition(id)
        .and_then(|node| Some((node, node.expr.as_deref()?)))
    else {
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
    let lowerer = DefTyLoweringCtx::new(id, gcx);
    // Even a forward reference used by a type header must compute at the
    // declared width. Start cycle tracking before lowering its annotation.
    let expected = gcx
        .try_get_type(id)
        .unwrap_or_else(|| lowerer.lowerer().lower_type(&node.ty));
    let evaluated =
        eval_const_expression_inner(gcx, expression, Some(expected), Evaluation::Early(&lowerer));
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

/// Evaluate a constant expression using `expected` as the type of arithmetic
/// subexpressions when type-check results are not available yet.
pub fn eval_const_expression_with_expected_type<'ctx>(
    lowerer: &dyn TypeLowerer<'ctx>,
    expression: &hir::Expression,
    expected: Ty<'ctx>,
) -> Option<ConstValue> {
    eval_const_expression_inner(
        lowerer.gcx(),
        expression,
        Some(expected),
        Evaluation::Early(lowerer),
    )
}

/// Evaluate a fully type-checked constant expression. Integer operations are
/// checked at their inferred width regardless of the runtime overflow mode.
pub fn eval_const_expression_with_type_results<'ctx>(
    gcx: GlobalContext<'ctx>,
    expression: &hir::Expression,
    results: &TypeCheckResults<'ctx>,
) -> Option<ConstValue> {
    eval_const_expression_inner(gcx, expression, None, Evaluation::Checked(results))
}

#[derive(Clone, Copy)]
enum Evaluation<'a, 'ctx> {
    Early(&'a dyn TypeLowerer<'ctx>),
    Checked(&'a TypeCheckResults<'ctx>),
}

impl<'ctx> Evaluation<'_, 'ctx> {
    fn node_type(self, id: hir::NodeID) -> Option<Ty<'ctx>> {
        match self {
            Self::Checked(results) => results.try_node_type(id),
            Self::Early(_) => None,
        }
    }
}

fn eval_const_expression_inner<'ctx>(
    gcx: GlobalContext<'ctx>,
    expression: &hir::Expression,
    expected: Option<Ty<'ctx>>,
    context: Evaluation<'_, 'ctx>,
) -> Option<ConstValue> {
    let expression_ty = context.node_type(expression.id).or(expected);

    let value = match &expression.kind {
        hir::ExpressionKind::Literal(lit) => eval_const_literal(gcx, lit, expression.span),
        hir::ExpressionKind::Unary(op, expr)
            if matches!(
                op,
                hir::UnaryOperator::Negate
                    | hir::UnaryOperator::LogicalNot
                    | hir::UnaryOperator::BitwiseNot
            ) =>
        {
            let value = eval_const_expression_inner(gcx, expr, expression_ty, context)?;
            eval_const_unary(gcx, *op, value, expression_ty, expression.span)
        }
        hir::ExpressionKind::Binary(op, lhs, rhs) => {
            if matches!(
                op,
                hir::BinaryOperator::BoolAnd | hir::BinaryOperator::BoolOr
            ) {
                let lhs = eval_const_expression_inner(gcx, lhs, Some(gcx.types.bool), context)?;
                let ConstValue::Bool(lhs) = lhs else {
                    return emit_const_type_error(gcx, expression.span);
                };

                if matches!((op, lhs), (hir::BinaryOperator::BoolAnd, false)) {
                    Some(ConstValue::Bool(false))
                } else if matches!((op, lhs), (hir::BinaryOperator::BoolOr, true)) {
                    Some(ConstValue::Bool(true))
                } else {
                    let rhs = eval_const_expression_inner(gcx, rhs, Some(gcx.types.bool), context)?;
                    match rhs {
                        ConstValue::Bool(rhs) => Some(ConstValue::Bool(rhs)),
                        _ => return emit_const_type_error(gcx, expression.span),
                    }
                }
            } else {
                let operand_expected = if binary_result_matches_operands(*op) {
                    expression_ty
                } else {
                    None
                };
                let lhs = eval_const_expression_inner(gcx, lhs, operand_expected, context)?;
                let rhs = eval_const_expression_inner(gcx, rhs, operand_expected, context)?;
                eval_const_binary(gcx, *op, lhs, rhs, expression_ty, expression.span)
            }
        }
        hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path)) => {
            eval_const_path(gcx, &path.resolution, expression.span)
        }
        hir::ExpressionKind::Path(hir::ResolvedPath::Relative(..))
        | hir::ExpressionKind::InferredMember { .. } => {
            let resolution = match context {
                Evaluation::Checked(results) => checked_static_resolution(gcx, expression, results),
                Evaluation::Early(lowerer) => {
                    early_static_member(lowerer, expression, expression_ty)
                }
            };
            if matches!(resolution, Some(hir::Resolution::Error)) {
                return None;
            }
            eval_const_path(
                gcx,
                &resolution.unwrap_or(hir::Resolution::Error),
                expression.span,
            )
        }
        hir::ExpressionKind::CastAs(value, target) => {
            let source_ty = context
                .node_type(value.id)
                .or_else(|| const_expression_type_hint(gcx, value));
            let target_ty = context
                .node_type(expression.id)
                .or_else(|| const_cast_target_type(gcx, target))
                .or(expression_ty);
            let value = eval_const_expression_inner(gcx, value, source_ty, context)?;
            eval_const_cast(gcx, value, source_ty, target_ty, expression.span)
        }
        hir::ExpressionKind::If(node) => {
            let condition =
                eval_const_expression_inner(gcx, &node.condition, Some(gcx.types.bool), context)?;
            let ConstValue::Bool(condition) = condition else {
                return emit_const_type_error(gcx, node.condition.span);
            };

            if condition {
                eval_const_expression_inner(gcx, &node.then_block, expression_ty, context)
            } else if let Some(else_block) = &node.else_block {
                eval_const_expression_inner(gcx, else_block, expression_ty, context)
            } else {
                Some(ConstValue::Unit)
            }
        }
        hir::ExpressionKind::Block(block) if block.statements.is_empty() => {
            if let Some(tail) = &block.tail {
                eval_const_expression_inner(gcx, tail, expression_ty, context)
            } else {
                Some(ConstValue::Unit)
            }
        }
        _ => {
            if crate::mir::const_eval::hir_expr_needs_mir_const_eval(expression)
                && let Evaluation::Early(lowerer) = context
                && let Some(owner_id) = lowerer.current_definition()
            {
                crate::mir::const_eval::eval_const_expr_on_demand(
                    gcx,
                    owner_id,
                    expression,
                    expression_ty,
                )
            } else {
                gcx.dcx().emit_error(
                    "initializer must be a constant expression".into(),
                    Some(expression.span),
                );
                None
            }
        }
    }?;

    if let Evaluation::Checked(results) = context
        && matches!(value, ConstValue::EnumUnitVariant(_))
        && results
            .node_adjustments(expression.id)
            .is_some_and(|a| !a.is_empty())
    {
        gcx.dcx().emit_error(
            "enum conversion is not a constant expression".into(),
            Some(expression.span),
        );
        return None;
    }
    validate_value_for_type(gcx, value, expression_ty, expression.span)
}

fn const_expression_type_hint<'ctx>(
    gcx: GlobalContext<'ctx>,
    expression: &hir::Expression,
) -> Option<Ty<'ctx>> {
    let hir::ExpressionKind::Literal(literal) = &expression.kind else {
        return None;
    };

    Some(match literal {
        hir::Literal::Bool(_) => gcx.types.bool,
        hir::Literal::Rune(_) => gcx.types.rune,
        hir::Literal::Bytes(value) => gcx.byte_array_type(value.len()),
        hir::Literal::String(_) => gcx.types.string,
        hir::Literal::Float(_) => gcx.types.float64,
        hir::Literal::Integer {
            suffix: Some(suffix),
            ..
        } => match suffix {
            crate::parse::IntegerTypeSuffix::I8 => gcx.types.int8,
            crate::parse::IntegerTypeSuffix::I16 => gcx.types.int16,
            crate::parse::IntegerTypeSuffix::I32 => gcx.types.int32,
            crate::parse::IntegerTypeSuffix::I64 => gcx.types.int64,
            crate::parse::IntegerTypeSuffix::U8 => gcx.types.uint8,
            crate::parse::IntegerTypeSuffix::U16 => gcx.types.uint16,
            crate::parse::IntegerTypeSuffix::U32 => gcx.types.uint32,
            crate::parse::IntegerTypeSuffix::U64 => gcx.types.uint64,
        },
        hir::Literal::Integer { suffix: None, .. } | hir::Literal::Nil => return None,
    })
}

fn const_cast_target_type<'ctx>(gcx: GlobalContext<'ctx>, target: &hir::Type) -> Option<Ty<'ctx>> {
    let hir::TypeKind::Nominal(hir::ResolvedPath::Resolved(path)) = &target.kind else {
        return None;
    };
    let hir::Resolution::PrimaryType(primary) = path.resolution else {
        return None;
    };

    Some(match primary {
        crate::sema::resolve::models::PrimaryType::Int(kind) => Ty::new_int(gcx, kind),
        crate::sema::resolve::models::PrimaryType::UInt(kind) => Ty::new_uint(gcx, kind),
        crate::sema::resolve::models::PrimaryType::Float(kind) => Ty::new_float(gcx, kind),
        crate::sema::resolve::models::PrimaryType::String => gcx.types.string,
        crate::sema::resolve::models::PrimaryType::Bool => gcx.types.bool,
        crate::sema::resolve::models::PrimaryType::Rune => gcx.types.rune,
    })
}

fn eval_const_cast<'ctx>(
    gcx: GlobalContext<'ctx>,
    value: ConstValue,
    source_ty: Option<Ty<'ctx>>,
    target_ty: Option<Ty<'ctx>>,
    span: Span,
) -> Option<ConstValue> {
    let Some(target_ty) = target_ty else {
        gcx.dcx().emit_error(
            "cannot determine constant cast target type".into(),
            Some(span),
        );
        return None;
    };

    let target_ty = crate::sema::tycheck::utils::normalize_aliases(gcx, target_ty);
    let source_ty = source_ty.map(|ty| crate::sema::tycheck::utils::normalize_aliases(gcx, ty));
    let converted = match (value, target_ty.kind()) {
        (ConstValue::Integer(value), TyKind::Int(_) | TyKind::UInt(_)) => {
            ConstValue::Integer(value)
        }
        (ConstValue::Rune(value), TyKind::Int(_) | TyKind::UInt(_)) => {
            ConstValue::Integer(value as u32 as i128)
        }
        (ConstValue::Integer(value), TyKind::Rune)
            if source_ty.is_some_and(|ty| matches!(ty.kind(), TyKind::UInt(UIntTy::U8))) =>
        {
            let Ok(value) = u32::try_from(value) else {
                return emit_const_cast_range_error(gcx, value, target_ty, span);
            };
            let Some(value) = char::from_u32(value) else {
                return emit_const_cast_range_error(gcx, value, target_ty, span);
            };
            ConstValue::Rune(value)
        }
        (ConstValue::Integer(_), TyKind::Rune) => {
            if let Some(source_ty) = source_ty {
                gcx.dcx().emit_error(
                    format!(
                        "cannot cast '{}' to rune; use checked conversion functions",
                        source_ty.format(gcx)
                    ),
                    Some(span),
                );
                return None;
            }
            return emit_const_type_error(gcx, span);
        }
        (ConstValue::Rune(value), TyKind::Rune) => ConstValue::Rune(value),
        (ConstValue::Float(value), TyKind::Float(FloatTy::F32)) => {
            if value.is_finite() && value.abs() > f32::MAX as f64 {
                gcx.dcx().emit_error(
                    format!(
                        "constant value `{value}` is out of range for type `{}`",
                        target_ty.format(gcx)
                    ),
                    Some(span),
                );
                return None;
            }
            ConstValue::Float((value as f32) as f64)
        }
        (ConstValue::Float(value), TyKind::Float(FloatTy::F64)) => ConstValue::Float(value),
        (value, _) if source_ty == Some(target_ty) => value,
        _ => return emit_const_type_error(gcx, span),
    };

    validate_value_for_type(gcx, converted, Some(target_ty), span)
}

fn emit_const_cast_range_error<'ctx, T: std::fmt::Display>(
    gcx: GlobalContext<'ctx>,
    value: T,
    target_ty: Ty<'ctx>,
    span: Span,
) -> Option<ConstValue> {
    gcx.dcx().emit_error(
        format!(
            "constant value `{value}` is out of range for type `{}`",
            target_ty.format(gcx)
        ),
        Some(span),
    );
    None
}

fn eval_const_literal<'ctx>(
    gcx: GlobalContext<'ctx>,
    lit: &hir::Literal,
    span: Span,
) -> Option<ConstValue> {
    Some(match lit {
        hir::Literal::Bool(b) => ConstValue::Bool(*b),
        hir::Literal::Rune(r) => ConstValue::Rune(*r),
        hir::Literal::Bytes(v) => ConstValue::Bytes(*v),
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
    ty: Option<Ty<'ctx>>,
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
            let value = match ty.and_then(|ty| integer_layout(gcx, ty)) {
                Some(IntegerLayout {
                    signed: false,
                    bits,
                }) => {
                    let mask = (1u128 << bits) - 1;
                    ((!i as u128) & mask) as i128
                }
                _ => !i,
            };
            Some(ConstValue::Integer(value))
        }
        _ => {
            gcx.dcx().emit_error(
                "initializer must be a constant expression".into(),
                Some(span),
            );
            None
        }
    }
}

/// Resolve a constant's receiver before bodies are checked. The declared
/// context can supply missing enum arguments; otherwise keep them open while
/// testing extension targets, just as for an ordinary type-relative read.
fn early_static_member<'ctx>(
    lowerer: &dyn TypeLowerer<'ctx>,
    expression: &hir::Expression,
    expected: Option<Ty<'ctx>>,
) -> Option<hir::Resolution> {
    let gcx = lowerer.gcx();
    let current = lowerer.current_definition()?;
    let mut local_inference = None;
    // Retain context only when lookup uses it to infer the receiver. For
    // example, an array length permits any nonnegative integer constant.
    let mut receiver_context = None;
    let (base_ty, name) = match &expression.kind {
        hir::ExpressionKind::Path(hir::ResolvedPath::Relative(base, segment)) => {
            let mut receiver = None;
            if let hir::TypeKind::Nominal(hir::ResolvedPath::Resolved(path)) = &base.kind {
                match path.resolution {
                    hir::Resolution::Definition(_, DefinitionKind::Interface) => return None,
                    hir::Resolution::Definition(
                        id,
                        DefinitionKind::Enum | DefinitionKind::Struct,
                    ) if path.segments.last()?.arguments.is_none()
                        && !gcx.generics_of(id).is_empty() =>
                    {
                        if let Some(context) = expected.map(|ty| normalize_aliases(gcx, ty))
                            && matches!(context.kind(), TyKind::Adt(def, _) if def.id == id)
                        {
                            receiver = Some(context);
                            receiver_context = Some(context);
                        } else {
                            let icx =
                                std::rc::Rc::new(crate::sema::tycheck::infer::InferCtx::new(gcx));
                            let args = icx.fresh_args_for_def(id, base.span);
                            receiver = Some(super::instantiate::instantiate_ty_with_args(
                                gcx,
                                gcx.get_type(id),
                                args,
                            ));
                            local_inference = Some(icx);
                            receiver_context = expected;
                        }
                    }
                    _ => {}
                }
            }
            (
                receiver.unwrap_or_else(|| lowerer.lower_type(base)),
                segment.identifier.symbol,
            )
        }
        hir::ExpressionKind::InferredMember { name } => {
            receiver_context = expected;
            (expected?, name.symbol)
        }
        _ => return None,
    };
    let base_ty = normalize_aliases(gcx, base_ty);
    if let TyKind::Adt(def, _) = base_ty.kind()
        && let Some(definition) = gcx.try_get_enum_definition(def.id)
        && let Some(variant) = definition.variants.iter().find(|v| v.name == name)
    {
        return Some(hir::Resolution::Definition(
            variant.ctor_def_id,
            gcx.definition_kind(variant.ctor_def_id),
        ));
    }
    let inherent = super::members::inherent_constant(
        gcx,
        base_ty,
        name,
        current,
        local_inference.as_ref(),
        expression.span,
    );
    let mut header_witness = None;
    let selected = inherent.and_then(|found| {
        if let Some(id) = found {
            return Ok(Some(hir::Resolution::Definition(
                id,
                DefinitionKind::AssociatedConstant,
            )));
        }
        let selected = super::members::interface_constant(gcx, base_ty, name, current)?;
        Ok(selected.map(|(requirement, reference)| {
            let resolution = constant_witness(gcx, requirement, reference, expression.span);
            if gcx.store.collecting_constant_headers.get() {
                header_witness = resolution.definition_id();
            }
            resolution
        }))
    });
    match selected {
        Ok(Some(resolution)) => {
            gcx.store
                .constant_member_uses
                .borrow_mut()
                .entry(expression.id)
                .or_insert_with(|| crate::compile::context::ConstantMemberUse {
                    owner: current,
                    expression: gcx.store.arenas.global.alloc(expression.clone()),
                    expected: receiver_context
                        .map(|ty| normalize_aliases(gcx, ty))
                        .filter(|ty| !ty.contains_inference()),
                    header_witness,
                });
            Some(resolution)
        }
        Ok(None) => None,
        Err(error) => {
            gcx.dcx()
                .emit_error(error.format(gcx), Some(expression.span));
            Some(hir::Resolution::Error)
        }
    }
}

pub(crate) fn checked_static_resolution<'ctx>(
    gcx: GlobalContext<'ctx>,
    expression: &hir::Expression,
    results: &TypeCheckResults<'ctx>,
) -> Option<hir::Resolution> {
    let resolved = results.value_resolution(expression.id);
    if let Some(hir::Resolution::Definition(id, DefinitionKind::AssociatedConstant)) = resolved
        && let Some(parent) = gcx.definition_parent(id)
        && gcx.definition_kind(parent) == DefinitionKind::Interface
    {
        let reference = InterfaceReference {
            id: parent,
            arguments: results.instantiation(expression.id)?,
            bindings: &[],
        };
        return Some(constant_witness(gcx, id, reference, expression.span));
    }
    resolved
}

/// Method signatures may themselves depend on this length. Select the actual
/// conformance record first and use its override, inherited override or default.
/// The checked expression verifies the definition again with the finished witness.
fn header_constant_witness<'ctx>(
    gcx: GlobalContext<'ctx>,
    requirement: hir::DefinitionID,
    mut goal: crate::sema::models::InterfaceGoal<'ctx>,
) -> Option<hir::DefinitionID> {
    use crate::sema::models::{SelectionMode, SelectionResult};
    let name = gcx.definition_ident(requirement).symbol;
    let mut visited = rustc_hash::FxHashSet::default();
    loop {
        let SelectionResult::Selected(selected) =
            gcx.select_interface_impl(goal, SelectionMode::Typecheck)
        else {
            return None;
        };
        let id = selected.record_id?;
        if !visited.insert(id) {
            return None;
        }
        let record = gcx.conformance_record(id)?;
        if record.extension.package() != gcx.package_index() {
            return gcx
                .build_conformance_witness(goal, SelectionMode::Typecheck)
                .ok()?
                .constant_witnesses
                .get(&requirement)
                .copied();
        }
        if let Some((_, id)) = gcx
            .named_constant_headers(name)
            .into_iter()
            .find(|(owner, _)| *owner == record.extension)
        {
            return Some(id);
        }
        match crate::sema::impl_engine::witness::inherited_class_goal(gcx, &record, selected.subst)
        {
            Some(parent) => goal = parent,
            None => return Some(requirement),
        }
    }
}

/// A declaration initializer needs a concrete value. Ordinary generic reads
/// keep the requirement in MIR until the caller's arguments are known.
fn constant_witness<'ctx>(
    gcx: GlobalContext<'ctx>,
    requirement: hir::DefinitionID,
    interface: InterfaceReference<'ctx>,
    span: Span,
) -> hir::Resolution {
    let witness = if gcx.store.collecting_constant_headers.get() {
        interface
            .to_goal(gcx, &[])
            .and_then(|goal| header_constant_witness(gcx, requirement, goal))
    } else {
        crate::sema::tycheck::resolve_conformance_witness(gcx, interface)
            .and_then(|witness| witness.constant_witnesses.get(&requirement).copied())
    };
    if let Some(id) = witness {
        return hir::Resolution::Definition(id, DefinitionKind::AssociatedConstant);
    }
    gcx.dcx().emit_error(
        format!(
            "constant evaluation requires a concrete implementation of '{}'",
            gcx.symbol_text(gcx.definition_ident(requirement).symbol)
        ),
        Some(span),
    );
    hir::Resolution::Error
}

fn eval_const_path<'ctx>(
    gcx: GlobalContext<'ctx>,
    resolution: &hir::Resolution,
    span: Span,
) -> Option<ConstValue> {
    match *resolution {
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
    ty: Option<Ty<'ctx>>,
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

    // Enum comparisons dispatch through an interface, including hand-written
    // equality. Comparing constructor IDs here would bypass that implementation.
    if matches!(lhs, ConstValue::EnumUnitVariant(_))
        || matches!(rhs, ConstValue::EnumUnitVariant(_))
    {
        return type_error();
    }
    match op {
        BinOp::IdentityEql | BinOp::IdentityNeq | BinOp::In | BinOp::NotIn => type_error(),
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
        BinOp::BoolAnd | BinOp::BoolOr => unreachable!("logical operators are evaluated lazily"),
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
                let Ok(shift) = u32::try_from(b) else {
                    return overflow_error();
                };
                let max_shift = ty
                    .and_then(|ty| integer_layout(gcx, ty))
                    .map(|layout| layout.bits)
                    .unwrap_or(i128::BITS);
                if shift >= max_shift {
                    return overflow_error();
                }
                a.checked_shl(shift)
                    .map(ConstValue::Integer)
                    .or_else(overflow_error)
            }
            _ => type_error(),
        },
        BinOp::BitShr => match (lhs, rhs) {
            (ConstValue::Integer(a), ConstValue::Integer(b)) if b >= 0 => {
                let Ok(shift) = u32::try_from(b) else {
                    return overflow_error();
                };
                let max_shift = ty
                    .and_then(|ty| integer_layout(gcx, ty))
                    .map(|layout| layout.bits)
                    .unwrap_or(i128::BITS);
                if shift >= max_shift {
                    return overflow_error();
                }
                a.checked_shr(shift)
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

fn binary_result_matches_operands(op: hir::BinaryOperator) -> bool {
    !matches!(
        op,
        hir::BinaryOperator::Eql
            | hir::BinaryOperator::Neq
            | hir::BinaryOperator::Lt
            | hir::BinaryOperator::Gt
            | hir::BinaryOperator::Leq
            | hir::BinaryOperator::Geq
            | hir::BinaryOperator::BoolAnd
            | hir::BinaryOperator::BoolOr
    )
}

fn emit_const_type_error<T>(gcx: GlobalContext<'_>, span: Span) -> Option<T> {
    gcx.dcx().emit_error(
        "initializer must be a constant expression".into(),
        Some(span),
    );
    None
}

#[derive(Clone, Copy)]
pub(crate) struct IntegerLayout {
    pub(crate) signed: bool,
    pub(crate) bits: u32,
}

impl IntegerLayout {
    pub(crate) fn bounds(self) -> std::ops::RangeInclusive<i128> {
        if self.signed {
            let magnitude = 1i128 << (self.bits - 1);
            -magnitude..=magnitude - 1
        } else {
            0..=(1i128 << self.bits) - 1
        }
    }

    pub(crate) fn contains(self, value: i128) -> bool {
        self.bounds().contains(&value)
    }
}

pub(crate) fn integer_layout<'ctx>(
    gcx: GlobalContext<'ctx>,
    ty: Ty<'ctx>,
) -> Option<IntegerLayout> {
    match crate::sema::tycheck::utils::normalize_aliases(gcx, ty).kind() {
        TyKind::Int(kind) => Some(IntegerLayout {
            signed: true,
            bits: match kind {
                IntTy::ISize => gcx.store.target_facts.pointer_bits(),
                IntTy::I8 => 8,
                IntTy::I16 => 16,
                IntTy::I32 => 32,
                IntTy::I64 => 64,
            },
        }),
        TyKind::UInt(kind) => Some(IntegerLayout {
            signed: false,
            bits: match kind {
                UIntTy::USize => gcx.store.target_facts.pointer_bits(),
                UIntTy::U8 => 8,
                UIntTy::U16 => 16,
                UIntTy::U32 => 32,
                UIntTy::U64 => 64,
            },
        }),
        _ => None,
    }
}

fn validate_value_for_type<'ctx>(
    gcx: GlobalContext<'ctx>,
    value: ConstValue,
    ty: Option<Ty<'ctx>>,
    span: Span,
) -> Option<ConstValue> {
    let Some(ty) = ty else {
        return Some(value);
    };
    let ConstValue::Integer(value) = value else {
        return Some(value);
    };
    let Some(layout) = integer_layout(gcx, ty) else {
        return Some(ConstValue::Integer(value));
    };

    if !layout.contains(value) {
        gcx.dcx().emit_error(
            format!(
                "constant value `{value}` is out of range for type `{}`",
                ty.format(gcx)
            ),
            Some(span),
        );
        return None;
    }

    Some(ConstValue::Integer(value))
}

#[cfg(test)]
mod tests {
    use crate::test_support::{analyze_package_diagnostics, analyze_script_diagnostics};

    #[test]
    fn forward_constant_dependencies_are_order_independent() {
        let diagnostics = analyze_script_diagnostics(
            r#"
const RESULT: int32 = BASE + 2
const BASE: int32 = 40

func main() {
    var _: int32 = RESULT
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

struct CastBuffer {
    bytes: [uint8; FORWARD_CAST_SIZE]
}

const DEFAULT_SIZE: usize = 4
const HEADER_SIZE: usize = 2
const FORWARD_CAST_SIZE: usize = 4_u16 as usize

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

    #[test]
    fn logical_constants_short_circuit_the_rhs() {
        let diagnostics = analyze_script_diagnostics(
            r#"
const SAFE_AND: bool = false && (1 / 0 == 0)
const SAFE_OR: bool = true || (1 / 0 == 0)

func main() {
    var _: bool = SAFE_AND
    var _: bool = SAFE_OR
}
"#,
        );

        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }

    #[test]
    fn constant_conditionals_only_evaluate_the_selected_branch() {
        let diagnostics = analyze_script_diagnostics(
            r#"
const SELECTED_TRUE: int32 = if true { 42 } else { 1 / 0 }
const SELECTED_FALSE: int32 = if false { 1 / 0 } else { 24 }

func main() {
    var _: int32 = SELECTED_TRUE
    var _: int32 = SELECTED_FALSE
}
"#,
        );

        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }

    #[test]
    fn primitive_constant_casts_are_evaluated_at_the_target_type() {
        let diagnostics = analyze_script_diagnostics(
            r#"
const BYTE: uint8 = 255_u16 as uint8
const LETTER: rune = 65_u8 as rune
const LETTER_CODE: uint32 = LETTER as uint32
const RATIO: float = 1.5 as float

func main() {
    var _: uint8 = BYTE
    var _: rune = LETTER
    var _: uint32 = LETTER_CODE
    var _: float = RATIO
}
"#,
        );

        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }

    #[test]
    fn narrowing_constant_casts_reject_out_of_range_values() {
        let diagnostics = analyze_script_diagnostics(
            r#"
const TOO_LARGE: uint8 = 256_u16 as uint8

func main() {}
"#,
        );

        assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
        assert_eq!(
            diagnostics[0].message,
            "constant value `256` is out of range for type `uint8`"
        );
    }

    #[test]
    fn integer_constant_arithmetic_checks_the_declared_width() {
        let diagnostics = analyze_script_diagnostics(
            r#"
const TOO_LARGE: uint8 = 200 + 100

func main() {}
"#,
        );

        assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
        assert_eq!(
            diagnostics[0].message,
            "constant value `300` is out of range for type `uint8`"
        );
    }

    #[test]
    fn integer_constant_intermediates_cannot_overflow_and_return_to_range() {
        let diagnostics = analyze_script_diagnostics(
            r#"
const TOO_LARGE: uint8 = 200 + 100 - 100

func main() {}
"#,
        );

        assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
        assert_eq!(
            diagnostics[0].message,
            "constant value `300` is out of range for type `uint8`"
        );
    }

    #[test]
    fn integer_constant_shifts_check_the_declared_width() {
        let diagnostics = analyze_script_diagnostics(
            r#"
const TOO_FAR: uint8 = 1 << 8

func main() {}
"#,
        );

        assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
        assert_eq!(diagnostics[0].message, "constant overflow");
    }

    #[test]
    fn unsigned_constant_bitwise_not_is_truncated_to_the_declared_width() {
        let diagnostics = analyze_script_diagnostics(
            r#"
const MASK: uint8 = ~0

func main() {
    var _: uint8 = MASK
}
"#,
        );

        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }
}
