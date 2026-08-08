use crate::{
    compile::context::Gcx,
    error::CompileResult,
    mir::{
        BasicBlockId, BinaryOperator, Body, CastKind, Constant, ConstantKind, LocalKind, Operand,
        Place, Rvalue, StatementKind, TerminatorKind, UnaryOperator,
        analysis::dominators::{Dominators, compute_dominators},
    },
    sema::models::{IntTy, Ty, TyKind, UIntTy},
};

use super::MirPass;

/// Conservatively propagates scalar constants through single-assignment locals.
///
/// The pass deliberately leaves potentially trapping operations untouched. In
/// particular, division, remainder, shifts, pointers, and floating-point values
/// remain available to the existing runtime/LLVM lowering paths.
pub struct ConstantPropagation;

#[derive(Clone, Copy)]
struct DefSite {
    block: BasicBlockId,
    statement: usize,
}

#[derive(Clone, Copy)]
struct UseSite {
    block: BasicBlockId,
    statement: usize,
}

#[derive(Clone, Copy)]
struct IntegerLayout {
    signed: bool,
    bits: u32,
}

impl<'ctx> MirPass<'ctx> for ConstantPropagation {
    fn name(&self) -> &'static str {
        "ConstantPropagation"
    }

    fn run(&mut self, gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
        let candidates = find_candidates(body);
        let mut constants: Vec<Option<Constant<'ctx>>> = vec![None; body.locals.len()];

        // Definitions can appear before their constant inputs in block order,
        // so discover values to a fixed point. Each local transitions at most
        // once from unknown to a concrete constant.
        loop {
            let mut changed = false;
            for block in &body.basic_blocks {
                for statement in &block.statements {
                    let StatementKind::Assign(destination, rvalue) = &statement.kind else {
                        continue;
                    };
                    if !destination.projection.is_empty()
                        || !candidates[destination.local.index()]
                        || constants[destination.local.index()].is_some()
                    {
                        continue;
                    }

                    let rewritten = rewritten_rvalue(rvalue, &constants);
                    let result_ty = body.locals[destination.local].ty;
                    if let Some(constant) = fold_rvalue(gcx, result_ty, &rewritten)
                        && is_propagatable(&constant)
                    {
                        constants[destination.local.index()] = Some(constant);
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }

        let local_tys: Vec<_> = body.locals.iter().map(|local| local.ty).collect();
        for block in &mut body.basic_blocks {
            for statement in &mut block.statements {
                if let StatementKind::Assign(destination, rvalue) = &mut statement.kind {
                    rewrite_rvalue_operands(rvalue, &constants);
                    if destination.projection.is_empty()
                        && let Some(constant) =
                            fold_rvalue(gcx, local_tys[destination.local.index()], rvalue)
                    {
                        *rvalue = Rvalue::Use(Operand::Constant(constant));
                    }
                }
            }

            let Some(terminator) = &mut block.terminator else {
                continue;
            };
            rewrite_terminator_operands(&mut terminator.kind, &constants);
            let replacement = match &terminator.kind {
                TerminatorKind::SwitchInt {
                    discr: Operand::Constant(constant),
                    targets,
                    otherwise,
                } => switch_value(gcx, constant).map(|(value, mask)| {
                    targets
                        .iter()
                        .find_map(|(candidate, target)| {
                            (((*candidate) & mask) == value).then_some(*target)
                        })
                        .unwrap_or(*otherwise)
                }),
                _ => None,
            };
            if let Some(target) = replacement {
                terminator.kind = TerminatorKind::Goto { target };
            }
        }

        Ok(())
    }
}

fn find_candidates(body: &Body<'_>) -> Vec<bool> {
    let local_count = body.locals.len();
    let mut assignments = vec![0usize; local_count];
    let mut invalid = vec![false; local_count];
    let mut definitions = vec![None; local_count];
    let mut uses: Vec<Vec<UseSite>> = vec![Vec::new(); local_count];

    for (block_id, block) in body.basic_blocks.iter_enumerated() {
        for (statement_index, statement) in block.statements.iter().enumerate() {
            match &statement.kind {
                StatementKind::Assign(destination, rvalue) => {
                    record_assignment(
                        destination,
                        block_id,
                        statement_index,
                        &mut assignments,
                        &mut invalid,
                        &mut definitions,
                    );
                    record_rvalue_uses(rvalue, block_id, statement_index, &mut uses, &mut invalid);
                }
                StatementKind::SetDiscriminant { place, .. } => {
                    invalid[place.local.index()] = true;
                    record_place_use(place, block_id, statement_index, &mut uses, &mut invalid);
                }
                StatementKind::KeepAlive(operand) => {
                    record_operand_use(operand, block_id, statement_index, &mut uses, &mut invalid);
                }
                StatementKind::SourceScope(_)
                | StatementKind::StorageLive(_)
                | StatementKind::SetInitialized(_)
                | StatementKind::GcSafepoint(_)
                | StatementKind::Nop => {}
            }
        }

        if let Some(terminator) = &block.terminator {
            let statement_index = block.statements.len();
            match &terminator.kind {
                TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    ..
                } => {
                    record_operand_use(func, block_id, statement_index, &mut uses, &mut invalid);
                    for argument in args {
                        record_operand_use(
                            argument,
                            block_id,
                            statement_index,
                            &mut uses,
                            &mut invalid,
                        );
                    }
                    record_assignment(
                        destination,
                        block_id,
                        statement_index,
                        &mut assignments,
                        &mut invalid,
                        &mut definitions,
                    );
                    // Call destinations are never compile-time constants.
                    invalid[destination.local.index()] = true;
                }
                TerminatorKind::SwitchInt { discr, .. } => {
                    record_operand_use(discr, block_id, statement_index, &mut uses, &mut invalid)
                }
                TerminatorKind::Yield {
                    value, resume_arg, ..
                } => {
                    record_operand_use(value, block_id, statement_index, &mut uses, &mut invalid);
                    invalid[resume_arg.local.index()] = true;
                }
                TerminatorKind::Goto { .. }
                | TerminatorKind::UnresolvedGoto
                | TerminatorKind::Return
                | TerminatorKind::ResumeUnwind
                | TerminatorKind::Unreachable => {}
            }
        }
    }

    let dominators = compute_dominators(body);
    body.locals
        .iter_enumerated()
        .map(|(local, declaration)| {
            if !matches!(declaration.kind, LocalKind::Temp | LocalKind::User)
                || assignments[local.index()] != 1
                || invalid[local.index()]
            {
                return false;
            }
            definitions[local.index()].is_some_and(|definition| {
                def_dominates_uses(definition, &uses[local.index()], &dominators)
            })
        })
        .collect()
}

fn record_assignment(
    place: &Place<'_>,
    block: BasicBlockId,
    statement: usize,
    assignments: &mut [usize],
    invalid: &mut [bool],
    definitions: &mut [Option<DefSite>],
) {
    assignments[place.local.index()] += 1;
    if place.projection.is_empty() && definitions[place.local.index()].is_none() {
        definitions[place.local.index()] = Some(DefSite { block, statement });
    } else if !place.projection.is_empty() {
        invalid[place.local.index()] = true;
    }
}

fn def_dominates_uses(definition: DefSite, uses: &[UseSite], dominators: &Dominators) -> bool {
    uses.iter().all(|use_site| {
        if definition.block == use_site.block {
            definition.statement < use_site.statement
        } else {
            dominators.dominates(definition.block, use_site.block)
        }
    })
}

fn record_place_use(
    place: &Place<'_>,
    block: BasicBlockId,
    statement: usize,
    uses: &mut [Vec<UseSite>],
    invalid: &mut [bool],
) {
    uses[place.local.index()].push(UseSite { block, statement });
    if !place.projection.is_empty() {
        invalid[place.local.index()] = true;
    }
}

fn record_operand_use(
    operand: &Operand<'_>,
    block: BasicBlockId,
    statement: usize,
    uses: &mut [Vec<UseSite>],
    invalid: &mut [bool],
) {
    match operand {
        Operand::Copy(place) => record_place_use(place, block, statement, uses, invalid),
        Operand::Move(place) | Operand::CopyWith(place, _) => {
            record_place_use(place, block, statement, uses, invalid);
            invalid[place.local.index()] = true;
        }
        Operand::Constant(_) => {}
    }
}

fn record_rvalue_uses(
    rvalue: &Rvalue<'_>,
    block: BasicBlockId,
    statement: usize,
    uses: &mut [Vec<UseSite>],
    invalid: &mut [bool],
) {
    match rvalue {
        Rvalue::Use(operand)
        | Rvalue::UnaryOp { operand, .. }
        | Rvalue::Cast { operand, .. }
        | Rvalue::Repeat { operand, .. } => {
            record_operand_use(operand, block, statement, uses, invalid)
        }
        Rvalue::BinaryOp { lhs, rhs, .. } => {
            record_operand_use(lhs, block, statement, uses, invalid);
            record_operand_use(rhs, block, statement, uses, invalid);
        }
        Rvalue::Ref { place, .. } | Rvalue::Discriminant { place } => {
            record_place_use(place, block, statement, uses, invalid);
            invalid[place.local.index()] = true;
        }
        Rvalue::Aggregate { fields, .. } => {
            for field in fields {
                record_operand_use(field, block, statement, uses, invalid);
            }
        }
        Rvalue::Alloc { .. } => {}
    }
}

fn rewritten_rvalue<'ctx>(
    rvalue: &Rvalue<'ctx>,
    constants: &[Option<Constant<'ctx>>],
) -> Rvalue<'ctx> {
    let mut rewritten = rvalue.clone();
    rewrite_rvalue_operands(&mut rewritten, constants);
    rewritten
}

fn rewrite_rvalue_operands<'ctx>(rvalue: &mut Rvalue<'ctx>, constants: &[Option<Constant<'ctx>>]) {
    match rvalue {
        Rvalue::Use(operand)
        | Rvalue::UnaryOp { operand, .. }
        | Rvalue::Cast { operand, .. }
        | Rvalue::Repeat { operand, .. } => rewrite_operand(operand, constants),
        Rvalue::BinaryOp { lhs, rhs, .. } => {
            rewrite_operand(lhs, constants);
            rewrite_operand(rhs, constants);
        }
        Rvalue::Aggregate { fields, .. } => {
            for field in fields {
                rewrite_operand(field, constants);
            }
        }
        Rvalue::Ref { .. } | Rvalue::Discriminant { .. } | Rvalue::Alloc { .. } => {}
    }
}

fn rewrite_terminator_operands<'ctx>(
    terminator: &mut TerminatorKind<'ctx>,
    constants: &[Option<Constant<'ctx>>],
) {
    match terminator {
        TerminatorKind::Call { func, args, .. } => {
            rewrite_operand(func, constants);
            for argument in args {
                rewrite_operand(argument, constants);
            }
        }
        TerminatorKind::SwitchInt { discr, .. } => rewrite_operand(discr, constants),
        TerminatorKind::Yield { value, .. } => rewrite_operand(value, constants),
        TerminatorKind::Goto { .. }
        | TerminatorKind::UnresolvedGoto
        | TerminatorKind::Return
        | TerminatorKind::ResumeUnwind
        | TerminatorKind::Unreachable => {}
    }
}

fn rewrite_operand<'ctx>(operand: &mut Operand<'ctx>, constants: &[Option<Constant<'ctx>>]) {
    let Operand::Copy(place) = operand else {
        return;
    };
    if place.projection.is_empty()
        && let Some(constant) = &constants[place.local.index()]
    {
        *operand = Operand::Constant(constant.clone());
    }
}

fn fold_rvalue<'ctx>(
    gcx: Gcx<'ctx>,
    result_ty: Ty<'ctx>,
    rvalue: &Rvalue<'ctx>,
) -> Option<Constant<'ctx>> {
    match rvalue {
        Rvalue::Use(Operand::Constant(constant))
            if constant.ty == result_ty && is_propagatable(constant) =>
        {
            Some(constant.clone())
        }
        Rvalue::UnaryOp {
            op,
            operand: Operand::Constant(operand),
        } => fold_unary(gcx, result_ty, *op, operand),
        Rvalue::BinaryOp {
            op,
            lhs: Operand::Constant(lhs),
            rhs: Operand::Constant(rhs),
        } => fold_binary(gcx, result_ty, *op, lhs, rhs),
        Rvalue::Cast {
            operand: Operand::Constant(operand),
            ty,
            kind: CastKind::Numeric,
        } if *ty == result_ty => fold_numeric_cast(gcx, operand, *ty),
        _ => None,
    }
}

fn fold_unary<'ctx>(
    gcx: Gcx<'ctx>,
    result_ty: Ty<'ctx>,
    operator: UnaryOperator,
    operand: &Constant<'ctx>,
) -> Option<Constant<'ctx>> {
    let value = match (operator, &operand.value) {
        (UnaryOperator::LogicalNot, ConstantKind::Bool(value)) => ConstantKind::Bool(!value),
        (UnaryOperator::BitwiseNot, ConstantKind::Integer(value)) => {
            let layout = integer_layout(gcx, operand.ty)?;
            ConstantKind::Integer((!value) & integer_mask(layout.bits))
        }
        (UnaryOperator::Negate, ConstantKind::Integer(value))
            if matches!(operand.ty.kind(), TyKind::Int(_)) =>
        {
            let layout = integer_layout(gcx, operand.ty)?;
            let signed = signed_value(*value, layout.bits);
            if gcx.config.overflow_checks && signed == signed_min(layout.bits) {
                return None;
            }
            ConstantKind::Integer(value.wrapping_neg() & integer_mask(layout.bits))
        }
        _ => return None,
    };
    Some(Constant {
        ty: result_ty,
        value,
    })
}

fn fold_binary<'ctx>(
    gcx: Gcx<'ctx>,
    result_ty: Ty<'ctx>,
    operator: BinaryOperator,
    lhs: &Constant<'ctx>,
    rhs: &Constant<'ctx>,
) -> Option<Constant<'ctx>> {
    if lhs.ty != rhs.ty {
        return None;
    }
    let layout = integer_layout(gcx, lhs.ty)?;
    let lhs_raw = integer_like_raw(lhs)? & integer_mask(layout.bits);
    let rhs_raw = integer_like_raw(rhs)? & integer_mask(layout.bits);

    use BinaryOperator as Op;
    let value = match operator {
        Op::Add | Op::Sub | Op::Mul
            if matches!(lhs.ty.kind(), TyKind::Int(_) | TyKind::UInt(_)) =>
        {
            let folded = fold_arithmetic(gcx, operator, lhs_raw, rhs_raw, layout)?;
            ConstantKind::Integer(folded)
        }
        Op::BitAnd if matches!(lhs.ty.kind(), TyKind::Int(_) | TyKind::UInt(_)) => {
            ConstantKind::Integer(lhs_raw & rhs_raw)
        }
        Op::BitOr if matches!(lhs.ty.kind(), TyKind::Int(_) | TyKind::UInt(_)) => {
            ConstantKind::Integer(lhs_raw | rhs_raw)
        }
        Op::BitXor if matches!(lhs.ty.kind(), TyKind::Int(_) | TyKind::UInt(_)) => {
            ConstantKind::Integer(lhs_raw ^ rhs_raw)
        }
        Op::Eql => ConstantKind::Bool(lhs_raw == rhs_raw),
        Op::Neq => ConstantKind::Bool(lhs_raw != rhs_raw),
        Op::Lt | Op::Gt | Op::Leq | Op::Geq => {
            let ordering = if layout.signed {
                signed_value(lhs_raw, layout.bits).cmp(&signed_value(rhs_raw, layout.bits))
            } else {
                lhs_raw.cmp(&rhs_raw)
            };
            let result = match operator {
                Op::Lt => ordering.is_lt(),
                Op::Gt => ordering.is_gt(),
                Op::Leq => ordering.is_le(),
                Op::Geq => ordering.is_ge(),
                _ => unreachable!(),
            };
            ConstantKind::Bool(result)
        }
        // These can trap or have target-specific edge semantics. Leave them
        // for the checked-intrinsic or LLVM lowering paths.
        Op::Div | Op::Rem | Op::BitShl | Op::BitShr => return None,
        _ => return None,
    };

    Some(Constant {
        ty: result_ty,
        value,
    })
}

fn fold_arithmetic(
    gcx: Gcx<'_>,
    operator: BinaryOperator,
    lhs: u64,
    rhs: u64,
    layout: IntegerLayout,
) -> Option<u64> {
    if gcx.config.overflow_checks {
        if layout.signed {
            let lhs = signed_value(lhs, layout.bits);
            let rhs = signed_value(rhs, layout.bits);
            let value = match operator {
                BinaryOperator::Add => lhs.checked_add(rhs)?,
                BinaryOperator::Sub => lhs.checked_sub(rhs)?,
                BinaryOperator::Mul => lhs.checked_mul(rhs)?,
                _ => return None,
            };
            if value < signed_min(layout.bits) || value > signed_max(layout.bits) {
                return None;
            }
            return Some((value as u64) & integer_mask(layout.bits));
        }

        let value = match operator {
            BinaryOperator::Add => (lhs as u128).checked_add(rhs as u128)?,
            BinaryOperator::Sub => (lhs as u128).checked_sub(rhs as u128)?,
            BinaryOperator::Mul => (lhs as u128).checked_mul(rhs as u128)?,
            _ => return None,
        };
        if value > integer_mask(layout.bits) as u128 {
            return None;
        }
        return Some(value as u64);
    }

    let value = match operator {
        BinaryOperator::Add => lhs.wrapping_add(rhs),
        BinaryOperator::Sub => lhs.wrapping_sub(rhs),
        BinaryOperator::Mul => lhs.wrapping_mul(rhs),
        _ => return None,
    };
    Some(value & integer_mask(layout.bits))
}

fn fold_numeric_cast<'ctx>(
    gcx: Gcx<'ctx>,
    operand: &Constant<'ctx>,
    target_ty: Ty<'ctx>,
) -> Option<Constant<'ctx>> {
    if operand.ty == target_ty {
        return Some(operand.clone());
    }

    let source_layout = integer_layout(gcx, operand.ty)?;
    let source = integer_like_raw(operand)? & integer_mask(source_layout.bits);
    if matches!(target_ty.kind(), TyKind::Bool) {
        return Some(Constant {
            ty: target_ty,
            value: ConstantKind::Bool(source != 0),
        });
    }

    let target_layout = integer_layout(gcx, target_ty)?;
    if !matches!(target_ty.kind(), TyKind::Int(_) | TyKind::UInt(_)) {
        return None;
    }
    let widened = if target_layout.bits > source_layout.bits && source_layout.signed {
        signed_value(source, source_layout.bits) as u64
    } else {
        source
    };
    Some(Constant {
        ty: target_ty,
        value: ConstantKind::Integer(widened & integer_mask(target_layout.bits)),
    })
}

fn switch_value(gcx: Gcx<'_>, constant: &Constant<'_>) -> Option<(u128, u128)> {
    let layout = integer_layout(gcx, constant.ty)?;
    let mask = integer_mask(layout.bits) as u128;
    Some(((integer_like_raw(constant)? as u128) & mask, mask))
}

fn integer_like_raw(constant: &Constant<'_>) -> Option<u64> {
    match constant.value {
        ConstantKind::Bool(value) => Some(value as u64),
        ConstantKind::Rune(value) => Some(value as u32 as u64),
        ConstantKind::Integer(value) => Some(value),
        _ => None,
    }
}

fn is_propagatable(constant: &Constant<'_>) -> bool {
    matches!(
        constant.value,
        ConstantKind::Bool(_) | ConstantKind::Rune(_) | ConstantKind::Integer(_)
    )
}

fn integer_layout(gcx: Gcx<'_>, ty: Ty<'_>) -> Option<IntegerLayout> {
    let pointer_bits = (gcx.store.target_layout.pointer_size * 8) as u32;
    Some(match ty.kind() {
        TyKind::Bool => IntegerLayout {
            signed: false,
            bits: 1,
        },
        TyKind::Rune => IntegerLayout {
            signed: false,
            bits: 32,
        },
        TyKind::Int(kind) => IntegerLayout {
            signed: true,
            bits: match kind {
                IntTy::ISize => pointer_bits,
                IntTy::I8 => 8,
                IntTy::I16 => 16,
                IntTy::I32 => 32,
                IntTy::I64 => 64,
            },
        },
        TyKind::UInt(kind) => IntegerLayout {
            signed: false,
            bits: match kind {
                UIntTy::USize => pointer_bits,
                UIntTy::U8 => 8,
                UIntTy::U16 => 16,
                UIntTy::U32 => 32,
                UIntTy::U64 => 64,
            },
        },
        _ => return None,
    })
}

fn integer_mask(bits: u32) -> u64 {
    if bits == u64::BITS {
        u64::MAX
    } else {
        (1u64 << bits) - 1
    }
}

fn signed_value(value: u64, bits: u32) -> i128 {
    let value = value & integer_mask(bits);
    let sign_bit = 1u64 << (bits - 1);
    if value & sign_bit == 0 {
        value as i128
    } else {
        value as i128 - (1i128 << bits)
    }
}

fn signed_min(bits: u32) -> i128 {
    -(1i128 << (bits - 1))
}

fn signed_max(bits: u32) -> i128 {
    (1i128 << (bits - 1)) - 1
}

#[cfg(test)]
mod tests {
    use super::{ConstantPropagation, fold_binary, fold_numeric_cast};
    use crate::{
        mir::{
            BasicBlockData, BinaryOperator, Constant, ConstantKind, Operand, Place, Rvalue,
            Statement, StatementKind, Terminator, TerminatorKind,
            optimize::{MirPass, run_passes},
            test_support::{minimal_body, push_temp, with_test_gcx},
        },
        span::Span,
    };

    #[test]
    fn folds_constant_chain_and_selects_switch_target() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let span = Span::empty(body.locals[body.return_local].span.file);
            let lhs = push_temp(&mut body, gcx.types.int32);
            let rhs = push_temp(&mut body, gcx.types.int32);
            let sum = push_temp(&mut body, gcx.types.int32);
            let condition = push_temp(&mut body, gcx.types.bool);
            let true_target = body.basic_blocks.push(BasicBlockData {
                note: Some("true".into()),
                statements: vec![],
                terminator: Some(Terminator {
                    kind: TerminatorKind::Return,
                    span,
                }),
            });
            let false_target = body.basic_blocks.push(BasicBlockData {
                note: Some("false".into()),
                statements: vec![],
                terminator: Some(Terminator {
                    kind: TerminatorKind::Unreachable,
                    span,
                }),
            });
            let int = |value| {
                Operand::Constant(Constant {
                    ty: gcx.types.int32,
                    value: ConstantKind::Integer(value),
                })
            };
            body.basic_blocks[body.start_block].statements = vec![
                Statement {
                    kind: StatementKind::Assign(Place::from_local(lhs), Rvalue::Use(int(2))),
                    span,
                },
                Statement {
                    kind: StatementKind::Assign(Place::from_local(rhs), Rvalue::Use(int(3))),
                    span,
                },
                Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(sum),
                        Rvalue::BinaryOp {
                            op: BinaryOperator::Add,
                            lhs: Operand::Copy(Place::from_local(lhs)),
                            rhs: Operand::Copy(Place::from_local(rhs)),
                        },
                    ),
                    span,
                },
                Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(condition),
                        Rvalue::BinaryOp {
                            op: BinaryOperator::Gt,
                            lhs: Operand::Copy(Place::from_local(sum)),
                            rhs: int(4),
                        },
                    ),
                    span,
                },
            ];
            body.basic_blocks[body.start_block].terminator = Some(Terminator {
                kind: TerminatorKind::SwitchInt {
                    discr: Operand::Copy(Place::from_local(condition)),
                    targets: vec![(0, false_target)],
                    otherwise: true_target,
                },
                span,
            });

            assert!(run_passes(gcx, &mut body, &mut [Box::new(ConstantPropagation)]).is_ok());

            assert!(matches!(
                body.basic_blocks[body.start_block]
                    .terminator
                    .as_ref()
                    .map(|terminator| &terminator.kind),
                Some(TerminatorKind::Goto { target }) if *target == true_target
            ));
            assert!(matches!(
                &body.basic_blocks[body.start_block].statements[2].kind,
                StatementKind::Assign(
                    _,
                    Rvalue::Use(Operand::Constant(Constant {
                        value: ConstantKind::Integer(5),
                        ..
                    }))
                )
            ));
        });
    }

    #[test]
    fn leaves_division_by_zero_for_runtime_lowering() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let span = body.locals[body.return_local].span;
            let destination = push_temp(&mut body, gcx.types.int32);
            let int = |value| {
                Operand::Constant(Constant {
                    ty: gcx.types.int32,
                    value: ConstantKind::Integer(value),
                })
            };
            body.basic_blocks[body.start_block]
                .statements
                .push(Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(destination),
                        Rvalue::BinaryOp {
                            op: BinaryOperator::Div,
                            lhs: int(1),
                            rhs: int(0),
                        },
                    ),
                    span,
                });

            assert!(ConstantPropagation.run(gcx, &mut body).is_ok());

            assert!(matches!(
                body.basic_blocks[body.start_block].statements[0].kind,
                StatementKind::Assign(
                    _,
                    Rvalue::BinaryOp {
                        op: BinaryOperator::Div,
                        ..
                    }
                )
            ));
        });
    }

    #[test]
    fn leaves_checked_integer_overflow_for_runtime_lowering() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let span = body.locals[body.return_local].span;
            let destination = push_temp(&mut body, gcx.types.int8);
            let int = |value| {
                Operand::Constant(Constant {
                    ty: gcx.types.int8,
                    value: ConstantKind::Integer(value),
                })
            };
            body.basic_blocks[body.start_block]
                .statements
                .push(Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(destination),
                        Rvalue::BinaryOp {
                            op: BinaryOperator::Add,
                            lhs: int(127),
                            rhs: int(1),
                        },
                    ),
                    span,
                });

            assert!(ConstantPropagation.run(gcx, &mut body).is_ok());

            assert!(matches!(
                body.basic_blocks[body.start_block].statements[0].kind,
                StatementKind::Assign(
                    _,
                    Rvalue::BinaryOp {
                        op: BinaryOperator::Add,
                        ..
                    }
                )
            ));
        });
    }

    #[test]
    fn folds_signed_comparisons_using_the_declared_width() {
        with_test_gcx(|gcx| {
            let negative_one = Constant {
                ty: gcx.types.int8,
                value: ConstantKind::Integer(0xff),
            };
            let one = Constant {
                ty: gcx.types.int8,
                value: ConstantKind::Integer(1),
            };

            let folded = fold_binary(gcx, gcx.types.bool, BinaryOperator::Lt, &negative_one, &one)
                .expect("signed comparison should fold");

            assert!(matches!(folded.value, ConstantKind::Bool(true)));
        });
    }

    #[test]
    fn folds_integer_casts_with_source_signedness() {
        with_test_gcx(|gcx| {
            let negative_one = Constant {
                ty: gcx.types.int8,
                value: ConstantKind::Integer(0xff),
            };

            let widened = fold_numeric_cast(gcx, &negative_one, gcx.types.int32)
                .expect("signed widening cast should fold");
            let truthy = fold_numeric_cast(gcx, &negative_one, gcx.types.bool)
                .expect("integer-to-bool cast should fold");

            assert!(matches!(widened.value, ConstantKind::Integer(0xffff_ffff)));
            assert!(matches!(truthy.value, ConstantKind::Bool(true)));
        });
    }
}
