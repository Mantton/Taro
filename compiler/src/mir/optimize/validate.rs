//! MIR validation passes that check for semantic errors.
//!
//! These validations run after MIR building to catch errors that are easier
//! to detect at the MIR level than during type checking.

use crate::{
    compile::context::Gcx,
    error::CompileResult,
    hir::{DefinitionKind, Mutability},
    mir::{
        AggregateKind, BasicBlockId, Body, CallUnwindAction, ConstantKind, Operand, Place,
        PlaceElem, Rvalue, StatementKind, TerminatorKind, UnaryOperator,
    },
    sema::models::{Const, ConstKind, ConstValue, EnumVariantKind, Ty, TyKind},
};
use rustc_hash::FxHashMap;
use std::rc::Rc;

use super::MirPass;

// ============================================================================
// MirPass Wrappers
// ============================================================================

/// MIR pass that validates core body invariants.
pub struct ValidateBodyInvariants;

impl<'ctx> MirPass<'ctx> for ValidateBodyInvariants {
    fn name(&self) -> &'static str {
        "ValidateBodyInvariants"
    }

    fn run(&mut self, gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
        validate_body_invariants(gcx, body)
    }
}

// ============================================================================
// Body Invariant Validation
// ============================================================================

pub fn validate_body_invariants<'ctx>(gcx: Gcx<'ctx>, body: &Body<'ctx>) -> CompileResult<()> {
    if gcx.config.is_std_provider {
        return Ok(());
    }

    let normalize_icx = Rc::new(crate::sema::tycheck::infer::InferCtx::new(gcx));
    let normalize_env = crate::sema::tycheck::utils::param_env::ParamEnv::new(
        crate::sema::tycheck::constraints::canonical_constraints_of(gcx, body.owner)
            .iter()
            .map(|constraint| constraint.value)
            .collect(),
    );
    let function_output = gcx.get_signature(body.owner).output;
    let return_local_ty = body.locals[body.return_local].ty;
    let require_return_slot = function_output != gcx.types.void;

    if !types_compatible(
        gcx,
        &normalize_icx,
        &normalize_env,
        return_local_ty,
        function_output,
    ) {
        gcx.dcx().emit_error(
            format!(
                "internal error: MIR return local has type `{}` but function output is `{}`",
                return_local_ty.format(gcx),
                function_output.format(gcx),
            ),
            Some(body.locals[body.return_local].span),
        );
    }

    let mut block_states: FxHashMap<BasicBlockId, bool> = FxHashMap::default();
    block_states.insert(body.start_block, !require_return_slot);
    let mut worklist = vec![body.start_block];

    while let Some(bb_id) = worklist.pop() {
        let Some(mut return_slot_initialized) = block_states.get(&bb_id).copied() else {
            continue;
        };
        let block = &body.basic_blocks[bb_id];

        for stmt in &block.statements {
            if let StatementKind::Assign(destination, rvalue) = &stmt.kind {
                let dest_ty = place_ty(body, gcx, destination);
                if let Some(value_ty) = rvalue_ty(body, gcx, rvalue) {
                    if !types_compatible(gcx, &normalize_icx, &normalize_env, dest_ty, value_ty) {
                        gcx.dcx().emit_error(
                            format!(
                                "internal error: MIR assignment type mismatch (`{}` <- `{}`)",
                                dest_ty.format(gcx),
                                value_ty.format(gcx),
                            ),
                            Some(stmt.span),
                        );
                    }

                    if is_full_return_place(body, destination)
                        && !types_compatible(
                            gcx,
                            &normalize_icx,
                            &normalize_env,
                            function_output,
                            value_ty,
                        )
                    {
                        gcx.dcx().emit_error(
                            format!(
                                "internal error: MIR assigned `{}` into return slot of type `{}`",
                                value_ty.format(gcx),
                                function_output.format(gcx),
                            ),
                            Some(stmt.span),
                        );
                    }
                }

                if is_full_return_place(body, destination) {
                    return_slot_initialized = true;
                }
            }
        }

        if let Some(term) = &block.terminator {
            match &term.kind {
                TerminatorKind::Call {
                    func,
                    destination,
                    target,
                    unwind,
                    ..
                } => {
                    let destination_ty = place_ty(body, gcx, destination);
                    let call_output = call_output_ty(body, gcx, func);

                    if let Some(call_output) = call_output {
                        if !types_compatible(
                            gcx,
                            &normalize_icx,
                            &normalize_env,
                            destination_ty,
                            call_output,
                        ) {
                            gcx.dcx().emit_error(
                                format!(
                                    "internal error: MIR call destination type mismatch (`{}` <- `{}`)",
                                    destination_ty.format(gcx),
                                    call_output.format(gcx),
                                ),
                                Some(term.span),
                            );
                        }

                        if is_full_return_place(body, destination)
                            && !types_compatible(
                                gcx,
                                &normalize_icx,
                                &normalize_env,
                                function_output,
                                call_output,
                            )
                        {
                            gcx.dcx().emit_error(
                                format!(
                                    "internal error: MIR call wrote `{}` into return slot of type `{}`",
                                    call_output.format(gcx),
                                    function_output.format(gcx),
                                ),
                                Some(term.span),
                            );
                        }
                    }

                    let call_returns_normally =
                        !call_output.is_some_and(|ty| matches!(ty.kind(), TyKind::Never));
                    if call_returns_normally {
                        let mut normal_state = return_slot_initialized;
                        if is_full_return_place(body, destination) {
                            normal_state = true;
                        }
                        propagate_bool_state(
                            &mut block_states,
                            &mut worklist,
                            *target,
                            normal_state,
                        );
                    }

                    if let CallUnwindAction::Cleanup(cleanup) = unwind {
                        propagate_bool_state(
                            &mut block_states,
                            &mut worklist,
                            *cleanup,
                            return_slot_initialized,
                        );
                    }
                }
                TerminatorKind::Return => {
                    if require_return_slot && !return_slot_initialized {
                        gcx.dcx().emit_error(
                            "internal error: MIR reached `Return` without initializing the return slot"
                                .to_string(),
                            Some(term.span),
                        );
                    }
                }
                _ => {
                    for succ in successors(&term.kind) {
                        propagate_bool_state(
                            &mut block_states,
                            &mut worklist,
                            succ,
                            return_slot_initialized,
                        );
                    }
                }
            }
        }
    }

    gcx.dcx().ok()
}

fn propagate_bool_state(
    block_states: &mut FxHashMap<BasicBlockId, bool>,
    worklist: &mut Vec<BasicBlockId>,
    succ: BasicBlockId,
    state: bool,
) {
    let changed = if let Some(existing) = block_states.get_mut(&succ) {
        let merged = *existing && state;
        if *existing != merged {
            *existing = merged;
            true
        } else {
            false
        }
    } else {
        block_states.insert(succ, state);
        true
    };

    if changed && !worklist.contains(&succ) {
        worklist.push(succ);
    }
}

fn is_full_return_place<'ctx>(body: &Body<'ctx>, place: &Place<'ctx>) -> bool {
    place.local == body.return_local && place.projection.is_empty()
}

/// Get successors of a terminator.
fn successors(term: &TerminatorKind) -> Vec<BasicBlockId> {
    match term {
        TerminatorKind::Goto { target } => vec![*target],
        TerminatorKind::SwitchInt {
            targets, otherwise, ..
        } => {
            let mut succs: Vec<_> = targets.iter().map(|(_, bb)| *bb).collect();
            succs.push(*otherwise);
            succs
        }
        TerminatorKind::Call { target, unwind, .. } => {
            let mut succs = vec![*target];
            if let CallUnwindAction::Cleanup(bb) = unwind {
                succs.push(*bb);
            }
            succs
        }
        TerminatorKind::Yield { resume, .. } => vec![*resume],
        TerminatorKind::Return
        | TerminatorKind::ResumeUnwind
        | TerminatorKind::Unreachable
        | TerminatorKind::UnresolvedGoto => vec![],
    }
}

fn call_output_ty<'ctx>(
    body: &Body<'ctx>,
    gcx: Gcx<'ctx>,
    operand: &Operand<'ctx>,
) -> Option<Ty<'ctx>> {
    fn normalize_if_possible<'ctx>(gcx: Gcx<'ctx>, ty: Ty<'ctx>) -> Ty<'ctx> {
        if ty.needs_instantiation() || ty.contains_inference() {
            ty
        } else {
            crate::sema::tycheck::utils::normalize_post_monomorphization(gcx, ty)
        }
    }

    match operand {
        Operand::Constant(constant) => {
            let output_from_ty = match constant.ty.kind() {
                TyKind::FnPointer { output, .. } | TyKind::Closure { output, .. } => {
                    Some(normalize_if_possible(gcx, output))
                }
                _ => None,
            };

            if let Some(output) = output_from_ty {
                if !output.needs_instantiation() {
                    return Some(output);
                }
            }

            match constant.value {
                ConstantKind::Function(def_id, args, _) => Some(normalize_if_possible(
                    gcx,
                    crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args(
                        gcx,
                        gcx.get_signature(def_id).output,
                        args,
                    ),
                )),
                _ => output_from_ty,
            }
        }
        Operand::Copy(place) | Operand::CopyWith(place, _) => {
            match place_ty(body, gcx, place).kind() {
                TyKind::FnPointer { output, .. } | TyKind::Closure { output, .. } => {
                    Some(normalize_if_possible(gcx, output))
                }
                _ => None,
            }
        }
    }
}

fn types_compatible<'ctx>(
    _gcx: Gcx<'ctx>,
    normalize_icx: &Rc<crate::sema::tycheck::infer::InferCtx<'ctx>>,
    normalize_env: &crate::sema::tycheck::utils::param_env::ParamEnv<'ctx>,
    expected: Ty<'ctx>,
    actual: Ty<'ctx>,
) -> bool {
    if expected.is_error() || actual.is_error() {
        return true;
    }

    let expected = crate::sema::tycheck::utils::normalize::normalize_ty(
        normalize_icx.clone(),
        expected,
        normalize_env,
    );
    let actual = crate::sema::tycheck::utils::normalize::normalize_ty(
        normalize_icx.clone(),
        actual,
        normalize_env,
    );

    actual == expected
        || matches!(actual.kind(), TyKind::Never)
        || matches!(
            (expected.kind(), actual.kind()),
            (TyKind::Reference(inner_expected, _), TyKind::Pointer(inner_actual, _))
                | (TyKind::Pointer(inner_expected, _), TyKind::Reference(inner_actual, _))
                if inner_expected == inner_actual
        )
        || matches!(
            (expected.kind(), actual.kind()),
            (
                TyKind::BoxedExistential {
                    interfaces: expected_ifaces,
                },
                TyKind::BoxedExistential {
                    interfaces: actual_ifaces,
                },
            ) if existential_interfaces_compatible(expected_ifaces, actual_ifaces)
        )
}

fn existential_interfaces_compatible<'ctx>(
    expected: &'ctx [crate::sema::models::InterfaceReference<'ctx>],
    actual: &'ctx [crate::sema::models::InterfaceReference<'ctx>],
) -> bool {
    if expected.len() != actual.len() {
        return false;
    }

    let mut matched = vec![false; actual.len()];
    for expected_iface in expected {
        let Some((idx, _)) = actual.iter().enumerate().find(|(idx, actual_iface)| {
            !matched[*idx] && interface_refs_compatible(*expected_iface, **actual_iface)
        }) else {
            return false;
        };
        matched[idx] = true;
    }

    true
}

fn interface_refs_compatible<'ctx>(
    expected: crate::sema::models::InterfaceReference<'ctx>,
    actual: crate::sema::models::InterfaceReference<'ctx>,
) -> bool {
    if expected.id != actual.id {
        return false;
    }

    let expected_args = if !expected.arguments.is_empty() {
        &expected.arguments[1..]
    } else {
        &expected.arguments
    };
    let actual_args = if !actual.arguments.is_empty() {
        &actual.arguments[1..]
    } else {
        &actual.arguments
    };

    if expected_args != actual_args || expected.bindings.len() != actual.bindings.len() {
        return false;
    }

    expected.bindings.iter().all(|expected_binding| {
        actual
            .bindings
            .iter()
            .find(|actual_binding| actual_binding.name == expected_binding.name)
            .is_some_and(|actual_binding| actual_binding.ty == expected_binding.ty)
    })
}

fn operand_ty<'ctx>(body: &Body<'ctx>, gcx: Gcx<'ctx>, operand: &Operand<'ctx>) -> Ty<'ctx> {
    match operand {
        Operand::Constant(constant) => constant.ty,
        Operand::Copy(place) | Operand::CopyWith(place, _) => place_ty(body, gcx, place),
    }
}

fn place_ty<'ctx>(body: &Body<'ctx>, gcx: Gcx<'ctx>, place: &Place<'ctx>) -> Ty<'ctx> {
    let mut ty = body.locals[place.local].ty;
    for elem in &place.projection {
        match elem {
            PlaceElem::Deref => {
                ty = ty.dereference().unwrap_or_else(|| Ty::error(gcx));
            }
            PlaceElem::Field(_, field_ty) => ty = *field_ty,
            PlaceElem::VariantDowncast { index, .. } => {
                let def = match ty.kind() {
                    TyKind::Adt(def, _) if def.kind == crate::sema::models::AdtKind::Enum => def,
                    _ => return Ty::error(gcx),
                };
                ty = enum_variant_tuple_ty(gcx, def.id, *index);
            }
        }
    }
    ty
}

fn rvalue_ty<'ctx>(body: &Body<'ctx>, gcx: Gcx<'ctx>, rvalue: &Rvalue<'ctx>) -> Option<Ty<'ctx>> {
    match rvalue {
        Rvalue::Use(operand) => Some(operand_ty(body, gcx, operand)),
        Rvalue::UnaryOp { op, operand } => Some(match op {
            UnaryOperator::LogicalNot => gcx.types.bool,
            UnaryOperator::Negate | UnaryOperator::BitwiseNot => operand_ty(body, gcx, operand),
        }),
        Rvalue::BinaryOp { op, lhs, .. } => Some(match op {
            crate::mir::BinaryOperator::Eql
            | crate::mir::BinaryOperator::Lt
            | crate::mir::BinaryOperator::Gt
            | crate::mir::BinaryOperator::Leq
            | crate::mir::BinaryOperator::Geq
            | crate::mir::BinaryOperator::Neq => gcx.types.bool,
            _ => operand_ty(body, gcx, lhs),
        }),
        Rvalue::Cast { ty, .. } => Some(*ty),
        Rvalue::Ref { mutable, place } => Some(Ty::new(
            TyKind::Reference(
                place_ty(body, gcx, place),
                if *mutable {
                    Mutability::Mutable
                } else {
                    Mutability::Immutable
                },
            ),
            gcx,
        )),
        Rvalue::Discriminant { .. } => Some(gcx.types.uint),
        Rvalue::Alloc { ty } => Some(Ty::new(TyKind::Pointer(*ty, Mutability::Immutable), gcx)),
        Rvalue::Aggregate { kind, fields } => match kind {
            AggregateKind::Tuple => Some(Ty::new(
                TyKind::Tuple(
                    gcx.store.interners.intern_ty_list(
                        fields
                            .iter()
                            .map(|field| operand_ty(body, gcx, field))
                            .collect(),
                    ),
                ),
                gcx,
            )),
            AggregateKind::Adt {
                def_id,
                generic_args,
                ..
            } => match gcx.definition_kind(*def_id) {
                DefinitionKind::Struct => Some(Ty::new(
                    TyKind::Adt(gcx.get_struct_definition(*def_id).adt_def, *generic_args),
                    gcx,
                )),
                DefinitionKind::Enum => Some(Ty::new(
                    TyKind::Adt(gcx.get_enum_definition(*def_id).adt_def, *generic_args),
                    gcx,
                )),
                _ => None,
            },
            AggregateKind::Array { len, element } => Some(Ty::new(
                TyKind::Array {
                    element: *element,
                    len: Const {
                        ty: gcx.types.uint,
                        kind: ConstKind::Value(ConstValue::Integer(*len as i128)),
                    },
                },
                gcx,
            )),
            AggregateKind::Closure {
                def_id,
                captured_generics,
            } => Some(closure_aggregate_ty(gcx, *def_id, *captured_generics)),
        },
        Rvalue::Repeat { count, element, .. } => Some(Ty::new(
            TyKind::Array {
                element: *element,
                len: Const {
                    ty: gcx.types.uint,
                    kind: ConstKind::Value(ConstValue::Integer(*count as i128)),
                },
            },
            gcx,
        )),
    }
}

fn enum_variant_tuple_ty<'ctx>(
    gcx: Gcx<'ctx>,
    def_id: crate::hir::DefinitionID,
    variant_index: crate::thir::VariantIndex,
) -> Ty<'ctx> {
    let def = gcx.get_enum_definition(def_id);
    let variant = def
        .variants
        .get(variant_index.index())
        .expect("enum variant index");
    match variant.kind {
        EnumVariantKind::Unit => gcx.types.void,
        EnumVariantKind::Tuple(fields) => {
            let list = gcx
                .store
                .interners
                .intern_ty_list(fields.iter().map(|field| field.ty).collect());
            Ty::new(TyKind::Tuple(list), gcx)
        }
    }
}

fn closure_aggregate_ty<'ctx>(
    gcx: Gcx<'ctx>,
    def_id: crate::hir::DefinitionID,
    captured_generics: crate::sema::models::GenericArguments<'ctx>,
) -> Ty<'ctx> {
    let signature = gcx.get_signature(def_id);
    let inputs = gcx.store.interners.intern_ty_list(
        signature
            .inputs
            .iter()
            .skip(1)
            .map(|param| param.ty)
            .collect(),
    );
    Ty::new(
        TyKind::Closure {
            closure_def_id: def_id,
            captured_generics,
            inputs,
            output: signature.output,
        },
        gcx,
    )
}
