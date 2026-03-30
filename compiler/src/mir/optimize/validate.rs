//! MIR validation passes that check for semantic errors.
//!
//! These validations run after MIR building to catch errors that are easier
//! to detect at the MIR level than during type checking.

use crate::{
    compile::context::Gcx,
    error::CompileResult,
    hir::{DefinitionKind, Mutability},
    mir::{
        AggregateKind, BasicBlockId, Body, CallUnwindAction, ConstantKind, LocalId, Operand,
        Place, PlaceElem, Rvalue, StatementKind, TerminatorKind, UnaryOperator,
    },
    sema::models::{Const, ConstKind, ConstValue, EnumVariantKind, Ty, TyKind},
    thir::FieldIndex,
};
use rustc_hash::{FxHashMap, FxHashSet};
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

/// MIR pass that validates mutable borrows.
pub struct ValidateMutability;

impl<'ctx> MirPass<'ctx> for ValidateMutability {
    fn name(&self) -> &'static str {
        "ValidateMutability"
    }

    fn run(&mut self, gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
        validate_mutability(gcx, body)
    }
}

/// MIR pass that validates use-after-move.
pub struct ValidateMoves;

impl<'ctx> MirPass<'ctx> for ValidateMoves {
    fn name(&self) -> &'static str {
        "ValidateMoves"
    }

    fn run(&mut self, gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
        validate_moves(gcx, body)
    }
}

/// MIR pass that validates that values are not moved while borrowed.
pub struct ValidateBorrows;

impl<'ctx> MirPass<'ctx> for ValidateBorrows {
    fn name(&self) -> &'static str {
        "ValidateBorrows"
    }

    fn run(&mut self, gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
        validate_borrows(gcx, body)
    }
}

// ============================================================================
// Body Invariant Validation
// ============================================================================

pub fn validate_body_invariants<'ctx>(gcx: Gcx<'ctx>, body: &Body<'ctx>) -> CompileResult<()> {
    validate_make_alloc_call_destination_invariant(gcx, body);

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
    let return_local_ty = body.locals[body.return_local].ty;
    let function_output = if body.is_async {
        gcx.function_body_output(body.owner)
    } else if gcx.definition_is_async(body.owner) {
        return_local_ty
    } else {
        gcx.get_signature(body.owner).output
    };
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
                TerminatorKind::Yield {
                    resume, resume_arg, ..
                } => {
                    let mut resume_state = return_slot_initialized;
                    if is_full_return_place(body, resume_arg) {
                        resume_state = true;
                    }
                    propagate_bool_state(&mut block_states, &mut worklist, *resume, resume_state);
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

fn validate_make_alloc_call_destination_invariant<'ctx>(gcx: Gcx<'ctx>, body: &Body<'ctx>) {
    for (bb_id, block) in body.basic_blocks.iter_enumerated() {
        let mut fresh_alloc_locals: FxHashSet<_> = FxHashSet::default();

        for stmt in &block.statements {
            let StatementKind::Assign(destination, rvalue) = &stmt.kind else {
                continue;
            };

            if destination.projection.is_empty() {
                if matches!(rvalue, Rvalue::Alloc { .. }) {
                    fresh_alloc_locals.insert(destination.local);
                    continue;
                }

                fresh_alloc_locals.remove(&destination.local);
            }

            if matches!(destination.projection.first(), Some(PlaceElem::Deref)) {
                fresh_alloc_locals.remove(&destination.local);
            }
        }

        let Some(term) = &block.terminator else {
            continue;
        };
        let TerminatorKind::Call { destination, .. } = &term.kind else {
            continue;
        };

        if destination.projection.len() == 1
            && matches!(destination.projection[0], PlaceElem::Deref)
            && fresh_alloc_locals.contains(&destination.local)
        {
            gcx.dcx().emit_error(
                format!(
                    "internal error: MIR make-lowering invariant violated in bb{}: call result \
                     was written directly into fresh alloc pointee `*local{}`",
                    bb_id.index(),
                    destination.local.index(),
                ),
                Some(term.span),
            );
        }
    }
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
            if let ConstantKind::Function(def_id, _, _) = constant.value {
                if gcx.definition_is_async(def_id) {
                    return Some(gcx.async_handle_ty());
                }
            }

            let output_from_ty = match constant.ty.kind() {
                TyKind::FnPointer { output, .. } => Some(normalize_if_possible(gcx, output)),
                TyKind::Closure { kind, output, .. } => {
                    Some(if matches!(
                        kind,
                        crate::sema::models::ClosureKind::AsyncFn
                            | crate::sema::models::ClosureKind::AsyncFnMut
                            | crate::sema::models::ClosureKind::AsyncFnOnce
                    ) {
                        gcx.async_handle_ty()
                    } else {
                        normalize_if_possible(gcx, output)
                    })
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
        Operand::Copy(place) | Operand::Move(place) | Operand::CopyWith(place, _) => {
            match place_ty(body, gcx, place).kind() {
                TyKind::FnPointer { output, .. } => Some(normalize_if_possible(gcx, output)),
                TyKind::Closure { kind, output, .. } => {
                    Some(if matches!(
                        kind,
                        crate::sema::models::ClosureKind::AsyncFn
                            | crate::sema::models::ClosureKind::AsyncFnMut
                            | crate::sema::models::ClosureKind::AsyncFnOnce
                    ) {
                        gcx.async_handle_ty()
                    } else {
                        normalize_if_possible(gcx, output)
                    })
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
        Operand::Copy(place) | Operand::Move(place) | Operand::CopyWith(place, _) => {
            place_ty(body, gcx, place)
        }
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
    let kind = gcx
        .get_closure_captures(def_id)
        .map(|captures| captures.kind)
        .unwrap_or_else(|| {
            if gcx.definition_is_async(def_id) {
                crate::sema::models::ClosureKind::AsyncFn
            } else {
                crate::sema::models::ClosureKind::Fn
            }
        });
    Ty::new(
        TyKind::Closure {
            closure_def_id: def_id,
            kind,
            captured_generics,
            inputs,
            output: signature.output,
        },
        gcx,
    )
}

// ============================================================================
// Mutability Validation
// ============================================================================

pub fn validate_mutability<'ctx>(gcx: Gcx<'ctx>, body: &Body<'ctx>) -> CompileResult<()> {
    for block in body.basic_blocks.iter() {
        for stmt in &block.statements {
            if let StatementKind::Assign(
                _,
                Rvalue::Ref {
                    mutable: true,
                    place,
                },
            ) = &stmt.kind
            {
                if !is_place_mutable(gcx, body, place) {
                    let local_decl = &body.locals[place.local];
                    let name = local_decl
                        .name
                        .map(|symbol| format!("'{}'", symbol))
                        .unwrap_or_else(|| "<temporary>".to_string());
                    gcx.dcx().emit_error(
                        format!("cannot borrow immutable local {} as mutable", name),
                        Some(stmt.span),
                    );
                }
            }
        }
    }
    gcx.dcx().ok()
}

fn is_place_mutable<'ctx>(_: Gcx<'ctx>, body: &Body<'ctx>, place: &Place<'ctx>) -> bool {
    let local_decl = &body.locals[place.local];
    let mut current_ty = local_decl.ty;

    let base_is_mutable = match current_ty.kind() {
        TyKind::Reference(_, mutability) | TyKind::Pointer(_, mutability) => {
            mutability == Mutability::Mutable
        }
        _ => local_decl.mutable,
    };

    if !base_is_mutable {
        return false;
    }

    for elem in &place.projection {
        match elem {
            PlaceElem::Deref => match current_ty.kind() {
                TyKind::Reference(inner, mutability) => {
                    if mutability == Mutability::Immutable {
                        return false;
                    }
                    current_ty = inner;
                }
                TyKind::Pointer(inner, mutability) => {
                    if mutability == Mutability::Immutable {
                        return false;
                    }
                    current_ty = inner;
                }
                _ => return true,
            },
            PlaceElem::Field(_, field_ty) => current_ty = *field_ty,
            PlaceElem::VariantDowncast { .. } => {}
        }
    }

    true
}

// ============================================================================
// Move Validation
// ============================================================================

#[derive(Clone, Default)]
struct MoveState {
    moved_locals: FxHashSet<LocalId>,
    partial_moves: FxHashMap<LocalId, FxHashSet<FieldIndex>>,
    moved_borrowed_contents: FxHashSet<LocalId>,
}

impl MoveState {
    fn merge(&mut self, other: &MoveState) -> bool {
        let mut changed = false;

        for &local in &other.moved_locals {
            if self.moved_locals.insert(local) {
                changed = true;
            }
        }

        for (&local, fields) in &other.partial_moves {
            let entry = self.partial_moves.entry(local).or_default();
            for &field in fields {
                if entry.insert(field) {
                    changed = true;
                }
            }
        }

        for &local in &other.moved_borrowed_contents {
            if self.moved_borrowed_contents.insert(local) {
                changed = true;
            }
        }

        changed
    }

    fn mark_moved(&mut self, local: LocalId) {
        self.moved_locals.insert(local);
        self.partial_moves.remove(&local);
    }

    fn mark_field_moved(&mut self, local: LocalId, field: FieldIndex) {
        if self.moved_locals.contains(&local) {
            return;
        }
        self.partial_moves.entry(local).or_default().insert(field);
    }

    fn reinitialize(&mut self, local: LocalId) {
        self.moved_locals.remove(&local);
        self.partial_moves.remove(&local);
        self.moved_borrowed_contents.remove(&local);
    }

    fn is_moved(&self, local: LocalId) -> bool {
        self.moved_locals.contains(&local)
    }

    fn is_field_moved(&self, local: LocalId, field: FieldIndex) -> bool {
        if self.moved_locals.contains(&local) {
            return true;
        }
        self.partial_moves
            .get(&local)
            .is_some_and(|fields| fields.contains(&field))
    }

    fn mark_borrowed_content_moved(&mut self, local: LocalId) {
        self.moved_borrowed_contents.insert(local);
    }

    fn reinitialize_borrowed_content(&mut self, local: LocalId) {
        self.moved_borrowed_contents.remove(&local);
    }

    fn is_borrowed_content_moved(&self, local: LocalId) -> bool {
        self.moved_borrowed_contents.contains(&local)
    }
}

pub fn validate_moves<'ctx>(gcx: Gcx<'ctx>, body: &Body<'ctx>) -> CompileResult<()> {
    let mut block_states: FxHashMap<BasicBlockId, MoveState> = FxHashMap::default();
    let mut worklist = vec![body.start_block];
    block_states.insert(body.start_block, MoveState::default());

    while let Some(bb_id) = worklist.pop() {
        let mut state = block_states.get(&bb_id).cloned().unwrap_or_default();
        let block = &body.basic_blocks[bb_id];

        for stmt in &block.statements {
            match &stmt.kind {
                StatementKind::Assign(dest, rvalue) => {
                    check_rvalue_uses(gcx, body, &state, rvalue, stmt.span)?;
                    state.reinitialize(dest.local);
                    reinitialize_borrowed_content_if_needed(body, dest, &mut state);
                    collect_moves_from_rvalue(body, rvalue, &mut state);
                }
                StatementKind::ShadowResync(locals) => {
                    for &local in locals {
                        check_place_not_moved(
                            gcx,
                            body,
                            &state,
                            &Place::from_local(local),
                            stmt.span,
                        )?;
                    }
                }
                StatementKind::SetDiscriminant { .. }
                | StatementKind::GcSafepoint
                | StatementKind::Nop => {}
            }
        }

        if let Some(term) = &block.terminator {
            check_terminator_uses(gcx, body, &state, term)?;
            collect_moves_from_terminator(body, term, &mut state);

            match &term.kind {
                TerminatorKind::Call {
                    destination,
                    target,
                    unwind,
                    ..
                } => {
                    let mut normal_state = state.clone();
                    normal_state.reinitialize(destination.local);
                    reinitialize_borrowed_content_if_needed(body, destination, &mut normal_state);
                    propagate_move_state(&mut block_states, &mut worklist, *target, &normal_state);

                    if let CallUnwindAction::Cleanup(cleanup) = unwind {
                        propagate_move_state(&mut block_states, &mut worklist, *cleanup, &state);
                    }
                }
                TerminatorKind::Yield {
                    resume, resume_arg, ..
                } => {
                    let mut resume_state = state.clone();
                    resume_state.reinitialize(resume_arg.local);
                    reinitialize_borrowed_content_if_needed(body, resume_arg, &mut resume_state);
                    propagate_move_state(&mut block_states, &mut worklist, *resume, &resume_state);
                }
                _ => {
                    for succ in successors(&term.kind) {
                        propagate_move_state(&mut block_states, &mut worklist, succ, &state);
                    }
                }
            }
        }
    }

    gcx.dcx().ok()
}

fn propagate_move_state(
    block_states: &mut FxHashMap<BasicBlockId, MoveState>,
    worklist: &mut Vec<BasicBlockId>,
    succ: BasicBlockId,
    state: &MoveState,
) {
    let changed = if let Some(succ_state) = block_states.get_mut(&succ) {
        succ_state.merge(state)
    } else {
        block_states.insert(succ, state.clone());
        true
    };

    if changed && !worklist.contains(&succ) {
        worklist.push(succ);
    }
}

fn check_rvalue_uses<'ctx>(
    gcx: Gcx<'ctx>,
    body: &Body<'ctx>,
    state: &MoveState,
    rvalue: &Rvalue<'ctx>,
    span: crate::span::Span,
) -> CompileResult<()> {
    match rvalue {
        Rvalue::Use(op) => check_operand(gcx, body, state, op, span)?,
        Rvalue::UnaryOp { operand, .. } => check_operand(gcx, body, state, operand, span)?,
        Rvalue::BinaryOp { lhs, rhs, .. } => {
            check_operand(gcx, body, state, lhs, span)?;
            check_operand(gcx, body, state, rhs, span)?;
        }
        Rvalue::Cast { operand, .. } => check_operand(gcx, body, state, operand, span)?,
        Rvalue::Ref { place, .. } => check_place_not_moved(gcx, body, state, place, span)?,
        Rvalue::Discriminant { place } => check_place_not_moved(gcx, body, state, place, span)?,
        Rvalue::Aggregate { fields, .. } => {
            for op in fields.iter() {
                check_operand(gcx, body, state, op, span)?;
            }
        }
        Rvalue::Repeat { operand, .. } => check_operand(gcx, body, state, operand, span)?,
        Rvalue::Alloc { .. } => {}
    }
    Ok(())
}

fn check_terminator_uses<'ctx>(
    gcx: Gcx<'ctx>,
    body: &Body<'ctx>,
    state: &MoveState,
    term: &crate::mir::Terminator<'ctx>,
) -> CompileResult<()> {
    let span = term.span;
    match &term.kind {
        TerminatorKind::SwitchInt { discr, .. } => check_operand(gcx, body, state, discr, span)?,
        TerminatorKind::Call { func, args, .. } => {
            check_operand(gcx, body, state, func, span)?;
            for arg in args {
                check_operand(gcx, body, state, arg, span)?;
            }
        }
        TerminatorKind::Yield { value, .. } => check_operand(gcx, body, state, value, span)?,
        TerminatorKind::Goto { .. }
        | TerminatorKind::Return
        | TerminatorKind::ResumeUnwind
        | TerminatorKind::Unreachable
        | TerminatorKind::UnresolvedGoto => {}
    }
    Ok(())
}

fn check_operand<'ctx>(
    gcx: Gcx<'ctx>,
    body: &Body<'ctx>,
    state: &MoveState,
    operand: &Operand<'ctx>,
    span: crate::span::Span,
) -> CompileResult<()> {
    let Some((place, is_move)) = operand_place_and_move_kind(operand) else {
        return Ok(());
    };

    check_place_not_moved(gcx, body, state, place, span)?;
    if is_move {
        check_borrow_move(gcx, body, place, span)?;
    }
    Ok(())
}

fn operand_place_and_move_kind<'a, 'ctx>(
    operand: &'a Operand<'ctx>,
) -> Option<(&'a Place<'ctx>, bool)> {
    match operand {
        Operand::Copy(place) => Some((place, false)),
        Operand::Move(place) => Some((place, true)),
        Operand::CopyWith(place, modifiers) => Some((place, modifiers.take)),
        Operand::Constant(_) => None,
    }
}

fn check_borrow_move<'ctx>(
    gcx: Gcx<'ctx>,
    body: &Body<'ctx>,
    place: &Place<'ctx>,
    span: crate::span::Span,
) -> CompileResult<()> {
    if place.projection.is_empty() {
        return Ok(());
    }

    let local_decl = &body.locals[place.local];
    let mut current_ty = local_decl.ty;
    let mut moved_out_of_immutable_reference = false;

    for elem in &place.projection {
        match elem {
            PlaceElem::Deref => match current_ty.kind() {
                TyKind::Reference(inner, mutability) => {
                    if mutability == Mutability::Immutable {
                        moved_out_of_immutable_reference = true;
                    }
                    current_ty = inner;
                }
                TyKind::Pointer(inner, _) => {
                    current_ty = inner;
                }
                _ => {
                    if let Some(inner) = current_ty.dereference() {
                        current_ty = inner;
                    }
                }
            },
            PlaceElem::Field(_, field_ty) => current_ty = *field_ty,
            PlaceElem::VariantDowncast { .. } => {}
        }
    }

    if moved_out_of_immutable_reference && !is_type_copyable_in_body_context(gcx, body, current_ty)
    {
        gcx.dcx()
            .emit_error("cannot move out of borrowed content".to_string(), Some(span));
        return gcx.dcx().ok();
    }

    Ok(())
}

fn is_type_copyable_in_body_context<'ctx>(gcx: Gcx<'ctx>, body: &Body<'ctx>, ty: Ty<'ctx>) -> bool {
    // Normalize alias types before checking copyability
    let icx = Rc::new(crate::sema::tycheck::infer::InferCtx::new(gcx));
    let env = crate::sema::tycheck::utils::param_env::ParamEnv::new(
        gcx.canonical_constraints_of(body.owner)
            .iter()
            .map(|constraint| constraint.value)
            .collect(),
    );
    let normalized = crate::sema::tycheck::utils::normalize::normalize_ty(icx, ty, &env);
    let ty = if normalized != ty { normalized } else { ty };

    gcx.is_type_copyable_in_def(ty, body.owner)
}

fn check_place_not_moved<'ctx>(
    gcx: Gcx<'ctx>,
    body: &Body<'ctx>,
    state: &MoveState,
    place: &Place<'ctx>,
    span: crate::span::Span,
) -> CompileResult<()> {
    let local_decl = &body.locals[place.local];

    if let Some(root_local) = mutable_reference_deref_root(body, place) {
        if state.is_borrowed_content_moved(root_local) {
            gcx.dcx().emit_error(
                "use of moved value behind mutable reference".to_string(),
                Some(span),
            );
            return gcx.dcx().ok();
        }
    }

    if state.is_moved(place.local) {
        let name = local_decl
            .name
            .map(|symbol| format!("'{}'", symbol))
            .unwrap_or_else(|| "<temporary>".to_string());
        gcx.dcx()
            .emit_error(format!("use of moved value {}", name), Some(span));
        return gcx.dcx().ok();
    }

    if let Some(PlaceElem::Field(idx, _)) = place.projection.first() {
        if state.is_field_moved(place.local, *idx) {
            let name = local_decl
                .name
                .map(|symbol| format!("'{}'", symbol))
                .unwrap_or_else(|| "<temporary>".to_string());
            gcx.dcx().emit_error(
                format!("use of partially moved value {} (field already moved)", name),
                Some(span),
            );
            return gcx.dcx().ok();
        }
    }

    if place.projection.is_empty() && state.partial_moves.contains_key(&place.local) {
        let name = local_decl
            .name
            .map(|symbol| format!("'{}'", symbol))
            .unwrap_or_else(|| "<temporary>".to_string());
        gcx.dcx()
            .emit_error(format!("use of partially moved value {}", name), Some(span));
        return gcx.dcx().ok();
    }

    Ok(())
}

fn collect_moves_from_rvalue<'ctx>(body: &Body<'ctx>, rvalue: &Rvalue<'ctx>, state: &mut MoveState) {
    match rvalue {
        Rvalue::Use(op) => collect_move_from_operand(body, op, state),
        Rvalue::UnaryOp { operand, .. } => collect_move_from_operand(body, operand, state),
        Rvalue::BinaryOp { lhs, rhs, .. } => {
            collect_move_from_operand(body, lhs, state);
            collect_move_from_operand(body, rhs, state);
        }
        Rvalue::Cast { operand, .. } => collect_move_from_operand(body, operand, state),
        Rvalue::Aggregate { fields, .. } => {
            for op in fields.iter() {
                collect_move_from_operand(body, op, state);
            }
        }
        Rvalue::Repeat { operand, .. } => collect_move_from_operand(body, operand, state),
        Rvalue::Ref { .. } | Rvalue::Discriminant { .. } | Rvalue::Alloc { .. } => {}
    }
}

fn collect_moves_from_terminator<'ctx>(
    body: &Body<'ctx>,
    term: &crate::mir::Terminator<'ctx>,
    state: &mut MoveState,
) {
    match &term.kind {
        TerminatorKind::SwitchInt { discr, .. } => collect_move_from_operand(body, discr, state),
        TerminatorKind::Call { func, args, .. } => {
            collect_move_from_operand(body, func, state);
            for arg in args {
                collect_move_from_operand(body, arg, state);
            }
        }
        TerminatorKind::Yield { value, .. } => collect_move_from_operand(body, value, state),
        TerminatorKind::Goto { .. }
        | TerminatorKind::Return
        | TerminatorKind::ResumeUnwind
        | TerminatorKind::Unreachable
        | TerminatorKind::UnresolvedGoto => {}
    }
}

fn collect_move_from_operand<'ctx>(
    body: &Body<'ctx>,
    operand: &Operand<'ctx>,
    state: &mut MoveState,
) {
    let Some((place, is_move)) = operand_place_and_move_kind(operand) else {
        return;
    };
    if !is_move {
        return;
    }

    if let Some(root_local) = mutable_reference_deref_root(body, place) {
        state.mark_borrowed_content_moved(root_local);
        return;
    }

    if place.projection.is_empty() {
        state.mark_moved(place.local);
    } else if let Some(PlaceElem::Field(idx, _)) = place.projection.first() {
        state.mark_field_moved(place.local, *idx);
    }
}

fn mutable_reference_deref_root<'ctx>(body: &Body<'ctx>, place: &Place<'ctx>) -> Option<LocalId> {
    if !matches!(place.projection.first(), Some(PlaceElem::Deref)) {
        return None;
    }

    match body.locals[place.local].ty.kind() {
        TyKind::Reference(_, Mutability::Mutable) => Some(place.local),
        _ => None,
    }
}

fn reinitialize_borrowed_content_if_needed<'ctx>(
    body: &Body<'ctx>,
    place: &Place<'ctx>,
    state: &mut MoveState,
) {
    if let Some(root_local) = mutable_reference_deref_root(body, place) {
        state.reinitialize_borrowed_content(root_local);
    }
}

// ============================================================================
// Borrow Validation
// ============================================================================

type BorrowState = FxHashMap<LocalId, FxHashSet<LocalId>>;

pub fn validate_borrows<'ctx>(gcx: Gcx<'ctx>, body: &Body<'ctx>) -> CompileResult<()> {
    use crate::mir::analysis::liveness::compute_liveness;

    let liveness = compute_liveness(body);
    let mut block_in_states: FxHashMap<BasicBlockId, BorrowState> = FxHashMap::default();
    let mut worklist = vec![body.start_block];
    block_in_states.insert(body.start_block, FxHashMap::default());

    while let Some(bb) = worklist.pop() {
        let block = &body.basic_blocks[bb];
        let statements = &block.statements;
        let mut active_borrows = block_in_states.get(&bb).cloned().unwrap_or_default();
        let live_before_terminator =
            compute_live_before_terminator(body, block.terminator.as_ref(), &liveness.live_out[bb]);
        let live_before_statements =
            compute_live_before_statements(statements, live_before_terminator.clone());

        for (idx, stmt) in statements.iter().enumerate() {
            match &stmt.kind {
                StatementKind::Assign(dest, rvalue) => {
                    check_rvalue_moves_borrowed(
                        gcx,
                        rvalue,
                        &active_borrows,
                        &live_before_statements[idx],
                        stmt.span,
                    )?;

                    if dest.projection.is_empty() {
                        kill_borrower(dest.local, &mut active_borrows);
                    }

                    if let Rvalue::Ref { place, .. } = rvalue {
                        if dest.projection.is_empty() {
                            active_borrows
                                .entry(place.local)
                                .or_default()
                                .insert(dest.local);
                        }
                    }

                    if dest.projection.is_empty() {
                        for src_local in borrowed_source_locals(rvalue) {
                            for borrowed in borrowed_locals_for_source(src_local, &active_borrows) {
                                active_borrows.entry(borrowed).or_default().insert(dest.local);
                            }
                        }
                    }
                }
                StatementKind::ShadowResync(_)
                | StatementKind::SetDiscriminant { .. }
                | StatementKind::GcSafepoint
                | StatementKind::Nop => {}
            }
        }

        if let Some(term) = &block.terminator {
            check_terminator_moves_borrowed(
                gcx,
                term,
                &active_borrows,
                &live_before_terminator,
                term.span,
            )?;

            match &term.kind {
                TerminatorKind::Call {
                    target,
                    destination,
                    unwind,
                    ..
                } => {
                    let mut normal_state = active_borrows.clone();
                    if destination.projection.is_empty() {
                        kill_borrower(destination.local, &mut normal_state);
                    }
                    propagate_borrow_state(
                        &mut block_in_states,
                        &mut worklist,
                        *target,
                        &normal_state,
                    );

                    if let CallUnwindAction::Cleanup(cleanup) = unwind {
                        propagate_borrow_state(
                            &mut block_in_states,
                            &mut worklist,
                            *cleanup,
                            &active_borrows,
                        );
                    }
                }
                TerminatorKind::Yield {
                    resume, resume_arg, ..
                } => {
                    let mut resume_state = active_borrows.clone();
                    if resume_arg.projection.is_empty() {
                        kill_borrower(resume_arg.local, &mut resume_state);
                    }
                    propagate_borrow_state(
                        &mut block_in_states,
                        &mut worklist,
                        *resume,
                        &resume_state,
                    );
                }
                _ => {
                    for succ in successors(&term.kind) {
                        propagate_borrow_state(
                            &mut block_in_states,
                            &mut worklist,
                            succ,
                            &active_borrows,
                        );
                    }
                }
            }
        }
    }

    gcx.dcx().ok()
}

fn propagate_borrow_state(
    block_in_states: &mut FxHashMap<BasicBlockId, BorrowState>,
    worklist: &mut Vec<BasicBlockId>,
    succ: BasicBlockId,
    state: &BorrowState,
) {
    let changed = if let Some(succ_state) = block_in_states.get_mut(&succ) {
        merge_borrow_state(succ_state, state)
    } else {
        block_in_states.insert(succ, state.clone());
        true
    };

    if changed && !worklist.contains(&succ) {
        worklist.push(succ);
    }
}

fn merge_borrow_state(into: &mut BorrowState, from: &BorrowState) -> bool {
    let mut changed = false;
    for (&borrowed, borrowers) in from {
        let entry = into.entry(borrowed).or_default();
        for &borrower in borrowers {
            if entry.insert(borrower) {
                changed = true;
            }
        }
    }
    changed
}

fn compute_live_before_terminator<'ctx>(
    body: &Body<'ctx>,
    terminator: Option<&crate::mir::Terminator<'ctx>>,
    live_out: &FxHashSet<LocalId>,
) -> FxHashSet<LocalId> {
    let mut live = live_out.clone();
    if let Some(term) = terminator {
        apply_terminator_liveness(body, term, &mut live);
    }
    live
}

fn compute_live_before_statements<'ctx>(
    statements: &[crate::mir::Statement<'ctx>],
    live_before_terminator: FxHashSet<LocalId>,
) -> Vec<FxHashSet<LocalId>> {
    let mut current_live = live_before_terminator;
    let mut result = vec![FxHashSet::default(); statements.len()];

    for (idx, stmt) in statements.iter().enumerate().rev() {
        apply_statement_liveness(stmt, &mut current_live);
        result[idx] = current_live.clone();
    }

    result
}

fn apply_terminator_liveness<'ctx>(
    body: &Body<'ctx>,
    term: &crate::mir::Terminator<'ctx>,
    live: &mut FxHashSet<LocalId>,
) {
    match &term.kind {
        TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } => {
            live_use_operand(func, live);
            for arg in args {
                live_use_operand(arg, live);
            }
            if destination.projection.is_empty() {
                live.remove(&destination.local);
            } else {
                live_use_place(destination, live);
            }
        }
        TerminatorKind::SwitchInt { discr, .. } => live_use_operand(discr, live),
        TerminatorKind::Yield {
            value, resume_arg, ..
        } => {
            live_use_operand(value, live);
            if resume_arg.projection.is_empty() {
                live.remove(&resume_arg.local);
            } else {
                live_use_place(resume_arg, live);
            }
        }
        TerminatorKind::Return => {
            live.insert(body.return_local);
        }
        TerminatorKind::Goto { .. }
        | TerminatorKind::ResumeUnwind
        | TerminatorKind::Unreachable
        | TerminatorKind::UnresolvedGoto => {}
    }
}

fn apply_statement_liveness<'ctx>(
    stmt: &crate::mir::Statement<'ctx>,
    live: &mut FxHashSet<LocalId>,
) {
    match &stmt.kind {
        StatementKind::Assign(dest, rvalue) => {
            if dest.projection.is_empty() {
                live.remove(&dest.local);
            } else {
                live_use_place(dest, live);
            }
            live_use_rvalue(rvalue, live);
        }
        StatementKind::ShadowResync(locals) => {
            for &local in locals {
                live.insert(local);
            }
        }
        StatementKind::SetDiscriminant { place, .. } => {
            if !place.projection.is_empty() {
                live_use_place(place, live);
            }
        }
        StatementKind::GcSafepoint | StatementKind::Nop => {}
    }
}

fn live_use_place<'ctx>(place: &Place<'ctx>, live: &mut FxHashSet<LocalId>) {
    live.insert(place.local);
}

fn live_use_operand<'ctx>(op: &Operand<'ctx>, live: &mut FxHashSet<LocalId>) {
    match op {
        Operand::Copy(place) | Operand::Move(place) | Operand::CopyWith(place, _) => {
            live_use_place(place, live);
        }
        Operand::Constant(_) => {}
    }
}

fn live_use_rvalue<'ctx>(rvalue: &Rvalue<'ctx>, live: &mut FxHashSet<LocalId>) {
    match rvalue {
        Rvalue::Use(op) => live_use_operand(op, live),
        Rvalue::UnaryOp { operand, .. } => live_use_operand(operand, live),
        Rvalue::BinaryOp { lhs, rhs, .. } => {
            live_use_operand(lhs, live);
            live_use_operand(rhs, live);
        }
        Rvalue::Cast { operand, .. } => live_use_operand(operand, live),
        Rvalue::Ref { place, .. } | Rvalue::Discriminant { place } => live_use_place(place, live),
        Rvalue::Aggregate { fields, .. } => {
            for field in fields {
                live_use_operand(field, live);
            }
        }
        Rvalue::Repeat { operand, .. } => live_use_operand(operand, live),
        Rvalue::Alloc { .. } => {}
    }
}

fn kill_borrower(borrower: LocalId, borrows: &mut BorrowState) {
    for borrowers in borrows.values_mut() {
        borrowers.remove(&borrower);
    }
}

fn borrowed_source_locals<'ctx>(rvalue: &Rvalue<'ctx>) -> Vec<LocalId> {
    match rvalue {
        Rvalue::Use(op) => operand_local(op).into_iter().collect(),
        Rvalue::Aggregate { fields, .. } => fields.iter().filter_map(operand_local).collect(),
        _ => Vec::new(),
    }
}

fn borrowed_locals_for_source(src_local: LocalId, borrows: &BorrowState) -> Vec<LocalId> {
    let mut borrowed = Vec::new();
    for (&borrowed_local, borrowers) in borrows {
        if borrowers.contains(&src_local) {
            borrowed.push(borrowed_local);
        }
    }
    borrowed
}

fn operand_local<'ctx>(operand: &Operand<'ctx>) -> Option<LocalId> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) | Operand::CopyWith(place, _)
            if place.projection.is_empty() =>
        {
            Some(place.local)
        }
        Operand::Copy(_)
        | Operand::Move(_)
        | Operand::CopyWith(_, _)
        | Operand::Constant(_) => None,
    }
}

fn check_rvalue_moves_borrowed<'ctx>(
    gcx: Gcx<'ctx>,
    rvalue: &Rvalue<'ctx>,
    borrows: &BorrowState,
    live: &FxHashSet<LocalId>,
    span: crate::span::Span,
) -> CompileResult<()> {
    match rvalue {
        Rvalue::Use(op) => check_operand_move_borrowed(gcx, op, borrows, live, span),
        Rvalue::UnaryOp { operand, .. }
        | Rvalue::Cast { operand, .. }
        | Rvalue::Repeat { operand, .. } => {
            check_operand_move_borrowed(gcx, operand, borrows, live, span)
        }
        Rvalue::BinaryOp { lhs, rhs, .. } => {
            check_operand_move_borrowed(gcx, lhs, borrows, live, span)?;
            check_operand_move_borrowed(gcx, rhs, borrows, live, span)
        }
        Rvalue::Aggregate { fields, .. } => {
            for field in fields {
                check_operand_move_borrowed(gcx, field, borrows, live, span)?;
            }
            Ok(())
        }
        Rvalue::Ref { .. } | Rvalue::Discriminant { .. } | Rvalue::Alloc { .. } => Ok(()),
    }
}

fn check_terminator_moves_borrowed<'ctx>(
    gcx: Gcx<'ctx>,
    term: &crate::mir::Terminator<'ctx>,
    borrows: &BorrowState,
    live: &FxHashSet<LocalId>,
    span: crate::span::Span,
) -> CompileResult<()> {
    match &term.kind {
        TerminatorKind::Call { func, args, .. } => {
            check_operand_move_borrowed(gcx, func, borrows, live, span)?;
            for arg in args {
                check_operand_move_borrowed(gcx, arg, borrows, live, span)?;
            }
            Ok(())
        }
        TerminatorKind::SwitchInt { discr, .. } => {
            check_operand_move_borrowed(gcx, discr, borrows, live, span)
        }
        TerminatorKind::Yield { value, .. } => {
            check_operand_move_borrowed(gcx, value, borrows, live, span)
        }
        TerminatorKind::Goto { .. }
        | TerminatorKind::Return
        | TerminatorKind::ResumeUnwind
        | TerminatorKind::Unreachable
        | TerminatorKind::UnresolvedGoto => Ok(()),
    }
}

fn check_operand_move_borrowed<'ctx>(
    gcx: Gcx<'ctx>,
    operand: &Operand<'ctx>,
    borrows: &BorrowState,
    live: &FxHashSet<LocalId>,
    span: crate::span::Span,
) -> CompileResult<()> {
    let Some((place, is_move)) = operand_place_and_move_kind(operand) else {
        return Ok(());
    };
    if !is_move {
        return Ok(());
    }

    if let Some(borrowers) = borrows.get(&place.local) {
        if borrowers.iter().any(|borrower| live.contains(borrower)) {
            gcx.dcx()
                .emit_error("cannot move out of borrowed content".to_string(), Some(span));
            return gcx.dcx().ok();
        }
    }

    Ok(())
}
