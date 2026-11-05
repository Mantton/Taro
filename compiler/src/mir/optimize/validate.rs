//! MIR validation passes that check for semantic errors.
//!
//! These validations run after MIR building to catch errors that are easier
//! to detect at the MIR level than during type checking.

use crate::{
    compile::context::Gcx,
    error::{CompileResult, ReportedError},
    hir::{DefinitionKind, Mutability},
    mir::{
        AggregateKind, BasicBlockId, Body, CallUnwindAction, ConstantKind, LocalId, Operand, Place,
        PlaceElem, Rvalue, StatementKind, TerminatorKind, UnaryOperator,
    },
    sema::models::{Const, ConstKind, ConstValue, Ty, TyKind},
};
use rustc_hash::FxHashMap;
use std::rc::Rc;

use super::MirPass;
use crate::mir::analysis::mutability::is_place_mutable;

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

/// MIR pass that validates initialized storage.
pub struct ValidateInitialization;

impl<'ctx> MirPass<'ctx> for ValidateInitialization {
    fn name(&self) -> &'static str {
        "ValidateInitialization"
    }

    fn run(&mut self, gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
        crate::mir::analysis::initialization::validate_initialization(gcx, body)
    }
}

// ============================================================================
// Phase-independent structural validation
// ============================================================================

/// Validate graph and index invariants that every completed MIR pass must
/// preserve. Unlike the semantic validators below, this is safe to run at any
/// MIR phase.
pub fn validate_body_structure<'ctx>(
    gcx: Gcx<'ctx>,
    body: &Body<'ctx>,
    after_pass: &str,
) -> CompileResult<()> {
    let local_count = body.locals.len();
    let block_count = body.basic_blocks.len();
    let mut validator = StructureValidator {
        gcx,
        owner: body.owner,
        after_pass,
        local_count,
        block_count,
        source_scope_count: body.source_scopes.len(),
        valid: true,
    };

    if body.source_scopes.is_empty() {
        validator.error("body has no physical source scope", None);
    } else {
        for (scope, data) in body.source_scopes.iter_enumerated() {
            if scope.index() == 0 {
                if data.definition != body.owner || data.parent.is_some() || data.callsite.is_some()
                {
                    validator.error(
                        "source scope zero is not the physical function root",
                        data.callsite,
                    );
                }
                continue;
            }
            let Some(parent) = data.parent else {
                validator.error(
                    format!("non-root source scope {scope:?} has no parent"),
                    data.callsite,
                );
                continue;
            };
            if parent.index() >= scope.index() {
                validator.error(
                    format!("source scope {scope:?} has non-ancestral parent {parent:?}"),
                    data.callsite,
                );
            }
            if data.callsite.is_none() {
                validator.error(
                    format!("inlined source scope {scope:?} has no callsite"),
                    None,
                );
            }
        }
    }

    if block_count == 0 {
        validator.error("body has no basic blocks", None);
    } else if body.start_block.index() >= block_count {
        validator.error(
            format!("start block {:?} is out of bounds", body.start_block),
            None,
        );
    }

    if local_count == 0 {
        validator.error("body has no locals", None);
    } else if body.return_local.index() >= local_count {
        validator.error(
            format!("return local {:?} is out of bounds", body.return_local),
            None,
        );
    } else if !matches!(
        body.locals[body.return_local].kind,
        crate::mir::LocalKind::Return | crate::mir::LocalKind::ConstructorSelf
    ) {
        validator.error(
            format!(
                "return local {:?} is not marked as a return local",
                body.return_local
            ),
            Some(body.locals[body.return_local].span),
        );
    }

    for (local, declaration) in body.locals.iter_enumerated() {
        if matches!(declaration.ty.kind(), TyKind::Error | TyKind::Infer(_)) {
            validator.error(
                format!(
                    "local {local:?} has unresolved type {}",
                    declaration.ty.format(gcx)
                ),
                Some(declaration.span),
            );
        }
    }

    for (block_id, block) in body.basic_blocks.iter_enumerated() {
        for statement in &block.statements {
            validator.check_statement(statement);
        }

        match &block.terminator {
            Some(terminator) => validator.check_terminator(terminator),
            None => validator.error(
                format!("basic block {block_id:?} has no terminator"),
                block.statements.last().map(|statement| statement.span),
            ),
        }
    }

    if validator.valid {
        Ok(())
    } else {
        Err(ReportedError)
    }
}

struct StructureValidator<'ctx, 'name> {
    gcx: Gcx<'ctx>,
    owner: crate::hir::DefinitionID,
    after_pass: &'name str,
    local_count: usize,
    block_count: usize,
    source_scope_count: usize,
    valid: bool,
}

impl<'ctx> StructureValidator<'ctx, '_> {
    fn error(&mut self, detail: impl Into<String>, span: Option<crate::span::Span>) {
        self.valid = false;
        self.gcx.dcx().emit_error(
            format!(
                "internal error: MIR structure invalid after `{}` for {:?}: {}",
                self.after_pass,
                self.owner,
                detail.into()
            ),
            span,
        );
    }

    fn check_local(&mut self, local: LocalId, span: crate::span::Span) {
        if local.index() >= self.local_count {
            self.error(format!("local {local:?} is out of bounds"), Some(span));
        }
    }

    fn check_edge(&mut self, block: BasicBlockId, span: crate::span::Span) {
        if block.index() >= self.block_count {
            self.error(
                format!("edge targets out-of-bounds block {block:?}"),
                Some(span),
            );
        }
    }

    fn check_source_scope(&mut self, scope: crate::mir::SourceScopeId, span: crate::span::Span) {
        if scope.index() >= self.source_scope_count {
            self.error(
                format!("source scope {scope:?} is out of bounds"),
                Some(span),
            );
        }
    }

    fn check_place(&mut self, place: &Place<'ctx>, span: crate::span::Span) {
        self.check_local(place.local, span);
        for projection in &place.projection {
            if let PlaceElem::Field(_, ty) = projection
                && matches!(ty.kind(), TyKind::Error | TyKind::Infer(_))
            {
                self.error(
                    format!(
                        "place projection has unresolved type {}",
                        ty.format(self.gcx)
                    ),
                    Some(span),
                );
            }
        }
    }

    fn check_operand(&mut self, operand: &Operand<'ctx>, span: crate::span::Span) {
        match operand {
            Operand::Copy(place) | Operand::CopyWith(place, _) => self.check_place(place, span),
            Operand::Constant(constant) => {
                if matches!(constant.ty.kind(), TyKind::Error | TyKind::Infer(_)) {
                    self.error(
                        format!(
                            "constant operand has unresolved type {}",
                            constant.ty.format(self.gcx)
                        ),
                        Some(span),
                    );
                }
            }
        }
    }

    fn check_rvalue(&mut self, rvalue: &Rvalue<'ctx>, span: crate::span::Span) {
        match rvalue {
            Rvalue::CopyValue { source } => {
                self.check_place(source, span);
            }
            Rvalue::Use(operand) | Rvalue::UnaryOp { operand, .. } => {
                self.check_operand(operand, span)
            }
            Rvalue::BinaryOp { lhs, rhs, .. } => {
                self.check_operand(lhs, span);
                self.check_operand(rhs, span);
            }
            Rvalue::Cast { operand, ty, .. } => {
                self.check_operand(operand, span);
                if matches!(ty.kind(), TyKind::Error | TyKind::Infer(_)) {
                    self.error(
                        format!("cast has unresolved target type {}", ty.format(self.gcx)),
                        Some(span),
                    );
                }
            }
            Rvalue::Ref { place, .. }
            | Rvalue::CleanupAddress { place }
            | Rvalue::Discriminant { place } => self.check_place(place, span),
            Rvalue::Alloc { ty } | Rvalue::Zeroed { ty } => {
                if matches!(ty.kind(), TyKind::Error | TyKind::Infer(_)) {
                    self.error(
                        format!(
                            "storage operation has unresolved type {}",
                            ty.format(self.gcx)
                        ),
                        Some(span),
                    );
                }
            }
            Rvalue::Aggregate { fields, .. } => {
                for operand in fields {
                    self.check_operand(operand, span);
                }
            }
            Rvalue::Repeat {
                operand, element, ..
            } => {
                self.check_operand(operand, span);
                if matches!(element.kind(), TyKind::Error | TyKind::Infer(_)) {
                    self.error(
                        format!(
                            "array repeat has unresolved element type {}",
                            element.format(self.gcx)
                        ),
                        Some(span),
                    );
                }
            }
        }
    }

    fn check_statement(&mut self, statement: &crate::mir::Statement<'ctx>) {
        match &statement.kind {
            StatementKind::SourceScope(scope) => self.check_source_scope(*scope, statement.span),
            StatementKind::StorageLive(local) | StatementKind::StorageDead(local) => {
                self.check_local(*local, statement.span)
            }
            StatementKind::SetInitialized(local) => self.check_local(*local, statement.span),

            StatementKind::Assign(place, rvalue) => {
                self.check_place(place, statement.span);
                self.check_rvalue(rvalue, statement.span);
            }
            StatementKind::SetDiscriminant { place, .. } => self.check_place(place, statement.span),
            StatementKind::KeepAlive(operand) => self.check_operand(operand, statement.span),
            StatementKind::GcSafepoint(_) | StatementKind::Nop => {}
        }
    }

    fn check_terminator(&mut self, terminator: &crate::mir::Terminator<'ctx>) {
        let span = terminator.span;
        match &terminator.kind {
            TerminatorKind::Goto { target } => self.check_edge(*target, span),
            TerminatorKind::UnresolvedGoto => {
                self.error("unresolved goto survived a completed pass", Some(span))
            }
            TerminatorKind::SwitchInt {
                discr,
                targets,
                otherwise,
            } => {
                self.check_operand(discr, span);
                for (_, target) in targets {
                    self.check_edge(*target, span);
                }
                self.check_edge(*otherwise, span);
            }

            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                unwind,
                ..
            } => {
                self.check_operand(func, span);
                for argument in args {
                    self.check_operand(argument, span);
                }
                self.check_place(destination, span);
                self.check_edge(*target, span);
                if let CallUnwindAction::Cleanup(cleanup) = unwind {
                    self.check_edge(*cleanup, span);
                }
            }
            TerminatorKind::Yield {
                value,
                resume,
                resume_arg,
                no_result,
                cancel,
                cancel_complete,
                unwind,
            } => {
                self.check_operand(value, span);
                self.check_place(resume_arg, span);
                self.check_edge(*resume, span);
                self.check_edge(*cancel, span);
                self.check_edge(*cancel_complete, span);
                if let Some(failed) = no_result {
                    self.check_edge(*failed, span);
                }
                if let CallUnwindAction::Cleanup(cleanup) = unwind {
                    self.check_edge(*cleanup, span);
                }
            }
            TerminatorKind::Return | TerminatorKind::ResumeUnwind | TerminatorKind::Unreachable => {
            }
        }
    }
}

// ============================================================================
// Body Invariant Validation
// ============================================================================

pub fn validate_body_invariants<'ctx>(gcx: Gcx<'ctx>, body: &Body<'ctx>) -> CompileResult<()> {
    validate_body_invariants_with_output(gcx, body, None)
}

/// Generated bodies are already concrete. Validate against the instantiated
/// declaration, not its still-generic template, without mutating shared metadata.
pub(crate) fn validate_generated_instance_body<'ctx>(
    gcx: Gcx<'ctx>,
    instance: crate::specialize::Instance<'ctx>,
    body: &Body<'ctx>,
) -> CompileResult<()> {
    if body.owner != instance.def_id() || !gcx.is_instance_generated(body.owner) || body.is_async {
        gcx.dcx()
            .emit_error("invalid owner for generated instance MIR".into(), None);
        return gcx.dcx().ok();
    }
    let signature = gcx.get_signature(body.owner);
    let concrete = |ty| {
        crate::sema::tycheck::utils::normalize_post_monomorphization(
            gcx,
            crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args(
                gcx,
                ty,
                instance.args(),
            ),
        )
    };
    let parameters: Vec<_> = body
        .locals
        .iter()
        .filter(|local| local.kind == crate::mir::LocalKind::Param)
        .collect();
    if parameters.len() != signature.inputs.len()
        || parameters
            .iter()
            .zip(&signature.inputs)
            .any(|(actual, expected)| actual.ty != concrete(expected.ty))
    {
        gcx.dcx().emit_error(
            "generated instance MIR parameters do not match its concrete ABI".into(),
            None,
        );
        return gcx.dcx().ok();
    }
    let output = if gcx.definition_is_async(body.owner) {
        gcx.async_handle_ty()
    } else {
        concrete(signature.output)
    };
    validate_body_invariants_with_output(gcx, body, Some(output))
}

fn validate_body_invariants_with_output<'ctx>(
    gcx: Gcx<'ctx>,
    body: &Body<'ctx>,
    concrete_output: Option<Ty<'ctx>>,
) -> CompileResult<()> {
    if gcx.config.is_std_provider && concrete_output.is_none() {
        return Ok(());
    }

    let normalize_icx = Rc::new(crate::sema::tycheck::infer::InferCtx::new(gcx));
    let normalize_env = if concrete_output.is_some() {
        // Generated storage/Clone glue has no source declaration environment;
        // its eligibility and full substitution were checked before building it.
        crate::sema::tycheck::utils::param_env::ParamEnv::default()
    } else {
        crate::sema::tycheck::utils::param_env::ParamEnv::new(
            crate::sema::tycheck::constraints::canonical_constraints_of(gcx, body.owner)
                .iter()
                .map(|constraint| constraint.value)
                .collect(),
        )
    };
    let return_local_ty = body.locals[body.return_local].ty;
    let function_output = if let Some(output) = concrete_output {
        output
    } else if body.is_async {
        gcx.function_body_output(body.owner)
    } else if gcx.definition_is_async(body.owner) {
        return_local_ty
    } else {
        gcx.get_signature(body.owner).output
    };
    let require_return_slot =
        crate::sema::tycheck::utils::normalize_aliases(gcx, function_output) != gcx.types.void;

    if !types_compatible(
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
            if matches!(stmt.kind, StatementKind::SetInitialized(local) if local == body.return_local)
            {
                return_slot_initialized = true;
            }
            if let StatementKind::Assign(destination, rvalue) = &stmt.kind {
                let dest_ty = body.place_ty(gcx, destination);
                if let Some(value_ty) = rvalue_ty(body, gcx, rvalue) {
                    if !types_compatible(&normalize_icx, &normalize_env, dest_ty, value_ty) {
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
                    let destination_ty = body.place_ty(gcx, destination);
                    let call_output = call_output_ty(body, gcx, func);

                    if let Some(call_output) = call_output {
                        if !types_compatible(
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
                    resume,
                    resume_arg,
                    cancel,
                    no_result,
                    unwind,
                    ..
                } => {
                    if let Some(failed) = no_result {
                        propagate_bool_state(
                            &mut block_states,
                            &mut worklist,
                            *failed,
                            return_slot_initialized,
                        );
                    }
                    let mut resume_state = return_slot_initialized;
                    if is_full_return_place(body, resume_arg) {
                        resume_state = true;
                    }
                    propagate_bool_state(&mut block_states, &mut worklist, *resume, resume_state);
                    propagate_bool_state(
                        &mut block_states,
                        &mut worklist,
                        *cancel,
                        return_slot_initialized,
                    );
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
                            if body.locals[body.return_local].kind == crate::mir::LocalKind::ConstructorSelf {
                                "constructor can complete with uninitialized fields".to_string()
                            } else {
                                "internal error: MIR reached `Return` without initializing the return slot".to_string()
                            },
                            Some(term.span),
                        );
                    }
                }
                _ => {
                    for succ in term.kind.successors() {
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
                TyKind::FnPointer {
                    output, effects, ..
                } => Some(
                    if effects.kind == crate::sema::models::ClosureKind::AsyncFn {
                        gcx.async_handle_ty()
                    } else {
                        normalize_if_possible(gcx, output)
                    },
                ),
                TyKind::Closure { kind, output, .. } => Some(
                    if matches!(kind, crate::sema::models::ClosureKind::AsyncFn) {
                        gcx.async_handle_ty()
                    } else {
                        normalize_if_possible(gcx, output)
                    },
                ),
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
            match body.place_ty(gcx, place).kind() {
                TyKind::FnPointer {
                    output, effects, ..
                } => Some(
                    if effects.kind == crate::sema::models::ClosureKind::AsyncFn {
                        gcx.async_handle_ty()
                    } else {
                        normalize_if_possible(gcx, output)
                    },
                ),
                TyKind::Closure { kind, output, .. } => Some(
                    if matches!(kind, crate::sema::models::ClosureKind::AsyncFn) {
                        gcx.async_handle_ty()
                    } else {
                        normalize_if_possible(gcx, output)
                    },
                ),
                _ => None,
            }
        }
    }
}

fn types_compatible<'ctx>(
    normalize_icx: &Rc<crate::sema::tycheck::infer::InferCtx<'ctx>>,
    normalize_env: &crate::sema::tycheck::utils::param_env::ParamEnv<'ctx>,
    expected: Ty<'ctx>,
    actual: Ty<'ctx>,
) -> bool {
    if expected.is_error() || actual.is_error() {
        return true;
    }

    let gcx = normalize_icx.gcx;
    let expected = crate::sema::tycheck::opaque::reveal_opaque_aliases(gcx, expected);
    let actual = crate::sema::tycheck::opaque::reveal_opaque_aliases(gcx, actual);
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
        || (normalize_env.has_type_equalities()
            && !actual.contains_inference()
            && !expected.contains_inference()
            && crate::sema::tycheck::utils::unify::TypeUnifier::with_env(
                normalize_icx.clone(),
                normalize_env,
            )
            .unify(actual, expected)
            .is_ok())
        || matches!(actual.kind(), TyKind::Never)
        || matches!(
            (expected.kind(), actual.kind()),
            (TyKind::Reference(inner_expected), TyKind::Reference(inner_actual))
                if types_compatible(normalize_icx, normalize_env, inner_expected, inner_actual)
        )
        || matches!(
            (expected.kind(), actual.kind()),
            (TyKind::Pointer(inner_expected, expected_mut), TyKind::Pointer(inner_actual, actual_mut))
                if expected_mut == actual_mut
                    && types_compatible(normalize_icx, normalize_env, inner_expected, inner_actual)
        )
        || matches!(
            (expected.kind(), actual.kind()),
            (TyKind::Reference(inner_expected), TyKind::Pointer(inner_actual, _))
                | (TyKind::Pointer(inner_expected, _), TyKind::Reference(inner_actual))
                if types_compatible(normalize_icx, normalize_env, inner_expected, inner_actual)
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
            ) if existential_interfaces_compatible(
                normalize_icx,
                normalize_env,
                expected_ifaces,
                actual_ifaces,
            )
        )
}

fn existential_interfaces_compatible<'ctx>(
    normalize_icx: &Rc<crate::sema::tycheck::infer::InferCtx<'ctx>>,
    normalize_env: &crate::sema::tycheck::utils::param_env::ParamEnv<'ctx>,
    expected: &'ctx [crate::sema::models::InterfaceReference<'ctx>],
    actual: &'ctx [crate::sema::models::InterfaceReference<'ctx>],
) -> bool {
    if expected.len() != actual.len() {
        return false;
    }

    let mut matched = vec![false; actual.len()];
    for expected_iface in expected {
        let Some((idx, _)) = actual.iter().enumerate().find(|(idx, actual_iface)| {
            !matched[*idx]
                && interface_refs_compatible(
                    normalize_icx,
                    normalize_env,
                    *expected_iface,
                    **actual_iface,
                )
        }) else {
            return false;
        };
        matched[idx] = true;
    }

    true
}

fn interface_refs_compatible<'ctx>(
    normalize_icx: &Rc<crate::sema::tycheck::infer::InferCtx<'ctx>>,
    normalize_env: &crate::sema::tycheck::utils::param_env::ParamEnv<'ctx>,
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

    if expected_args.len() != actual_args.len() || expected.bindings.len() != actual.bindings.len()
    {
        return false;
    }

    if !expected_args
        .iter()
        .zip(actual_args.iter())
        .all(|(expected_arg, actual_arg)| {
            generic_args_compatible(normalize_icx, normalize_env, *expected_arg, *actual_arg)
        })
    {
        return false;
    }

    expected.bindings.iter().all(|expected_binding| {
        actual
            .bindings
            .iter()
            .find(|actual_binding| actual_binding.name == expected_binding.name)
            .is_some_and(|actual_binding| {
                types_compatible(
                    normalize_icx,
                    normalize_env,
                    expected_binding.ty,
                    actual_binding.ty,
                )
            })
    })
}

fn generic_args_compatible<'ctx>(
    normalize_icx: &Rc<crate::sema::tycheck::infer::InferCtx<'ctx>>,
    normalize_env: &crate::sema::tycheck::utils::param_env::ParamEnv<'ctx>,
    expected: crate::sema::models::GenericArgument<'ctx>,
    actual: crate::sema::models::GenericArgument<'ctx>,
) -> bool {
    match (expected, actual) {
        (
            crate::sema::models::GenericArgument::Type(expected),
            crate::sema::models::GenericArgument::Type(actual),
        ) => types_compatible(normalize_icx, normalize_env, expected, actual),
        (
            crate::sema::models::GenericArgument::Const(expected),
            crate::sema::models::GenericArgument::Const(actual),
        ) => expected == actual,
        _ => false,
    }
}

fn rvalue_ty<'ctx>(body: &Body<'ctx>, gcx: Gcx<'ctx>, rvalue: &Rvalue<'ctx>) -> Option<Ty<'ctx>> {
    match rvalue {
        Rvalue::Alloc { ty } => Some(Ty::new(TyKind::Reference(*ty), gcx)),
        Rvalue::Use(operand) => Some(body.operand_ty(gcx, operand)),
        Rvalue::CopyValue { source } => Some(body.place_ty(gcx, source)),
        Rvalue::UnaryOp { op, operand } => Some(match op {
            UnaryOperator::LogicalNot => gcx.types.bool,
            UnaryOperator::Negate | UnaryOperator::BitwiseNot => body.operand_ty(gcx, operand),
        }),
        Rvalue::BinaryOp { op, lhs, .. } => Some(match op {
            crate::mir::BinaryOperator::Eql
            | crate::mir::BinaryOperator::Lt
            | crate::mir::BinaryOperator::Gt
            | crate::mir::BinaryOperator::Leq
            | crate::mir::BinaryOperator::Geq
            | crate::mir::BinaryOperator::Neq => gcx.types.bool,
            _ => body.operand_ty(gcx, lhs),
        }),
        Rvalue::Cast { ty, .. } => Some(*ty),
        Rvalue::CleanupAddress { place } => Some(Ty::new(
            TyKind::Pointer(body.place_ty(gcx, place), Mutability::Mutable),
            gcx,
        )),
        Rvalue::Ref { place } => Some(Ty::new(TyKind::Reference(body.place_ty(gcx, place)), gcx)),
        Rvalue::Discriminant { .. } => Some(gcx.types.uint),
        Rvalue::Zeroed { ty } => Some(*ty),
        Rvalue::Aggregate { kind, fields } => match kind {
            AggregateKind::Tuple => Some(Ty::new(
                TyKind::Tuple(
                    gcx.store.interners.intern_ty_list(
                        fields
                            .iter()
                            .map(|field| body.operand_ty(gcx, field))
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
    crate::mir::analysis::class_self::validate(gcx, body)?;
    crate::mir::analysis::class_lifecycle::validate(gcx, body)?;
    crate::mir::analysis::constructor::validate(gcx, body)?;
    let check_write = |place: &Place<'ctx>, span| {
        if !is_place_mutable(gcx, body, place)
            && crate::mir::analysis::constructor::readonly_field(gcx, body, place).is_none()
        {
            gcx.dcx()
                .emit_error("cannot assign to an immutable place".into(), Some(span));
        }
    };
    for block in &body.basic_blocks {
        for statement in &block.statements {
            match &statement.kind {
                StatementKind::Assign(destination, value) => {
                    // Generated construction writes fresh pointee storage,
                    // including fields that become readonly after initialization.
                    let initializing = matches!(value, Rvalue::Use(Operand::CopyWith(_, modifiers)) if modifiers.init);
                    if !initializing && !destination.projection.is_empty() {
                        check_write(destination, statement.span);
                    }
                }

                _ => {}
            }
        }
    }
    gcx.dcx().ok()
}

// ============================================================================
// Value capability checks
// ============================================================================

#[cfg(test)]
mod value_copy_tests {
    use crate::test_support::analyze_script_mir_diagnostics;

    #[test]
    fn reading_a_field_preserves_it_across_sibling_assignments() {
        for replacement in ["Token { id: 3 }", "makeToken()"] {
            let source = format!(
                "struct Token {{ id: int32 }}\nstruct Pair {{ left: Token; right: Token }}\nfunc consume(_ value: Token) {{}}\nfunc makeToken() -> Token {{ Token {{ id: 3 }} }}\nfunc main() {{\nvar pair = Pair {{ left: Token {{ id: 1 }}, right: Token {{ id: 2 }} }}\nleft := pair.left\npair.right = {replacement}\nconsume(pair.left)\nconsume(left)\n}}"
            );
            let diagnostics = analyze_script_mir_diagnostics(&source);
            assert!(diagnostics.is_empty(), "{diagnostics:?}");
        }
    }

    #[test]
    fn replacing_a_field_keeps_the_whole_value_initialized() {
        let diagnostics = analyze_script_mir_diagnostics(
            "struct Token { id: int32 }\nstruct Pair { left: Token; right: Token }\nfunc consume(_ value: Pair) {}\nfunc main() {\nvar pair = Pair { left: Token { id: 1 }, right: Token { id: 2 } }\nleft := pair.left\npair.left = Token { id: 3 }\nconsume(pair)\n}",
        );
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
    }
}
