use crate::{
    compile::context::Gcx,
    error::{CompileResult, ReportedError},
    hir::DefinitionID,
    mir::{
        BasicBlockData, BasicBlockId, Body, CallUnwindAction, Constant, ConstantKind,
        CopyModifiers, LocalDecl, LocalId, LocalKind, Operand, Place, PlaceElem, Rvalue,
        SourceScopeId, Statement, StatementKind, Terminator, TerminatorKind,
        analysis::liveness::compute_block_liveness,
    },
    sema::{
        models::{
            GenericArgument, GenericArguments, LabeledFunctionParameter, LabeledFunctionSignature,
            Ty, TyKind,
        },
        resolve::models::DefinitionKind,
        tycheck::utils::generics::GenericsBuilder,
    },
    span::Span,
    thir::FieldIndex,
};
use rustc_hash::FxHashSet;

use super::MirPass;

mod gc_frame;
mod tail_await;

/// Lowers async functions into:
/// 1. A public constructor body that allocates and initializes a frame, then
///    returns a compiler/runtime-private async handle.
/// 2. A synthetic poll thunk body that restores locals from the frame, runs the
///    original MIR until the next suspension point, then saves locals back into
///    the frame on pending.
pub struct AsyncTransform;

#[derive(Clone)]
struct YieldSite<'ctx> {
    block: BasicBlockId,
    future_place: Place<'ctx>,
    resume: BasicBlockId,
    resume_arg: Place<'ctx>,
    no_result: Option<BasicBlockId>,
    cancel: BasicBlockId,
    cancel_complete: BasicBlockId,
    unwind: CallUnwindAction,
    span: Span,
}

struct AsyncFrameLayout<'ctx> {
    ty: Ty<'ctx>,
    state_ty: Ty<'ctx>,
    stored_locals: Vec<LocalId>,
    resident_locals: Vec<LocalId>,
    /// Directly address-taken locals: a live reference may still read them.
    pinned_locals: FxHashSet<LocalId>,
    start_locals: Vec<LocalId>,
    /// Initialized by the constructor even when the body never starts.
    input_locals: Vec<LocalId>,
    /// Outside the suspended dispatch states; published before body execution.
    started_state: usize,
    yield_locals: Vec<Vec<LocalId>>,
}

struct PollThunkLocals<'ctx> {
    frame_raw: LocalId,
    _ctx_raw: LocalId,
    out_raw: LocalId,
    frame_ptr: LocalId,
    out_ptr: LocalId,
    state: LocalId,
    tag_return: LocalId,
    output_ty: Ty<'ctx>,
}

impl<'ctx> MirPass<'ctx> for AsyncTransform {
    fn name(&self) -> &'static str {
        "AsyncTransform"
    }

    fn run(&mut self, gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
        if !body.is_async {
            return Ok(());
        }
        if tail_await::forward_tail_await(gcx, body) {
            return Ok(());
        }

        let span = body_span(body);
        let poll_id = register_async_poll_definition(gcx, body.owner, span);
        let mut poll_body = body.clone();
        poll_body.owner = poll_id;
        // Source scope zero describes the physical function whose frame is
        // being emitted. The remaining scopes deliberately keep the original
        // async function as their logical owner for diagnostics and debug
        // inlining information.
        poll_body.source_scopes[SourceScopeId::from_raw(0)].definition = poll_id;
        let frame = lower_async_poll_body(gcx, &mut poll_body)?;

        let (drop_id, drop_body) = build_async_drop_body(gcx, body.owner, &frame, &poll_body)?;
        let constructor = build_async_constructor(gcx, body, poll_id, drop_id, &frame)?;

        gcx.queue_synthetic_mir_body(poll_id, poll_body);
        gcx.queue_synthetic_mir_body(drop_id, drop_body);
        *body = constructor;
        Ok(())
    }
}

fn register_async_poll_definition<'ctx>(
    gcx: Gcx<'ctx>,
    owner: DefinitionID,
    span: Span,
) -> DefinitionID {
    let poll_id = gcx.allocate_synthetic_id(owner.package());
    let ptr_u8_mut = raw_ptr_ty(gcx, gcx.types.uint8, crate::hir::Mutability::Mutable);
    let signature = LabeledFunctionSignature {
        inputs: vec![
            LabeledFunctionParameter {
                name: gcx.intern_symbol("frame"),
                ty: ptr_u8_mut,
                label: None,
                is_lazy: false,
                default_provider: None,
            },
            LabeledFunctionParameter {
                name: gcx.intern_symbol("ctx"),
                ty: ptr_u8_mut,
                label: None,
                is_lazy: false,
                default_provider: None,
            },
            LabeledFunctionParameter {
                name: gcx.intern_symbol("out"),
                ty: ptr_u8_mut,
                label: None,
                is_lazy: false,
                default_provider: None,
            },
        ],
        output: gcx.types.uint8,
        is_variadic: false,
        abi: None,
    };
    let signature = gcx
        .store
        .arenas
        .function_signatures
        .alloc(signature.clone());
    let owner_name = gcx.definition_symbol_or_fallback(owner);
    let def = crate::sema::models::SyntheticDefinition {
        kind: crate::sema::models::SyntheticDefinitionKind::AsyncPoll,
        name: gcx.intern_symbol(&format!("{}$poll", gcx.symbol_text(owner_name))),
        generics: gcx.generics_of(owner),
        signature,
        span,
    };
    gcx.register_synthetic_definition(poll_id, def);
    gcx.cache_type(poll_id, Ty::from_labeled_signature(gcx, &signature));
    poll_id
}

/// The callback tag conveys only a wire ABI. Validate imported headers before
/// publication; it must never stand in for native/body/storage proofs.
pub(crate) fn validate_poll_declaration<'ctx>(
    gcx: Gcx<'ctx>,
    definition: &crate::sema::models::SyntheticDefinition<'ctx>,
) -> Result<(), String> {
    if definition.kind != crate::sema::models::SyntheticDefinitionKind::AsyncPoll {
        return Ok(());
    }
    let signature = definition.signature;
    let pointer = raw_ptr_ty(gcx, gcx.types.uint8, crate::hir::Mutability::Mutable);
    if signature.abi.is_some()
        || signature.is_variadic
        || signature.output != gcx.types.uint8
        || signature.inputs.len() != 3
        || signature.inputs.iter().any(|input| input.ty != pointer)
    {
        return Err("async poll callback metadata has an invalid C wire signature".into());
    }
    Ok(())
}

fn lower_async_poll_body<'ctx>(
    gcx: Gcx<'ctx>,
    body: &mut Body<'ctx>,
) -> CompileResult<AsyncFrameLayout<'ctx>> {
    body.is_async = false;

    let original_return_local = body.return_local;
    let output_ty = body.locals[original_return_local].ty;
    body.locals[original_return_local].kind = LocalKind::Temp;
    body.locals[original_return_local].mutable = true;

    let original_params: Vec<_> = body
        .locals
        .iter_enumerated()
        .filter_map(|(local, decl)| matches!(decl.kind, LocalKind::Param).then_some(local))
        .collect();
    for local in &original_params {
        body.locals[*local].kind = LocalKind::Temp;
        body.locals[*local].mutable = true;
    }

    let mut yields = materialize_await_futures(gcx, body);
    let mut frame = build_frame_layout(gcx, body, &yields);
    frame.input_locals = original_params
        .into_iter()
        .filter(|local| frame.stored_locals.contains(local))
        .collect();
    let original_locals = body.locals.len();
    let locals = add_poll_thunk_locals(gcx, body, frame.ty, output_ty);
    rewrite_resident_local_places(body, &frame, locals.frame_ptr, &mut yields);

    rewrite_returns(gcx, body, original_return_local, &frame, &locals)?;
    rewrite_yields(gcx, body, &yields, &frame, &locals)?;
    install_dispatch(gcx, body, &yields, &frame, &locals)?;
    verify_frame_reference_storage(body, original_locals).map_err(|(local, span)| {
        gcx.dcx().emit_error(
            format!(
                "internal error: async borrow still refers to movable poll-stack storage {local:?}"
            ),
            Some(span),
        );
        ReportedError
    })?;

    Ok(frame)
}

fn materialize_await_futures<'ctx>(gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> Vec<YieldSite<'ctx>> {
    let yield_blocks: Vec<_> = body
        .basic_blocks
        .indices()
        .filter(|&bb_id| {
            body.basic_blocks[bb_id]
                .terminator
                .as_ref()
                .is_some_and(|term| matches!(term.kind, TerminatorKind::Yield { .. }))
        })
        .collect();

    let mut sites = Vec::with_capacity(yield_blocks.len());
    for bb_id in yield_blocks {
        let terminator = body.basic_blocks[bb_id]
            .terminator
            .as_ref()
            .cloned()
            .expect("ICE: block in yield set has no terminator");
        let TerminatorKind::Yield {
            value,
            resume,
            resume_arg,
            no_result,
            cancel,
            cancel_complete,
            unwind,
        } = terminator.kind
        else {
            unreachable!();
        };

        let future_place = if let Some(place) = value.place() {
            place.clone()
        } else {
            let future_ty = body.operand_ty(gcx, &value);
            let temp = push_local(
                body,
                future_ty,
                LocalKind::Temp,
                true,
                Some(gcx.intern_symbol("$await_future")),
                terminator.span,
            );
            body.basic_blocks[bb_id].statements.push(Statement {
                kind: StatementKind::Assign(Place::from_local(temp), Rvalue::Use(value)),
                span: terminator.span,
            });
            Place::from_local(temp)
        };
        sites.push(YieldSite {
            block: bb_id,
            future_place,
            resume,
            resume_arg,
            no_result,
            cancel,
            cancel_complete,
            unwind,
            span: terminator.span,
        });
    }

    sites
}

fn build_frame_layout<'ctx>(
    gcx: Gcx<'ctx>,
    body: &Body<'ctx>,
    yields: &[YieldSite<'ctx>],
) -> AsyncFrameLayout<'ctx> {
    let state_ty = gcx.types.uint;
    // A reference can be the only future use of its owner's storage. Ordinary
    // local liveness cannot see that dependency through an aggregate/view.
    // Reserve a stable field for every directly address-taken local, including
    // NoCopy values, rather than moving it through transient poll-stack slots.
    let mut pinned = FxHashSet::default();
    for block in &body.basic_blocks {
        for statement in &block.statements {
            if let StatementKind::Assign(
                _,
                Rvalue::Ref { place, .. } | Rvalue::CleanupAddress { place },
            ) = &statement.kind
            {
                if !place.projection.contains(&PlaceElem::Deref) {
                    pinned.insert(place.local);
                }
            }
        }
    }
    let liveness = compute_block_liveness(body);
    let start_locals = collect_async_state_locals(body, &liveness.live_in[body.start_block], None);
    let yield_locals: Vec<_> = yields
        .iter()
        .map(|site| {
            collect_async_state_locals(
                body,
                &liveness.live_in[site.block],
                Some(site.future_place.local),
            )
        })
        .collect();
    let stored_locals: Vec<_> = body
        .locals
        .indices()
        .filter(|&local| {
            start_locals.contains(&local)
                || yield_locals.iter().any(|locals| locals.contains(&local))
                || pinned.contains(&local)
        })
        .collect();
    // References must keep pointing into stable GC frame storage across
    // suspension and cleanup, rather than temporary resumed poll-stack slots.
    let resident_locals = stored_locals.clone();
    let mut fields = Vec::with_capacity(stored_locals.len() + 1);
    fields.push(state_ty);
    fields.extend(stored_locals.iter().map(|local| body.locals[*local].ty));
    let frame_ty = Ty::new(
        TyKind::Tuple(gcx.store.interners.intern_ty_list(fields)),
        gcx,
    );
    AsyncFrameLayout {
        ty: frame_ty,
        state_ty,
        stored_locals,
        resident_locals,
        pinned_locals: pinned,
        start_locals,
        input_locals: vec![],
        started_state: yields.len() + 1,
        yield_locals,
    }
}

fn collect_async_state_locals(
    body: &Body<'_>,
    live_locals: &FxHashSet<LocalId>,
    extra_local: Option<LocalId>,
) -> Vec<LocalId> {
    body.locals
        .indices()
        .filter(|&local| live_locals.contains(&local) || extra_local == Some(local))
        .collect()
}

/// Saved values stay at their final frame addresses throughout the future.
fn rewrite_resident_local_places<'ctx>(
    body: &mut Body<'ctx>,
    frame: &AsyncFrameLayout<'ctx>,
    frame_ptr_local: LocalId,
    yields: &mut [YieldSite<'ctx>],
) {
    let remaps: Vec<Option<Place<'ctx>>> = body
        .locals
        .indices()
        .map(|local| {
            frame
                .resident_locals
                .contains(&local)
                .then(|| frame_local_place(body, frame, frame_ptr_local, local))
        })
        .collect();

    for block in body.basic_blocks.iter_mut() {
        for statement in &mut block.statements {
            match &mut statement.kind {
                StatementKind::SourceScope(_)
                | StatementKind::StorageLive(_)
                | StatementKind::StorageDead(_)
                | StatementKind::SetInitialized(_) => {}

                StatementKind::Assign(destination, rvalue) => {
                    remap_resident_place(destination, &remaps);
                    rvalue.for_each_place_mut(|place| remap_resident_place(place, &remaps));
                }
                StatementKind::SetDiscriminant { place, .. } => {
                    remap_resident_place(place, &remaps);
                }
                StatementKind::KeepAlive(operand) => remap_resident_operand(operand, &remaps),
                StatementKind::GcSafepoint(_) | StatementKind::Nop => {}
            }
        }
        let Some(terminator) = &mut block.terminator else {
            continue;
        };
        match &mut terminator.kind {
            TerminatorKind::SwitchInt { discr, .. } => {
                remap_resident_operand(discr, &remaps);
            }
            TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } => {
                remap_resident_operand(func, &remaps);
                for argument in args {
                    remap_resident_operand(argument, &remaps);
                }
                remap_resident_place(destination, &remaps);
            }
            TerminatorKind::Yield {
                value, resume_arg, ..
            } => {
                remap_resident_operand(value, &remaps);
                remap_resident_place(resume_arg, &remaps);
            }
            TerminatorKind::GeneratorYield { value, .. } => {
                remap_resident_operand(value, &remaps);
            }
            TerminatorKind::Goto { .. }
            | TerminatorKind::UnresolvedGoto
            | TerminatorKind::Return
            | TerminatorKind::ResumeUnwind
            | TerminatorKind::Unreachable => {}
        }
    }

    for site in yields {
        remap_resident_place(&mut site.future_place, &remaps);
        remap_resident_place(&mut site.resume_arg, &remaps);
    }
}

fn remap_resident_place<'ctx>(place: &mut Place<'ctx>, remaps: &[Option<Place<'ctx>>]) {
    let Some(base) = remaps[place.local.index()].as_ref() else {
        return;
    };
    let mut projection = base.projection.clone();
    projection.extend(place.projection.iter().copied());
    place.local = base.local;
    place.projection = projection;
}

fn remap_resident_operand<'ctx>(operand: &mut Operand<'ctx>, remaps: &[Option<Place<'ctx>>]) {
    match operand {
        Operand::Copy(place) | Operand::CopyWith(place, _) => {
            remap_resident_place(place, remaps);
        }
        Operand::Constant(_) => {}
    }
}

/// Every source address-taken owner is assigned final frame storage before
/// executing the body. A missed rewrite must fail in the compiler, rather than
/// letting a suspended child retain an address into an obsolete poll stack.
fn verify_frame_reference_storage(
    body: &Body<'_>,
    original_locals: usize,
) -> Result<(), (LocalId, Span)> {
    for block in &body.basic_blocks {
        for statement in &block.statements {
            let StatementKind::Assign(_, value) = &statement.kind else {
                continue;
            };
            let place = match value {
                Rvalue::Ref { place, .. } | Rvalue::CleanupAddress { place } => place,
                _ => continue,
            };
            if place.local.index() < original_locals
                && !place.projection.contains(&PlaceElem::Deref)
            {
                return Err((place.local, statement.span));
            }
        }
    }
    Ok(())
}

fn add_poll_thunk_locals<'ctx>(
    gcx: Gcx<'ctx>,
    body: &mut Body<'ctx>,
    frame_ty: Ty<'ctx>,
    output_ty: Ty<'ctx>,
) -> PollThunkLocals<'ctx> {
    let span = body_span(body);
    let frame_raw = push_local(
        body,
        raw_ptr_ty(gcx, gcx.types.uint8, crate::hir::Mutability::Mutable),
        LocalKind::Param,
        false,
        Some(gcx.intern_symbol("$frame")),
        span,
    );
    let ctx_raw = push_local(
        body,
        raw_ptr_ty(gcx, gcx.types.uint8, crate::hir::Mutability::Mutable),
        LocalKind::Param,
        false,
        Some(gcx.intern_symbol("$ctx")),
        span,
    );
    let out_raw = push_local(
        body,
        raw_ptr_ty(gcx, gcx.types.uint8, crate::hir::Mutability::Mutable),
        LocalKind::Param,
        false,
        Some(gcx.intern_symbol("$out")),
        span,
    );
    let tag_return = push_local(
        body,
        gcx.types.uint8,
        LocalKind::Return,
        true,
        Some(gcx.intern_symbol("$poll_tag")),
        span,
    );
    let frame_ptr = push_local(
        body,
        raw_ptr_ty(gcx, frame_ty, crate::hir::Mutability::Mutable),
        LocalKind::Temp,
        true,
        Some(gcx.intern_symbol("$frame_ptr")),
        span,
    );
    let out_ptr = push_local(
        body,
        raw_ptr_ty(gcx, output_ty, crate::hir::Mutability::Mutable),
        LocalKind::Temp,
        true,
        Some(gcx.intern_symbol("$out_ptr")),
        span,
    );
    let state = push_local(
        body,
        gcx.types.uint,
        LocalKind::Temp,
        true,
        Some(gcx.intern_symbol("$state")),
        span,
    );
    body.return_local = tag_return;

    PollThunkLocals {
        frame_raw,
        _ctx_raw: ctx_raw,
        out_raw,
        frame_ptr,
        out_ptr,
        state,
        tag_return,
        output_ty,
    }
}

fn rewrite_returns<'ctx>(
    gcx: Gcx<'ctx>,
    body: &mut Body<'ctx>,
    original_return_local: LocalId,
    frame: &AsyncFrameLayout<'ctx>,
    locals: &PollThunkLocals<'ctx>,
) -> CompileResult<()> {
    let return_blocks: Vec<_> = body
        .basic_blocks
        .indices()
        .filter(|&bb_id| {
            body.basic_blocks[bb_id]
                .terminator
                .as_ref()
                .is_some_and(|term| matches!(term.kind, TerminatorKind::Return))
        })
        .collect();

    for bb_id in return_blocks {
        let span = body.basic_blocks[bb_id]
            .terminator
            .as_ref()
            .expect("ICE: block in return set has no terminator")
            .span;
        let return_place = poll_local_place(body, frame, locals.frame_ptr, original_return_local);
        let output_block = bb_id;
        body.basic_blocks[output_block].statements.push(Statement {
            kind: StatementKind::Assign(
                Place {
                    local: locals.out_ptr,
                    projection: vec![PlaceElem::Deref],
                },
                Rvalue::Use(Operand::CopyWith(
                    return_place,
                    CopyModifiers { init: true },
                )),
            ),
            span,
        });
        body.basic_blocks[output_block].statements.push(Statement {
            kind: StatementKind::Assign(
                Place::from_local(locals.tag_return),
                Rvalue::Use(const_uint8_operand(gcx, 1)),
            ),
            span,
        });
    }
    Ok(())
}

fn rewrite_yields<'ctx>(
    gcx: Gcx<'ctx>,
    body: &mut Body<'ctx>,
    yields: &[YieldSite<'ctx>],
    frame: &AsyncFrameLayout<'ctx>,
    locals: &PollThunkLocals<'ctx>,
) -> CompileResult<()> {
    let span = body_span(body);
    let async_poll_id = find_or_register_async_runtime_function(gcx, AsyncRuntimeFn::Poll, span);
    let async_poll_ty = gcx.get_type(async_poll_id);
    let async_destroy_id =
        find_or_register_async_runtime_function(gcx, AsyncRuntimeFn::Destroy, span);
    let async_destroy_ty = gcx.get_type(async_destroy_id);
    let async_cancel_id =
        find_or_register_async_runtime_function(gcx, AsyncRuntimeFn::CancelPoll, span);
    let async_cancel_ty = gcx.get_type(async_cancel_id);
    let is_cancelled_id =
        find_or_register_async_runtime_function(gcx, AsyncRuntimeFn::IsTaskCancelled, span);
    let is_cancelled_ty = gcx.get_type(is_cancelled_id);
    for (index, site) in yields.iter().enumerate() {
        let ready_ty = body.place_ty(gcx, &site.resume_arg);
        let ready_is_never = matches!(ready_ty.kind(), TyKind::Never);
        let ready_storage_ty = if ready_ty == gcx.types.void || ready_is_never {
            gcx.types.uint8
        } else {
            ready_ty
        };
        let handle_local = push_local(
            body,
            gcx.async_handle_ty(),
            LocalKind::Temp,
            true,
            Some(gcx.intern_symbol("$await_handle")),
            site.span,
        );
        let ready_storage_local = push_local(
            body,
            ready_storage_ty,
            LocalKind::Temp,
            true,
            Some(gcx.intern_symbol("$await_ready")),
            site.span,
        );
        let ready_ref_local = push_local(
            body,
            gcx.store
                .interners
                .intern_ty(TyKind::Reference(ready_storage_ty)),
            LocalKind::Temp,
            true,
            Some(gcx.intern_symbol("$await_ready_ref")),
            site.span,
        );
        let ready_ptr_local = push_local(
            body,
            raw_ptr_ty(gcx, ready_storage_ty, crate::hir::Mutability::Mutable),
            LocalKind::Temp,
            true,
            Some(gcx.intern_symbol("$await_ready_ptr")),
            site.span,
        );
        let ready_raw_local = push_local(
            body,
            raw_ptr_ty(gcx, gcx.types.uint8, crate::hir::Mutability::Mutable),
            LocalKind::Temp,
            true,
            Some(gcx.intern_symbol("$await_ready_raw")),
            site.span,
        );
        let tag_local = push_local(
            body,
            gcx.types.uint8,
            LocalKind::Temp,
            true,
            Some(gcx.intern_symbol("$await_tag")),
            site.span,
        );
        let cancelled_local = push_local(
            body,
            gcx.types.bool,
            LocalKind::Temp,
            true,
            Some(gcx.intern_symbol("$await_cancelled")),
            site.span,
        );

        // The MIR builder leaves a unique unreachable marker at the end of
        // each ordinary cancellation cleanup path. Turn that marker into the
        // poll ABI's distinct cancelled completion tag after normal returns
        // have already been rewritten.
        body.basic_blocks[site.cancel_complete]
            .statements
            .push(Statement {
                kind: StatementKind::Assign(
                    Place::from_local(locals.tag_return),
                    Rvalue::Use(const_uint8_operand(gcx, 2)),
                ),
                span: site.span,
            });
        body.basic_blocks[site.cancel_complete].terminator = Some(Terminator {
            kind: TerminatorKind::Return,
            span: site.span,
        });

        let mut poll_statements = Vec::with_capacity(4);
        poll_statements.push(Statement {
            kind: StatementKind::Assign(
                Place::from_local(handle_local),
                Rvalue::Use(Operand::Copy(site.future_place.clone())),
            ),
            span: site.span,
        });
        poll_statements.push(Statement {
            kind: StatementKind::Assign(
                Place::from_local(ready_ref_local),
                Rvalue::Ref {
                    place: Place::from_local(ready_storage_local),
                },
            ),
            span: site.span,
        });
        poll_statements.push(Statement {
            kind: StatementKind::Assign(
                Place::from_local(ready_ptr_local),
                Rvalue::Cast {
                    operand: Operand::Copy(Place::from_local(ready_ref_local)),
                    ty: raw_ptr_ty(gcx, ready_storage_ty, crate::hir::Mutability::Mutable),
                    kind: crate::mir::CastKind::Pointer,
                },
            ),
            span: site.span,
        });
        poll_statements.push(Statement {
            kind: StatementKind::Assign(
                Place::from_local(ready_raw_local),
                Rvalue::Cast {
                    operand: Operand::Copy(Place::from_local(ready_ptr_local)),
                    ty: raw_ptr_ty(gcx, gcx.types.uint8, crate::hir::Mutability::Mutable),
                    kind: crate::mir::CastKind::Pointer,
                },
            ),
            span: site.span,
        });
        let poll_block = body.basic_blocks.push(BasicBlockData {
            note: Some(format!("await-poll-{}", index)),
            statements: poll_statements,
            terminator: None,
        });
        let poll_handle_block = body.basic_blocks.push(BasicBlockData {
            note: Some(format!("await-handle-poll-{}", index)),
            statements: vec![],
            terminator: None,
        });
        let check_block = body.basic_blocks.push(BasicBlockData {
            note: Some(format!("await-check-{}", index)),
            statements: vec![],
            terminator: None,
        });
        let pending_store_block = body.basic_blocks.push(BasicBlockData {
            note: Some(format!("await-pending-store-{}", index)),
            statements: pending_save_statements(
                gcx,
                frame,
                &frame.yield_locals[index],
                locals.frame_ptr,
                locals.tag_return,
                index + 1,
                site.span,
            )
            .into_iter()
            .chain(clear_dead_frame_fields(
                frame,
                &frame.yield_locals[index],
                locals.frame_ptr,
                site.span,
            ))
            .collect(),
            terminator: Some(Terminator {
                kind: TerminatorKind::Return,
                span: site.span,
            }),
        });
        let destroy_void_local = push_local(
            body,
            gcx.types.void,
            LocalKind::Temp,
            true,
            Some(gcx.intern_symbol("$await_destroy_void")),
            site.span,
        );
        let cancel_switch_block = body.basic_blocks.push(BasicBlockData {
            note: Some(format!("await-cancel-check-{}", index)),
            statements: vec![],
            terminator: None,
        });
        let cancel_progress_block = body.basic_blocks.push(BasicBlockData {
            note: Some(format!("await-cancel-progress-{}", index)),
            statements: vec![],
            terminator: Some(Terminator {
                kind: TerminatorKind::SwitchInt {
                    discr: Operand::Copy(Place::from_local(tag_local)),
                    targets: vec![(0, pending_store_block)],
                    otherwise: site.cancel,
                },
                span: site.span,
            }),
        });
        let cancel_destroy_block = body.basic_blocks.push(BasicBlockData {
            note: Some(format!("await-cancel-destroy-{}", index)),
            statements: vec![],
            terminator: Some(Terminator {
                kind: TerminatorKind::Call {
                    func: fn_operand(async_cancel_id, GenericArguments::empty(), async_cancel_ty),
                    args: vec![Operand::Copy(Place::from_local(handle_local))],
                    destination: Place::from_local(tag_local),
                    target: cancel_progress_block,
                    unwind: site.unwind,
                },
                span: site.span,
            }),
        });
        let ready_target = body.basic_blocks.push(BasicBlockData {
            note: Some(format!("await-destroy-{}", index)),
            statements: vec![],
            terminator: Some(Terminator {
                kind: TerminatorKind::Call {
                    func: fn_operand(
                        async_destroy_id,
                        GenericArguments::empty(),
                        async_destroy_ty,
                    ),
                    args: vec![Operand::Copy(Place::from_local(handle_local))],
                    destination: Place::from_local(destroy_void_local),
                    target: site.resume,
                    unwind: site.unwind,
                },
                span: site.span,
            }),
        });

        let mut ready_statements = Vec::new();
        if ready_ty == gcx.types.void {
            ready_statements.push(Statement {
                kind: StatementKind::Assign(
                    site.resume_arg.clone(),
                    Rvalue::Use(Operand::Constant(Constant {
                        ty: gcx.types.void,
                        value: ConstantKind::Unit,
                    })),
                ),
                span: site.span,
            });
        } else if !ready_is_never {
            ready_statements.push(Statement {
                kind: StatementKind::Assign(
                    site.resume_arg.clone(),
                    Rvalue::Use(Operand::CopyWith(
                        Place::from_local(ready_storage_local),
                        CopyModifiers { init: true },
                    )),
                ),
                span: site.span,
            });
        }

        let ready_block = body.basic_blocks.push(BasicBlockData {
            note: Some(format!("await-ready-{}", index)),
            statements: ready_statements,
            terminator: Some(Terminator {
                kind: TerminatorKind::Goto {
                    target: ready_target,
                },
                span: site.span,
            }),
        });

        let no_result_target = body.basic_blocks.push(BasicBlockData {
            note: Some(format!("await-without-result-{}", index)),
            statements: vec![],
            terminator: Some(Terminator {
                kind: if let Some(target) = site.no_result {
                    TerminatorKind::Call {
                        func: fn_operand(
                            async_destroy_id,
                            GenericArguments::empty(),
                            async_destroy_ty,
                        ),
                        args: vec![Operand::Copy(Place::from_local(handle_local))],
                        destination: Place::from_local(destroy_void_local),
                        target,
                        unwind: site.unwind,
                    }
                } else {
                    TerminatorKind::Unreachable
                },
                span: site.span,
            }),
        });

        // Cancellation can arrive on another worker after the check above.
        // A child that then observes it before starting reports cancelled (2)
        // without a result; take this frame's cancellation path, where
        // cancel_poll consumes the terminal child.
        body.basic_blocks[check_block].terminator = Some(Terminator {
            kind: TerminatorKind::SwitchInt {
                discr: Operand::Copy(Place::from_local(tag_local)),
                targets: vec![
                    (0u128, pending_store_block),
                    (2, cancel_destroy_block),
                    (3, no_result_target),
                ],
                otherwise: ready_block,
            },
            span: site.span,
        });

        body.basic_blocks[poll_handle_block].terminator = Some(Terminator {
            kind: TerminatorKind::Call {
                func: fn_operand(async_poll_id, GenericArguments::empty(), async_poll_ty),
                args: vec![
                    Operand::Copy(Place::from_local(handle_local)),
                    Operand::Copy(Place::from_local(ready_raw_local)),
                ],
                destination: Place::from_local(tag_local),
                target: check_block,
                unwind: site.unwind,
            },
            span: site.span,
        });
        body.basic_blocks[cancel_switch_block].terminator = Some(Terminator {
            kind: TerminatorKind::SwitchInt {
                discr: Operand::Copy(Place::from_local(cancelled_local)),
                targets: vec![(0, poll_handle_block)],
                otherwise: cancel_destroy_block,
            },
            span: site.span,
        });
        body.basic_blocks[poll_block].terminator = Some(Terminator {
            kind: TerminatorKind::Call {
                func: fn_operand(is_cancelled_id, GenericArguments::empty(), is_cancelled_ty),
                args: vec![],
                destination: Place::from_local(cancelled_local),
                target: cancel_switch_block,
                unwind: site.unwind,
            },
            span: site.span,
        });
        body.basic_blocks[site.block].terminator = Some(Terminator {
            kind: TerminatorKind::Goto { target: poll_block },
            span: site.span,
        });
    }
    Ok(())
}

fn install_dispatch<'ctx>(
    gcx: Gcx<'ctx>,
    body: &mut Body<'ctx>,
    yields: &[YieldSite<'ctx>],
    frame: &AsyncFrameLayout<'ctx>,
    locals: &PollThunkLocals<'ctx>,
) -> CompileResult<()> {
    let span = body_span(body);
    let original_start = body.start_block;

    // Entry block: compute sizeOf[FrameTy], then dispatch.
    let dispatch = body.basic_blocks.push(BasicBlockData {
        note: Some("async-dispatch".into()),
        statements: vec![
            Statement {
                kind: StatementKind::Assign(
                    Place::from_local(locals.frame_ptr),
                    Rvalue::Cast {
                        operand: Operand::Copy(Place::from_local(locals.frame_raw)),
                        ty: raw_ptr_ty(gcx, frame.ty, crate::hir::Mutability::Mutable),
                        kind: crate::mir::CastKind::Pointer,
                    },
                ),
                span,
            },
            Statement {
                kind: StatementKind::Assign(
                    Place::from_local(locals.out_ptr),
                    Rvalue::Cast {
                        operand: Operand::Copy(Place::from_local(locals.out_raw)),
                        ty: raw_ptr_ty(gcx, locals.output_ty, crate::hir::Mutability::Mutable),
                        kind: crate::mir::CastKind::Pointer,
                    },
                ),
                span,
            },
            Statement {
                kind: StatementKind::Assign(
                    Place::from_local(locals.state),
                    Rvalue::Use(Operand::Copy(frame_state_place(
                        locals.frame_ptr,
                        frame.state_ty,
                    ))),
                ),
                span,
            },
        ],
        terminator: None,
    });

    let start_restore = restore_block(
        body,
        frame,
        &frame.start_locals,
        locals.frame_ptr,
        original_start,
        span,
    );
    let mut targets = vec![(0u128, start_restore)];
    for (index, site) in yields.iter().enumerate() {
        let restore = restore_block(
            body,
            frame,
            &frame.yield_locals[index],
            locals.frame_ptr,
            site.block,
            site.span,
        );
        targets.push(((index + 1) as u128, restore));
    }
    let invalid_state = body.basic_blocks.push(BasicBlockData {
        note: Some("async-invalid-state".into()),
        statements: vec![],
        terminator: Some(Terminator {
            kind: TerminatorKind::Unreachable,
            span,
        }),
    });
    body.basic_blocks[dispatch].terminator = Some(Terminator {
        kind: TerminatorKind::SwitchInt {
            discr: Operand::Copy(Place::from_local(locals.state)),
            targets,
            otherwise: invalid_state,
        },
        span,
    });
    body.start_block = dispatch;
    Ok(())
}

/// Restore non-resident locals from the frame. Resident locals continue to be
/// addressed through their stable frame fields.
fn restore_block<'ctx>(
    body: &mut Body<'ctx>,
    frame: &AsyncFrameLayout<'ctx>,
    locals_to_restore: &[LocalId],
    frame_ptr_local: LocalId,
    target: BasicBlockId,
    span: Span,
) -> BasicBlockId {
    let mut statements: Vec<_> = locals_to_restore
        .iter()
        .filter(|local| !frame.resident_locals.contains(local))
        .map(|local| Statement {
            // Take ownership out of the field and clear that field. Resident
            // fields are never transferred to poll-stack locals.
            kind: StatementKind::Assign(
                Place::from_local(*local),
                Rvalue::Use(Operand::CopyWith(
                    frame_local_place(body, frame, frame_ptr_local, *local),
                    CopyModifiers { init: true },
                )),
            ),
            span,
        })
        .collect();

    // Retire both initial and suspended admission before any continuation can
    // unwind. If cleanup then panics, destruction must not reenter this state.
    // A real Pending return republishes its suspension tag in the save path.
    statements.insert(
        0,
        Statement {
            span,
            kind: StatementKind::Assign(
                frame_state_place(frame_ptr_local, frame.state_ty),
                Rvalue::Use(Operand::Constant(Constant {
                    ty: frame.state_ty,
                    value: ConstantKind::Integer(frame.started_state as u64),
                })),
            ),
        },
    );

    let restore = body.basic_blocks.push(BasicBlockData {
        note: Some("async-restore".into()),
        statements,
        terminator: Some(Terminator {
            kind: TerminatorKind::Goto { target },
            span,
        }),
    });
    restore
}

fn pending_save_statements<'ctx>(
    gcx: Gcx<'ctx>,
    frame: &AsyncFrameLayout<'ctx>,
    locals_to_save: &[LocalId],
    frame_ptr_local: LocalId,
    tag_return_local: LocalId,
    state: usize,
    span: Span,
) -> Vec<Statement<'ctx>> {
    let mut statements = Vec::with_capacity(locals_to_save.len() + 2);
    for local in locals_to_save
        .iter()
        .filter(|local| !frame.resident_locals.contains(local))
    {
        // Use take semantics: the codegen will zero the source local after copying
        // so the moved value only remains in the frame.
        statements.push(Statement {
            kind: StatementKind::Assign(
                frame_local_place_stub(frame, frame_ptr_local, *local),
                Rvalue::Use(Operand::CopyWith(
                    Place::from_local(*local),
                    CopyModifiers { init: true },
                )),
            ),
            span,
        });
    }
    statements.push(Statement {
        kind: StatementKind::Assign(
            frame_state_place(frame_ptr_local, frame.state_ty),
            Rvalue::Use(const_uint_operand(gcx, frame.state_ty, state as u64)),
        ),
        span,
    });
    statements.push(Statement {
        kind: StatementKind::Assign(
            Place::from_local(tag_return_local),
            Rvalue::Use(const_uint8_operand(gcx, 0)),
        ),
        span,
    });
    statements
}

/// Zeroes frame fields whose locals are dead while suspended at this await,
/// so a suspended frame traces only the values its resumption can read. A
/// zeroed field is the same state as a never-initialized one, which tracing
/// already accepts for every type; nothing reads it before reassignment.
fn clear_dead_frame_fields<'ctx>(
    frame: &AsyncFrameLayout<'ctx>,
    live_locals: &[LocalId],
    frame_ptr_local: LocalId,
    span: Span,
) -> Vec<Statement<'ctx>> {
    frame
        .resident_locals
        .iter()
        .filter(|local| !live_locals.contains(local) && !frame.pinned_locals.contains(local))
        .filter_map(|&local| {
            let ty = frame_local_ty(frame, local);
            let scalar = matches!(
                ty.kind(),
                TyKind::Bool | TyKind::Rune | TyKind::Int(_) | TyKind::UInt(_) | TyKind::Float(_)
            ) || matches!(ty.kind(), TyKind::Tuple(items) if items.is_empty());
            (!scalar).then(|| Statement {
                kind: StatementKind::Assign(
                    frame_local_place_stub(frame, frame_ptr_local, local),
                    Rvalue::Zeroed { ty },
                ),
                span,
            })
        })
        .collect()
}

fn build_async_constructor<'ctx>(
    gcx: Gcx<'ctx>,
    original: &Body<'ctx>,
    poll_id: DefinitionID,
    drop_id: DefinitionID,
    frame: &AsyncFrameLayout<'ctx>,
) -> CompileResult<Body<'ctx>> {
    let span = body_span(original);
    let async_return_ty = gcx.async_handle_ty();
    let frame_ptr_mut_ty = raw_ptr_ty(gcx, frame.ty, crate::hir::Mutability::Mutable);
    let ptr_u8_mut = raw_ptr_ty(gcx, gcx.types.uint8, crate::hir::Mutability::Mutable);
    let ptr_u8_const = raw_ptr_ty(gcx, gcx.types.uint8, crate::hir::Mutability::Immutable);

    let mut body = Body {
        escape_locals: Vec::new(),

        owner: original.owner,
        source_scopes: Body::initial_source_scopes(original.owner),
        locals: Default::default(),
        basic_blocks: Default::default(),
        start_block: BasicBlockId::from_raw(0),
        return_local: LocalId::from_raw(0),
        phase: original.phase,
        is_async: false,
        generator_element_ty: None,
    };

    let async_return_local = push_local(
        &mut body,
        async_return_ty,
        LocalKind::Return,
        true,
        Some(gcx.intern_symbol("$async_ret")),
        span,
    );
    body.return_local = async_return_local;

    if is_std_yield_now(gcx, original.owner) {
        let yield_now_id =
            find_or_register_async_runtime_function(gcx, AsyncRuntimeFn::YieldNow, span);
        let ret_block = body.basic_blocks.push(BasicBlockData {
            note: Some("async-yield-now-ret".into()),
            statements: vec![],
            terminator: Some(Terminator {
                kind: TerminatorKind::Return,
                span,
            }),
        });
        let entry = body.basic_blocks.push(BasicBlockData {
            note: Some("async-yield-now-ctor".into()),
            statements: vec![],
            terminator: Some(Terminator {
                kind: TerminatorKind::Call {
                    func: fn_operand(
                        yield_now_id,
                        GenericArguments::empty(),
                        gcx.get_type(yield_now_id),
                    ),
                    args: vec![],
                    destination: Place::from_local(async_return_local),
                    target: ret_block,
                    unwind: CallUnwindAction::Terminate,
                },
                span,
            }),
        });
        body.start_block = entry;
        return Ok(body);
    }

    let poll_param_locals: Vec<_> = original
        .locals
        .iter_enumerated()
        .filter_map(|(local, decl)| matches!(decl.kind, LocalKind::Param).then_some((local, decl)))
        .collect();
    let ctor_param_locals: Vec<_> = poll_param_locals
        .iter()
        .map(|(_, decl)| {
            push_local(
                &mut body,
                decl.ty,
                LocalKind::Param,
                false,
                decl.name,
                decl.span,
            )
        })
        .collect();

    let frame_ptr_local = push_local(
        &mut body,
        frame_ptr_mut_ty,
        LocalKind::Temp,
        true,
        Some(gcx.intern_symbol("$frame_ptr")),
        span,
    );
    let frame_bytes_local = push_local(
        &mut body,
        ptr_u8_mut,
        LocalKind::Temp,
        true,
        Some(gcx.intern_symbol("$frame_bytes")),
        span,
    );
    let poll_ptr_local = push_local(
        &mut body,
        ptr_u8_const,
        LocalKind::Temp,
        true,
        Some(gcx.intern_symbol("$poll_ptr")),
        span,
    );
    let drop_ptr_local = push_local(
        &mut body,
        ptr_u8_const,
        LocalKind::Temp,
        true,
        Some(gcx.intern_symbol("$drop_ptr")),
        span,
    );

    let entry = body.basic_blocks.push(BasicBlockData {
        note: Some("async-ctor-entry".into()),
        statements: vec![],
        terminator: None,
    });
    body.start_block = entry;

    let after_memset = body.basic_blocks.push(BasicBlockData {
        note: Some("async-ctor-after-memset".into()),
        statements: vec![],
        terminator: None,
    });
    let ret_block = body.basic_blocks.push(BasicBlockData {
        note: Some("async-ctor-ret".into()),
        statements: vec![],
        terminator: Some(Terminator {
            kind: TerminatorKind::Return,
            span,
        }),
    });

    for ((poll_local, _), ctor_local) in poll_param_locals.iter().zip(ctor_param_locals.iter()) {
        if !frame.stored_locals.contains(poll_local) {
            continue;
        }
        body.basic_blocks[after_memset].statements.push(Statement {
            kind: StatementKind::Assign(
                frame_local_place_stub(frame, frame_ptr_local, *poll_local),
                // Parameters transfer their one initialized obligation into
                // the frame, including Copy handles already acquired by the
                // caller. This is not another environment/header copy.
                Rvalue::Use(Operand::Copy(Place::from_local(*ctor_local))),
            ),
            span,
        });
    }
    body.basic_blocks[after_memset].statements.push(Statement {
        kind: StatementKind::Assign(
            Place::from_local(poll_ptr_local),
            Rvalue::Cast {
                operand: fn_operand(
                    poll_id,
                    GenericsBuilder::identity_for_item(gcx, poll_id),
                    gcx.get_type(poll_id),
                ),
                ty: ptr_u8_const,
                kind: crate::mir::CastKind::Pointer,
            },
        ),
        span,
    });
    body.basic_blocks[after_memset].statements.push(Statement {
        kind: StatementKind::Assign(
            Place::from_local(drop_ptr_local),
            Rvalue::Cast {
                operand: fn_operand(
                    drop_id,
                    GenericsBuilder::identity_for_item(gcx, drop_id),
                    gcx.get_type(drop_id),
                ),
                ty: ptr_u8_const,
                kind: crate::mir::CastKind::Pointer,
            },
        ),
        span,
    });

    let native_owner = push_local(
        &mut body,
        ptr_u8_mut,
        LocalKind::Temp,
        true,
        Some(gcx.intern_symbol("$gc_frame_owner")),
        span,
    );
    let create = AsyncRuntimeFn::CreateOwned;
    let async_create_id = find_or_register_async_runtime_function(gcx, create, span);
    let async_create_ty = gcx.get_type(async_create_id);
    body.basic_blocks[after_memset].terminator = Some(Terminator {
        kind: TerminatorKind::Call {
            func: fn_operand(async_create_id, GenericArguments::empty(), async_create_ty),
            args: vec![
                Operand::Copy(Place::from_local(native_owner)),
                Operand::Copy(Place::from_local(poll_ptr_local)),
                Operand::Copy(Place::from_local(drop_ptr_local)),
                // Source frames and captures use stable GC storage. Only
                // internal native tasks can request worker affinity.
                const_uint8_operand(gcx, 1),
            ],
            destination: Place::from_local(async_return_local),
            target: ret_block,
            unwind: CallUnwindAction::Terminate,
        },
        span,
    });

    {
        gc_frame::install(
            gcx,
            &mut body,
            frame.ty,
            entry,
            after_memset,
            native_owner,
            frame_bytes_local,
            frame_ptr_local,
            span,
        );
    }

    Ok(body)
}

/// Register a synthetic drop definition for the async frame cleanup function.
fn register_async_drop_definition<'ctx>(
    gcx: Gcx<'ctx>,
    owner: DefinitionID,
    span: Span,
) -> DefinitionID {
    let drop_id = gcx.allocate_synthetic_id(owner.package());
    let ptr_u8_mut = raw_ptr_ty(gcx, gcx.types.uint8, crate::hir::Mutability::Mutable);
    let signature = LabeledFunctionSignature {
        inputs: vec![LabeledFunctionParameter {
            name: gcx.intern_symbol("frame"),
            ty: ptr_u8_mut,
            label: None,
            is_lazy: false,
            default_provider: None,
        }],
        output: gcx.types.void,
        is_variadic: false,
        abi: None,
    };
    let signature = gcx
        .store
        .arenas
        .function_signatures
        .alloc(signature.clone());
    let owner_name = gcx.definition_symbol_or_fallback(owner);
    let def = crate::sema::models::SyntheticDefinition {
        kind: crate::sema::models::SyntheticDefinitionKind::Ordinary,
        name: gcx.intern_symbol(&format!("{}$drop", gcx.symbol_text(owner_name))),
        generics: gcx.generics_of(owner),
        signature,
        span,
    };
    gcx.register_synthetic_definition(drop_id, def);
    gcx.cache_type(drop_id, Ty::from_labeled_signature(gcx, &signature));
    drop_id
}

/// Before the first poll, only constructor inputs own initialized values.
/// Started bodies use their checked cleanup paths on normal/cancellation/unwind
/// exits. Never read uninitialized body-local slots or register body defers here.
fn build_async_drop_body<'ctx>(
    gcx: Gcx<'ctx>,
    owner: DefinitionID,
    frame: &AsyncFrameLayout<'ctx>,
    poll_body: &Body<'ctx>,
) -> CompileResult<(DefinitionID, Body<'ctx>)> {
    let span = poll_body.locals[poll_body.return_local].span;
    let drop_id = register_async_drop_definition(gcx, owner, span);
    let ptr_u8_mut = raw_ptr_ty(gcx, gcx.types.uint8, crate::hir::Mutability::Mutable);
    let frame_ptr_mut_ty = raw_ptr_ty(gcx, frame.ty, crate::hir::Mutability::Mutable);
    let mut body = Body {
        escape_locals: Vec::new(),

        owner: drop_id,
        source_scopes: Body::initial_source_scopes(drop_id),
        locals: Default::default(),
        basic_blocks: Default::default(),
        start_block: BasicBlockId::from_raw(0),
        return_local: LocalId::from_raw(0),
        phase: poll_body.phase,
        is_async: false,
        generator_element_ty: None,
    };
    body.return_local = push_local(
        &mut body,
        gcx.types.void,
        LocalKind::Return,
        true,
        Some(gcx.intern_symbol("$ret")),
        span,
    );
    let frame_raw = push_local(
        &mut body,
        ptr_u8_mut,
        LocalKind::Param,
        false,
        Some(gcx.intern_symbol("$frame")),
        span,
    );
    let frame_ptr = push_local(
        &mut body,
        frame_ptr_mut_ty,
        LocalKind::Temp,
        true,
        Some(gcx.intern_symbol("$frame_ptr")),
        span,
    );
    let state = push_local(
        &mut body,
        frame.state_ty,
        LocalKind::Temp,
        true,
        Some(gcx.intern_symbol("$state")),
        span,
    );
    let done = body.basic_blocks.push(BasicBlockData {
        note: Some("async-drop-done".into()),
        statements: vec![],
        terminator: Some(Terminator {
            kind: TerminatorKind::Return,
            span,
        }),
    });
    // GC reclaims frame inputs; explicit cancellation is handled by the poll body.
    let unstarted = body.basic_blocks.push(BasicBlockData {
        note: Some("async-drop-unstarted-inputs".into()),
        statements: vec![Statement {
            span,
            kind: StatementKind::Assign(
                frame_state_place(frame_ptr, frame.state_ty),
                Rvalue::Use(const_uint_operand(
                    gcx,
                    frame.state_ty,
                    frame.started_state as u64,
                )),
            ),
        }],
        terminator: Some(Terminator {
            span,
            kind: TerminatorKind::Goto { target: done },
        }),
    });
    let drop_targets = vec![(0, unstarted)];
    let entry = body.basic_blocks.push(BasicBlockData {
        note: Some("async-drop-entry".into()),
        statements: vec![
            Statement {
                span,
                kind: StatementKind::Assign(
                    Place::from_local(frame_ptr),
                    Rvalue::Cast {
                        operand: Operand::Copy(Place::from_local(frame_raw)),
                        ty: frame_ptr_mut_ty,
                        kind: crate::mir::CastKind::Pointer,
                    },
                ),
            },
            Statement {
                span,
                kind: StatementKind::Assign(
                    Place::from_local(state),
                    Rvalue::Use(Operand::Copy(frame_state_place(frame_ptr, frame.state_ty))),
                ),
            },
        ],
        terminator: Some(Terminator {
            span,
            kind: TerminatorKind::SwitchInt {
                discr: Operand::Copy(Place::from_local(state)),
                targets: drop_targets,
                otherwise: done,
            },
        }),
    });
    body.start_block = entry;
    Ok((drop_id, body))
}

fn push_local<'ctx>(
    body: &mut Body<'ctx>,
    ty: Ty<'ctx>,
    kind: LocalKind,
    mutable: bool,
    name: Option<crate::span::Symbol>,
    span: Span,
) -> LocalId {
    let local = body.locals.push(LocalDecl {
        ty,
        kind,
        mutable,
        name,
        span,
    });
    local
}

fn body_span<'ctx>(body: &Body<'ctx>) -> Span {
    body.locals[body.return_local].span
}

pub(crate) fn raw_ptr_ty<'ctx>(
    gcx: Gcx<'ctx>,
    inner: Ty<'ctx>,
    mutability: crate::hir::Mutability,
) -> Ty<'ctx> {
    gcx.store
        .interners
        .intern_ty(TyKind::Pointer(inner, mutability))
}

fn fn_operand<'ctx>(
    def_id: DefinitionID,
    generic_args: crate::sema::models::GenericArguments<'ctx>,
    ty: Ty<'ctx>,
) -> Operand<'ctx> {
    Operand::Constant(Constant {
        ty,
        value: ConstantKind::Function(def_id, generic_args, ty),
    })
}

fn const_uint_operand<'ctx>(gcx: Gcx<'ctx>, ty: Ty<'ctx>, value: u64) -> Operand<'ctx> {
    let _ = gcx;
    Operand::Constant(Constant {
        ty,
        value: ConstantKind::Integer(value),
    })
}

fn const_uint8_operand<'ctx>(gcx: Gcx<'ctx>, value: u64) -> Operand<'ctx> {
    const_uint_operand(gcx, gcx.types.uint8, value)
}

fn frame_state_place<'ctx>(frame_ptr_local: LocalId, state_ty: Ty<'ctx>) -> Place<'ctx> {
    Place {
        local: frame_ptr_local,
        projection: vec![
            PlaceElem::Deref,
            PlaceElem::Field(FieldIndex::from_raw(0), state_ty),
        ],
    }
}

fn frame_local_place<'ctx>(
    body: &Body<'ctx>,
    frame: &AsyncFrameLayout<'ctx>,
    frame_ptr_local: LocalId,
    local: LocalId,
) -> Place<'ctx> {
    frame_local_place_impl(frame, frame_ptr_local, local, body.locals[local].ty)
}

fn poll_local_place<'ctx>(
    body: &Body<'ctx>,
    frame: &AsyncFrameLayout<'ctx>,
    frame_ptr_local: LocalId,
    local: LocalId,
) -> Place<'ctx> {
    if frame.resident_locals.contains(&local) {
        frame_local_place(body, frame, frame_ptr_local, local)
    } else {
        Place::from_local(local)
    }
}

fn frame_local_place_stub<'ctx>(
    frame: &AsyncFrameLayout<'ctx>,
    frame_ptr_local: LocalId,
    local: LocalId,
) -> Place<'ctx> {
    frame_local_place_impl(frame, frame_ptr_local, local, frame_local_ty(frame, local))
}

fn frame_local_place_impl<'ctx>(
    frame: &AsyncFrameLayout<'ctx>,
    frame_ptr_local: LocalId,
    local: LocalId,
    local_ty: Ty<'ctx>,
) -> Place<'ctx> {
    let field_index = frame
        .stored_locals
        .iter()
        .position(|candidate| *candidate == local)
        .unwrap_or_else(|| panic!("ICE: async frame missing local {:?}", local))
        + 1;
    Place {
        local: frame_ptr_local,
        projection: vec![
            PlaceElem::Deref,
            PlaceElem::Field(FieldIndex::from_raw(field_index as u32), local_ty),
        ],
    }
}

fn frame_local_ty<'ctx>(frame: &AsyncFrameLayout<'ctx>, local: LocalId) -> Ty<'ctx> {
    let field_index = frame
        .stored_locals
        .iter()
        .position(|candidate| *candidate == local)
        .unwrap_or_else(|| panic!("ICE: async frame missing local {:?}", local));
    let TyKind::Tuple(items) = frame.ty.kind() else {
        unreachable!("async frame is always a tuple");
    };
    items[field_index + 1]
}

pub(crate) use crate::runtime_abi::RuntimeAbiFunction as AsyncRuntimeFn;

pub(crate) fn find_or_register_async_runtime_function<'ctx>(
    gcx: Gcx<'ctx>,
    which: AsyncRuntimeFn,
    span: Span,
) -> DefinitionID {
    find_or_register_runtime_function(gcx, which.spec(), span)
}

/// Register a typed compiler call only when its exact signature is present in
/// the canonical native ABI, including entries without a convenience enum.
pub(crate) fn find_or_register_runtime_function<'ctx>(
    gcx: Gcx<'ctx>,
    spec: crate::runtime_abi::RuntimeFunctionSpec,
    span: Span,
) -> DefinitionID {
    let expected = crate::runtime_abi::RuntimeAbiFunction::ALL
        .iter()
        .map(|function| function.spec())
        .find(|known| known.symbol == spec.symbol)
        .map(|known| known.signature())
        .or_else(|| {
            crate::runtime_abi::ADDITIONAL_RUNTIME_SYMBOLS
                .iter()
                .find(|known| known.symbol == spec.symbol)
                .map(|known| known.signature.to_owned())
        });
    assert_eq!(
        expected.as_deref(),
        Some(spec.signature().as_str()),
        "compiler runtime declaration must match the canonical ABI"
    );
    let name = spec.symbol;
    let inputs = spec
        .inputs
        .iter()
        .copied()
        .map(|ty| lower_runtime_abi_type(gcx, ty))
        .collect::<Vec<_>>();
    let output = lower_runtime_abi_type(gcx, spec.output);

    let symbol = gcx.intern_symbol(name);
    if let Some(id) = gcx
        .store
        .synthetic_definitions
        .borrow()
        .iter()
        .find_map(|(id, def)| {
            (gcx.symbol_eq(def.name, name)
                && def.signature.abi == Some(crate::hir::Abi::Runtime)
                && def
                    .signature
                    .inputs
                    .iter()
                    .map(|input| input.ty)
                    .eq(inputs.iter().copied())
                && def.signature.output == output)
                .then_some(*id)
        })
    {
        return id;
    }

    let id = gcx.allocate_synthetic_id(gcx.package_index());
    let signature = LabeledFunctionSignature {
        inputs: inputs
            .into_iter()
            .enumerate()
            .map(|(index, ty)| LabeledFunctionParameter {
                name: gcx.intern_symbol(&format!("arg{index}")),
                ty,
                label: None,
                is_lazy: false,
                default_provider: None,
            })
            .collect(),
        output,
        is_variadic: false,
        abi: Some(crate::hir::Abi::Runtime),
    };
    let signature = gcx
        .store
        .arenas
        .function_signatures
        .alloc(signature.clone());
    let def = crate::sema::models::SyntheticDefinition {
        kind: crate::sema::models::SyntheticDefinitionKind::Ordinary,
        name: symbol,
        generics: gcx.empty_generics_for_package(gcx.package_index()),
        signature,
        span,
    };
    gcx.register_synthetic_definition(id, def);
    gcx.cache_type(id, Ty::from_labeled_signature(gcx, &signature));
    id
}

fn lower_runtime_abi_type<'ctx>(
    gcx: Gcx<'ctx>,
    ty: crate::runtime_abi::RuntimeAbiType,
) -> Ty<'ctx> {
    use crate::runtime_abi::RuntimeAbiType;

    match ty {
        RuntimeAbiType::Void => gcx.types.void,
        RuntimeAbiType::Never => Ty::new(TyKind::Never, gcx),
        RuntimeAbiType::Bool => gcx.types.bool,
        RuntimeAbiType::U8 => gcx.types.uint8,
        RuntimeAbiType::U32 => gcx.types.uint32,
        RuntimeAbiType::U64 => gcx.types.uint64,
        RuntimeAbiType::Usize => gcx.types.uint,
        RuntimeAbiType::String => gcx.types.string,
        RuntimeAbiType::MutU8Ptr => {
            raw_ptr_ty(gcx, gcx.types.uint8, crate::hir::Mutability::Mutable)
        }
        RuntimeAbiType::ConstU8Ptr => {
            raw_ptr_ty(gcx, gcx.types.uint8, crate::hir::Mutability::Immutable)
        }
        RuntimeAbiType::AsyncHandle => gcx.async_handle_ty(),
    }
}

pub(crate) fn definition_in_std_module<'ctx>(
    gcx: Gcx<'ctx>,
    id: DefinitionID,
    module: &str,
) -> bool {
    let Some(std_pkg) = gcx.std_package_index() else {
        return false;
    };
    if id.package() != std_pkg {
        return false;
    }
    let output = gcx.resolution_output(std_pkg);
    let mut current = id;
    while let Some(parent) = output.definition_to_parent.get(&current).copied() {
        if parent == current {
            break;
        }
        current = parent;
        if matches!(
            output.definition_to_kind.get(&current),
            Some(DefinitionKind::Module)
        ) && output
            .definition_to_ident
            .get(&current)
            .is_some_and(|ident| gcx.symbol_eq(ident.symbol, module))
        {
            return true;
        }
    }
    false
}

fn is_std_yield_now<'ctx>(gcx: Gcx<'ctx>, owner: DefinitionID) -> bool {
    (definition_in_std_module(gcx, owner, "testing")
        || definition_in_std_module(gcx, owner, "task"))
        && gcx.symbol_eq(gcx.definition_symbol_or_fallback(owner), "yieldNow")
}

pub(crate) fn find_std_function<'ctx>(
    gcx: Gcx<'ctx>,
    module: &str,
    name: &str,
    span: Span,
) -> CompileResult<DefinitionID> {
    let Some(std_pkg) = gcx.std_package_index() else {
        gcx.dcx().emit_error(
            "async/await requires the standard library but it was not found".into(),
            Some(span),
        );
        return Err(ReportedError);
    };
    let output = gcx.resolution_output(std_pkg);

    let in_module = |id: DefinitionID| {
        let mut current = id;
        while let Some(parent) = output.definition_to_parent.get(&current).copied() {
            if parent == current {
                break;
            }
            current = parent;
            if matches!(
                output.definition_to_kind.get(&current),
                Some(DefinitionKind::Module)
            ) && output
                .definition_to_ident
                .get(&current)
                .is_some_and(|ident| gcx.symbol_eq(ident.symbol, module))
            {
                return true;
            }
        }
        false
    };

    let mut fallback = None;
    for (id, ident) in output.definition_to_ident.iter() {
        if !gcx.symbol_eq(ident.symbol, name) {
            continue;
        }
        if !matches!(
            output.definition_to_kind.get(id),
            Some(DefinitionKind::Function)
        ) {
            continue;
        }
        if !gcx.with_type_database(id.package(), |db| db.def_to_fn_sig.contains_key(id)) {
            continue;
        }
        if in_module(*id) {
            return Ok(*id);
        }
        fallback = Some(*id);
    }

    match fallback {
        Some(id) => Ok(id),
        None => {
            gcx.dcx().emit_error(
                format!(
                    "async/await requires 'std.{}.{}' but it was not found",
                    module, name
                )
                .into(),
                Some(span),
            );
            Err(ReportedError)
        }
    }
}

#[cfg(test)]
mod frame_storage_tests {
    use super::*;
    use crate::hir::Mutability;
    use crate::mir::test_support::minimal_body;

    #[test]
    fn address_taken_aggregate_storage_resides_in_the_frame_even_without_ordinary_liveness() {
        crate::test_support::analyze_script(
            "struct Owner { value: int32 }\nfunc main() {}",
            |package, gcx| {
                let mut body = minimal_body(gcx);
                let ty = gcx.get_type(package.root.declarations[0].id);
                let owner = crate::mir::test_support::push_temp(&mut body, ty);
                let reference = crate::mir::test_support::push_temp(
                    &mut body,
                    Ty::new(TyKind::Reference(ty), gcx),
                );
                let span = body.locals[owner].span;
                let TyKind::Adt(definition, _) = ty.kind() else {
                    unreachable!()
                };
                body.basic_blocks[body.start_block].statements = vec![
                    Statement {
                        span,
                        kind: StatementKind::Assign(
                            Place::from_local(owner),
                            Rvalue::Aggregate {
                                kind: crate::mir::AggregateKind::Adt {
                                    def_id: definition.id,
                                    variant_index: None,
                                    generic_args: GenericArguments::empty(),
                                },
                                fields: index_vec::IndexVec::from(vec![Operand::Constant(
                                    Constant {
                                        ty: gcx.types.int32,
                                        value: ConstantKind::Integer(7),
                                    },
                                )]),
                            },
                        ),
                    },
                    Statement {
                        span,
                        kind: StatementKind::Assign(
                            Place::from_local(reference),
                            Rvalue::Ref {
                                place: Place::from_local(owner),
                            },
                        ),
                    },
                ];
                assert!(!compute_block_liveness(&body).live_in[body.start_block].contains(&owner));
                let frame = build_frame_layout(gcx, &body, &[]);
                assert!(frame.stored_locals.contains(&owner));
                assert!(
                    frame.resident_locals.contains(&owner),
                    "taking an address cannot depend on Copy conformance"
                );
            },
        );
    }

    #[test]
    fn verifier_rejects_poll_stack_borrows_until_the_owner_is_rewritten() {
        crate::test_support::analyze_script(
            "struct Owner { value: int32 }\nfunc main() {}",
            |package, gcx| {
                let mut body = minimal_body(gcx);
                let ty = gcx.get_type(package.root.declarations[0].id);
                let owner = crate::mir::test_support::push_temp(&mut body, ty);
                let reference = crate::mir::test_support::push_temp(
                    &mut body,
                    Ty::new(TyKind::Reference(gcx.types.int32), gcx),
                );
                let span = body.locals[owner].span;
                body.basic_blocks[body.start_block]
                    .statements
                    .push(Statement {
                        span,
                        kind: StatementKind::Assign(
                            Place::from_local(reference),
                            Rvalue::Ref {
                                place: Place {
                                    local: owner,
                                    projection: vec![PlaceElem::Field(
                                        FieldIndex::from_raw(0),
                                        gcx.types.int32,
                                    )],
                                },
                            },
                        ),
                    });
                let original_locals = body.locals.len();
                assert_eq!(
                    verify_frame_reference_storage(&body, original_locals)
                        .unwrap_err()
                        .0,
                    owner
                );
                let frame = build_frame_layout(gcx, &body, &[]);
                let frame_pointer = crate::mir::test_support::push_temp(
                    &mut body,
                    raw_ptr_ty(gcx, frame.ty, Mutability::Mutable),
                );
                rewrite_resident_local_places(&mut body, &frame, frame_pointer, &mut []);
                assert!(verify_frame_reference_storage(&body, original_locals).is_ok());
                let StatementKind::Assign(_, Rvalue::Ref { place, .. }) =
                    &body.basic_blocks[body.start_block].statements[0].kind
                else {
                    unreachable!()
                };
                assert_eq!(place.local, frame_pointer);
                assert_eq!(place.projection.first(), Some(&PlaceElem::Deref));
            },
        );
    }
}
