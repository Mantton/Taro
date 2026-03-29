use crate::{
    compile::context::Gcx,
    error::{CompileResult, ReportedError},
    hir::DefinitionID,
    hir::StdItem,
    mir::{
        BasicBlockData, BasicBlockId, Body, CallUnwindAction, Constant, ConstantKind,
        CopyModifiers, LocalDecl, LocalId, LocalKind, Operand, Place, PlaceElem, Rvalue, Statement,
        StatementKind, Terminator, TerminatorKind, analysis::liveness::compute_liveness,
    },
    sema::{
        models::{
            AdtKind, EnumVariantKind, GenericArgument, GenericArguments, LabeledFunctionParameter,
            LabeledFunctionSignature, Ty, TyKind,
        },
        resolve::models::DefinitionKind,
        tycheck::utils::generics::GenericsBuilder,
        tycheck::utils::{instantiate::instantiate_ty_with_args, normalize::normalize_aliases},
    },
    span::{FileID, Span},
    thir::FieldIndex,
};
use rustc_hash::FxHashSet;

use super::MirPass;

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
    span: Span,
}

struct AsyncFrameLayout<'ctx> {
    ty: Ty<'ctx>,
    state_ty: Ty<'ctx>,
    stored_locals: Vec<LocalId>,
    start_locals: Vec<LocalId>,
    yield_locals: Vec<Vec<LocalId>>,
    mobility: AsyncTaskMobility,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum AsyncTaskMobility {
    Pinned,
    Movable,
}

struct PollThunkLocals<'ctx> {
    frame_raw: LocalId,
    _ctx_raw: LocalId,
    out_raw: LocalId,
    frame_ptr: LocalId,
    out_ptr: LocalId,
    state: LocalId,
    tag_return: LocalId,
    frame_size: LocalId,
    memset_void: LocalId,
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

        let span = body_span(body);
        let poll_id = register_async_poll_definition(gcx, body.owner, span);
        let mut poll_body = body.clone();
        poll_body.owner = poll_id;
        let frame = lower_async_poll_body(gcx, &mut poll_body)?;

        let (drop_id, drop_body) = build_async_drop_body(gcx, body.owner, &frame, &poll_body);
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
                default_provider: None,
            },
            LabeledFunctionParameter {
                name: gcx.intern_symbol("ctx"),
                ty: ptr_u8_mut,
                label: None,
                default_provider: None,
            },
            LabeledFunctionParameter {
                name: gcx.intern_symbol("out"),
                ty: ptr_u8_mut,
                label: None,
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
        name: gcx.intern_symbol(&format!("{}$poll", gcx.symbol_text(owner_name))),
        generics: gcx.generics_of(owner),
        signature,
        span,
    };
    gcx.register_synthetic_definition(poll_id, def);
    gcx.cache_type(poll_id, Ty::from_labeled_signature(gcx, &signature));
    poll_id
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

    let yields = materialize_await_futures(gcx, body);
    let frame = build_frame_layout(gcx, body, &yields);
    let locals = add_poll_thunk_locals(gcx, body, frame.ty, output_ty);

    rewrite_returns(gcx, body, original_return_local, &locals);
    rewrite_yields(gcx, body, &yields, &frame, &locals)?;
    install_dispatch(gcx, body, &yields, &frame, &locals)?;

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
        } = terminator.kind
        else {
            unreachable!();
        };

        let future_place = if let Some((place, _)) = value.as_copy() {
            place.clone()
        } else {
            let future_ty = operand_ty(body, gcx, &value);
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
    let liveness = compute_liveness(body);
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
                || yield_locals
                    .iter()
                    .any(|locals| locals.contains(&local))
        })
        .collect();
    let mut fields = Vec::with_capacity(stored_locals.len() + 1);
    fields.push(state_ty);
    fields.extend(stored_locals.iter().map(|local| body.locals[*local].ty));
    let frame_ty = Ty::new(
        TyKind::Tuple(gcx.store.interners.intern_ty_list(fields)),
        gcx,
    );
    let mobility = infer_async_task_mobility(gcx, body, &stored_locals);
    AsyncFrameLayout {
        ty: frame_ty,
        state_ty,
        stored_locals,
        start_locals,
        yield_locals,
        mobility,
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

fn infer_async_task_mobility<'ctx>(
    gcx: Gcx<'ctx>,
    body: &Body<'ctx>,
    stored_locals: &[LocalId],
) -> AsyncTaskMobility {
    let mut visited = FxHashSet::default();
    if stored_locals
        .iter()
        .all(|local| ty_is_movable_across_workers(gcx, body.locals[*local].ty, &mut visited))
    {
        AsyncTaskMobility::Movable
    } else {
        AsyncTaskMobility::Pinned
    }
}

fn ty_is_movable_across_workers<'ctx>(
    gcx: Gcx<'ctx>,
    ty: Ty<'ctx>,
    visited: &mut FxHashSet<Ty<'ctx>>,
) -> bool {
    let ty = normalize_aliases(gcx, ty);
    if ty == gcx.async_handle_ty() {
        // Async handles can encapsulate child futures that transiently hold
        // stack-derived pointers/references across await boundaries. Treat
        // them as non-movable until we can prove cross-worker safety.
        return false;
    }
    if !visited.insert(ty) {
        return true;
    }

    let movable = match ty.kind() {
        TyKind::Bool
        | TyKind::Rune
        | TyKind::String
        | TyKind::Int(_)
        | TyKind::UInt(_)
        | TyKind::Float(_)
        | TyKind::Never => true,
        TyKind::Pointer(..)
        | TyKind::Reference(..)
        | TyKind::BoxedExistential { .. }
        | TyKind::Alias { .. }
        | TyKind::Infer(_)
        | TyKind::Parameter(_)
        | TyKind::Opaque(_)
        | TyKind::Error => false,
        TyKind::Array { element, .. } => ty_is_movable_across_workers(gcx, element, visited),
        TyKind::Tuple(items) => items
            .iter()
            .copied()
            .all(|item| ty_is_movable_across_workers(gcx, item, visited)),
        TyKind::FnPointer { .. } => true,
        TyKind::Closure { closure_def_id, .. } => gcx
            .get_closure_captures(closure_def_id)
            .map(|captures| {
                captures
                    .captures
                    .iter()
                    .all(|capture| ty_is_movable_across_workers(gcx, capture.ty, visited))
            })
            .unwrap_or(true),
        TyKind::Adt(def, args) => {
            if gcx.std_item_def(StdItem::Task) == Some(def.id) {
                true
            } else {
                match def.kind {
                    AdtKind::Struct => {
                        gcx.get_struct_definition(def.id)
                            .fields
                            .iter()
                            .all(|field| {
                                let field_ty = instantiate_ty_with_args(gcx, field.ty, args);
                                ty_is_movable_across_workers(gcx, field_ty, visited)
                            })
                    }
                    AdtKind::Enum => {
                        gcx.get_enum_definition(def.id)
                            .variants
                            .iter()
                            .all(|variant| match variant.kind {
                                EnumVariantKind::Unit => true,
                                EnumVariantKind::Tuple(fields) => fields.iter().all(|field| {
                                    let field_ty = instantiate_ty_with_args(gcx, field.ty, args);
                                    ty_is_movable_across_workers(gcx, field_ty, visited)
                                }),
                            })
                    }
                }
            }
        }
    };

    visited.remove(&ty);
    movable
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
    let frame_size = push_local(
        body,
        gcx.types.uint,
        LocalKind::Temp,
        true,
        Some(gcx.intern_symbol("$frame_size")),
        span,
    );
    let memset_void = push_local(
        body,
        gcx.types.void,
        LocalKind::Temp,
        true,
        Some(gcx.intern_symbol("$memset_void")),
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
        frame_size,
        memset_void,
        output_ty,
    }
}

fn rewrite_returns<'ctx>(
    gcx: Gcx<'ctx>,
    body: &mut Body<'ctx>,
    original_return_local: LocalId,
    locals: &PollThunkLocals<'ctx>,
) {
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
        body.basic_blocks[bb_id].statements.push(Statement {
            kind: StatementKind::Assign(
                Place {
                    local: locals.out_ptr,
                    projection: vec![PlaceElem::Deref],
                },
                Rvalue::Use(Operand::CopyWith(
                    Place::from_local(original_return_local),
                    CopyModifiers {
                        init: true,
                        take: false,
                    },
                )),
            ),
            span,
        });
        body.basic_blocks[bb_id].statements.push(Statement {
            kind: StatementKind::Assign(
                Place::from_local(locals.tag_return),
                Rvalue::Use(const_uint8_operand(gcx, 1)),
            ),
            span,
        });
    }
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
    let memset_id = find_std_function(gcx, "intrinsic", "__intrinsic_memset", span)?;
    let memset_ty = gcx.get_type(memset_id);

    for (index, site) in yields.iter().enumerate() {
        let ready_ty = place_ty(body, gcx, &site.resume_arg);
        let ready_storage_ty = if ready_ty == gcx.types.void {
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
            gcx.store.interners.intern_ty(TyKind::Reference(
                ready_storage_ty,
                crate::hir::Mutability::Mutable,
            )),
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
                    mutable: true,
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
            ),
            terminator: Some(Terminator {
                kind: TerminatorKind::Return,
                span: site.span,
            }),
        });
        let pending_block = body.basic_blocks.push(BasicBlockData {
            note: Some(format!("await-pending-{}", index)),
            statements: vec![],
            terminator: Some(Terminator {
                kind: TerminatorKind::Call {
                    func: fn_operand(
                        memset_id,
                        gcx.store
                            .interners
                            .intern_generic_args(vec![GenericArgument::Type(gcx.types.uint8)]),
                        memset_ty,
                    ),
                    args: vec![
                        Operand::Copy(Place::from_local(locals.frame_raw)),
                        const_uint8_operand(gcx, 0),
                        Operand::Copy(Place::from_local(locals.frame_size)),
                    ],
                    destination: Place::from_local(locals.memset_void),
                    target: pending_store_block,
                    unwind: CallUnwindAction::Terminate,
                },
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
                    unwind: CallUnwindAction::Terminate,
                },
                span: site.span,
            }),
        });

        let ready_block = body.basic_blocks.push(BasicBlockData {
            note: Some(format!("await-ready-{}", index)),
            statements: vec![if ready_ty == gcx.types.void {
                Statement {
                    kind: StatementKind::Assign(
                        site.resume_arg.clone(),
                        Rvalue::Use(Operand::Constant(Constant {
                            ty: gcx.types.void,
                            value: ConstantKind::Unit,
                        })),
                    ),
                    span: site.span,
                }
            } else {
                Statement {
                    kind: StatementKind::Assign(
                        site.resume_arg.clone(),
                        Rvalue::Use(Operand::CopyWith(
                            Place::from_local(ready_storage_local),
                            CopyModifiers {
                                init: true,
                                take: true,
                            },
                        )),
                    ),
                    span: site.span,
                }
            }],
            terminator: Some(Terminator {
                kind: TerminatorKind::Goto {
                    target: ready_target,
                },
                span: site.span,
            }),
        });

        body.basic_blocks[check_block].terminator = Some(Terminator {
            kind: TerminatorKind::SwitchInt {
                discr: Operand::Copy(Place::from_local(tag_local)),
                targets: vec![(0u128, pending_block)],
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
                unwind: CallUnwindAction::Terminate,
            },
            span: site.span,
        });
        body.basic_blocks[poll_block].terminator = Some(Terminator {
            kind: TerminatorKind::Goto {
                target: poll_handle_block,
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

    // Compute sizeOf[FrameTy] before dispatch so restore blocks can memset the frame.
    let size_of_entry = body.basic_blocks.push(BasicBlockData {
        note: Some("async-sizeof".into()),
        statements: vec![],
        terminator: None,
    });
    let size_of_id = find_std_function(gcx, "mem", "sizeOf", span)?;
    let size_of_ty = gcx.get_type(size_of_id);
    body.basic_blocks[size_of_entry].terminator = Some(Terminator {
        kind: TerminatorKind::Call {
            func: fn_operand(
                size_of_id,
                gcx.store
                    .interners
                    .intern_generic_args(vec![GenericArgument::Type(frame.ty)]),
                size_of_ty,
            ),
            args: vec![],
            destination: Place::from_local(locals.frame_size),
            target: dispatch,
            unwind: CallUnwindAction::Terminate,
        },
        span,
    });

    // Resolve memset for use in restore blocks.
    let memset_id = find_std_function(gcx, "intrinsic", "__intrinsic_memset", span)?;
    let memset_ty = gcx.get_type(memset_id);

    let start_restore = restore_block(
        gcx,
        body,
        frame,
        &frame.start_locals,
        locals.frame_raw,
        locals.frame_ptr,
        original_start,
        locals.frame_size,
        locals.memset_void,
        memset_id,
        memset_ty,
        span,
    );
    let mut targets = vec![(0u128, start_restore)];
    for (index, site) in yields.iter().enumerate() {
        let restore = restore_block(
            gcx,
            body,
            frame,
            &frame.yield_locals[index],
            locals.frame_raw,
            locals.frame_ptr,
            site.block,
            locals.frame_size,
            locals.memset_void,
            memset_id,
            memset_ty,
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
    body.start_block = size_of_entry;
    Ok(())
}

/// Build a restore block that loads all stored locals from the frame, then
/// memsets the frame to zero (transferring Rc ownership to locals).
fn restore_block<'ctx>(
    gcx: Gcx<'ctx>,
    body: &mut Body<'ctx>,
    frame: &AsyncFrameLayout<'ctx>,
    locals_to_restore: &[LocalId],
    frame_raw_local: LocalId,
    frame_ptr_local: LocalId,
    target: BasicBlockId,
    frame_size_local: LocalId,
    memset_void_local: LocalId,
    memset_id: DefinitionID,
    memset_ty: Ty<'ctx>,
    span: Span,
) -> BasicBlockId {
    let statements: Vec<_> = locals_to_restore
        .iter()
        .map(|local| Statement {
            // Use init+take modifiers: skip pre-save of old local (may be
            // uninit or zeroed) and skip retain (the memset below will clear
            // the frame's copy, leaving the local as sole owner).
            kind: StatementKind::Assign(
                Place::from_local(*local),
                Rvalue::Use(Operand::CopyWith(
                    frame_local_place(body, frame, frame_ptr_local, *local),
                    CopyModifiers {
                        init: true,
                        take: true,
                    },
                )),
            ),
            span,
        })
        .collect();

    // After loading locals, memset the frame to zero. This transfers Rc
    // ownership to the locals so that emit_rc_cleanup at Return correctly
    // releases them, while the drop body (which loads from the frame) will
    // see zeroed Rc pointers and no-op.
    let restore = body.basic_blocks.push(BasicBlockData {
        note: Some("async-restore".into()),
        statements,
        terminator: Some(Terminator {
            kind: TerminatorKind::Call {
                func: fn_operand(
                    memset_id,
                    gcx.store
                        .interners
                        .intern_generic_args(vec![GenericArgument::Type(gcx.types.uint8)]),
                    memset_ty,
                ),
                args: vec![
                    Operand::Copy(Place::from_local(frame_raw_local)),
                    const_uint8_operand(gcx, 0),
                    Operand::Copy(Place::from_local(frame_size_local)),
                ],
                destination: Place::from_local(memset_void_local),
                target,
                unwind: CallUnwindAction::Terminate,
            },
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
    for local in locals_to_save {
        // Use take semantics: the codegen will zero the source local after copying,
        // which prevents emit_rc_cleanup from double-releasing Rc-containing locals
        // that now live in the frame.
        statements.push(Statement {
            kind: StatementKind::Assign(
                frame_local_place_stub(frame, frame_ptr_local, *local),
                Rvalue::Use(Operand::CopyWith(
                    Place::from_local(*local),
                    CopyModifiers {
                        init: true,
                        take: true,
                    },
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

fn build_async_constructor<'ctx>(
    gcx: Gcx<'ctx>,
    original: &Body<'ctx>,
    poll_id: DefinitionID,
    drop_id: DefinitionID,
    frame: &AsyncFrameLayout<'ctx>,
) -> CompileResult<Body<'ctx>> {
    let span = body_span(original);
    let async_return_ty = gcx.async_handle_ty();
    let frame_ptr_const_ty = raw_ptr_ty(gcx, frame.ty, crate::hir::Mutability::Immutable);
    let frame_ptr_mut_ty = raw_ptr_ty(gcx, frame.ty, crate::hir::Mutability::Mutable);
    let ptr_u8_mut = raw_ptr_ty(gcx, gcx.types.uint8, crate::hir::Mutability::Mutable);
    let ptr_u8_const = raw_ptr_ty(gcx, gcx.types.uint8, crate::hir::Mutability::Immutable);

    let mut body = Body {
        owner: original.owner,
        locals: Default::default(),
        basic_blocks: Default::default(),
        start_block: BasicBlockId::from_raw(0),
        return_local: LocalId::from_raw(0),
        escape_locals: vec![],
        phase: original.phase,
        is_async: false,
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

    if is_std_testing_yield_now(gcx, original.owner) {
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

    let alloc_local = push_local(
        &mut body,
        frame_ptr_const_ty,
        LocalKind::Temp,
        true,
        Some(gcx.intern_symbol("$frame_alloc")),
        span,
    );
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
    let size_local = push_local(
        &mut body,
        gcx.types.uint,
        LocalKind::Temp,
        true,
        Some(gcx.intern_symbol("$frame_size")),
        span,
    );
    let memset_tmp = push_local(
        &mut body,
        gcx.types.void,
        LocalKind::Temp,
        true,
        Some(gcx.intern_symbol("$memset")),
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
        statements: vec![
            Statement {
                kind: StatementKind::Assign(
                    Place::from_local(alloc_local),
                    Rvalue::Alloc { ty: frame.ty },
                ),
                span,
            },
            Statement {
                kind: StatementKind::Assign(
                    Place::from_local(frame_ptr_local),
                    Rvalue::Cast {
                        operand: Operand::Copy(Place::from_local(alloc_local)),
                        ty: frame_ptr_mut_ty,
                        kind: crate::mir::CastKind::Pointer,
                    },
                ),
                span,
            },
            Statement {
                kind: StatementKind::Assign(
                    Place::from_local(frame_bytes_local),
                    Rvalue::Cast {
                        operand: Operand::Copy(Place::from_local(frame_ptr_local)),
                        ty: ptr_u8_mut,
                        kind: crate::mir::CastKind::Pointer,
                    },
                ),
                span,
            },
        ],
        terminator: None,
    });
    body.start_block = entry;

    let after_size = body.basic_blocks.push(BasicBlockData {
        note: Some("async-ctor-after-size".into()),
        statements: vec![],
        terminator: None,
    });
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

    let size_of_id = find_std_function(gcx, "mem", "sizeOf", span)?;
    let size_of_ty = gcx.get_type(size_of_id);
    body.basic_blocks[entry].terminator = Some(Terminator {
        kind: TerminatorKind::Call {
            func: fn_operand(
                size_of_id,
                gcx.store
                    .interners
                    .intern_generic_args(vec![GenericArgument::Type(frame.ty)]),
                size_of_ty,
            ),
            args: vec![],
            destination: Place::from_local(size_local),
            target: after_size,
            unwind: CallUnwindAction::Terminate,
        },
        span,
    });

    let memset_id = find_std_function(gcx, "intrinsic", "__intrinsic_memset", span)?;
    let memset_ty = gcx.get_type(memset_id);
    body.basic_blocks[after_size].terminator = Some(Terminator {
        kind: TerminatorKind::Call {
            func: fn_operand(
                memset_id,
                gcx.store
                    .interners
                    .intern_generic_args(vec![GenericArgument::Type(gcx.types.uint8)]),
                memset_ty,
            ),
            args: vec![
                Operand::Copy(Place::from_local(frame_bytes_local)),
                const_uint8_operand(gcx, 0),
                Operand::Copy(Place::from_local(size_local)),
            ],
            destination: Place::from_local(memset_tmp),
            target: after_memset,
            unwind: CallUnwindAction::Terminate,
        },
        span,
    });

    for ((poll_local, _), ctor_local) in poll_param_locals.iter().zip(ctor_param_locals.iter()) {
        if !frame.stored_locals.contains(poll_local) {
            continue;
        }
        body.basic_blocks[after_memset].statements.push(Statement {
            kind: StatementKind::Assign(
                frame_local_place_stub(frame, frame_ptr_local, *poll_local),
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

    let async_create_id =
        find_or_register_async_runtime_function(gcx, AsyncRuntimeFn::Create, span);
    let async_create_ty = gcx.get_type(async_create_id);
    body.basic_blocks[after_memset].terminator = Some(Terminator {
        kind: TerminatorKind::Call {
            func: fn_operand(async_create_id, GenericArguments::empty(), async_create_ty),
            args: vec![
                Operand::Copy(Place::from_local(frame_bytes_local)),
                Operand::Copy(Place::from_local(poll_ptr_local)),
                Operand::Copy(Place::from_local(drop_ptr_local)),
                const_uint8_operand(
                    gcx,
                    match frame.mobility {
                        AsyncTaskMobility::Pinned => 0,
                        AsyncTaskMobility::Movable => 1,
                    },
                ),
            ],
            destination: Place::from_local(async_return_local),
            target: ret_block,
            unwind: CallUnwindAction::Terminate,
        },
        span,
    });

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
        name: gcx.intern_symbol(&format!("{}$drop", gcx.symbol_text(owner_name))),
        generics: gcx.generics_of(owner),
        signature,
        span,
    };
    gcx.register_synthetic_definition(drop_id, def);
    gcx.cache_type(drop_id, Ty::from_labeled_signature(gcx, &signature));
    drop_id
}

/// Build a synthetic drop body that loads all frame locals into temps, then
/// returns. The codegen's `emit_rc_cleanup` will release any Rc fields
/// contained in those locals at the return point.
fn build_async_drop_body<'ctx>(
    gcx: Gcx<'ctx>,
    owner: DefinitionID,
    frame: &AsyncFrameLayout<'ctx>,
    poll_body: &Body<'ctx>,
) -> (DefinitionID, Body<'ctx>) {
    let span = poll_body.locals[poll_body.return_local].span;
    let drop_id = register_async_drop_definition(gcx, owner, span);

    let ptr_u8_mut = raw_ptr_ty(gcx, gcx.types.uint8, crate::hir::Mutability::Mutable);
    let frame_ptr_mut_ty = raw_ptr_ty(gcx, frame.ty, crate::hir::Mutability::Mutable);

    let mut body = Body {
        owner: drop_id,
        locals: Default::default(),
        basic_blocks: Default::default(),
        start_block: BasicBlockId::from_raw(0),
        return_local: LocalId::from_raw(0),
        escape_locals: vec![],
        phase: poll_body.phase,
        is_async: false,
    };

    // Return local (void)
    let ret_local = push_local(
        &mut body,
        gcx.types.void,
        LocalKind::Return,
        true,
        Some(gcx.intern_symbol("$ret")),
        span,
    );
    body.return_local = ret_local;

    // Parameter: frame raw pointer
    let frame_raw = push_local(
        &mut body,
        ptr_u8_mut,
        LocalKind::Param,
        false,
        Some(gcx.intern_symbol("$frame")),
        span,
    );

    // Typed frame pointer
    let frame_ptr = push_local(
        &mut body,
        frame_ptr_mut_ty,
        LocalKind::Temp,
        true,
        Some(gcx.intern_symbol("$frame_ptr")),
        span,
    );

    // Create temp locals mirroring the frame's stored locals (only those with
    // types that may contain Rc — but for simplicity and correctness we load
    // all of them; the codegen no-ops for non-Rc types).
    let mirror_locals: Vec<_> = frame
        .stored_locals
        .iter()
        .map(|&local| {
            let ty = poll_body.locals[local].ty;
            push_local(&mut body, ty, LocalKind::Temp, true, None, span)
        })
        .collect();

    // Entry block: cast frame pointer and load all locals
    let mut statements = vec![Statement {
        kind: StatementKind::Assign(
            Place::from_local(frame_ptr),
            Rvalue::Cast {
                operand: Operand::Copy(Place::from_local(frame_raw)),
                ty: frame_ptr_mut_ty,
                kind: crate::mir::CastKind::Pointer,
            },
        ),
        span,
    }];

    for (i, &mirror) in mirror_locals.iter().enumerate() {
        let field_index = i + 1; // +1 because field 0 is the state tag
        let field_ty = poll_body.locals[frame.stored_locals[i]].ty;
        // Use init+take modifiers: skip retain (init) and zero the frame's
        // field after loading (take).  This transfers Rc ownership from the
        // frame to the mirror local so emit_rc_cleanup at Return releases
        // exactly once, and the frame is left zeroed (safe against GC scans).
        statements.push(Statement {
            kind: StatementKind::Assign(
                Place::from_local(mirror),
                Rvalue::Use(Operand::CopyWith(
                    Place {
                        local: frame_ptr,
                        projection: vec![
                            PlaceElem::Deref,
                            PlaceElem::Field(FieldIndex::from_raw(field_index as u32), field_ty),
                        ],
                    },
                    CopyModifiers {
                        init: true,
                        take: true,
                    },
                )),
            ),
            span,
        });
    }

    let entry = body.basic_blocks.push(BasicBlockData {
        note: Some("async-drop-entry".into()),
        statements,
        terminator: Some(Terminator {
            kind: TerminatorKind::Return,
            span,
        }),
    });
    body.start_block = entry;

    (drop_id, body)
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
    body.escape_locals.push(false);
    local
}

fn body_span<'ctx>(body: &Body<'ctx>) -> Span {
    body.locals[body.return_local].span
}

fn raw_ptr_ty<'ctx>(
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

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum AsyncRuntimeFn {
    Create,
    Poll,
    Destroy,
    RunRoot,
    Spawn,
    FromSpawned,
    WaitReadable,
    WaitWritable,
    Sleep,
    YieldNow,
}

pub(crate) fn find_or_register_async_runtime_function<'ctx>(
    gcx: Gcx<'ctx>,
    which: AsyncRuntimeFn,
    span: Span,
) -> DefinitionID {
    let (name, inputs, output) = match which {
        AsyncRuntimeFn::Create => (
            "__rt__async_create",
            vec![
                raw_ptr_ty(gcx, gcx.types.uint8, crate::hir::Mutability::Mutable),
                raw_ptr_ty(gcx, gcx.types.uint8, crate::hir::Mutability::Immutable),
                raw_ptr_ty(gcx, gcx.types.uint8, crate::hir::Mutability::Immutable),
                gcx.types.uint8,
            ],
            gcx.async_handle_ty(),
        ),
        AsyncRuntimeFn::Poll => (
            "__rt__async_poll",
            vec![
                gcx.async_handle_ty(),
                raw_ptr_ty(gcx, gcx.types.uint8, crate::hir::Mutability::Mutable),
            ],
            gcx.types.uint8,
        ),
        AsyncRuntimeFn::Destroy => (
            "__rt__async_destroy",
            vec![gcx.async_handle_ty()],
            gcx.types.void,
        ),
        AsyncRuntimeFn::RunRoot => (
            "__rt__async_run_root",
            vec![
                gcx.async_handle_ty(),
                raw_ptr_ty(gcx, gcx.types.uint8, crate::hir::Mutability::Mutable),
            ],
            gcx.types.void,
        ),
        AsyncRuntimeFn::Spawn => (
            "__rt__executor_spawn",
            vec![gcx.async_handle_ty(), gcx.types.uint],
            gcx.types.uint,
        ),
        AsyncRuntimeFn::FromSpawned => (
            "__rt__async_from_spawned",
            vec![gcx.types.uint],
            gcx.async_handle_ty(),
        ),
        AsyncRuntimeFn::WaitReadable => (
            "__rt__async_wait_readable",
            vec![gcx.types.uint],
            gcx.async_handle_ty(),
        ),
        AsyncRuntimeFn::WaitWritable => (
            "__rt__async_wait_writable",
            vec![gcx.types.uint],
            gcx.async_handle_ty(),
        ),
        AsyncRuntimeFn::Sleep => (
            "__rt__async_sleep",
            vec![gcx.types.uint64, gcx.types.uint32],
            gcx.async_handle_ty(),
        ),
        AsyncRuntimeFn::YieldNow => ("__rt__async_yield_now", vec![], gcx.async_handle_ty()),
    };

    let symbol = gcx.intern_symbol(name);
    if let Some(id) = gcx
        .store
        .synthetic_definitions
        .borrow()
        .iter()
        .find_map(|(id, def)| {
            (gcx.symbol_eq(def.name, name)
                && def.signature.abi == Some(crate::hir::Abi::Runtime)
                && def.signature.inputs.len() == inputs.len()
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
        name: symbol,
        generics: gcx.empty_generics_for_package(gcx.package_index()),
        signature,
        span,
    };
    gcx.register_synthetic_definition(id, def);
    gcx.cache_type(id, Ty::from_labeled_signature(gcx, &signature));
    id
}

fn definition_in_std_module<'ctx>(gcx: Gcx<'ctx>, id: DefinitionID, module: &str) -> bool {
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

fn is_std_testing_yield_now<'ctx>(gcx: Gcx<'ctx>, owner: DefinitionID) -> bool {
    definition_in_std_module(gcx, owner, "testing")
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
                    TyKind::Adt(def, _) if def.kind == AdtKind::Enum => def,
                    _ => return Ty::error(gcx),
                };
                ty = enum_variant_tuple_ty(gcx, def.id, *index);
            }
        }
    }
    ty
}

fn enum_variant_tuple_ty<'ctx>(
    gcx: Gcx<'ctx>,
    def_id: DefinitionID,
    variant_index: crate::thir::VariantIndex,
) -> Ty<'ctx> {
    let def = gcx.get_enum_definition(def_id);
    let variant = def.variants.get(variant_index.index()).unwrap_or_else(|| {
        panic!(
            "ICE: variant index {} out of bounds for enum {:?}",
            variant_index.index(),
            def_id
        )
    });
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

#[allow(dead_code)]
fn synthetic_span() -> Span {
    Span::empty(FileID::from_raw(0))
}
