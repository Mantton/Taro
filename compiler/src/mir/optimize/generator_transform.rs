//! Lowers synchronous generator functions (`func f(...) -> some Iterator[Element = T]`)
//! into:
//! 1. A public constructor body that allocates a GC-traced frame tuple, copies
//!    parameters into the frame (without running any body side effects), and
//!    returns `std::iter::SyncGenerator[T]`.
//! 2. A synthetic step thunk `(*mut uint8, *mut uint8, uint8) -> uint8` that
//!    handles both `next()` (`mode == 0`) and `close()` (`mode == 1`).

use crate::{
    compile::context::Gcx,
    error::{CompileResult, ReportedError},
    hir::{DefinitionID, Mutability, StdItem},
    mir::{
        AggregateKind, BasicBlockData, BasicBlockId, Body, CallUnwindAction, CastKind, Constant,
        ConstantKind, CopyModifiers, LocalDecl, LocalId, LocalKind, Operand, Place, PlaceElem,
        Rvalue, SourceScopeId, Statement, StatementKind, Terminator, TerminatorKind,
        analysis::liveness::compute_block_liveness,
    },
    sema::{
        models::{
            GenericArgument, GenericArguments, GenericParameterDefinition,
            GenericParameterDefinitionKind, Generics, LabeledFunctionParameter,
            LabeledFunctionSignature, SyntheticDefinition, SyntheticDefinitionKind, Ty, TyKind,
        },
        tycheck::utils::generics::GenericsBuilder,
    },
    span::Span,
    thir::{FieldIndex, VariantIndex},
};
use index_vec::IndexVec;
use rustc_hash::FxHashSet;

use super::{
    MirPass,
    async_transform::{AsyncRuntimeFn, find_or_register_async_runtime_function},
};

const FRAME_ALLOCATOR: &str = "$gcSyncGeneratorFrameAllocate";
const MODE_NEXT: u8 = 0;

pub struct GeneratorTransform;

struct GeneratorYieldSite<'ctx> {
    block: BasicBlockId,
    value: Operand<'ctx>,
    resume: BasicBlockId,
    cancel: BasicBlockId,
    cancel_complete: BasicBlockId,
    span: Span,
}

struct GeneratorFrameLayout<'ctx> {
    ty: Ty<'ctx>,
    state_ty: Ty<'ctx>,
    stored_locals: Vec<LocalId>,
    pinned_locals: FxHashSet<LocalId>,
    yield_live_locals: Vec<Vec<LocalId>>,
    done_state: usize,
}

impl<'ctx> MirPass<'ctx> for GeneratorTransform {
    fn name(&self) -> &'static str {
        "GeneratorTransform"
    }

    fn run(&mut self, gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
        let Some(element_ty) = body.generator_element_ty else {
            return Ok(());
        };

        if gcx.async_generator_element_ty(body.owner).is_some() {
            return lower_async_generator(gcx, body, element_ty);
        }

        let span = body_span(body);
        let step_id = register_step_definition(gcx, body.owner, span);
        let mut step_body = body.clone();
        step_body.owner = step_id;
        step_body.generator_element_ty = None;
        step_body.source_scopes[SourceScopeId::from_raw(0)].definition = step_id;

        let frame = lower_step_body(gcx, &mut step_body, element_ty)?;
        let constructor = build_constructor(gcx, body, step_id, element_ty, &frame)?;

        gcx.queue_synthetic_mir_body(step_id, step_body);
        *body = constructor;
        Ok(())
    }
}

fn body_span(body: &Body<'_>) -> Span {
    body.locals[body.return_local].span
}

fn raw_ptr_ty<'ctx>(gcx: Gcx<'ctx>, inner: Ty<'ctx>, mutability: Mutability) -> Ty<'ctx> {
    Ty::new(TyKind::Pointer(inner, mutability), gcx)
}

fn push_local<'ctx>(
    body: &mut Body<'ctx>,
    ty: Ty<'ctx>,
    kind: LocalKind,
    mutable: bool,
    name: Option<crate::span::Symbol>,
    span: Span,
) -> LocalId {
    body.locals.push(LocalDecl {
        ty,
        kind,
        mutable,
        name,
        span,
    })
}

fn const_uint_operand<'ctx>(_gcx: Gcx<'ctx>, ty: Ty<'ctx>, value: u64) -> Operand<'ctx> {
    Operand::Constant(Constant {
        ty,
        value: ConstantKind::Integer(value),
    })
}

fn const_uint8_operand<'ctx>(gcx: Gcx<'ctx>, value: u8) -> Operand<'ctx> {
    Operand::Constant(Constant {
        ty: gcx.types.uint8,
        value: ConstantKind::Integer(u64::from(value)),
    })
}

fn fn_operand<'ctx>(def_id: DefinitionID, args: GenericArguments<'ctx>, ty: Ty<'ctx>) -> Operand<'ctx> {
    Operand::Constant(Constant {
        ty,
        value: ConstantKind::Function(def_id, args, ty),
    })
}

fn frame_state_place<'ctx>(frame_ptr: LocalId, state_ty: Ty<'ctx>) -> Place<'ctx> {
    Place {
        local: frame_ptr,
        projection: vec![PlaceElem::Deref, PlaceElem::Field(FieldIndex::from_raw(0), state_ty)],
    }
}

fn frame_local_place<'ctx>(
    frame: &GeneratorFrameLayout<'ctx>,
    frame_ptr: LocalId,
    local: LocalId,
) -> Place<'ctx> {
    let idx = frame
        .stored_locals
        .iter()
        .position(|&stored| stored == local)
        .expect("resident generator local must be in frame");
    let ty = frame_field_ty(frame, idx);
    Place {
        local: frame_ptr,
        projection: vec![
            PlaceElem::Deref,
            PlaceElem::Field(FieldIndex::from_raw((idx + 1) as u32), ty),
        ],
    }
}

fn frame_field_ty<'ctx>(frame: &GeneratorFrameLayout<'ctx>, local_idx: usize) -> Ty<'ctx> {
    let TyKind::Tuple(items) = frame.ty.kind() else {
        unreachable!("generator frame is always a tuple");
    };
    items[local_idx + 1]
}

fn register_step_definition<'ctx>(
    gcx: Gcx<'ctx>,
    owner: DefinitionID,
    span: Span,
) -> DefinitionID {
    let step_id = gcx.allocate_synthetic_id(owner.package());
    let ptr_u8_mut = raw_ptr_ty(gcx, gcx.types.uint8, Mutability::Mutable);
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
                name: gcx.intern_symbol("out"),
                ty: ptr_u8_mut,
                label: None,
                is_lazy: false,
                default_provider: None,
            },
            LabeledFunctionParameter {
                name: gcx.intern_symbol("mode"),
                ty: gcx.types.uint8,
                label: None,
                is_lazy: false,
                default_provider: None,
            },
        ],
        output: gcx.types.uint8,
        is_variadic: false,
        abi: None,
    };
    let signature = gcx.store.arenas.function_signatures.alloc(signature);
    let owner_name = gcx.definition_symbol_or_fallback(owner);
    let def = SyntheticDefinition {
        kind: SyntheticDefinitionKind::Ordinary,
        name: gcx.intern_symbol(&format!("{}$step", gcx.symbol_text(owner_name))),
        generics: gcx.generics_of(owner),
        signature,
        span,
    };
    gcx.register_synthetic_definition(step_id, def);
    gcx.cache_type(step_id, Ty::from_labeled_signature(gcx, signature));
    step_id
}

fn frame_allocator<'ctx>(gcx: Gcx<'ctx>, span: Span) -> DefinitionID {
    if let Some(id) = gcx
        .store
        .synthetic_definitions
        .borrow()
        .iter()
        .find_map(|(id, def)| {
            (id.package() == gcx.package_index()
                && def.signature.abi == Some(crate::hir::Abi::Intrinsic)
                && gcx.symbol_eq(def.name, FRAME_ALLOCATOR))
            .then_some(*id)
        })
    {
        return id;
    }
    let id = gcx.allocate_synthetic_id(gcx.package_index());
    let parameter = gcx.allocate_synthetic_id(gcx.package_index());
    let name = gcx.intern_symbol("Frame");
    let generics = gcx.store.arenas.generics.alloc(Generics {
        parameters: vec![GenericParameterDefinition {
            is_anonymous: false,
            name,
            id: parameter,
            index: 0,
            kind: GenericParameterDefinitionKind::Type { default: None },
        }],
        has_self: false,
        parent: None,
        parent_count: 0,
    });
    let signature = gcx
        .store
        .arenas
        .function_signatures
        .alloc(LabeledFunctionSignature {
            inputs: vec![],
            output: raw_ptr_ty(gcx, gcx.types.uint8, Mutability::Mutable),
            is_variadic: false,
            abi: Some(crate::hir::Abi::Intrinsic),
        });
    gcx.register_synthetic_definition(
        id,
        SyntheticDefinition {
            kind: SyntheticDefinitionKind::Ordinary,
            name: gcx.intern_symbol(FRAME_ALLOCATOR),
            generics,
            signature,
            span,
        },
    );
    gcx.with_session_type_database(|db| {
        db.def_to_unsafe.insert(id);
    });
    gcx.cache_type(id, Ty::from_labeled_signature(gcx, signature));
    id
}

fn collect_yield_sites<'ctx>(body: &Body<'ctx>) -> Vec<GeneratorYieldSite<'ctx>> {
    let mut sites = Vec::new();
    for bb_id in body.basic_blocks.indices() {
        let Some(term) = body.basic_blocks[bb_id].terminator.as_ref() else {
            continue;
        };
        if let TerminatorKind::GeneratorYield {
            value,
            resume,
            cancel,
            cancel_complete,
        } = &term.kind
        {
            sites.push(GeneratorYieldSite {
                block: bb_id,
                value: value.clone(),
                resume: *resume,
                cancel: *cancel,
                cancel_complete: *cancel_complete,
                span: term.span,
            });
        }
    }
    sites
}

fn build_frame_layout<'ctx>(
    gcx: Gcx<'ctx>,
    body: &Body<'ctx>,
    original_params: &[LocalId],
    yields: &[GeneratorYieldSite<'ctx>],
) -> GeneratorFrameLayout<'ctx> {
    let state_ty = gcx.types.uint;
    let mut pinned = FxHashSet::default();
    for block in &body.basic_blocks {
        for stmt in &block.statements {
            if let StatementKind::Assign(
                _,
                Rvalue::Ref { place, .. } | Rvalue::CleanupAddress { place },
            ) = &stmt.kind
                && !place.projection.contains(&PlaceElem::Deref)
            {
                pinned.insert(place.local);
            }
        }
    }

    let liveness = compute_block_liveness(body);
    let start_live = &liveness.live_in[body.start_block];
    let yield_live_locals: Vec<Vec<LocalId>> = yields
        .iter()
        .map(|site| {
            let resume_live = &liveness.live_in[site.resume];
            let cancel_live = &liveness.live_in[site.cancel];
            body.locals
                .indices()
                .filter(|local| resume_live.contains(local) || cancel_live.contains(local))
                .collect()
        })
        .collect();

    let stored_locals: Vec<LocalId> = body
        .locals
        .indices()
        .filter(|local| {
            original_params.contains(local)
                || start_live.contains(local)
                || yield_live_locals.iter().any(|live| live.contains(local))
                || pinned.contains(local)
        })
        .collect();

    let mut fields = Vec::with_capacity(stored_locals.len() + 1);
    fields.push(state_ty);
    fields.extend(stored_locals.iter().map(|&local| body.locals[local].ty));
    let frame_ty = Ty::new(
        TyKind::Tuple(gcx.store.interners.intern_ty_list(fields)),
        gcx,
    );

    GeneratorFrameLayout {
        ty: frame_ty,
        state_ty,
        stored_locals,
        pinned_locals: pinned,
        yield_live_locals,
        done_state: yields.len() + 1,
    }
}

fn remap_place<'ctx>(place: &mut Place<'ctx>, remaps: &[Option<Place<'ctx>>]) {
    if let Some(Some(replacement)) = remaps.get(place.local.index()) {
        let mut projection = replacement.projection.clone();
        projection.extend(place.projection.iter().cloned());
        place.local = replacement.local;
        place.projection = projection;
    }
}

fn remap_operand<'ctx>(operand: &mut Operand<'ctx>, remaps: &[Option<Place<'ctx>>]) {
    if let Some(place) = operand.place_mut() {
        remap_place(place, remaps);
    }
}

fn rewrite_resident_places<'ctx>(
    body: &mut Body<'ctx>,
    frame: &GeneratorFrameLayout<'ctx>,
    frame_ptr: LocalId,
    yields: &mut [GeneratorYieldSite<'ctx>],
) {
    let remaps: Vec<Option<Place<'ctx>>> = body
        .locals
        .indices()
        .map(|local| {
            frame
                .stored_locals
                .contains(&local)
                .then(|| frame_local_place(frame, frame_ptr, local))
        })
        .collect();

    for block in body.basic_blocks.iter_mut() {
        for stmt in &mut block.statements {
            match &mut stmt.kind {
                StatementKind::SourceScope(_)
                | StatementKind::StorageLive(_)
                | StatementKind::StorageDead(_)
                | StatementKind::SetInitialized(_)
                | StatementKind::GcSafepoint(_)
                | StatementKind::Nop => {}
                StatementKind::Assign(dest, rvalue) => {
                    remap_place(dest, &remaps);
                    rvalue.for_each_place_mut(|place| remap_place(place, &remaps));
                }
                StatementKind::SetDiscriminant { place, .. } => {
                    remap_place(place, &remaps);
                }
                StatementKind::KeepAlive(operand) => remap_operand(operand, &remaps),
            }
        }
        let Some(term) = &mut block.terminator else {
            continue;
        };
        match &mut term.kind {
            TerminatorKind::SwitchInt { discr, .. } => remap_operand(discr, &remaps),
            TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } => {
                remap_operand(func, &remaps);
                for arg in args {
                    remap_operand(arg, &remaps);
                }
                remap_place(destination, &remaps);
            }
            TerminatorKind::Yield {
                value, resume_arg, ..
            } => {
                remap_operand(value, &remaps);
                remap_place(resume_arg, &remaps);
            }
            TerminatorKind::GeneratorYield { value, .. } => {
                remap_operand(value, &remaps);
            }
            TerminatorKind::Goto { .. }
            | TerminatorKind::Return
            | TerminatorKind::ResumeUnwind
            | TerminatorKind::Unreachable
            | TerminatorKind::UnresolvedGoto => {}
        }
    }

    for site in yields {
        remap_operand(&mut site.value, &remaps);
    }
}

fn clear_frame_fields<'ctx>(
    frame: &GeneratorFrameLayout<'ctx>,
    keep_locals: Option<&[LocalId]>,
    frame_ptr: LocalId,
    span: Span,
) -> Vec<Statement<'ctx>> {
    frame
        .stored_locals
        .iter()
        .enumerate()
        .filter(|(_, local)| {
            keep_locals.is_none_or(|live| !live.contains(local) && !frame.pinned_locals.contains(local))
        })
        .filter_map(|(idx, &local)| {
            let ty = frame_field_ty(frame, idx);
            let scalar = matches!(
                ty.kind(),
                TyKind::Bool | TyKind::Rune | TyKind::Int(_) | TyKind::UInt(_) | TyKind::Float(_)
            ) || matches!(ty.kind(), TyKind::Tuple(items) if items.is_empty());
            (!scalar).then(|| Statement {
                kind: StatementKind::Assign(
                    frame_local_place(frame, frame_ptr, local),
                    Rvalue::Zeroed { ty },
                ),
                span,
            })
        })
        .collect()
}

fn lower_step_body<'ctx>(
    gcx: Gcx<'ctx>,
    body: &mut Body<'ctx>,
    element_ty: Ty<'ctx>,
) -> CompileResult<GeneratorFrameLayout<'ctx>> {
    let span = body_span(body);
    let original_start = body.start_block;
    let original_return_local = body.return_local;
    body.locals[original_return_local].kind = LocalKind::Temp;
    body.locals[original_return_local].mutable = true;

    let original_params: Vec<LocalId> = body
        .locals
        .iter_enumerated()
        .filter_map(|(local, decl)| matches!(decl.kind, LocalKind::Param).then_some(local))
        .collect();
    for &local in &original_params {
        body.locals[local].kind = LocalKind::Temp;
        body.locals[local].mutable = true;
    }

    let mut yields = collect_yield_sites(body);
    let frame = build_frame_layout(gcx, body, &original_params, &yields);

    let ptr_u8_mut = raw_ptr_ty(gcx, gcx.types.uint8, Mutability::Mutable);
    let frame_ptr_ty = raw_ptr_ty(gcx, frame.ty, Mutability::Mutable);
    let out_ptr_ty = raw_ptr_ty(gcx, element_ty, Mutability::Mutable);

    let tag_return = push_local(
        body,
        gcx.types.uint8,
        LocalKind::Return,
        true,
        Some(gcx.intern_symbol("$gen_tag")),
        span,
    );
    body.return_local = tag_return;
    let frame_raw = push_local(
        body,
        ptr_u8_mut,
        LocalKind::Param,
        false,
        Some(gcx.intern_symbol("$frame")),
        span,
    );
    let out_raw = push_local(
        body,
        ptr_u8_mut,
        LocalKind::Param,
        false,
        Some(gcx.intern_symbol("$out")),
        span,
    );
    let mode_local = push_local(
        body,
        gcx.types.uint8,
        LocalKind::Param,
        false,
        Some(gcx.intern_symbol("$mode")),
        span,
    );
    let frame_ptr = push_local(
        body,
        frame_ptr_ty,
        LocalKind::Temp,
        true,
        Some(gcx.intern_symbol("$frame_ptr")),
        span,
    );
    let out_ptr = push_local(
        body,
        out_ptr_ty,
        LocalKind::Temp,
        true,
        Some(gcx.intern_symbol("$out_ptr")),
        span,
    );
    let state_local = push_local(
        body,
        frame.state_ty,
        LocalKind::Temp,
        true,
        Some(gcx.intern_symbol("$state")),
        span,
    );

    rewrite_resident_places(body, &frame, frame_ptr, &mut yields);

    // Exhausted/closed completion block: zeroes all frame fields, publishes
    // `done_state`, and returns 0 (.none).
    let mut finish_stmts = clear_frame_fields(&frame, None, frame_ptr, span);
    finish_stmts.push(Statement {
        kind: StatementKind::Assign(
            frame_state_place(frame_ptr, frame.state_ty),
            Rvalue::Use(const_uint_operand(gcx, frame.state_ty, frame.done_state as u64)),
        ),
        span,
    });
    finish_stmts.push(Statement {
        kind: StatementKind::Assign(
            Place::from_local(tag_return),
            Rvalue::Use(const_uint8_operand(gcx, 0)),
        ),
        span,
    });
    let finish_done = body.basic_blocks.push(BasicBlockData {
        note: Some("gen-finish-done".into()),
        statements: finish_stmts,
        terminator: Some(Terminator {
            kind: TerminatorKind::Return,
            span,
        }),
    });

    // Fast path when already exhausted or closed.
    let already_done = body.basic_blocks.push(BasicBlockData {
        note: Some("gen-already-done".into()),
        statements: vec![Statement {
            kind: StatementKind::Assign(
                Place::from_local(tag_return),
                Rvalue::Use(const_uint8_operand(gcx, 0)),
            ),
            span,
        }],
        terminator: Some(Terminator {
            kind: TerminatorKind::Return,
            span,
        }),
    });

    // Redirect all existing `Return` terminators in the generator body to `finish_done`.
    for bb_id in body.basic_blocks.indices() {
        if bb_id == finish_done || bb_id == already_done {
            continue;
        }
        if let Some(term) = body.basic_blocks[bb_id].terminator.as_mut()
            && matches!(term.kind, TerminatorKind::Return)
        {
            term.kind = TerminatorKind::Goto { target: finish_done };
        }
    }

    // Rewrite every `GeneratorYield` site to store the yielded value into `*out_ptr`,
    // clear dead frame fields, save the resume state, and return 1 (.some).
    // Also patch each site's `cancel_complete` block to jump to `finish_done`.
    for (index, site) in yields.iter().enumerate() {
        let resume_state = (index + 1) as u64;
        if element_ty != gcx.types.void {
            body.basic_blocks[site.block].statements.push(Statement {
                kind: StatementKind::Assign(
                    Place {
                        local: out_ptr,
                        projection: vec![PlaceElem::Deref],
                    },
                    Rvalue::Use(site.value.clone()),
                ),
                span: site.span,
            });
        }
        body.basic_blocks[site.block]
            .statements
            .extend(clear_frame_fields(
                &frame,
                Some(&frame.yield_live_locals[index]),
                frame_ptr,
                site.span,
            ));
        body.basic_blocks[site.block].statements.push(Statement {
            kind: StatementKind::Assign(
                frame_state_place(frame_ptr, frame.state_ty),
                Rvalue::Use(const_uint_operand(gcx, frame.state_ty, resume_state)),
            ),
            span: site.span,
        });
        body.basic_blocks[site.block].statements.push(Statement {
            kind: StatementKind::Assign(
                Place::from_local(tag_return),
                Rvalue::Use(const_uint8_operand(gcx, 1)),
            ),
            span: site.span,
        });
        body.basic_blocks[site.block].terminator = Some(Terminator {
            kind: TerminatorKind::Return,
            span: site.span,
        });

        body.basic_blocks[site.cancel_complete].terminator = Some(Terminator {
            kind: TerminatorKind::Goto {
                target: finish_done,
            },
            span: site.span,
        });
    }

    // Build trampolines that set state = done_state before entering body/resume/cancel
    // so an unwinding panic never leaves the generator in a re-enterable state.
    let make_trampoline = |body: &mut Body<'ctx>, note: &str, target: BasicBlockId, s: Span| {
        body.basic_blocks.push(BasicBlockData {
            note: Some(note.into()),
            statements: vec![Statement {
                kind: StatementKind::Assign(
                    frame_state_place(frame_ptr, frame.state_ty),
                    Rvalue::Use(const_uint_operand(
                        gcx,
                        frame.state_ty,
                        frame.done_state as u64,
                    )),
                ),
                span: s,
            }],
            terminator: Some(Terminator {
                kind: TerminatorKind::Goto { target },
                span: s,
            }),
        })
    };

    let start_trampoline = make_trampoline(body, "gen-start", original_start, span);
    let mut next_targets = vec![(0u128, start_trampoline)];
    let mut close_targets = vec![(0u128, finish_done)];
    for (index, site) in yields.iter().enumerate() {
        let state_val = (index + 1) as u128;
        let resume_tramp = make_trampoline(body, "gen-resume", site.resume, site.span);
        next_targets.push((state_val, resume_tramp));
        let close_tramp = make_trampoline(body, "gen-close", site.cancel, site.span);
        close_targets.push((state_val, close_tramp));
    }

    let next_dispatch = body.basic_blocks.push(BasicBlockData {
        note: Some("gen-next-dispatch".into()),
        statements: vec![],
        terminator: Some(Terminator {
            kind: TerminatorKind::SwitchInt {
                discr: Operand::Copy(Place::from_local(state_local)),
                targets: next_targets,
                otherwise: already_done,
            },
            span,
        }),
    });

    let close_dispatch = body.basic_blocks.push(BasicBlockData {
        note: Some("gen-close-dispatch".into()),
        statements: vec![],
        terminator: Some(Terminator {
            kind: TerminatorKind::SwitchInt {
                discr: Operand::Copy(Place::from_local(state_local)),
                targets: close_targets,
                otherwise: already_done,
            },
            span,
        }),
    });

    let entry = body.basic_blocks.push(BasicBlockData {
        note: Some("gen-entry".into()),
        statements: vec![
            Statement {
                kind: StatementKind::Assign(
                    Place::from_local(frame_ptr),
                    Rvalue::Cast {
                        operand: Operand::Copy(Place::from_local(frame_raw)),
                        ty: frame_ptr_ty,
                        kind: CastKind::Pointer,
                    },
                ),
                span,
            },
            Statement {
                kind: StatementKind::Assign(
                    Place::from_local(out_ptr),
                    Rvalue::Cast {
                        operand: Operand::Copy(Place::from_local(out_raw)),
                        ty: out_ptr_ty,
                        kind: CastKind::Pointer,
                    },
                ),
                span,
            },
            Statement {
                kind: StatementKind::Assign(
                    Place::from_local(state_local),
                    Rvalue::Use(Operand::Copy(frame_state_place(frame_ptr, frame.state_ty))),
                ),
                span,
            },
        ],
        terminator: Some(Terminator {
            kind: TerminatorKind::SwitchInt {
                discr: Operand::Copy(Place::from_local(mode_local)),
                targets: vec![(u128::from(MODE_NEXT), next_dispatch)],
                otherwise: close_dispatch,
            },
            span,
        }),
    });

    body.start_block = entry;
    Ok(frame)
}

fn build_constructor<'ctx>(
    gcx: Gcx<'ctx>,
    original: &Body<'ctx>,
    step_id: DefinitionID,
    element_ty: Ty<'ctx>,
    frame: &GeneratorFrameLayout<'ctx>,
) -> CompileResult<Body<'ctx>> {
    let span = body_span(original);
    let Some(sync_gen_def) = gcx.std_item_def(StdItem::SyncGenerator) else {
        gcx.dcx().emit_error(
            "internal error: missing `SyncGenerator` std item during generator lowering".into(),
            Some(span),
        );
        return Err(ReportedError);
    };
    let adt_def = gcx.get_struct_definition(sync_gen_def).adt_def;
    let gen_args = gcx
        .store
        .interners
        .intern_generic_args(vec![GenericArgument::Type(element_ty)]);
    let sync_gen_ty = Ty::new(TyKind::Adt(adt_def, gen_args), gcx);

    let ptr_u8_mut = raw_ptr_ty(gcx, gcx.types.uint8, Mutability::Mutable);
    let frame_ptr_ty = raw_ptr_ty(gcx, frame.ty, Mutability::Mutable);

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

    let ret_local = push_local(
        &mut body,
        sync_gen_ty,
        LocalKind::Return,
        true,
        Some(gcx.intern_symbol("$gen_ret")),
        span,
    );
    body.return_local = ret_local;

    let orig_params: Vec<_> = original
        .locals
        .iter_enumerated()
        .filter_map(|(local, decl)| matches!(decl.kind, LocalKind::Param).then_some((local, decl)))
        .collect();
    let ctor_params: Vec<_> = orig_params
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

    let frame_raw = push_local(
        &mut body,
        ptr_u8_mut,
        LocalKind::Temp,
        true,
        Some(gcx.intern_symbol("$frame_raw")),
        span,
    );
    let frame_ptr = push_local(
        &mut body,
        frame_ptr_ty,
        LocalKind::Temp,
        true,
        Some(gcx.intern_symbol("$frame_ptr")),
        span,
    );

    let mut init_stmts = vec![Statement {
        kind: StatementKind::Assign(
            Place::from_local(frame_ptr),
            Rvalue::Cast {
                operand: Operand::Copy(Place::from_local(frame_raw)),
                ty: frame_ptr_ty,
                kind: CastKind::Pointer,
            },
        ),
        span,
    }];

    for ((orig_local, _), ctor_local) in orig_params.iter().zip(ctor_params.iter()) {
        if !frame.stored_locals.contains(orig_local) {
            continue;
        }
        init_stmts.push(Statement {
            kind: StatementKind::Assign(
                frame_local_place(frame, frame_ptr, *orig_local),
                Rvalue::Use(Operand::CopyWith(
                    Place::from_local(*ctor_local),
                    CopyModifiers { init: true },
                )),
            ),
            span,
        });
    }

    let step_fn_ty = gcx.get_type(step_id);
    let step_fn_operand = fn_operand(
        step_id,
        GenericsBuilder::identity_for_item(gcx, step_id),
        step_fn_ty,
    );
    init_stmts.push(Statement {
        kind: StatementKind::Assign(
            Place::from_local(ret_local),
            Rvalue::Aggregate {
                kind: AggregateKind::Adt {
                    def_id: sync_gen_def,
                    variant_index: None,
                    generic_args: gen_args,
                },
                fields: IndexVec::from_vec(vec![
                    Operand::Copy(Place::from_local(frame_raw)),
                    step_fn_operand,
                ]),
            },
        ),
        span,
    });

    let init_block = body.basic_blocks.push(BasicBlockData {
        note: Some("gen-ctor-init".into()),
        statements: init_stmts,
        terminator: Some(Terminator {
            kind: TerminatorKind::Return,
            span,
        }),
    });

    let allocate = frame_allocator(gcx, span);
    let alloc_args = gcx
        .store
        .interners
        .intern_generic_args(vec![GenericArgument::Type(frame.ty)]);
    let entry = body.basic_blocks.push(BasicBlockData {
        note: Some("gen-ctor-alloc".into()),
        statements: vec![],
        terminator: Some(Terminator {
            kind: TerminatorKind::Call {
                func: fn_operand(allocate, alloc_args, gcx.get_type(allocate)),
                args: vec![],
                destination: Place::from_local(frame_raw),
                target: init_block,
                unwind: CallUnwindAction::Terminate,
            },
            span,
        }),
    });
    body.start_block = entry;
    Ok(body)
}

// ============================================================================
// Async generator lowering (TAR-49)
// ============================================================================

#[derive(Clone)]
struct AsyncAwaitSite<'ctx> {
    block: BasicBlockId,
    future: Operand<'ctx>,
    resume: BasicBlockId,
    resume_arg: Place<'ctx>,
    no_result: Option<BasicBlockId>,
    cancel: BasicBlockId,
    cancel_complete: BasicBlockId,
    unwind: CallUnwindAction,
    span: Span,
}

struct AsyncGeneratorFrameLayout<'ctx> {
    base: GeneratorFrameLayout<'ctx>,
    await_live_locals: Vec<Vec<LocalId>>,
}

fn lower_async_generator<'ctx>(
    gcx: Gcx<'ctx>,
    body: &mut Body<'ctx>,
    element_ty: Ty<'ctx>,
) -> CompileResult<()> {
    let span = body_span(body);
    let poll_id = register_async_gen_poll_definition(gcx, body.owner, span);
    let close_id = register_async_gen_close_definition(gcx, body.owner, span);

    let mut poll_body = body.clone();
    poll_body.owner = poll_id;
    poll_body.generator_element_ty = None;
    poll_body.is_async = false;
    poll_body.source_scopes[SourceScopeId::from_raw(0)].definition = poll_id;

    let mut close_body = body.clone();
    close_body.owner = close_id;
    close_body.generator_element_ty = None;
    close_body.is_async = false;
    close_body.source_scopes[SourceScopeId::from_raw(0)].definition = close_id;

    let original_params: Vec<LocalId> = poll_body
        .locals
        .iter_enumerated()
        .filter_map(|(id, decl)| matches!(decl.kind, LocalKind::Param).then_some(id))
        .collect();

    let mut await_sites = collect_await_sites(&poll_body);
    let mut yield_sites = collect_yield_sites(&poll_body);
    let frame = build_async_gen_frame_layout(gcx, &poll_body, &original_params, &await_sites, &yield_sites);

    lower_async_gen_poll_body(
        gcx,
        &mut poll_body,
        element_ty,
        &frame,
        &mut await_sites,
        &mut yield_sites,
    )?;

    lower_async_gen_close_body(gcx, &mut close_body, &frame, await_sites.len())?;

    let constructor = build_async_gen_constructor(
        gcx,
        body,
        poll_id,
        close_id,
        element_ty,
        &frame.base,
    )?;

    gcx.queue_synthetic_mir_body(poll_id, poll_body);
    gcx.queue_synthetic_mir_body(close_id, close_body);
    *body = constructor;
    Ok(())
}

fn register_async_gen_poll_definition<'ctx>(
    gcx: Gcx<'ctx>,
    owner: DefinitionID,
    span: Span,
) -> DefinitionID {
    let poll_id = gcx.allocate_synthetic_id(owner.package());
    let ptr_u8_mut = raw_ptr_ty(gcx, gcx.types.uint8, Mutability::Mutable);
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
    let signature = gcx.store.arenas.function_signatures.alloc(signature);
    let owner_name = gcx.definition_symbol_or_fallback(owner);
    gcx.register_synthetic_definition(
        poll_id,
        SyntheticDefinition {
            kind: SyntheticDefinitionKind::AsyncPoll,
            name: gcx.intern_symbol(&format!("{}$gen_poll", gcx.symbol_text(owner_name))),
            generics: gcx.generics_of(owner),
            signature,
            span,
        },
    );
    gcx.cache_type(poll_id, Ty::from_labeled_signature(gcx, signature));
    poll_id
}

fn register_async_gen_close_definition<'ctx>(
    gcx: Gcx<'ctx>,
    owner: DefinitionID,
    span: Span,
) -> DefinitionID {
    let close_id = gcx.allocate_synthetic_id(owner.package());
    let ptr_u8_mut = raw_ptr_ty(gcx, gcx.types.uint8, Mutability::Mutable);
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
    let signature = gcx.store.arenas.function_signatures.alloc(signature);
    let owner_name = gcx.definition_symbol_or_fallback(owner);
    gcx.register_synthetic_definition(
        close_id,
        SyntheticDefinition {
            kind: SyntheticDefinitionKind::Ordinary,
            name: gcx.intern_symbol(&format!("{}$gen_close", gcx.symbol_text(owner_name))),
            generics: gcx.generics_of(owner),
            signature,
            span,
        },
    );
    gcx.cache_type(close_id, Ty::from_labeled_signature(gcx, signature));
    close_id
}

fn collect_await_sites<'ctx>(body: &Body<'ctx>) -> Vec<AsyncAwaitSite<'ctx>> {
    let mut sites = Vec::new();
    for bb_id in body.basic_blocks.indices() {
        let Some(term) = body.basic_blocks[bb_id].terminator.as_ref() else {
            continue;
        };
        if let TerminatorKind::Yield {
            value,
            resume,
            resume_arg,
            no_result,
            cancel,
            cancel_complete,
            unwind,
        } = &term.kind
        {
            sites.push(AsyncAwaitSite {
                block: bb_id,
                future: value.clone(),
                resume: *resume,
                resume_arg: resume_arg.clone(),
                no_result: *no_result,
                cancel: *cancel,
                cancel_complete: *cancel_complete,
                unwind: *unwind,
                span: term.span,
            });
        }
    }
    sites
}

fn build_async_gen_frame_layout<'ctx>(
    gcx: Gcx<'ctx>,
    body: &Body<'ctx>,
    original_params: &[LocalId],
    awaits: &[AsyncAwaitSite<'ctx>],
    yields: &[GeneratorYieldSite<'ctx>],
) -> AsyncGeneratorFrameLayout<'ctx> {
    let state_ty = gcx.types.uint;
    let mut pinned = FxHashSet::default();
    for block in &body.basic_blocks {
        for stmt in &block.statements {
            if let StatementKind::Assign(
                _,
                Rvalue::Ref { place, .. } | Rvalue::CleanupAddress { place },
            ) = &stmt.kind
                && !place.projection.contains(&PlaceElem::Deref)
            {
                pinned.insert(place.local);
            }
        }
    }

    let liveness = compute_block_liveness(body);
    let start_live = &liveness.live_in[body.start_block];

    let await_live_locals: Vec<Vec<LocalId>> = awaits
        .iter()
        .map(|site| {
            let resume_live = &liveness.live_in[site.resume];
            let cancel_live = &liveness.live_in[site.cancel];
            let no_result_live = site.no_result.map(|b| &liveness.live_in[b]);
            let future_local = site.future.place().map(|p| p.local);
            body.locals
                .indices()
                .filter(|local| {
                    resume_live.contains(local)
                        || cancel_live.contains(local)
                        || no_result_live.is_some_and(|set| set.contains(local))
                        || future_local == Some(*local)
                })
                .collect()
        })
        .collect();

    let yield_live_locals: Vec<Vec<LocalId>> = yields
        .iter()
        .map(|site| {
            let resume_live = &liveness.live_in[site.resume];
            let cancel_live = &liveness.live_in[site.cancel];
            body.locals
                .indices()
                .filter(|local| resume_live.contains(local) || cancel_live.contains(local))
                .collect()
        })
        .collect();

    let stored_locals: Vec<LocalId> = body
        .locals
        .indices()
        .filter(|local| {
            original_params.contains(local)
                || start_live.contains(local)
                || await_live_locals.iter().any(|live| live.contains(local))
                || yield_live_locals.iter().any(|live| live.contains(local))
                || pinned.contains(local)
        })
        .collect();

    let mut fields = Vec::with_capacity(stored_locals.len() + 1);
    fields.push(state_ty);
    fields.extend(stored_locals.iter().map(|&local| body.locals[local].ty));
    let frame_ty = Ty::new(
        TyKind::Tuple(gcx.store.interners.intern_ty_list(fields)),
        gcx,
    );

    AsyncGeneratorFrameLayout {
        base: GeneratorFrameLayout {
            ty: frame_ty,
            state_ty,
            stored_locals,
            pinned_locals: pinned,
            yield_live_locals,
            done_state: awaits.len() + yields.len() + 1,
        },
        await_live_locals,
    }
}

fn optional_type_and_variants<'ctx>(
    gcx: Gcx<'ctx>,
    element_ty: Ty<'ctx>,
    span: Span,
) -> CompileResult<(DefinitionID, GenericArguments<'ctx>, Ty<'ctx>, VariantIndex, VariantIndex)> {
    let Some(opt_def) = gcx.std_item_def(StdItem::Optional) else {
        gcx.dcx().emit_error(
            "internal error: missing `Optional` std item during async generator lowering".into(),
            Some(span),
        );
        return Err(ReportedError);
    };
    let enum_def = gcx.get_enum_definition(opt_def);
    let some_idx = enum_def
        .variants
        .iter()
        .position(|v| gcx.symbol_eq(v.name, "some"))
        .map(VariantIndex::from_usize)
        .unwrap_or_else(|| VariantIndex::from_usize(0));
    let none_idx = enum_def
        .variants
        .iter()
        .position(|v| gcx.symbol_eq(v.name, "none"))
        .map(VariantIndex::from_usize)
        .unwrap_or_else(|| VariantIndex::from_usize(1));
    let opt_args = gcx
        .store
        .interners
        .intern_generic_args(vec![GenericArgument::Type(element_ty)]);
    let opt_ty = Ty::new(TyKind::Adt(enum_def.adt_def, opt_args), gcx);
    Ok((opt_def, opt_args, opt_ty, some_idx, none_idx))
}

fn rewrite_async_gen_resident_places<'ctx>(
    body: &mut Body<'ctx>,
    frame: &GeneratorFrameLayout<'ctx>,
    frame_ptr: LocalId,
    awaits: &mut [AsyncAwaitSite<'ctx>],
    yields: &mut [GeneratorYieldSite<'ctx>],
) {
    rewrite_resident_places(body, frame, frame_ptr, yields);
    let remaps: Vec<Option<Place<'ctx>>> = body
        .locals
        .indices()
        .map(|local| {
            frame
                .stored_locals
                .contains(&local)
                .then(|| frame_local_place(frame, frame_ptr, local))
        })
        .collect();
    for site in awaits {
        remap_operand(&mut site.future, &remaps);
        remap_place(&mut site.resume_arg, &remaps);
    }
}

fn lower_async_gen_poll_body<'ctx>(
    gcx: Gcx<'ctx>,
    body: &mut Body<'ctx>,
    element_ty: Ty<'ctx>,
    frame: &AsyncGeneratorFrameLayout<'ctx>,
    awaits: &mut [AsyncAwaitSite<'ctx>],
    yields: &mut [GeneratorYieldSite<'ctx>],
) -> CompileResult<()> {
    let span = body_span(body);
    let original_start = body.start_block;
    let (opt_def, opt_args, opt_ty, some_idx, none_idx) =
        optional_type_and_variants(gcx, element_ty, span)?;

    // Convert original params and return local into ordinary locals before
    // installing the poll thunk signature: (frame, ctx, out) -> uint8.
    for decl in body.locals.iter_mut() {
        if matches!(decl.kind, LocalKind::Param | LocalKind::Return) {
            decl.kind = LocalKind::Temp;
            decl.mutable = true;
        }
    }

    let ptr_u8_mut = raw_ptr_ty(gcx, gcx.types.uint8, Mutability::Mutable);
    let frame_ptr_ty = raw_ptr_ty(gcx, frame.base.ty, Mutability::Mutable);
    let out_ptr_ty = raw_ptr_ty(gcx, opt_ty, Mutability::Mutable);

    let frame_raw = push_local(
        body,
        ptr_u8_mut,
        LocalKind::Param,
        false,
        Some(gcx.intern_symbol("$frame_raw")),
        span,
    );
    let _ctx_raw = push_local(
        body,
        ptr_u8_mut,
        LocalKind::Param,
        false,
        Some(gcx.intern_symbol("$ctx_raw")),
        span,
    );
    let out_raw = push_local(
        body,
        ptr_u8_mut,
        LocalKind::Param,
        false,
        Some(gcx.intern_symbol("$out_raw")),
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
        frame_ptr_ty,
        LocalKind::Temp,
        true,
        Some(gcx.intern_symbol("$frame_ptr")),
        span,
    );
    let out_ptr = push_local(
        body,
        out_ptr_ty,
        LocalKind::Temp,
        true,
        Some(gcx.intern_symbol("$out_ptr")),
        span,
    );
    let state_local = push_local(
        body,
        frame.base.state_ty,
        LocalKind::Temp,
        true,
        Some(gcx.intern_symbol("$state")),
        span,
    );
    body.return_local = tag_return;

    rewrite_async_gen_resident_places(body, &frame.base, frame_ptr, awaits, yields);

    // 1. Rewrite normal returns (end of body or bare `return`):
    //    *out_ptr = Optional::none; frame.state = done_state; clear frame; return 1_u8.
    let return_blocks: Vec<BasicBlockId> = body
        .basic_blocks
        .indices()
        .filter(|&bb| {
            body.basic_blocks[bb]
                .terminator
                .as_ref()
                .is_some_and(|t| matches!(t.kind, TerminatorKind::Return))
        })
        .collect();
    for bb in return_blocks {
        let ret_span = body.basic_blocks[bb].terminator.as_ref().unwrap().span;
        body.basic_blocks[bb].statements.push(Statement {
            kind: StatementKind::Assign(
                Place {
                    local: out_ptr,
                    projection: vec![PlaceElem::Deref],
                },
                Rvalue::Aggregate {
                    kind: AggregateKind::Adt {
                        def_id: opt_def,
                        variant_index: Some(none_idx),
                        generic_args: opt_args,
                    },
                    fields: IndexVec::new(),
                },
            ),
            span: ret_span,
        });
        body.basic_blocks[bb].statements.push(Statement {
            kind: StatementKind::Assign(
                frame_state_place(frame_ptr, frame.base.state_ty),
                Rvalue::Use(const_uint_operand(
                    gcx,
                    frame.base.state_ty,
                    frame.base.done_state as u64,
                )),
            ),
            span: ret_span,
        });
        body.basic_blocks[bb]
            .statements
            .extend(clear_frame_fields(&frame.base, None, frame_ptr, ret_span));
        body.basic_blocks[bb].statements.push(Statement {
            kind: StatementKind::Assign(
                Place::from_local(tag_return),
                Rvalue::Use(const_uint8_operand(gcx, 1)),
            ),
            span: ret_span,
        });
    }

    // 2. Rewrite GeneratorYield sites (`yield value`):
    //    *out_ptr = Optional::some(value);
    //    frame.state = 1 + awaits.len() + index;
    //    clear dead frame fields;
    //    return 1_u8.
    for (index, site) in yields.iter().enumerate() {
        let resume_state = 1 + awaits.len() + index;
        body.basic_blocks[site.block].statements.push(Statement {
            kind: StatementKind::Assign(
                Place {
                    local: out_ptr,
                    projection: vec![PlaceElem::Deref],
                },
                Rvalue::Aggregate {
                    kind: AggregateKind::Adt {
                        def_id: opt_def,
                        variant_index: Some(some_idx),
                        generic_args: opt_args,
                    },
                    fields: IndexVec::from_vec(vec![site.value.clone()]),
                },
            ),
            span: site.span,
        });
        body.basic_blocks[site.block].statements.push(Statement {
            kind: StatementKind::Assign(
                frame_state_place(frame_ptr, frame.base.state_ty),
                Rvalue::Use(const_uint_operand(
                    gcx,
                    frame.base.state_ty,
                    resume_state as u64,
                )),
            ),
            span: site.span,
        });
        body.basic_blocks[site.block]
            .statements
            .extend(clear_frame_fields(
                &frame.base,
                Some(&frame.base.yield_live_locals[index]),
                frame_ptr,
                site.span,
            ));
        body.basic_blocks[site.block].statements.push(Statement {
            kind: StatementKind::Assign(
                Place::from_local(tag_return),
                Rvalue::Use(const_uint8_operand(gcx, 1)),
            ),
            span: site.span,
        });
        body.basic_blocks[site.block].terminator = Some(Terminator {
            kind: TerminatorKind::Return,
            span: site.span,
        });
        // GeneratorYield cancel path is executed by `$gen_close`, not `$gen_poll`.
        body.basic_blocks[site.cancel_complete].terminator = Some(Terminator {
            kind: TerminatorKind::Unreachable,
            span: site.span,
        });
    }

    // 3. Rewrite async await sites (`TerminatorKind::Yield`):
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

    let mut await_poll_blocks = Vec::with_capacity(awaits.len());
    for (index, site) in awaits.iter().enumerate() {
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
            Some(gcx.intern_symbol("$gen_await_handle")),
            site.span,
        );
        let ready_storage_local = push_local(
            body,
            ready_storage_ty,
            LocalKind::Temp,
            true,
            Some(gcx.intern_symbol("$gen_await_ready")),
            site.span,
        );
        let ready_ref_local = push_local(
            body,
            gcx.store
                .interners
                .intern_ty(TyKind::Reference(ready_storage_ty)),
            LocalKind::Temp,
            true,
            Some(gcx.intern_symbol("$gen_await_ready_ref")),
            site.span,
        );
        let ready_ptr_local = push_local(
            body,
            raw_ptr_ty(gcx, ready_storage_ty, Mutability::Mutable),
            LocalKind::Temp,
            true,
            Some(gcx.intern_symbol("$gen_await_ready_ptr")),
            site.span,
        );
        let ready_raw_local = push_local(
            body,
            ptr_u8_mut,
            LocalKind::Temp,
            true,
            Some(gcx.intern_symbol("$gen_await_ready_raw")),
            site.span,
        );
        let tag_local = push_local(
            body,
            gcx.types.uint8,
            LocalKind::Temp,
            true,
            Some(gcx.intern_symbol("$gen_await_tag")),
            site.span,
        );
        let cancelled_local = push_local(
            body,
            gcx.types.bool,
            LocalKind::Temp,
            true,
            Some(gcx.intern_symbol("$gen_await_cancelled")),
            site.span,
        );
        let destroy_void_local = push_local(
            body,
            gcx.types.void,
            LocalKind::Temp,
            true,
            Some(gcx.intern_symbol("$gen_await_destroy_void")),
            site.span,
        );

        // Cancellation cleanup completion: mark frame done, clear all fields, return tag 2.
        body.basic_blocks[site.cancel_complete]
            .statements
            .push(Statement {
                kind: StatementKind::Assign(
                    frame_state_place(frame_ptr, frame.base.state_ty),
                    Rvalue::Use(const_uint_operand(
                        gcx,
                        frame.base.state_ty,
                        frame.base.done_state as u64,
                    )),
                ),
                span: site.span,
            });
        body.basic_blocks[site.cancel_complete]
            .statements
            .extend(clear_frame_fields(&frame.base, None, frame_ptr, site.span));
        body.basic_blocks[site.cancel_complete]
            .statements
            .push(Statement {
                kind: StatementKind::Assign(
                    Place::from_local(tag_return),
                    Rvalue::Use(const_uint8_operand(gcx, 2)),
                ),
                span: site.span,
            });
        body.basic_blocks[site.cancel_complete].terminator = Some(Terminator {
            kind: TerminatorKind::Return,
            span: site.span,
        });

        let poll_block = body.basic_blocks.push(BasicBlockData {
            note: Some(format!("gen-await-poll-{}", index)),
            statements: vec![
                Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(handle_local),
                        Rvalue::Use(site.future.clone()),
                    ),
                    span: site.span,
                },
                Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(ready_ref_local),
                        Rvalue::Ref {
                            place: Place::from_local(ready_storage_local),
                        },
                    ),
                    span: site.span,
                },
                Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(ready_ptr_local),
                        Rvalue::Cast {
                            operand: Operand::Copy(Place::from_local(ready_ref_local)),
                            ty: raw_ptr_ty(gcx, ready_storage_ty, Mutability::Mutable),
                            kind: CastKind::Pointer,
                        },
                    ),
                    span: site.span,
                },
                Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(ready_raw_local),
                        Rvalue::Cast {
                            operand: Operand::Copy(Place::from_local(ready_ptr_local)),
                            ty: ptr_u8_mut,
                            kind: CastKind::Pointer,
                        },
                    ),
                    span: site.span,
                },
            ],
            terminator: None,
        });
        await_poll_blocks.push(poll_block);

        let poll_handle_block = body.basic_blocks.push(BasicBlockData {
            note: Some(format!("gen-await-handle-poll-{}", index)),
            statements: vec![],
            terminator: None,
        });
        let check_block = body.basic_blocks.push(BasicBlockData {
            note: Some(format!("gen-await-check-{}", index)),
            statements: vec![],
            terminator: None,
        });

        let mut pending_stmts = vec![Statement {
            kind: StatementKind::Assign(
                frame_state_place(frame_ptr, frame.base.state_ty),
                Rvalue::Use(const_uint_operand(
                    gcx,
                    frame.base.state_ty,
                    (index + 1) as u64,
                )),
            ),
            span: site.span,
        }];
        pending_stmts.extend(clear_frame_fields(
            &frame.base,
            Some(&frame.await_live_locals[index]),
            frame_ptr,
            site.span,
        ));
        pending_stmts.push(Statement {
            kind: StatementKind::Assign(
                Place::from_local(tag_return),
                Rvalue::Use(const_uint8_operand(gcx, 0)),
            ),
            span: site.span,
        });
        let pending_block = body.basic_blocks.push(BasicBlockData {
            note: Some(format!("gen-await-pending-{}", index)),
            statements: pending_stmts,
            terminator: Some(Terminator {
                kind: TerminatorKind::Return,
                span: site.span,
            }),
        });

        let cancel_switch_block = body.basic_blocks.push(BasicBlockData {
            note: Some(format!("gen-await-cancel-check-{}", index)),
            statements: vec![],
            terminator: None,
        });
        let cancel_progress_block = body.basic_blocks.push(BasicBlockData {
            note: Some(format!("gen-await-cancel-progress-{}", index)),
            statements: vec![],
            terminator: Some(Terminator {
                kind: TerminatorKind::SwitchInt {
                    discr: Operand::Copy(Place::from_local(tag_local)),
                    targets: vec![(0, pending_block)],
                    otherwise: site.cancel,
                },
                span: site.span,
            }),
        });
        let cancel_destroy_block = body.basic_blocks.push(BasicBlockData {
            note: Some(format!("gen-await-cancel-destroy-{}", index)),
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
            note: Some(format!("gen-await-destroy-{}", index)),
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

        let mut ready_stmts = Vec::new();
        if ready_ty == gcx.types.void {
            ready_stmts.push(Statement {
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
            ready_stmts.push(Statement {
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
            note: Some(format!("gen-await-ready-{}", index)),
            statements: ready_stmts,
            terminator: Some(Terminator {
                kind: TerminatorKind::Goto {
                    target: ready_target,
                },
                span: site.span,
            }),
        });
        let no_result_target = body.basic_blocks.push(BasicBlockData {
            note: Some(format!("gen-await-no-result-{}", index)),
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

        body.basic_blocks[check_block].terminator = Some(Terminator {
            kind: TerminatorKind::SwitchInt {
                discr: Operand::Copy(Place::from_local(tag_local)),
                targets: vec![
                    (0u128, pending_block),
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

    // 4. Build dispatch entry block for `$gen_poll`:
    let done_block = body.basic_blocks.push(BasicBlockData {
        note: Some("async-gen-done".into()),
        statements: vec![
            Statement {
                kind: StatementKind::Assign(
                    Place {
                        local: out_ptr,
                        projection: vec![PlaceElem::Deref],
                    },
                    Rvalue::Aggregate {
                        kind: AggregateKind::Adt {
                            def_id: opt_def,
                            variant_index: Some(none_idx),
                            generic_args: opt_args,
                        },
                        fields: IndexVec::new(),
                    },
                ),
                span,
            },
            Statement {
                kind: StatementKind::Assign(
                    Place::from_local(tag_return),
                    Rvalue::Use(const_uint8_operand(gcx, 1)),
                ),
                span,
            },
        ],
        terminator: Some(Terminator {
            kind: TerminatorKind::Return,
            span,
        }),
    });

    let make_resume_trampoline = |body: &mut Body<'ctx>, target: BasicBlockId, note: String, s: Span| {
        body.basic_blocks.push(BasicBlockData {
            note: Some(note),
            statements: vec![Statement {
                kind: StatementKind::Assign(
                    frame_state_place(frame_ptr, frame.base.state_ty),
                    Rvalue::Use(const_uint_operand(
                        gcx,
                        frame.base.state_ty,
                        frame.base.done_state as u64,
                    )),
                ),
                span: s,
            }],
            terminator: Some(Terminator {
                kind: TerminatorKind::Goto { target },
                span: s,
            }),
        })
    };

    let start_trampoline =
        make_resume_trampoline(body, original_start, "async-gen-start".into(), span);
    let mut dispatch_targets = vec![(0u128, start_trampoline)];
    for (index, &poll_block) in await_poll_blocks.iter().enumerate() {
        let trampoline = make_resume_trampoline(
            body,
            poll_block,
            format!("async-gen-resume-await-{}", index),
            awaits[index].span,
        );
        dispatch_targets.push(((index + 1) as u128, trampoline));
    }
    for (index, site) in yields.iter().enumerate() {
        let state_id = 1 + awaits.len() + index;
        let trampoline = make_resume_trampoline(
            body,
            site.resume,
            format!("async-gen-resume-yield-{}", index),
            site.span,
        );
        dispatch_targets.push((state_id as u128, trampoline));
    }

    let entry = body.basic_blocks.push(BasicBlockData {
        note: Some("async-gen-poll-entry".into()),
        statements: vec![
            Statement {
                kind: StatementKind::Assign(
                    Place::from_local(frame_ptr),
                    Rvalue::Cast {
                        operand: Operand::Copy(Place::from_local(frame_raw)),
                        ty: frame_ptr_ty,
                        kind: CastKind::Pointer,
                    },
                ),
                span,
            },
            Statement {
                kind: StatementKind::Assign(
                    Place::from_local(out_ptr),
                    Rvalue::Cast {
                        operand: Operand::Copy(Place::from_local(out_raw)),
                        ty: out_ptr_ty,
                        kind: CastKind::Pointer,
                    },
                ),
                span,
            },
            Statement {
                kind: StatementKind::Assign(
                    Place::from_local(state_local),
                    Rvalue::Use(Operand::Copy(frame_state_place(
                        frame_ptr,
                        frame.base.state_ty,
                    ))),
                ),
                span,
            },
        ],
        terminator: Some(Terminator {
            kind: TerminatorKind::SwitchInt {
                discr: Operand::Copy(Place::from_local(state_local)),
                targets: dispatch_targets,
                otherwise: done_block,
            },
            span,
        }),
    });
    body.start_block = entry;
    Ok(())
}

fn lower_async_gen_close_body<'ctx>(
    gcx: Gcx<'ctx>,
    body: &mut Body<'ctx>,
    frame: &AsyncGeneratorFrameLayout<'ctx>,
    await_count: usize,
) -> CompileResult<()> {
    let span = body_span(body);
    let mut yields = collect_yield_sites(body);

    for decl in body.locals.iter_mut() {
        if matches!(decl.kind, LocalKind::Param | LocalKind::Return) {
            decl.kind = LocalKind::Temp;
            decl.mutable = true;
        }
    }

    let ptr_u8_mut = raw_ptr_ty(gcx, gcx.types.uint8, Mutability::Mutable);
    let frame_ptr_ty = raw_ptr_ty(gcx, frame.base.ty, Mutability::Mutable);

    let frame_raw = push_local(
        body,
        ptr_u8_mut,
        LocalKind::Param,
        false,
        Some(gcx.intern_symbol("$frame_raw")),
        span,
    );
    let ret_local = push_local(
        body,
        gcx.types.void,
        LocalKind::Return,
        true,
        Some(gcx.intern_symbol("$close_ret")),
        span,
    );
    let frame_ptr = push_local(
        body,
        frame_ptr_ty,
        LocalKind::Temp,
        true,
        Some(gcx.intern_symbol("$frame_ptr")),
        span,
    );
    let state_local = push_local(
        body,
        frame.base.state_ty,
        LocalKind::Temp,
        true,
        Some(gcx.intern_symbol("$state")),
        span,
    );
    body.return_local = ret_local;

    rewrite_resident_places(body, &frame.base, frame_ptr, &mut yields);

    // Neither `await` nor `yield` can run inside `defer`, so any block with a
    // Yield or GeneratorYield terminator is unreachable from `$gen_close`.
    for bb in body.basic_blocks.iter_mut() {
        if let Some(term) = bb.terminator.as_mut()
            && matches!(
                term.kind,
                TerminatorKind::Yield { .. } | TerminatorKind::GeneratorYield { .. }
            )
        {
            term.kind = TerminatorKind::Unreachable;
        }
    }

    for site in &yields {
        body.basic_blocks[site.cancel_complete]
            .statements
            .extend(clear_frame_fields(&frame.base, None, frame_ptr, site.span));
        body.basic_blocks[site.cancel_complete]
            .statements
            .push(Statement {
                kind: StatementKind::Assign(
                    Place::from_local(ret_local),
                    Rvalue::Use(Operand::Constant(Constant {
                        ty: gcx.types.void,
                        value: ConstantKind::Unit,
                    })),
                ),
                span: site.span,
            });
        body.basic_blocks[site.cancel_complete].terminator = Some(Terminator {
            kind: TerminatorKind::Return,
            span: site.span,
        });
    }

    let mut noop_stmts = vec![Statement {
        kind: StatementKind::Assign(
            frame_state_place(frame_ptr, frame.base.state_ty),
            Rvalue::Use(const_uint_operand(
                gcx,
                frame.base.state_ty,
                frame.base.done_state as u64,
            )),
        ),
        span,
    }];
    noop_stmts.extend(clear_frame_fields(&frame.base, None, frame_ptr, span));
    noop_stmts.push(Statement {
        kind: StatementKind::Assign(
            Place::from_local(ret_local),
            Rvalue::Use(Operand::Constant(Constant {
                ty: gcx.types.void,
                value: ConstantKind::Unit,
            })),
        ),
        span,
    });
    let close_noop = body.basic_blocks.push(BasicBlockData {
        note: Some("async-gen-close-noop".into()),
        statements: noop_stmts,
        terminator: Some(Terminator {
            kind: TerminatorKind::Return,
            span,
        }),
    });

    let mut close_targets = Vec::with_capacity(yields.len());
    for (index, site) in yields.iter().enumerate() {
        let state_id = 1 + await_count + index;
        let close_entry = body.basic_blocks.push(BasicBlockData {
            note: Some(format!("async-gen-close-yield-{}", index)),
            statements: vec![Statement {
                kind: StatementKind::Assign(
                    frame_state_place(frame_ptr, frame.base.state_ty),
                    Rvalue::Use(const_uint_operand(
                        gcx,
                        frame.base.state_ty,
                        frame.base.done_state as u64,
                    )),
                ),
                span: site.span,
            }],
            terminator: Some(Terminator {
                kind: TerminatorKind::Goto {
                    target: site.cancel,
                },
                span: site.span,
            }),
        });
        close_targets.push((state_id as u128, close_entry));
    }

    let entry = body.basic_blocks.push(BasicBlockData {
        note: Some("async-gen-close-entry".into()),
        statements: vec![
            Statement {
                kind: StatementKind::Assign(
                    Place::from_local(frame_ptr),
                    Rvalue::Cast {
                        operand: Operand::Copy(Place::from_local(frame_raw)),
                        ty: frame_ptr_ty,
                        kind: CastKind::Pointer,
                    },
                ),
                span,
            },
            Statement {
                kind: StatementKind::Assign(
                    Place::from_local(state_local),
                    Rvalue::Use(Operand::Copy(frame_state_place(
                        frame_ptr,
                        frame.base.state_ty,
                    ))),
                ),
                span,
            },
        ],
        terminator: Some(Terminator {
            kind: TerminatorKind::SwitchInt {
                discr: Operand::Copy(Place::from_local(state_local)),
                targets: close_targets,
                otherwise: close_noop,
            },
            span,
        }),
    });
    body.start_block = entry;
    Ok(())
}

fn build_async_gen_constructor<'ctx>(
    gcx: Gcx<'ctx>,
    original: &Body<'ctx>,
    poll_id: DefinitionID,
    close_id: DefinitionID,
    element_ty: Ty<'ctx>,
    frame: &GeneratorFrameLayout<'ctx>,
) -> CompileResult<Body<'ctx>> {
    let span = body_span(original);
    let Some(async_gen_def) = gcx.std_item_def(StdItem::AsyncGenerator) else {
        gcx.dcx().emit_error(
            "internal error: missing `AsyncGenerator` std item during async generator lowering"
                .into(),
            Some(span),
        );
        return Err(ReportedError);
    };
    let adt_def = gcx.get_struct_definition(async_gen_def).adt_def;
    let gen_args = gcx
        .store
        .interners
        .intern_generic_args(vec![GenericArgument::Type(element_ty)]);
    let async_gen_ty = Ty::new(TyKind::Adt(adt_def, gen_args), gcx);

    let ptr_u8_mut = raw_ptr_ty(gcx, gcx.types.uint8, Mutability::Mutable);
    let frame_ptr_ty = raw_ptr_ty(gcx, frame.ty, Mutability::Mutable);

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

    let ret_local = push_local(
        &mut body,
        async_gen_ty,
        LocalKind::Return,
        true,
        Some(gcx.intern_symbol("$async_gen_ret")),
        span,
    );
    body.return_local = ret_local;

    let orig_params: Vec<_> = original
        .locals
        .iter_enumerated()
        .filter_map(|(local, decl)| matches!(decl.kind, LocalKind::Param).then_some((local, decl)))
        .collect();
    let ctor_params: Vec<_> = orig_params
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

    let frame_raw = push_local(
        &mut body,
        ptr_u8_mut,
        LocalKind::Temp,
        true,
        Some(gcx.intern_symbol("$frame_raw")),
        span,
    );
    let frame_ptr = push_local(
        &mut body,
        frame_ptr_ty,
        LocalKind::Temp,
        true,
        Some(gcx.intern_symbol("$frame_ptr")),
        span,
    );

    let mut init_stmts = vec![Statement {
        kind: StatementKind::Assign(
            Place::from_local(frame_ptr),
            Rvalue::Cast {
                operand: Operand::Copy(Place::from_local(frame_raw)),
                ty: frame_ptr_ty,
                kind: CastKind::Pointer,
            },
        ),
        span,
    }];

    for ((orig_local, _), ctor_local) in orig_params.iter().zip(ctor_params.iter()) {
        if !frame.stored_locals.contains(orig_local) {
            continue;
        }
        init_stmts.push(Statement {
            kind: StatementKind::Assign(
                frame_local_place(frame, frame_ptr, *orig_local),
                Rvalue::Use(Operand::CopyWith(
                    Place::from_local(*ctor_local),
                    CopyModifiers { init: true },
                )),
            ),
            span,
        });
    }

    let poll_fn_ty = gcx.get_type(poll_id);
    let poll_fn_operand = fn_operand(
        poll_id,
        GenericsBuilder::identity_for_item(gcx, poll_id),
        poll_fn_ty,
    );
    let close_fn_ty = gcx.get_type(close_id);
    let close_fn_operand = fn_operand(
        close_id,
        GenericsBuilder::identity_for_item(gcx, close_id),
        close_fn_ty,
    );
    init_stmts.push(Statement {
        kind: StatementKind::Assign(
            Place::from_local(ret_local),
            Rvalue::Aggregate {
                kind: AggregateKind::Adt {
                    def_id: async_gen_def,
                    variant_index: None,
                    generic_args: gen_args,
                },
                fields: IndexVec::from_vec(vec![
                    Operand::Copy(Place::from_local(frame_raw)),
                    poll_fn_operand,
                    close_fn_operand,
                ]),
            },
        ),
        span,
    });

    let init_block = body.basic_blocks.push(BasicBlockData {
        note: Some("async-gen-ctor-init".into()),
        statements: init_stmts,
        terminator: Some(Terminator {
            kind: TerminatorKind::Return,
            span,
        }),
    });

    let allocate = frame_allocator(gcx, span);
    let alloc_args = gcx
        .store
        .interners
        .intern_generic_args(vec![GenericArgument::Type(frame.ty)]);
    let entry = body.basic_blocks.push(BasicBlockData {
        note: Some("async-gen-ctor-alloc".into()),
        statements: vec![],
        terminator: Some(Terminator {
            kind: TerminatorKind::Call {
                func: fn_operand(allocate, alloc_args, gcx.get_type(allocate)),
                args: vec![],
                destination: Place::from_local(frame_raw),
                target: init_block,
                unwind: CallUnwindAction::Terminate,
            },
            span,
        }),
    });
    body.start_block = entry;
    Ok(body)
}
