use super::MirPass;
use crate::compile::context::Gcx;
use crate::error::CompileResult;
use crate::mir::{
    BasicBlockId, Body, CastKind, ConstantKind, DevirtHint, Operand, Place, PlaceElem, Rvalue,
    StatementKind, TerminatorKind,
};
use crate::sema::models::{GenericArgument, GenericArguments, Ty, TyKind};
use crate::specialize::{InstanceKind, resolve_instance};
use index_vec::IndexVec;
use std::sync::atomic::{AtomicU64, Ordering};

static DEVIRT_CANDIDATES: AtomicU64 = AtomicU64::new(0);
static DEVIRT_HINTS_EMITTED: AtomicU64 = AtomicU64::new(0);
static DEVIRT_CODEGEN_USED: AtomicU64 = AtomicU64::new(0);
static DEVIRT_CODEGEN_FALLBACK: AtomicU64 = AtomicU64::new(0);

#[derive(Debug, Clone, Copy, Default)]
pub struct DevirtCounters {
    pub candidates: u64,
    pub hints_emitted: u64,
    pub codegen_used: u64,
    pub codegen_fallback: u64,
}

pub fn devirt_counters_snapshot() -> DevirtCounters {
    DevirtCounters {
        candidates: DEVIRT_CANDIDATES.load(Ordering::Relaxed),
        hints_emitted: DEVIRT_HINTS_EMITTED.load(Ordering::Relaxed),
        codegen_used: DEVIRT_CODEGEN_USED.load(Ordering::Relaxed),
        codegen_fallback: DEVIRT_CODEGEN_FALLBACK.load(Ordering::Relaxed),
    }
}

pub(crate) fn bump_codegen_used() {
    DEVIRT_CODEGEN_USED.fetch_add(1, Ordering::Relaxed);
}

pub(crate) fn bump_codegen_fallback() {
    DEVIRT_CODEGEN_FALLBACK.fetch_add(1, Ordering::Relaxed);
}

pub struct DevirtualizeStaticCalls;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum KnownConcreteExistentialState<'ctx> {
    Untracked,
    Unknown,
    Known(Ty<'ctx>),
}

impl<'ctx> KnownConcreteExistentialState<'ctx> {
    #[inline]
    fn join(self, other: Self) -> Self {
        use KnownConcreteExistentialState::*;
        match (self, other) {
            (Untracked, Untracked) => Untracked,
            (Known(a), Known(b)) if a == b => Known(a),
            (Known(_), Known(_)) => Unknown,
            (Unknown, _) | (_, Unknown) => Unknown,
            // Different tracked/untracked states only happen if local shape changed,
            // which should not occur within a single body. Be conservative.
            (Untracked, Known(_)) | (Known(_), Untracked) => Unknown,
        }
    }
}

impl<'ctx> MirPass<'ctx> for DevirtualizeStaticCalls {
    fn name(&self) -> &'static str {
        "DevirtualizeStaticCalls"
    }

    fn run(&mut self, gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
        if body.locals.is_empty() || body.basic_blocks.is_empty() {
            return Ok(());
        }

        let tracked_locals: Vec<bool> = body
            .locals
            .iter()
            .map(|decl| is_tracked_ty(decl.ty))
            .collect();

        if !tracked_locals.iter().any(|tracked| *tracked) {
            // Clear stale hints if there are no tracked locals.
            for block in body.basic_blocks.iter_mut() {
                if let Some(term) = &mut block.terminator {
                    if let TerminatorKind::Call { devirt_hint, .. } = &mut term.kind {
                        *devirt_hint = None;
                    }
                }
            }
            return Ok(());
        }

        let preds = build_predecessors(body);
        let default_state = default_state_for_locals(&tracked_locals);

        let mut in_states: IndexVec<BasicBlockId, Vec<KnownConcreteExistentialState<'ctx>>> =
            IndexVec::from(vec![default_state.clone(); body.basic_blocks.len()]);
        let mut out_states: IndexVec<BasicBlockId, Vec<KnownConcreteExistentialState<'ctx>>> =
            IndexVec::from(vec![default_state.clone(); body.basic_blocks.len()]);

        let mut worklist: Vec<BasicBlockId> = body.basic_blocks.indices().collect();
        while let Some(bb) = worklist.pop() {
            let new_in = join_predecessor_states(body, bb, &preds, &out_states, &default_state);
            let new_out = transfer_block(body, bb, new_in.clone(), &tracked_locals);

            let changed = new_in != in_states[bb] || new_out != out_states[bb];
            if changed {
                in_states[bb] = new_in;
                out_states[bb] = new_out;
                if let Some(term) = &body.basic_blocks[bb].terminator {
                    for succ in terminator_successors(&term.kind) {
                        worklist.push(succ);
                    }
                }
            }
        }

        // Second pass: annotate call terminators with devirtualization hints.
        let block_ids: Vec<BasicBlockId> = body.basic_blocks.indices().collect();
        for bb in block_ids {
            let mut state = in_states[bb].clone();
            {
                let statements = body.basic_blocks[bb].statements.clone();
                for stmt in &statements {
                    apply_statement_transfer(body, stmt, &tracked_locals, &mut state);
                }
            }

            let maybe_hint = body.basic_blocks[bb]
                .terminator
                .as_ref()
                .and_then(|term| match &term.kind {
                    TerminatorKind::Call { func, args, .. } => {
                        maybe_build_devirt_hint(gcx, body, &state, func, args)
                    }
                    _ => None,
                });

            let Some(term) = body.basic_blocks[bb].terminator.as_mut() else {
                continue;
            };

            if let TerminatorKind::Call {
                destination,
                devirt_hint,
                ..
            } = &mut term.kind
            {
                *devirt_hint = maybe_hint;
                if devirt_hint.is_some() {
                    DEVIRT_HINTS_EMITTED.fetch_add(1, Ordering::Relaxed);
                }
                if tracked_locals
                    .get(destination.local.index())
                    .copied()
                    .unwrap_or(false)
                {
                    state[destination.local.index()] = KnownConcreteExistentialState::Unknown;
                }
            }
        }

        Ok(())
    }
}

fn maybe_build_devirt_hint<'ctx>(
    gcx: Gcx<'ctx>,
    body: &Body<'ctx>,
    state: &[KnownConcreteExistentialState<'ctx>],
    func: &Operand<'ctx>,
    args: &[Operand<'ctx>],
) -> Option<DevirtHint<'ctx>> {
    let Operand::Constant(c) = func else {
        return None;
    };
    let ConstantKind::Function(def_id, call_args, _) = c.value else {
        return None;
    };

    let current_instance = resolve_instance(gcx, def_id, call_args);
    if !matches!(current_instance.kind(), InstanceKind::Virtual(_)) {
        return None;
    }
    DEVIRT_CANDIDATES.fetch_add(1, Ordering::Relaxed);

    let receiver = args.first()?;
    let concrete_self_ty = operand_known_concrete_ty(body, state, receiver)?;

    let substituted_args = substitute_self_arg(gcx, def_id, call_args, concrete_self_ty)?;
    let resolved = resolve_instance(gcx, def_id, substituted_args);
    let InstanceKind::Item(impl_def_id) = resolved.kind() else {
        return None;
    };

    Some(DevirtHint {
        impl_def_id,
        impl_args: resolved.args(),
        concrete_self_ty,
    })
}

fn substitute_self_arg<'ctx>(
    gcx: Gcx<'ctx>,
    def_id: crate::hir::DefinitionID,
    call_args: GenericArguments<'ctx>,
    concrete_self_ty: Ty<'ctx>,
) -> Option<GenericArguments<'ctx>> {
    let generics = gcx.generics_of(def_id);
    if !generics.has_self {
        return None;
    }

    let mut out: Vec<GenericArgument<'ctx>> = call_args.iter().copied().collect();
    if out.is_empty() {
        return None;
    }

    if !matches!(out[0], GenericArgument::Type(_)) {
        return None;
    }

    out[0] = GenericArgument::Type(concrete_self_ty);
    Some(gcx.store.interners.intern_generic_args(out))
}

fn default_state_for_locals<'ctx>(
    tracked_locals: &[bool],
) -> Vec<KnownConcreteExistentialState<'ctx>> {
    tracked_locals
        .iter()
        .map(|tracked| {
            if *tracked {
                KnownConcreteExistentialState::Unknown
            } else {
                KnownConcreteExistentialState::Untracked
            }
        })
        .collect()
}

fn join_predecessor_states<'ctx>(
    body: &Body<'ctx>,
    bb: BasicBlockId,
    preds: &IndexVec<BasicBlockId, Vec<BasicBlockId>>,
    out_states: &IndexVec<BasicBlockId, Vec<KnownConcreteExistentialState<'ctx>>>,
    default_state: &[KnownConcreteExistentialState<'ctx>],
) -> Vec<KnownConcreteExistentialState<'ctx>> {
    if bb == body.start_block {
        return default_state.to_vec();
    }
    let pred_list = &preds[bb];
    if pred_list.is_empty() {
        return default_state.to_vec();
    }

    let mut joined = out_states[pred_list[0]].clone();
    for pred in pred_list.iter().skip(1) {
        for (idx, item) in joined.iter_mut().enumerate() {
            *item = item.join(out_states[*pred][idx]);
        }
    }
    joined
}

fn transfer_block<'ctx>(
    body: &Body<'ctx>,
    bb: BasicBlockId,
    mut state: Vec<KnownConcreteExistentialState<'ctx>>,
    tracked_locals: &[bool],
) -> Vec<KnownConcreteExistentialState<'ctx>> {
    let block = &body.basic_blocks[bb];
    for stmt in &block.statements {
        apply_statement_transfer(body, stmt, tracked_locals, &mut state);
    }
    if let Some(term) = &block.terminator {
        apply_terminator_transfer(tracked_locals, &mut state, &term.kind);
    }
    state
}

fn apply_statement_transfer<'ctx>(
    body: &Body<'ctx>,
    stmt: &crate::mir::Statement<'ctx>,
    tracked_locals: &[bool],
    state: &mut [KnownConcreteExistentialState<'ctx>],
) {
    let StatementKind::Assign(dest, rvalue) = &stmt.kind else {
        return;
    };

    let tracked = tracked_locals
        .get(dest.local.index())
        .copied()
        .unwrap_or(false);
    if !tracked {
        return;
    }

    if !dest.projection.is_empty() {
        state[dest.local.index()] = KnownConcreteExistentialState::Unknown;
        return;
    }

    let next = match rvalue {
        Rvalue::Cast {
            operand,
            kind: CastKind::BoxExistential,
            ..
        } => operand_concrete_or_tracked(body, state, operand)
            .map(KnownConcreteExistentialState::Known)
            .unwrap_or(KnownConcreteExistentialState::Unknown),
        Rvalue::Cast {
            operand,
            kind: CastKind::ExistentialUpcast,
            ..
        }
        | Rvalue::Use(operand)
        | Rvalue::Cast {
            operand,
            kind: CastKind::Pointer,
            ..
        } => operand_state(state, operand).unwrap_or(KnownConcreteExistentialState::Unknown),
        Rvalue::Ref { place, .. } => {
            if place.projection.is_empty() {
                state
                    .get(place.local.index())
                    .copied()
                    .unwrap_or(KnownConcreteExistentialState::Unknown)
            } else {
                KnownConcreteExistentialState::Unknown
            }
        }
        _ => KnownConcreteExistentialState::Unknown,
    };

    state[dest.local.index()] = next;
}

fn apply_terminator_transfer<'ctx>(
    tracked_locals: &[bool],
    state: &mut [KnownConcreteExistentialState<'ctx>],
    term: &TerminatorKind<'ctx>,
) {
    if let TerminatorKind::Call { destination, .. } = term {
        if tracked_locals
            .get(destination.local.index())
            .copied()
            .unwrap_or(false)
        {
            state[destination.local.index()] = KnownConcreteExistentialState::Unknown;
        }
    }
}

fn operand_concrete_or_tracked<'ctx>(
    body: &Body<'ctx>,
    state: &[KnownConcreteExistentialState<'ctx>],
    operand: &Operand<'ctx>,
) -> Option<Ty<'ctx>> {
    if let Some(known) = operand_known_concrete_ty(body, state, operand) {
        return Some(known);
    }

    let ty = operand_ty(body, operand);
    if is_concrete_existential_source_ty(ty) {
        Some(ty)
    } else {
        None
    }
}

fn operand_known_concrete_ty<'ctx>(
    body: &Body<'ctx>,
    state: &[KnownConcreteExistentialState<'ctx>],
    operand: &Operand<'ctx>,
) -> Option<Ty<'ctx>> {
    let local = operand_local(operand)?;
    match state.get(local.index()).copied()? {
        KnownConcreteExistentialState::Known(ty) => Some(ty),
        KnownConcreteExistentialState::Unknown | KnownConcreteExistentialState::Untracked => None,
    }
    .or_else(|| {
        let ty = operand_ty(body, operand);
        is_concrete_existential_source_ty(ty).then_some(ty)
    })
}

fn operand_state<'ctx>(
    state: &[KnownConcreteExistentialState<'ctx>],
    operand: &Operand<'ctx>,
) -> Option<KnownConcreteExistentialState<'ctx>> {
    let local = operand_local(operand)?;
    state.get(local.index()).copied()
}

fn operand_local<'ctx>(operand: &Operand<'ctx>) -> Option<crate::mir::LocalId> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) | Operand::CopyWith(place, _)
            if place.projection.is_empty() =>
        {
            Some(place.local)
        }
        _ => None,
    }
}

fn operand_ty<'ctx>(body: &Body<'ctx>, operand: &Operand<'ctx>) -> Ty<'ctx> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) | Operand::CopyWith(place, _) => {
            place_ty(body, place)
        }
        Operand::Constant(c) => c.ty,
    }
}

fn place_ty<'ctx>(body: &Body<'ctx>, place: &Place<'ctx>) -> Ty<'ctx> {
    let mut ty = body.locals[place.local].ty;
    for projection in &place.projection {
        match projection {
            PlaceElem::Deref => {
                ty = match ty.kind() {
                    TyKind::Reference(inner, _) | TyKind::Pointer(inner, _) => inner,
                    _ => ty,
                };
            }
            PlaceElem::Field(_, field_ty) => ty = *field_ty,
            PlaceElem::VariantDowncast { .. } => {}
        }
    }
    ty
}

fn is_tracked_ty(ty: Ty<'_>) -> bool {
    match ty.kind() {
        TyKind::BoxedExistential { .. } => true,
        TyKind::Reference(inner, _) | TyKind::Pointer(inner, _) => {
            matches!(inner.kind(), TyKind::BoxedExistential { .. })
        }
        _ => false,
    }
}

fn is_concrete_existential_source_ty(ty: Ty<'_>) -> bool {
    match ty.kind() {
        TyKind::BoxedExistential { .. } => false,
        TyKind::Reference(inner, _) | TyKind::Pointer(inner, _) => {
            !matches!(inner.kind(), TyKind::BoxedExistential { .. })
        }
        _ => true,
    }
}

fn build_predecessors(body: &Body<'_>) -> IndexVec<BasicBlockId, Vec<BasicBlockId>> {
    let mut preds: IndexVec<BasicBlockId, Vec<BasicBlockId>> =
        IndexVec::from(vec![Vec::new(); body.basic_blocks.len()]);

    for (bb, data) in body.basic_blocks.iter_enumerated() {
        if let Some(term) = &data.terminator {
            for succ in terminator_successors(&term.kind) {
                preds[succ].push(bb);
            }
        }
    }

    preds
}

fn terminator_successors(term: &TerminatorKind<'_>) -> Vec<BasicBlockId> {
    match term {
        TerminatorKind::Goto { target } => vec![*target],
        TerminatorKind::SwitchInt {
            targets, otherwise, ..
        } => {
            let mut out = Vec::with_capacity(targets.len() + 1);
            for (_, bb) in targets {
                out.push(*bb);
            }
            out.push(*otherwise);
            out
        }
        TerminatorKind::Call { target, unwind, .. } => {
            let mut out = vec![*target];
            if let crate::mir::CallUnwindAction::Cleanup(bb) = unwind {
                out.push(*bb);
            }
            out
        }
        TerminatorKind::Yield { resume, .. } => vec![*resume],
        TerminatorKind::Return
        | TerminatorKind::ResumeUnwind
        | TerminatorKind::Unreachable
        | TerminatorKind::UnresolvedGoto => Vec::new(),
    }
}
