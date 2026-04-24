use super::MirPass;
use crate::compile::context::Gcx;
use crate::error::CompileResult;
use crate::hir::DefinitionID;
use crate::mir::{
    BasicBlockId, Body, CallUnwindAction, CastKind, ConstantKind, LocalDecl, LocalId, LocalKind,
    Operand, ParamEscapeInfo, Place, Rvalue, Statement, StatementKind, TerminatorKind,
};
use crate::sema::models::{GenericArguments, Ty, TyKind};
use index_vec::IndexVec;
use rustc_hash::FxHashSet;

pub struct AllocEscapeAnalysis;
pub struct StackPromoteAllocations;

impl<'ctx> MirPass<'ctx> for AllocEscapeAnalysis {
    fn name(&self) -> &'static str {
        "AllocEscapeAnalysis"
    }

    fn run(&mut self, gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
        let local_count = body.locals.len();
        body.escape_locals.clear();
        body.escape_locals.resize(local_count, false);

        if local_count == 0 || body.basic_blocks.is_empty() {
            return Ok(());
        }

        let (alloc_defs, alloc_tys, invalid_alloc_locals) = collect_alloc_definitions(body);
        if !alloc_defs.iter().any(|count| *count > 0) {
            return Ok(());
        }

        let preds = build_predecessors(body);
        let mut in_states: IndexVec<BasicBlockId, Vec<FxHashSet<LocalId>>> = IndexVec::from(vec![
                vec![FxHashSet::default(); local_count];
                body.basic_blocks.len()
            ]);
        let mut out_states: IndexVec<BasicBlockId, Vec<FxHashSet<LocalId>>> = IndexVec::from(vec![
                vec![FxHashSet::default(); local_count];
                body.basic_blocks.len()
            ]);

        let mut worklist: Vec<BasicBlockId> = body.basic_blocks.indices().collect();
        while let Some(bb) = worklist.pop() {
            let new_in = join_points_to_states(bb, &preds, &out_states, local_count);
            let new_out = transfer_block_points_to(body, bb, new_in.clone(), &alloc_defs);

            if new_in != in_states[bb] || new_out != out_states[bb] {
                in_states[bb] = new_in;
                out_states[bb] = new_out;
                if let Some(term) = &body.basic_blocks[bb].terminator {
                    for succ in terminator_successors(&term.kind) {
                        worklist.push(succ);
                    }
                }
            }
        }

        let mut escaped = vec![false; local_count];

        for (idx, count) in alloc_defs.iter().enumerate() {
            if *count != 1 || invalid_alloc_locals[idx] {
                escaped[idx] = true;
            }
        }

        for bb in body.basic_blocks.indices() {
            let mut state = in_states[bb].clone();
            let block = &body.basic_blocks[bb];
            for stmt in &block.statements {
                mark_statement_escapes(gcx, body, stmt, &state, &mut escaped);
                apply_statement_points_to(stmt, &mut state, &alloc_defs);
            }

            if let Some(term) = &block.terminator {
                mark_terminator_escapes(gcx, body, term, &state, &mut escaped);
                apply_terminator_points_to(term, &mut state);
            }
        }

        for local_idx in 0..local_count {
            if alloc_defs[local_idx] == 0 {
                continue;
            }
            if alloc_tys[local_idx].is_none() {
                escaped[local_idx] = true;
            }
            body.escape_locals[local_idx] = escaped[local_idx];
        }

        Ok(())
    }
}

impl<'ctx> MirPass<'ctx> for StackPromoteAllocations {
    fn name(&self) -> &'static str {
        "StackPromoteAllocations"
    }

    fn run(&mut self, gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
        let (alloc_defs, alloc_tys, _) = collect_alloc_definitions(body);
        if !alloc_defs.iter().any(|count| *count > 0) {
            return Ok(());
        }

        let mut promoted: Vec<Option<(LocalId, LocalId, Ty<'ctx>)>> = vec![None; body.locals.len()];
        let original_len = body.locals.len();

        for idx in 0..original_len {
            if alloc_defs[idx] != 1 {
                continue;
            }
            if body.escape_locals.get(idx).copied().unwrap_or(true) {
                continue;
            }
            let Some(alloc_ty) = alloc_tys[idx] else {
                continue;
            };

            let span = body.locals[idx].span;
            let stack_obj = body.locals.push(LocalDecl {
                ty: alloc_ty,
                kind: LocalKind::Temp,
                mutable: true,
                name: None,
                span,
            });
            body.escape_locals.push(false);

            let stack_ref_ty = gcx
                .store
                .interners
                .intern_ty(TyKind::Reference(alloc_ty, crate::hir::Mutability::Mutable));
            let stack_ref = body.locals.push(LocalDecl {
                ty: stack_ref_ty,
                kind: LocalKind::Temp,
                mutable: true,
                name: None,
                span,
            });
            body.escape_locals.push(false);

            promoted[idx] = Some((stack_obj, stack_ref, alloc_ty));
        }

        if promoted.iter().all(|item| item.is_none()) {
            return Ok(());
        }

        for bb in body.basic_blocks.iter_mut() {
            let old = std::mem::take(&mut bb.statements);
            let mut rewritten = Vec::with_capacity(old.len());
            for stmt in old {
                match stmt.kind {
                    StatementKind::Assign(dest, Rvalue::Alloc { ty })
                        if dest.projection.is_empty()
                            && promoted
                                .get(dest.local.index())
                                .and_then(|item| *item)
                                .is_some() =>
                    {
                        let (stack_obj, stack_ref, alloc_ty) =
                            promoted[dest.local.index()].expect("promoted alloc local");
                        if alloc_ty != ty {
                            rewritten.push(Statement {
                                kind: StatementKind::Assign(dest, Rvalue::Alloc { ty }),
                                span: stmt.span,
                            });
                            continue;
                        }

                        rewritten.push(Statement {
                            kind: StatementKind::Assign(
                                Place::from_local(stack_ref),
                                Rvalue::Ref {
                                    mutable: true,
                                    place: Place::from_local(stack_obj),
                                },
                            ),
                            span: stmt.span,
                        });

                        let ptr_ty = body.locals[dest.local].ty;
                        rewritten.push(Statement {
                            kind: StatementKind::Assign(
                                dest,
                                Rvalue::Cast {
                                    operand: Operand::Copy(Place::from_local(stack_ref)),
                                    ty: ptr_ty,
                                    kind: CastKind::Pointer,
                                },
                            ),
                            span: stmt.span,
                        });
                    }
                    other => rewritten.push(Statement {
                        kind: other,
                        span: stmt.span,
                    }),
                }
            }
            bb.statements = rewritten;
        }

        Ok(())
    }
}

fn collect_alloc_definitions<'ctx>(
    body: &Body<'ctx>,
) -> (Vec<usize>, Vec<Option<Ty<'ctx>>>, Vec<bool>) {
    let local_count = body.locals.len();
    let mut alloc_defs = vec![0usize; local_count];
    let mut alloc_tys = vec![None; local_count];
    let mut invalid = vec![false; local_count];

    for block in &body.basic_blocks {
        for stmt in &block.statements {
            let StatementKind::Assign(dest, rvalue) = &stmt.kind else {
                continue;
            };
            if !dest.projection.is_empty() {
                continue;
            }

            match rvalue {
                Rvalue::Alloc { ty } => {
                    alloc_defs[dest.local.index()] += 1;
                    if let Some(existing) = alloc_tys[dest.local.index()] {
                        if existing != *ty {
                            invalid[dest.local.index()] = true;
                        }
                    } else {
                        alloc_tys[dest.local.index()] = Some(*ty);
                    }
                }
                _ => {
                    if alloc_defs[dest.local.index()] > 0 {
                        invalid[dest.local.index()] = true;
                    }
                }
            }
        }

        if let Some(term) = &block.terminator {
            if let TerminatorKind::Call { destination, .. } = &term.kind {
                if destination.projection.is_empty() && alloc_defs[destination.local.index()] > 0 {
                    invalid[destination.local.index()] = true;
                }
            }
        }
    }

    (alloc_defs, alloc_tys, invalid)
}

fn join_points_to_states(
    bb: BasicBlockId,
    preds: &IndexVec<BasicBlockId, Vec<BasicBlockId>>,
    out_states: &IndexVec<BasicBlockId, Vec<FxHashSet<LocalId>>>,
    local_count: usize,
) -> Vec<FxHashSet<LocalId>> {
    let pred_list = &preds[bb];
    if pred_list.is_empty() {
        return vec![FxHashSet::default(); local_count];
    }

    let mut joined = out_states[pred_list[0]].clone();
    for pred in pred_list.iter().skip(1) {
        for idx in 0..local_count {
            for item in &out_states[*pred][idx] {
                joined[idx].insert(*item);
            }
        }
    }
    joined
}

fn transfer_block_points_to<'ctx>(
    body: &Body<'ctx>,
    bb: BasicBlockId,
    mut state: Vec<FxHashSet<LocalId>>,
    alloc_defs: &[usize],
) -> Vec<FxHashSet<LocalId>> {
    let block = &body.basic_blocks[bb];
    for stmt in &block.statements {
        apply_statement_points_to(stmt, &mut state, alloc_defs);
    }
    if let Some(term) = &block.terminator {
        apply_terminator_points_to(term, &mut state);
    }
    state
}

fn apply_statement_points_to<'ctx>(
    stmt: &Statement<'ctx>,
    state: &mut [FxHashSet<LocalId>],
    alloc_defs: &[usize],
) {
    let StatementKind::Assign(dest, rvalue) = &stmt.kind else {
        return;
    };
    if !dest.projection.is_empty() {
        return;
    }

    let idx = dest.local.index();
    state[idx].clear();

    match rvalue {
        Rvalue::Alloc { .. } => {
            if alloc_defs[idx] > 0 {
                state[idx].insert(dest.local);
            }
        }
        _ => {
            if let Some(src_local) = alias_source_from_rvalue(rvalue) {
                for item in state[src_local.index()].clone() {
                    state[idx].insert(item);
                }
            }
        }
    }
}

fn apply_terminator_points_to<'ctx>(
    term: &crate::mir::Terminator<'ctx>,
    state: &mut [FxHashSet<LocalId>],
) {
    if let TerminatorKind::Call { destination, .. } = &term.kind {
        if destination.projection.is_empty() {
            state[destination.local.index()].clear();
        }
    }
}

fn mark_statement_escapes<'ctx>(
    _gcx: Gcx<'ctx>,
    body: &Body<'ctx>,
    stmt: &Statement<'ctx>,
    state: &[FxHashSet<LocalId>],
    escaped: &mut [bool],
) {
    let StatementKind::Assign(dest, rvalue) = &stmt.kind else {
        return;
    };

    if !dest.projection.is_empty() {
        mark_rvalue_alias_objects_escaped(rvalue, state, escaped);
        return;
    }

    if dest.local == body.return_local {
        mark_rvalue_alias_objects_escaped(rvalue, state, escaped);
    }

    if let Rvalue::Cast { operand, ty, kind } = rvalue {
        if !matches!(kind, CastKind::Pointer)
            && !is_address_like_ty(*ty)
            && let Some(src_local) = operand_local(operand)
        {
            for obj in &state[src_local.index()] {
                escaped[obj.index()] = true;
            }
        }
    }

    // Unsupported alias shape: if pointer aliases appear in a non-trivial rvalue,
    // conservatively mark them escaping.
    if has_alias_operand_in_rvalue(rvalue, state) && alias_source_from_rvalue(rvalue).is_none() {
        mark_rvalue_alias_objects_escaped(rvalue, state, escaped);
    }
}

fn mark_terminator_escapes<'ctx>(
    gcx: Gcx<'ctx>,
    body: &Body<'ctx>,
    term: &crate::mir::Terminator<'ctx>,
    state: &[FxHashSet<LocalId>],
    escaped: &mut [bool],
) {
    match &term.kind {
        TerminatorKind::Return => {
            for obj in &state[body.return_local.index()] {
                escaped[obj.index()] = true;
            }
        }
        TerminatorKind::Call { func, args, .. } => {
            let callee_summary = extract_callee(func).and_then(|(callee_id, _)| {
                if let Some(summary) = gcx.get_escape_summary(callee_id) {
                    return Some(summary);
                }
                let sig = gcx.get_signature(callee_id);
                if sig.abi.is_some() {
                    return Some(get_external_summary(gcx, callee_id));
                }
                None
            });

            for (arg_idx, arg) in args.iter().enumerate() {
                let Some(local) = operand_local(arg) else {
                    continue;
                };
                if state[local.index()].is_empty() {
                    continue;
                }

                let escapes = callee_summary
                    .as_ref()
                    .and_then(|s| s.params.get(arg_idx))
                    .map(|param| param.leaks_to_heap)
                    .unwrap_or(true);
                if !escapes {
                    continue;
                }

                for obj in &state[local.index()] {
                    escaped[obj.index()] = true;
                }
            }
        }
        _ => {}
    }
}

fn has_alias_operand_in_rvalue<'ctx>(rvalue: &Rvalue<'ctx>, state: &[FxHashSet<LocalId>]) -> bool {
    match rvalue {
        Rvalue::Use(op)
        | Rvalue::UnaryOp { operand: op, .. }
        | Rvalue::Cast { operand: op, .. }
        | Rvalue::Repeat { operand: op, .. } => operand_aliases_any(op, state),
        Rvalue::BinaryOp { lhs, rhs, .. } => {
            operand_aliases_any(lhs, state) || operand_aliases_any(rhs, state)
        }
        Rvalue::Aggregate { fields, .. } => {
            fields.iter().any(|field| operand_aliases_any(field, state))
        }
        Rvalue::Ref { place, .. } | Rvalue::Discriminant { place } => {
            !place.projection.is_empty() && !state[place.local.index()].is_empty()
        }
        Rvalue::Alloc { .. } => false,
    }
}

fn mark_rvalue_alias_objects_escaped<'ctx>(
    rvalue: &Rvalue<'ctx>,
    state: &[FxHashSet<LocalId>],
    escaped: &mut [bool],
) {
    match rvalue {
        Rvalue::Use(op)
        | Rvalue::UnaryOp { operand: op, .. }
        | Rvalue::Cast { operand: op, .. }
        | Rvalue::Repeat { operand: op, .. } => mark_operand_aliases_escaped(op, state, escaped),
        Rvalue::BinaryOp { lhs, rhs, .. } => {
            mark_operand_aliases_escaped(lhs, state, escaped);
            mark_operand_aliases_escaped(rhs, state, escaped);
        }
        Rvalue::Aggregate { fields, .. } => {
            for field in fields {
                mark_operand_aliases_escaped(field, state, escaped);
            }
        }
        Rvalue::Ref { place, .. } | Rvalue::Discriminant { place } => {
            for obj in &state[place.local.index()] {
                escaped[obj.index()] = true;
            }
        }
        Rvalue::Alloc { .. } => {}
    }
}

fn operand_aliases_any<'ctx>(operand: &Operand<'ctx>, state: &[FxHashSet<LocalId>]) -> bool {
    let Some(local) = operand_local(operand) else {
        return false;
    };
    !state[local.index()].is_empty()
}

fn mark_operand_aliases_escaped<'ctx>(
    operand: &Operand<'ctx>,
    state: &[FxHashSet<LocalId>],
    escaped: &mut [bool],
) {
    let Some(local) = operand_local(operand) else {
        return;
    };
    for obj in &state[local.index()] {
        escaped[obj.index()] = true;
    }
}

fn alias_source_from_rvalue<'ctx>(rvalue: &Rvalue<'ctx>) -> Option<LocalId> {
    match rvalue {
        Rvalue::Use(operand)
        | Rvalue::UnaryOp {
            operand,
            op: crate::mir::UnaryOperator::BitwiseNot,
        }
        | Rvalue::Cast {
            operand,
            kind: CastKind::Pointer,
            ..
        } => operand_local(operand),
        _ => None,
    }
}

fn operand_local<'ctx>(operand: &Operand<'ctx>) -> Option<LocalId> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) | Operand::CopyWith(place, _)
            if place.projection.is_empty() =>
        {
            Some(place.local)
        }
        _ => None,
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
            if let CallUnwindAction::Cleanup(bb) = unwind {
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

fn extract_callee<'ctx>(func: &Operand<'ctx>) -> Option<(DefinitionID, GenericArguments<'ctx>)> {
    match func {
        Operand::Constant(c) => {
            if let ConstantKind::Function(def_id, gen_args, _) = c.value {
                Some((def_id, gen_args))
            } else {
                None
            }
        }
        _ => None,
    }
}

fn get_external_summary<'ctx>(gcx: Gcx<'ctx>, def_id: DefinitionID) -> crate::mir::EscapeSummary {
    let sig = gcx.get_signature(def_id);
    crate::mir::EscapeSummary {
        params: sig
            .inputs
            .iter()
            .map(|p| {
                let is_addr = is_address_like_ty(p.ty);
                ParamEscapeInfo {
                    leaks_to_heap: is_addr,
                    flows_to_return: is_addr,
                }
            })
            .collect(),
    }
}

fn is_address_like_ty(ty: Ty<'_>) -> bool {
    matches!(ty.kind(), TyKind::Reference(..) | TyKind::Pointer(..))
}
