//! Interprocedural Escape Analysis
//!
//! This module implements Go-style escape analysis with function escape summaries.
//! Instead of conservatively assuming all function arguments escape, we compute
//! per-function summaries that describe how each parameter's references escape.
//!
//! The analysis runs in two phases:
//! 1. `compute_escape_summaries` - Computes `EscapeSummary` for all functions using fixpoint iteration
//! 2. `EscapeAnalysis` pass - Uses summaries to determine which locals actually escape
//!
//! This enables more precise escape analysis, avoiding heap allocations when
//! a reference is passed to a function that doesn't leak it.

use super::MirPass;
use crate::compile::context::Gcx;
use crate::error::CompileResult;
use crate::hir::{DefinitionID, Mutability};
use crate::mir::{
    Body, ConstantKind, EscapeSummary, LocalDecl, LocalId, LocalKind, Operand, ParamEscapeInfo,
    Place, PlaceElem, Rvalue, Statement, StatementKind, TerminatorKind,
};
use crate::sema::models::{GenericArguments, Ty, TyKind};
use rustc_hash::FxHashMap;

pub struct EscapeAnalysis;
pub struct ApplyEscapeAnalysis;

/// Compute escape summaries for all functions in the package.
/// Uses fixpoint iteration to handle recursive/mutually-recursive functions.
pub fn compute_escape_summaries<'ctx>(
    gcx: Gcx<'ctx>,
    functions: &FxHashMap<DefinitionID, &'ctx Body<'ctx>>,
) {
    let def_ids: Vec<DefinitionID> = functions.keys().copied().collect();

    // Initialize all summaries with "nothing escapes"
    let mut summaries: FxHashMap<DefinitionID, EscapeSummary> = FxHashMap::default();
    for &def_id in &def_ids {
        let sig = gcx.get_signature(def_id);
        summaries.insert(
            def_id,
            EscapeSummary {
                params: vec![ParamEscapeInfo::default(); sig.inputs.len()],
            },
        );
    }

    // Fixpoint iteration: keep refining summaries until no changes
    let mut changed = true;
    while changed {
        changed = false;
        for &def_id in &def_ids {
            if let Some(body) = functions.get(&def_id) {
                let new_summary = analyze_function_for_summary(gcx, body, &summaries);
                if summaries.get(&def_id) != Some(&new_summary) {
                    summaries.insert(def_id, new_summary);
                    changed = true;
                }
            }
        }
    }

    // Store computed summaries in the type database
    for (def_id, summary) in summaries {
        gcx.set_escape_summary(def_id, summary);
    }
}

/// Analyze a function body to produce its escape summary.
/// This tracks how parameters flow to returns or leak to the heap.
fn analyze_function_for_summary<'ctx>(
    _gcx: Gcx<'ctx>,
    body: &Body<'ctx>,
    current_summaries: &FxHashMap<DefinitionID, EscapeSummary>,
) -> EscapeSummary {
    let local_count = body.locals.len();

    // Map from local to parameter index (for params only)
    let mut local_to_param: FxHashMap<LocalId, usize> = FxHashMap::default();
    let mut param_count = 0;
    for (local_id, decl) in body.locals.iter_enumerated() {
        if decl.kind == LocalKind::Param {
            local_to_param.insert(local_id, param_count);
            param_count += 1;
        }
    }

    // Track which reference locals might contain references to parameters
    // ref_param_sources[local] = set of param indices this local might reference
    let mut ref_param_sources: Vec<Vec<usize>> = vec![Vec::new(); local_count];

    // Initialize: each param's local can reference itself
    for (local_id, &param_idx) in &local_to_param {
        ref_param_sources[local_id.index()].push(param_idx);
    }

    // Track escape info per parameter
    let mut param_escapes: Vec<ParamEscapeInfo> = vec![ParamEscapeInfo::default(); param_count];

    let is_ref_local: Vec<bool> = body
        .locals
        .iter()
        .map(|decl| matches!(decl.ty.kind(), TyKind::Reference(..)))
        .collect();

    // Analyze all statements and terminators
    for bb in body.basic_blocks.iter() {
        for stmt in &bb.statements {
            match &stmt.kind {
                // Reference creation: &x or &mut x
                StatementKind::Assign(dest, Rvalue::Ref { place, .. }) => {
                    if let Some(base) = base_local_for_ref(place) {
                        // If the base local is derived from a parameter...
                        let param_sources =
                            get_param_sources(base, &local_to_param, &ref_param_sources);

                        if dest.projection.is_empty() && dest.local == body.return_local {
                            // Reference flows to return
                            for param_idx in &param_sources {
                                param_escapes[*param_idx].flows_to_return = true;
                            }
                        } else if dest.projection.is_empty() && is_ref_local[dest.local.index()] {
                            // Propagate param sources to dest
                            for param_idx in param_sources {
                                if !ref_param_sources[dest.local.index()].contains(&param_idx) {
                                    ref_param_sources[dest.local.index()].push(param_idx);
                                }
                            }
                        } else {
                            // Reference stored somewhere unexpected - mark as heap leak
                            for param_idx in &param_sources {
                                param_escapes[*param_idx].leaks_to_heap = true;
                            }
                        }
                    }
                }
                // Reference copy/move
                StatementKind::Assign(dest, Rvalue::Use(op)) => {
                    if let Some(src_local) = ref_local_operand(body, op) {
                        let param_sources =
                            get_param_sources(src_local, &local_to_param, &ref_param_sources);

                        if dest.projection.is_empty() && dest.local == body.return_local {
                            // Reference flows to return
                            for param_idx in &param_sources {
                                param_escapes[*param_idx].flows_to_return = true;
                            }
                        } else if dest.projection.is_empty() && is_ref_local[dest.local.index()] {
                            // Propagate param sources to dest
                            for param_idx in param_sources {
                                if !ref_param_sources[dest.local.index()].contains(&param_idx) {
                                    ref_param_sources[dest.local.index()].push(param_idx);
                                }
                            }
                        } else {
                            // Reference stored somewhere unexpected
                            for param_idx in &param_sources {
                                param_escapes[*param_idx].leaks_to_heap = true;
                            }
                        }
                    }
                }
                _ => {}
            }
        }

        // Analyze call terminators
        if let Some(term) = &bb.terminator {
            if let TerminatorKind::Call { func, args, .. } = &term.kind {
                // Try to get callee info
                if let Some((callee_id, _)) = extract_callee(func) {
                    let callee_summary = current_summaries.get(&callee_id).or_else(|| {
                        // For external functions, use conservative default
                        None
                    });

                    for (arg_idx, arg) in args.iter().enumerate() {
                        if let Some(local) = ref_local_operand(body, arg) {
                            let param_sources =
                                get_param_sources(local, &local_to_param, &ref_param_sources);

                            // Check if this argument escapes according to callee's summary
                            let arg_leaks = callee_summary
                                .and_then(|s| s.params.get(arg_idx))
                                .map(|p| p.leaks_to_heap)
                                .unwrap_or(true); // Conservative default

                            if arg_leaks {
                                for param_idx in &param_sources {
                                    param_escapes[*param_idx].leaks_to_heap = true;
                                }
                            }
                        }
                    }
                } else {
                    // Unknown callee (function pointer, etc.) - all ref args leak
                    for arg in args {
                        if let Some(local) = ref_local_operand(body, arg) {
                            let param_sources =
                                get_param_sources(local, &local_to_param, &ref_param_sources);
                            for param_idx in &param_sources {
                                param_escapes[*param_idx].leaks_to_heap = true;
                            }
                        }
                    }
                }
            }
        }
    }

    EscapeSummary {
        params: param_escapes,
    }
}

/// Get the parameter indices that a local might reference.
fn get_param_sources(
    local: LocalId,
    local_to_param: &FxHashMap<LocalId, usize>,
    ref_param_sources: &[Vec<usize>],
) -> Vec<usize> {
    // If this local is directly a parameter
    if let Some(&param_idx) = local_to_param.get(&local) {
        return vec![param_idx];
    }
    // Otherwise, return tracked sources
    ref_param_sources
        .get(local.index())
        .cloned()
        .unwrap_or_default()
}

/// Extract callee definition ID and generic args from a call operand.
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

/// Get the default escape summary for an external function (FFI, intrinsic, runtime).
/// Conservative: all reference parameters are assumed to escape.
fn get_external_summary<'ctx>(gcx: Gcx<'ctx>, def_id: DefinitionID) -> EscapeSummary {
    let sig = gcx.get_signature(def_id);
    EscapeSummary {
        params: sig
            .inputs
            .iter()
            .map(|p| {
                let is_ref = matches!(p.ty.kind(), TyKind::Reference(..));
                ParamEscapeInfo {
                    leaks_to_heap: is_ref,
                    flows_to_return: is_ref,
                }
            })
            .collect(),
    }
}

impl<'ctx> MirPass<'ctx> for EscapeAnalysis {
    fn name(&self) -> &'static str {
        "EscapeAnalysis"
    }

    fn run(&mut self, gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
        let local_count = body.locals.len();
        body.escape_locals.clear();
        body.escape_locals.resize(local_count, false);

        // ref_bases[local] = list of base locals this reference local points to
        let mut ref_bases: Vec<Vec<LocalId>> = vec![Vec::new(); local_count];
        // ref_sources[local] = list of source reference locals this local was copied from
        let mut ref_sources: Vec<Vec<LocalId>> = vec![Vec::new(); local_count];
        // Whether each reference local has escaped
        let mut ref_escapes = vec![false; local_count];

        let is_ref_local: Vec<bool> = body
            .locals
            .iter()
            .map(|decl| matches!(decl.ty.kind(), TyKind::Reference(..)))
            .collect();

        for bb in body.basic_blocks.iter() {
            for stmt in &bb.statements {
                match &stmt.kind {
                    StatementKind::Assign(dest, Rvalue::Ref { place, .. }) => {
                        if let Some(base) = base_local_for_ref(place) {
                            // Direct return of reference
                            if dest.projection.is_empty() && dest.local == body.return_local {
                                body.escape_locals[base.index()] = true;
                                continue;
                            }

                            if dest.projection.is_empty() && is_ref_local[dest.local.index()] {
                                if !ref_bases[dest.local.index()].contains(&base) {
                                    ref_bases[dest.local.index()].push(base);
                                }
                            } else {
                                // Stored in non-reference location
                                body.escape_locals[base.index()] = true;
                            }
                        }
                    }
                    StatementKind::Assign(dest, Rvalue::Use(op)) => {
                        if let Some(src) = ref_local_operand(body, op) {
                            if dest.projection.is_empty() && is_ref_local[dest.local.index()] {
                                ref_sources[dest.local.index()].push(src);
                            } else {
                                ref_escapes[src.index()] = true;
                            }
                        }

                        // Direct return of reference
                        if dest.projection.is_empty() && dest.local == body.return_local {
                            if let Some(src) = ref_local_operand(body, op) {
                                ref_escapes[src.index()] = true;
                            }
                        }
                    }
                    _ => {}
                }
            }

            // Analyze calls with escape summaries
            if let Some(term) = &bb.terminator {
                if let TerminatorKind::Call { func, args, .. } = &term.kind {
                    // Try to get the callee's escape summary
                    let callee_summary = extract_callee(func).and_then(|(callee_id, _)| {
                        // First check if we have a computed summary
                        if let Some(summary) = gcx.get_escape_summary(callee_id) {
                            return Some(summary);
                        }
                        // For external functions, use conservative default
                        let sig = gcx.get_signature(callee_id);
                        if sig.abi.is_some() {
                            return Some(get_external_summary(gcx, callee_id));
                        }
                        None
                    });

                    for (arg_idx, arg) in args.iter().enumerate() {
                        if let Some(local) = ref_local_operand(body, arg) {
                            // Check if this argument escapes according to summary
                            let escapes = callee_summary
                                .as_ref()
                                .and_then(|s| s.params.get(arg_idx))
                                .map(|p| p.leaks_to_heap)
                                .unwrap_or(true); // Conservative default if no summary

                            if escapes {
                                ref_escapes[local.index()] = true;
                            }
                        }
                    }
                }
            }
        }

        // Propagate escapes through ref_sources using worklist
        let mut worklist: Vec<LocalId> = ref_escapes
            .iter()
            .enumerate()
            .filter_map(|(idx, &escaped)| escaped.then(|| LocalId::from_raw(idx as u32)))
            .collect();

        while let Some(local) = worklist.pop() {
            for &src in &ref_sources[local.index()] {
                if !ref_escapes[src.index()] {
                    ref_escapes[src.index()] = true;
                    worklist.push(src);
                }
            }
        }

        // Mark base locals as escaping if their references escape
        for (idx, bases) in ref_bases.iter().enumerate() {
            if !ref_escapes[idx] {
                continue;
            }
            for base in bases {
                body.escape_locals[base.index()] = true;
            }
        }

        Ok(())
    }
}

impl<'ctx> MirPass<'ctx> for ApplyEscapeAnalysis {
    fn name(&self) -> &'static str {
        "ApplyEscapeAnalysis"
    }

    fn run(&mut self, gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
        let mut heapified: Vec<Option<Ty<'ctx>>> = vec![None; body.locals.len()];
        let mut param_replacements: Vec<Option<LocalId>> = vec![None; body.locals.len()];
        let original_local_count = body.locals.len();

        for idx in 0..original_local_count {
            let kind = body.locals[idx].kind;
            if matches!(kind, LocalKind::Return) {
                continue;
            }
            if body.escape_locals.get(idx).copied().unwrap_or(false) {
                let old_ty = body.locals[idx].ty;
                let span = body.locals[idx].span;
                let new_ty = gcx
                    .store
                    .interners
                    .intern_ty(TyKind::Reference(old_ty, Mutability::Mutable));
                if matches!(kind, LocalKind::Param) {
                    let heap_local = body.locals.push(LocalDecl {
                        ty: new_ty,
                        kind: LocalKind::Temp,
                        mutable: true,
                        name: None,
                        span,
                    });
                    body.escape_locals.push(false);
                    heapified.push(Some(old_ty));
                    param_replacements[idx] = Some(heap_local);
                } else {
                    body.locals[idx].ty = new_ty;
                    heapified[idx] = Some(old_ty);
                }
            }
        }

        if heapified.iter().all(|item| item.is_none()) {
            return Ok(());
        }

        for bb in body.basic_blocks.iter_mut() {
            for stmt in &mut bb.statements {
                rewrite_statement(stmt, &heapified, &param_replacements);
            }
            if let Some(term) = &mut bb.terminator {
                rewrite_terminator(term, &heapified, &param_replacements);
            }
        }

        let span = body.locals[body.return_local].span;
        let mut allocs: Vec<Statement<'ctx>> = Vec::new();
        for (idx, ty) in heapified.iter().enumerate() {
            let Some(old_ty) = ty else { continue };
            let place = Place::from_local(LocalId::from_raw(idx as u32));
            allocs.push(Statement {
                kind: StatementKind::Assign(place, Rvalue::Alloc { ty: *old_ty }),
                span,
            });
        }

        let mut param_inits: Vec<Statement<'ctx>> = Vec::new();
        for (idx, heap_local) in param_replacements.iter().enumerate() {
            let Some(heap_local) = heap_local else {
                continue;
            };
            let heap_place = Place {
                local: *heap_local,
                projection: vec![PlaceElem::Deref],
            };
            let param_place = Place::from_local(LocalId::from_raw(idx as u32));
            param_inits.push(Statement {
                kind: StatementKind::Assign(heap_place, Rvalue::Use(Operand::Move(param_place))),
                span,
            });
        }

        if !allocs.is_empty() || !param_inits.is_empty() {
            let entry = body.start_block;
            let statements = &mut body.basic_blocks[entry].statements;
            let mut insertions = Vec::with_capacity(allocs.len() + param_inits.len());
            insertions.extend(allocs);
            insertions.extend(param_inits);
            statements.splice(0..0, insertions);
        }
        Ok(())
    }
}

// Helper functions

fn base_local_for_ref(place: &Place<'_>) -> Option<LocalId> {
    if place
        .projection
        .iter()
        .any(|elem| matches!(elem, PlaceElem::Deref))
    {
        return None;
    }
    Some(place.local)
}

fn ref_local_operand<'a>(body: &Body<'a>, operand: &Operand<'a>) -> Option<LocalId> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            if !place.projection.is_empty() {
                return None;
            }
            let ty = body.locals[place.local].ty;
            matches!(ty.kind(), TyKind::Reference(..)).then_some(place.local)
        }
        Operand::Constant(_) => None,
    }
}

fn rewrite_statement<'ctx>(
    stmt: &mut Statement<'ctx>,
    heapified: &[Option<Ty<'ctx>>],
    param_replacements: &[Option<LocalId>],
) {
    if let StatementKind::Assign(place, rvalue) = &mut stmt.kind {
        rewrite_place(place, heapified, param_replacements);
        rewrite_rvalue(rvalue, heapified, param_replacements);
    }
}

fn rewrite_rvalue<'ctx>(
    rvalue: &mut Rvalue<'ctx>,
    heapified: &[Option<Ty<'ctx>>],
    param_replacements: &[Option<LocalId>],
) {
    match rvalue {
        Rvalue::Use(op) => rewrite_operand(op, heapified, param_replacements),
        Rvalue::UnaryOp { operand, .. } => rewrite_operand(operand, heapified, param_replacements),
        Rvalue::BinaryOp { lhs, rhs, .. } => {
            rewrite_operand(lhs, heapified, param_replacements);
            rewrite_operand(rhs, heapified, param_replacements);
        }
        Rvalue::Cast { operand, .. } => rewrite_operand(operand, heapified, param_replacements),
        Rvalue::Ref { place, .. } => rewrite_place(place, heapified, param_replacements),
        Rvalue::Discriminant { place } => rewrite_place(place, heapified, param_replacements),
        Rvalue::Aggregate { fields, .. } => {
            for field in fields.iter_mut() {
                rewrite_operand(field, heapified, param_replacements);
            }
        }
        Rvalue::Repeat { operand, .. } => {
            rewrite_operand(operand, heapified, param_replacements);
        }
        Rvalue::Alloc { .. } => {}
    }
}

fn rewrite_operand<'ctx>(
    operand: &mut Operand<'ctx>,
    heapified: &[Option<Ty<'ctx>>],
    param_replacements: &[Option<LocalId>],
) {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            rewrite_place(place, heapified, param_replacements)
        }
        Operand::Constant(_) => {}
    }
}

fn rewrite_terminator<'ctx>(
    term: &mut crate::mir::Terminator<'ctx>,
    heapified: &[Option<Ty<'ctx>>],
    param_replacements: &[Option<LocalId>],
) {
    match &mut term.kind {
        TerminatorKind::SwitchInt { discr, .. } => {
            rewrite_operand(discr, heapified, param_replacements)
        }
        TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } => {
            rewrite_operand(func, heapified, param_replacements);
            for arg in args {
                rewrite_operand(arg, heapified, param_replacements);
            }
            rewrite_place(destination, heapified, param_replacements);
        }
        _ => {}
    }
}

fn rewrite_place<'ctx>(
    place: &mut Place<'ctx>,
    heapified: &[Option<Ty<'ctx>>],
    param_replacements: &[Option<LocalId>],
) {
    if let Some(local) = param_replacements
        .get(place.local.index())
        .and_then(|item| *item)
    {
        place.local = local;
    }

    if heapified
        .get(place.local.index())
        .and_then(|item| *item)
        .is_none()
    {
        return;
    }
    place.projection.insert(0, PlaceElem::Deref);
}
