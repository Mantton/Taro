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
    BasicBlockData, BasicBlockId, Body, CallUnwindAction, CastKind, ConstantKind, CopyModifiers,
    EscapeSummary, LocalDecl, LocalId, LocalKind, Operand, ParamEscapeInfo, Place, PlaceElem,
    Rvalue, Statement, StatementKind, Terminator, TerminatorKind,
};
use crate::sema::models::{GenericArguments, Ty, TyKind};
use index_vec::IndexVec;
use rustc_hash::{FxHashMap, FxHashSet};

pub struct EscapeAnalysis;
pub struct ApplyEscapeAnalysis;

/// Compute escape summaries for all functions in the package.
/// Uses fixpoint iteration to handle recursive/mutually-recursive functions.
pub fn compute_escape_summaries<'ctx>(
    gcx: Gcx<'ctx>,
    functions: &FxHashMap<DefinitionID, &'ctx Body<'ctx>>,
) {
    let def_ids: Vec<DefinitionID> = functions.keys().cloned().collect();

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
    gcx: Gcx<'ctx>,
    body: &Body<'ctx>,
    current_summaries: &FxHashMap<DefinitionID, EscapeSummary>,
) -> EscapeSummary {
    let local_count = body.locals.len();

    // Map from address-like local parameter to parameter index.
    let mut local_to_param: FxHashMap<LocalId, usize> = FxHashMap::default();
    let mut param_count = 0;
    for (local_id, decl) in body.locals.iter_enumerated() {
        if decl.kind == LocalKind::Param && is_address_like_ty(decl.ty) {
            local_to_param.insert(local_id, param_count);
        }
        if decl.kind == LocalKind::Param {
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
        .map(|decl| is_address_like_ty(decl.ty))
        .collect();

    // Analyze all statements and terminators
    for bb in body.basic_blocks.iter() {
        for stmt in &bb.statements {
            match &stmt.kind {
                // Reference creation: &x or &mut x
                StatementKind::Assign(dest, Rvalue::Ref { place, .. }) => {
                    // A base and a reborrow both carry the provenance of
                    // `place.local`: for a base it is the referent itself, for a
                    // reborrow it is the reference already recorded as pointing
                    // at a parameter.
                    if let Some(source) = ref_source_for_place(place, &is_ref_local) {
                        let param_sources =
                            get_param_sources(source.local(), &local_to_param, &ref_param_sources);

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
                // Reference copy/move, including a reference-to-pointer cast.
                // Runtime APIs commonly erase a managed reference to `*u8`;
                // that cast must not sever its escape provenance.
                StatementKind::Assign(dest, Rvalue::Use(op))
                | StatementKind::Assign(
                    dest,
                    Rvalue::Cast {
                        operand: op,
                        kind: CastKind::Pointer | CastKind::Numeric,
                        ..
                    },
                ) => {
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
                // Building a struct, tuple, enum payload or array out of a
                // reference puts it somewhere this analysis cannot follow, so
                // the parameter it came from has to be assumed reachable.
                StatementKind::Assign(_, Rvalue::Aggregate { fields, .. }) => {
                    for field in fields.iter() {
                        if let Some(src_local) = ref_local_operand(body, field) {
                            for param_idx in
                                get_param_sources(src_local, &local_to_param, &ref_param_sources)
                            {
                                param_escapes[param_idx].leaks_to_heap = true;
                            }
                        }
                    }
                }
                StatementKind::Assign(_, Rvalue::Repeat { operand, .. }) => {
                    if let Some(src_local) = ref_local_operand(body, operand) {
                        for param_idx in
                            get_param_sources(src_local, &local_to_param, &ref_param_sources)
                        {
                            param_escapes[param_idx].leaks_to_heap = true;
                        }
                    }
                }
                _ => {}
            }
        }

        // Analyze call terminators
        if let Some(term) = &bb.terminator {
            if let TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } = &term.kind
            {
                // Try to get callee info
                if let Some((callee_id, _)) = extract_callee(func) {
                    let callee_summary = current_summaries.get(&callee_id).cloned().or_else(|| {
                        gcx.get_signature(callee_id)
                            .abi
                            .is_some()
                            .then(|| get_external_summary(gcx, callee_id))
                    });

                    for (arg_idx, arg) in args.iter().enumerate() {
                        if let Some(local) = ref_local_operand(body, arg) {
                            let param_sources =
                                get_param_sources(local, &local_to_param, &ref_param_sources);

                            // Check if this argument escapes according to callee's summary
                            let arg_leaks = callee_summary
                                .as_ref()
                                .and_then(|s| s.params.get(arg_idx))
                                .map(|p| p.leaks_to_heap)
                                .unwrap_or(true); // Conservative default

                            if arg_leaks {
                                for param_idx in &param_sources {
                                    param_escapes[*param_idx].leaks_to_heap = true;
                                }
                            }

                            // A callee that hands the argument back keeps it
                            // reachable through the result, so the result
                            // carries the argument's provenance onwards.
                            let arg_returns = callee_summary
                                .as_ref()
                                .and_then(|s| s.params.get(arg_idx))
                                .map(|p| p.flows_to_return)
                                .unwrap_or(true);

                            if arg_returns {
                                if destination.projection.is_empty()
                                    && destination.local != body.return_local
                                    && is_ref_local[destination.local.index()]
                                {
                                    for param_idx in param_sources {
                                        if !ref_param_sources[destination.local.index()]
                                            .contains(&param_idx)
                                        {
                                            ref_param_sources[destination.local.index()]
                                                .push(param_idx);
                                        }
                                    }
                                } else {
                                    // The result leaves this function, so the
                                    // parameter it came from does too.
                                    for param_idx in &param_sources {
                                        param_escapes[*param_idx].flows_to_return = true;
                                    }
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
    // `keepAlive` is a compiler-visible liveness barrier. The runtime observes
    // the address for the duration of the call but never stores or returns it,
    // so treating it like ordinary FFI would cause needless heap promotion.
    let noescape = gcx.symbol_eq(
        gcx.definition_symbol_or_fallback(def_id),
        "__rt__keep_alive",
    );
    EscapeSummary {
        params: sig
            .inputs
            .iter()
            .map(|p| {
                let is_ref = is_address_like_ty(p.ty) && !noescape;
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
            .map(|decl| is_address_like_ty(decl.ty))
            .collect();

        for bb in body.basic_blocks.iter() {
            for stmt in &bb.statements {
                match &stmt.kind {
                    StatementKind::Assign(dest, Rvalue::Ref { place, .. }) => {
                        let returns_directly =
                            dest.projection.is_empty() && dest.local == body.return_local;
                        let into_ref_local =
                            dest.projection.is_empty() && is_ref_local[dest.local.index()];

                        match ref_source_for_place(place, &is_ref_local) {
                            Some(RefSource::Base(base)) => {
                                if returns_directly {
                                    body.escape_locals[base.index()] = true;
                                } else if into_ref_local {
                                    if !ref_bases[dest.local.index()].contains(&base) {
                                        ref_bases[dest.local.index()].push(base);
                                    }
                                } else {
                                    // Stored in non-reference location
                                    body.escape_locals[base.index()] = true;
                                }
                            }
                            // A reborrow escapes exactly when the reference it
                            // was taken through does, so it inherits that
                            // reference's bases rather than naming its own.
                            Some(RefSource::Reborrow(source)) => {
                                if into_ref_local && !returns_directly {
                                    ref_sources[dest.local.index()].push(source);
                                } else {
                                    ref_escapes[source.index()] = true;
                                }
                            }
                            None => {}
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
                    // A reference built into a struct, tuple, enum payload or
                    // array goes somewhere this analysis cannot follow, so its
                    // referent has to outlive the frame.
                    StatementKind::Assign(_, Rvalue::Aggregate { fields, .. }) => {
                        for field in fields.iter() {
                            if let Some(src) = ref_local_operand(body, field) {
                                ref_escapes[src.index()] = true;
                            }
                        }
                    }
                    StatementKind::Assign(_, Rvalue::Repeat { operand, .. }) => {
                        if let Some(src) = ref_local_operand(body, operand) {
                            ref_escapes[src.index()] = true;
                        }
                    }
                    _ => {}
                }
            }

            // Analyze calls with escape summaries
            if let Some(term) = &bb.terminator {
                if let TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    ..
                } = &term.kind
                {
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

                            // The result of a call that hands the argument back
                            // still points at whatever the argument did, so it
                            // keeps that argument's bases alive.
                            let returns = callee_summary
                                .as_ref()
                                .and_then(|s| s.params.get(arg_idx))
                                .map(|p| p.flows_to_return)
                                .unwrap_or(true);

                            if returns {
                                if destination.projection.is_empty()
                                    && destination.local != body.return_local
                                    && is_ref_local[destination.local.index()]
                                {
                                    // A plain reference result can be followed.
                                    ref_sources[destination.local.index()].push(local);
                                } else {
                                    // Returned straight out of this function, or
                                    // into an aggregate whose references this
                                    // analysis does not track. Either way the
                                    // referent outlives the frame.
                                    ref_escapes[local.index()] = true;
                                }
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
            if body.escape_locals.get(idx).cloned().unwrap_or(false) {
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

        rewrite_fresh_heapified_initializations(body, &heapified);

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
                kind: StatementKind::Assign(heap_place, Rvalue::Use(Operand::Copy(param_place))),
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

fn rewrite_fresh_heapified_initializations<'ctx>(
    body: &mut Body<'ctx>,
    heapified: &[Option<Ty<'ctx>>],
) {
    let may_assigned_in = compute_heapified_may_assigned_in(body, heapified);
    let original_blocks: Vec<BasicBlockId> = body.basic_blocks.indices().collect();

    for bb in original_blocks {
        let mut assigned = may_assigned_in[bb].clone();

        let old_statements = std::mem::take(&mut body.basic_blocks[bb].statements);
        let mut new_statements = Vec::with_capacity(old_statements.len());
        for stmt in old_statements {
            let span = stmt.span;
            match stmt.kind {
                StatementKind::Assign(destination, rvalue) => {
                    if let Some(pointee_ty) =
                        heapified_direct_deref_pointee_ty(&destination, heapified)
                    {
                        let is_first_write = !assigned.contains(&destination.local);
                        assigned.insert(destination.local);
                        if is_first_write {
                            let tmp_local = body.locals.push(LocalDecl {
                                ty: pointee_ty,
                                kind: LocalKind::Temp,
                                mutable: true,
                                name: None,
                                span,
                            });
                            body.escape_locals.push(false);
                            new_statements.push(Statement {
                                kind: StatementKind::Assign(Place::from_local(tmp_local), rvalue),
                                span,
                            });
                            new_statements.push(Statement {
                                kind: StatementKind::Assign(
                                    destination,
                                    Rvalue::Use(Operand::copy_with(
                                        Place::from_local(tmp_local),
                                        CopyModifiers {
                                            init: true,
                                            take: true,
                                        },
                                    )),
                                ),
                                span,
                            });
                            continue;
                        }
                    }

                    new_statements.push(Statement {
                        kind: StatementKind::Assign(destination, rvalue),
                        span,
                    });
                }
                other => new_statements.push(Statement { kind: other, span }),
            }
        }
        body.basic_blocks[bb].statements = new_statements;

        let Some(mut term) = body.basic_blocks[bb].terminator.take() else {
            continue;
        };
        if let TerminatorKind::Call {
            destination,
            target,
            ..
        } = &mut term.kind
        {
            if let Some(pointee_ty) = heapified_direct_deref_pointee_ty(destination, heapified) {
                let is_first_write = !assigned.contains(&destination.local);
                assigned.insert(destination.local);
                if is_first_write {
                    let original_destination = destination.clone();
                    let tmp_local = body.locals.push(LocalDecl {
                        ty: pointee_ty,
                        kind: LocalKind::Temp,
                        mutable: true,
                        name: None,
                        span: term.span,
                    });
                    body.escape_locals.push(false);
                    *destination = Place::from_local(tmp_local);

                    let original_target = *target;
                    let init_block = body.basic_blocks.push(BasicBlockData {
                        note: Some("escape-init-call-destination".into()),
                        statements: vec![Statement {
                            kind: StatementKind::Assign(
                                original_destination,
                                Rvalue::Use(Operand::copy_with(
                                    Place::from_local(tmp_local),
                                    CopyModifiers {
                                        init: true,
                                        take: true,
                                    },
                                )),
                            ),
                            span: term.span,
                        }],
                        terminator: Some(Terminator {
                            kind: TerminatorKind::Goto {
                                target: original_target,
                            },
                            span: term.span,
                        }),
                    });
                    *target = init_block;
                }
            }
        }
        body.basic_blocks[bb].terminator = Some(term);
    }
}

fn compute_heapified_may_assigned_in<'ctx>(
    body: &Body<'ctx>,
    heapified: &[Option<Ty<'ctx>>],
) -> IndexVec<BasicBlockId, FxHashSet<LocalId>> {
    let mut in_sets: IndexVec<BasicBlockId, FxHashSet<LocalId>> =
        IndexVec::from(vec![FxHashSet::default(); body.basic_blocks.len()]);
    let mut out_sets: IndexVec<BasicBlockId, FxHashSet<LocalId>> =
        IndexVec::from(vec![FxHashSet::default(); body.basic_blocks.len()]);

    let preds = build_predecessors(body);
    let succs = build_successors(body);
    let mut worklist: Vec<BasicBlockId> = body.basic_blocks.indices().collect();

    while let Some(bb) = worklist.pop() {
        let mut new_in = FxHashSet::default();
        for &pred in &preds[bb] {
            for &local in &out_sets[pred] {
                new_in.insert(local);
            }
        }

        let mut new_out = new_in.clone();
        let block = &body.basic_blocks[bb];
        for stmt in &block.statements {
            apply_heapified_statement_def(stmt, heapified, &mut new_out);
        }
        if let Some(term) = &block.terminator {
            apply_heapified_terminator_def(&term.kind, heapified, &mut new_out);
        }

        let changed = new_in != in_sets[bb] || new_out != out_sets[bb];
        if changed {
            in_sets[bb] = new_in;
            out_sets[bb] = new_out;
            for &succ in &succs[bb] {
                worklist.push(succ);
            }
        }
    }

    in_sets
}

fn apply_heapified_statement_def<'ctx>(
    stmt: &Statement<'ctx>,
    heapified: &[Option<Ty<'ctx>>],
    assigned: &mut FxHashSet<LocalId>,
) {
    if let StatementKind::Assign(destination, _) = &stmt.kind {
        if heapified_direct_deref_pointee_ty(destination, heapified).is_some() {
            assigned.insert(destination.local);
        }
    }
}

fn apply_heapified_terminator_def<'ctx>(
    term: &TerminatorKind<'ctx>,
    heapified: &[Option<Ty<'ctx>>],
    assigned: &mut FxHashSet<LocalId>,
) {
    if let TerminatorKind::Call { destination, .. } = term {
        if heapified_direct_deref_pointee_ty(destination, heapified).is_some() {
            assigned.insert(destination.local);
        }
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

fn build_successors(body: &Body<'_>) -> IndexVec<BasicBlockId, Vec<BasicBlockId>> {
    let mut succs: IndexVec<BasicBlockId, Vec<BasicBlockId>> =
        IndexVec::from(vec![Vec::new(); body.basic_blocks.len()]);
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        if let Some(term) = &data.terminator {
            succs[bb] = terminator_successors(&term.kind);
        }
    }
    succs
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
        TerminatorKind::Yield {
            resume,
            cancel,
            unwind,
            ..
        } => {
            let mut out = vec![*resume, *cancel];
            if let CallUnwindAction::Cleanup(bb) = unwind {
                out.push(*bb);
            }
            out
        }
        TerminatorKind::Return
        | TerminatorKind::ResumeUnwind
        | TerminatorKind::Unreachable
        | TerminatorKind::UnresolvedGoto => Vec::new(),
    }
}

fn heapified_direct_deref_pointee_ty<'ctx>(
    place: &Place<'ctx>,
    heapified: &[Option<Ty<'ctx>>],
) -> Option<Ty<'ctx>> {
    if place.projection.len() != 1 || !matches!(place.projection[0], PlaceElem::Deref) {
        return None;
    }
    heapified
        .get(place.local.index())
        .and_then(|item| item.as_ref().copied())
}

// Helper functions

/// Where a newly created reference inherits its provenance from.
#[derive(Clone, Copy)]
enum RefSource {
    /// The reference points at this local, as `&local` or `&local.field` does.
    Base(LocalId),
    /// The reference points into whatever this reference local points at.
    ///
    /// This is a reborrow: `&(*r).field`. Pattern matching lowers every payload
    /// binding this way, so missing it loses the connection between a match on
    /// `&local` and the reference the arm hands out.
    Reborrow(LocalId),
}

impl RefSource {
    fn local(self) -> LocalId {
        match self {
            RefSource::Base(local) | RefSource::Reborrow(local) => local,
        }
    }
}

fn ref_source_for_place(place: &Place<'_>, is_ref_local: &[bool]) -> Option<RefSource> {
    let mut elements = place.projection.iter();
    let reborrows = matches!(elements.next(), Some(PlaceElem::Deref));

    // A `Deref` past the first dereferences a reference loaded out of memory,
    // whose provenance this analysis does not follow.
    if elements.any(|elem| matches!(elem, PlaceElem::Deref)) {
        return None;
    }

    if !reborrows {
        return Some(RefSource::Base(place.local));
    }
    is_ref_local
        .get(place.local.index())
        .copied()
        .unwrap_or(false)
        .then_some(RefSource::Reborrow(place.local))
}

fn ref_local_operand<'a>(body: &Body<'a>, operand: &Operand<'a>) -> Option<LocalId> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) | Operand::CopyWith(place, _) => {
            if !place.projection.is_empty() {
                return None;
            }
            let ty = body.locals[place.local].ty;
            is_address_like_ty(ty).then_some(place.local)
        }
        Operand::Constant(_) => None,
    }
}

fn is_address_like_ty(ty: Ty<'_>) -> bool {
    matches!(ty.kind(), TyKind::Reference(..) | TyKind::Pointer(..))
}

fn rewrite_statement<'ctx>(
    stmt: &mut Statement<'ctx>,
    heapified: &[Option<Ty<'ctx>>],
    param_replacements: &[Option<LocalId>],
) {
    match &mut stmt.kind {
        StatementKind::Assign(place, rvalue) => {
            rewrite_place(place, heapified, param_replacements);
            rewrite_rvalue(rvalue, heapified, param_replacements);
        }
        StatementKind::SetDiscriminant { place, .. } => {
            // Enum aggregate lowering runs before escape analysis. Once an
            // address-taken enum local is heapified, its already-lowered tag
            // write must target the pointee just like an ordinary assignment.
            rewrite_place(place, heapified, param_replacements);
        }
        StatementKind::ShadowResync(_) | StatementKind::GcSafepoint | StatementKind::Nop => {}
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
        Operand::Copy(place) | Operand::Move(place) | Operand::CopyWith(place, _) => {
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

#[cfg(test)]
mod tests {
    use super::analyze_function_for_summary;
    use crate::{
        hir::Mutability,
        mir::{
            AggregateKind, CastKind, LocalDecl, LocalId, LocalKind, Operand, Place, PlaceElem,
            Rvalue, Statement, StatementKind,
            test_support::{minimal_body, push_temp, with_test_gcx},
        },
        sema::models::{Ty, TyKind},
    };
    use index_vec::IndexVec;
    use rustc_hash::FxHashMap;

    fn push_parameter<'ctx>(body: &mut crate::mir::Body<'ctx>, ty: Ty<'ctx>) -> LocalId {
        let span = body.locals[body.return_local].span;
        body.escape_locals.push(false);
        body.locals.push(LocalDecl {
            ty,
            kind: LocalKind::Param,
            mutable: false,
            name: None,
            span,
        })
    }

    #[test]
    fn pointer_cast_kinds_preserve_parameter_escape_provenance() {
        with_test_gcx(|gcx| {
            for kind in [CastKind::Pointer, CastKind::Numeric] {
                let mut body = minimal_body(gcx);
                let span = body.locals[body.return_local].span;
                let reference_ty = Ty::new(
                    TyKind::Reference(gcx.types.uint8, Mutability::Immutable),
                    gcx,
                );
                let pointer_ty =
                    Ty::new(TyKind::Pointer(gcx.types.uint8, Mutability::Immutable), gcx);
                body.locals[body.return_local].ty = pointer_ty;

                let parameter = push_parameter(&mut body, reference_ty);
                let erased = push_temp(&mut body, pointer_ty);
                body.basic_blocks[body.start_block].statements.extend([
                    Statement {
                        kind: StatementKind::Assign(
                            Place::from_local(erased),
                            Rvalue::Cast {
                                operand: Operand::Copy(Place::from_local(parameter)),
                                ty: pointer_ty,
                                kind,
                            },
                        ),
                        span,
                    },
                    Statement {
                        kind: StatementKind::Assign(
                            Place::from_local(body.return_local),
                            Rvalue::Use(Operand::Copy(Place::from_local(erased))),
                        ),
                        span,
                    },
                ]);

                let summary = analyze_function_for_summary(gcx, &body, &FxHashMap::default());
                assert_eq!(summary.params.len(), 1);
                assert!(
                    summary.params[0].flows_to_return,
                    "{kind:?} cast should preserve reference provenance"
                );
            }
        });
    }

    #[test]
    fn reborrow_preserves_parameter_return_provenance() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let span = body.locals[body.return_local].span;
            let reference_ty = Ty::new(
                TyKind::Reference(gcx.types.uint8, Mutability::Immutable),
                gcx,
            );
            body.locals[body.return_local].ty = reference_ty;

            let parameter = push_parameter(&mut body, reference_ty);
            let reborrow = push_temp(&mut body, reference_ty);
            body.basic_blocks[body.start_block].statements.extend([
                Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(reborrow),
                        Rvalue::Ref {
                            mutable: false,
                            place: Place {
                                local: parameter,
                                projection: vec![PlaceElem::Deref],
                            },
                        },
                    ),
                    span,
                },
                Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(body.return_local),
                        Rvalue::Use(Operand::Copy(Place::from_local(reborrow))),
                    ),
                    span,
                },
            ]);

            let summary = analyze_function_for_summary(gcx, &body, &FxHashMap::default());
            assert_eq!(summary.params.len(), 1);
            assert!(summary.params[0].flows_to_return);
        });
    }

    #[test]
    fn aggregate_and_repeat_storage_mark_reference_parameters_as_escaping() {
        with_test_gcx(|gcx| {
            for aggregate in [true, false] {
                let mut body = minimal_body(gcx);
                let span = body.locals[body.return_local].span;
                let reference_ty = Ty::new(
                    TyKind::Reference(gcx.types.uint8, Mutability::Immutable),
                    gcx,
                );
                let parameter = push_parameter(&mut body, reference_ty);
                let destination = push_temp(&mut body, gcx.types.void);
                let operand = Operand::Copy(Place::from_local(parameter));
                let value = if aggregate {
                    Rvalue::Aggregate {
                        kind: AggregateKind::Tuple,
                        fields: IndexVec::from_vec(vec![operand]),
                    }
                } else {
                    Rvalue::Repeat {
                        operand,
                        count: 2,
                        element: reference_ty,
                    }
                };
                body.basic_blocks[body.start_block]
                    .statements
                    .push(Statement {
                        kind: StatementKind::Assign(Place::from_local(destination), value),
                        span,
                    });

                let summary = analyze_function_for_summary(gcx, &body, &FxHashMap::default());
                assert_eq!(summary.params.len(), 1);
                assert!(
                    summary.params[0].leaks_to_heap,
                    "{} storage should make the reference escape",
                    if aggregate { "aggregate" } else { "repeat" }
                );
            }
        });
    }
}
