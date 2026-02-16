//! MIR validation passes that check for semantic errors.
//!
//! These validations run after MIR building to catch errors that are easier
//! to detect at the MIR level than during type checking.

use crate::{
    compile::context::Gcx,
    error::CompileResult,
    mir::{
        BasicBlockId, Body, CallUnwindAction, LocalId, Operand, Place, PlaceElem, Rvalue,
        StatementKind, TerminatorKind,
    },
    sema::models::TyKind,
    thir::FieldIndex,
};
use rustc_hash::{FxHashMap, FxHashSet};

use super::MirPass;

// ============================================================================
// MirPass Wrappers
// ============================================================================

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

// ============================================================================
// Mutability Validation
// ============================================================================

/// Validates that mutable borrows only occur on mutable places.
///
/// This check ensures that code like:
/// ```ignore
/// let a: [int32: string] = [:]
/// a.insert(key: 10, value: "Hello")  // Error: cannot borrow immutable local `a` as mutable
/// ```
/// is rejected.
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
                // Check if the base local is mutable
                if !is_place_mutable(gcx, body, place) {
                    let local_decl = &body.locals[place.local];
                    let name_str = local_decl
                        .name
                        .map(|s| format!("'{}'", s))
                        .unwrap_or_else(|| "<temporary>".to_string());
                    gcx.dcx().emit_error(
                        format!("cannot borrow immutable local {} as mutable", name_str).into(),
                        Some(stmt.span),
                    );
                }
            }
        }
    }
    gcx.dcx().ok()
}

/// Determines if a place is mutable.
///
/// A place is mutable if:
/// - The base local is declared mutable (for value types), OR
/// - The base local holds a mutable reference/pointer (for ref types), AND
/// - All projections through references are to mutable references
fn is_place_mutable<'ctx>(
    _: Gcx<'ctx>,
    body: &Body<'ctx>,
    place: &crate::mir::Place<'ctx>,
) -> bool {
    let local_decl = &body.locals[place.local];
    let mut current_ty = local_decl.ty;

    // For reference/pointer types, the mutability comes from the reference itself,
    // not from whether the local is mutable. A local holding `&mut T` can be immutable
    // (we never reassign it), but we can still take mutable borrows through it.
    let base_is_mutable = match current_ty.kind() {
        TyKind::Reference(_, mutability) | TyKind::Pointer(_, mutability) => {
            // For reference types, check the reference's mutability
            mutability == crate::hir::Mutability::Mutable
        }
        _ => {
            // For value types, check the local's mutability
            local_decl.mutable
        }
    };

    if !base_is_mutable {
        return false;
    }

    // Walk the projection to check for immutable reference dereferences
    for elem in &place.projection {
        match elem {
            PlaceElem::Deref => {
                // If dereferencing an immutable reference, the result is not mutable
                match current_ty.kind() {
                    TyKind::Reference(inner, mutability) => {
                        if mutability == crate::hir::Mutability::Immutable {
                            return false;
                        }
                        current_ty = inner;
                    }
                    TyKind::Pointer(inner, mutability) => {
                        if mutability == crate::hir::Mutability::Immutable {
                            return false;
                        }
                        current_ty = inner;
                    }
                    _ => {
                        // Shouldn't happen but continue anyway
                        return true;
                    }
                }
            }
            PlaceElem::Field(_, field_ty) => {
                current_ty = *field_ty;
            }
            PlaceElem::VariantDowncast { .. } => {
                // Type doesn't change for variant downcast, patterns should handle this
            }
        }
    }

    true
}

// ============================================================================
// Use-After-Move Validation
// ============================================================================

/// Tracks initialization state of places (supports partial moves).
#[derive(Clone, Default)]
struct MoveState {
    /// Fully moved locals.
    moved_locals: FxHashSet<LocalId>,
    /// Partially moved locals with specific moved fields.
    partial_moves: FxHashMap<LocalId, FxHashSet<FieldIndex>>,
}

impl MoveState {
    /// Merge another state into this one (union of moved values).
    /// Returns true if this state changed.
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

        changed
    }

    /// Mark a local as fully moved.
    fn mark_moved(&mut self, local: LocalId) {
        self.moved_locals.insert(local);
        self.partial_moves.remove(&local);
    }

    /// Mark a field of a local as moved (partial move).
    fn mark_field_moved(&mut self, local: LocalId, field: FieldIndex) {
        // If already fully moved, nothing more to do
        if self.moved_locals.contains(&local) {
            return;
        }
        self.partial_moves.entry(local).or_default().insert(field);
    }

    /// Reinitialize a local (assignment clears moved state).
    fn reinitialize(&mut self, local: LocalId) {
        self.moved_locals.remove(&local);
        self.partial_moves.remove(&local);
    }

    /// Check if a local is fully moved.
    fn is_moved(&self, local: LocalId) -> bool {
        self.moved_locals.contains(&local)
    }

    /// Check if a specific field is moved.
    fn is_field_moved(&self, local: LocalId, field: FieldIndex) -> bool {
        if self.moved_locals.contains(&local) {
            return true;
        }
        self.partial_moves
            .get(&local)
            .map(|fields| fields.contains(&field))
            .unwrap_or(false)
    }
}

/// Validates that moved values are not used after being moved.
///
/// This check ensures that code like:
/// ```ignore
/// let x = SomeNonCopyableType { ... }
/// let y = x  // moves x
/// let z = x  // ERROR: use of moved value 'x'
/// ```
/// is rejected.
pub fn validate_moves<'ctx>(gcx: Gcx<'ctx>, body: &Body<'ctx>) -> CompileResult<()> {
    // Per-block entry states (for proper dataflow)
    let mut block_states: FxHashMap<BasicBlockId, MoveState> = FxHashMap::default();

    // Worklist algorithm for fixed-point iteration
    let mut worklist: Vec<BasicBlockId> = vec![body.start_block];
    block_states.insert(body.start_block, MoveState::default());

    while let Some(bb_id) = worklist.pop() {
        let entry_state = block_states.get(&bb_id).cloned().unwrap_or_default();
        let mut state = entry_state;
        let block = &body.basic_blocks[bb_id];

        for stmt in &block.statements {
            match &stmt.kind {
                StatementKind::Assign(dest, rvalue) => {
                    // First check uses in the rvalue
                    check_rvalue_uses(gcx, body, &state, rvalue, stmt.span)?;

                    // Assignment reinitializes the destination
                    state.reinitialize(dest.local);

                    // Collect moves from rvalue
                    collect_moves_from_rvalue(gcx, body, rvalue, &mut state);
                }
                StatementKind::SetDiscriminant { .. }
                | StatementKind::GcSafepoint
                | StatementKind::Nop => {}
            }
        }

        // Process terminator
        if let Some(term) = &block.terminator {
            check_terminator_uses(gcx, body, &state, term)?;
            collect_moves_from_terminator(gcx, body, term, &mut state);

            // Propagate state to successors
            for succ in successors(&term.kind) {
                let changed = if let Some(succ_state) = block_states.get_mut(&succ) {
                    succ_state.merge(&state)
                } else {
                    block_states.insert(succ, state.clone());
                    true
                };

                if changed && !worklist.contains(&succ) {
                    worklist.push(succ);
                }
            }
        }
    }

    gcx.dcx().ok()
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
        TerminatorKind::Return
        | TerminatorKind::ResumeUnwind
        | TerminatorKind::Unreachable
        | TerminatorKind::UnresolvedGoto => vec![],
    }
}

/// Check that operands in an rvalue are not moved.
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

/// Check that operands in a terminator are not moved.
fn check_terminator_uses<'ctx>(
    gcx: Gcx<'ctx>,
    body: &Body<'ctx>,
    state: &MoveState,
    term: &crate::mir::Terminator<'ctx>,
) -> CompileResult<()> {
    let span = term.span;
    match &term.kind {
        TerminatorKind::SwitchInt { discr, .. } => {
            check_operand(gcx, body, state, discr, span)?;
        }
        TerminatorKind::Call { func, args, .. } => {
            check_operand(gcx, body, state, func, span)?;
            for arg in args {
                check_operand(gcx, body, state, arg, span)?;
            }
        }
        TerminatorKind::Goto { .. }
        | TerminatorKind::Return
        | TerminatorKind::ResumeUnwind
        | TerminatorKind::Unreachable
        | TerminatorKind::UnresolvedGoto => {}
    }
    Ok(())
}

/// Check that an operand is not using a moved value.
fn check_operand<'ctx>(
    gcx: Gcx<'ctx>,
    body: &Body<'ctx>,
    state: &MoveState,
    operand: &Operand<'ctx>,
    span: crate::span::Span,
) -> CompileResult<()> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            check_place_not_moved(gcx, body, state, place, span)?;
            if matches!(operand, Operand::Move(_)) {
                check_borrow_move(gcx, body, place, span)?;
            }
        }
        Operand::Constant(_) => {}
    }
    Ok(())
}

/// Check that we are not moving out of a reference (unless Copy).
fn check_borrow_move<'ctx>(
    gcx: Gcx<'ctx>,
    body: &Body<'ctx>,
    place: &Place<'ctx>,
    span: crate::span::Span,
) -> CompileResult<()> {
    let local_decl = &body.locals[place.local];
    let mut current_ty = local_decl.ty;
    let mut moved_out_of_reference = false;

    // quick check: if the place is just a local, we can't be moving out of a reference
    if place.projection.is_empty() {
        return Ok(());
    }

    for elem in &place.projection {
        match elem {
            PlaceElem::Deref => {
                match current_ty.kind() {
                    TyKind::Reference(inner, _) => {
                        moved_out_of_reference = true;
                        current_ty = inner;
                    }
                    TyKind::Pointer(inner, _) => {
                        // Pointers are ignored for now (unsafe)
                        current_ty = inner;
                    }
                    _ => {
                        // Attempt to deref other types if possible
                        if let Some(inner) = current_ty.dereference() {
                            current_ty = inner;
                        }
                    }
                }
            }
            PlaceElem::Field(_, field_ty) => {
                current_ty = *field_ty;
            }
            PlaceElem::VariantDowncast { .. } => {
                // Type stays the same (enum)
            }
        }
    }

    if moved_out_of_reference {
        if !gcx.is_type_copyable(current_ty) {
            gcx.dcx().emit_error(
                format!("cannot move out of borrowed content").into(),
                Some(span),
            );
            return gcx.dcx().ok();
        }
    }

    Ok(())
}

fn check_place_not_moved<'ctx>(
    gcx: Gcx<'ctx>,
    body: &Body<'ctx>,
    state: &MoveState,
    place: &Place<'ctx>,
    span: crate::span::Span,
) -> CompileResult<()> {
    let local_decl = &body.locals[place.local];

    // Check if the local is fully moved
    if state.is_moved(place.local) {
        let name = local_decl
            .name
            .map(|s| format!("'{}'", s))
            .unwrap_or_else(|| "<temporary>".to_string());
        gcx.dcx()
            .emit_error(format!("use of moved value {}", name).into(), Some(span));
        return gcx.dcx().ok();
    }

    // Check if we're accessing a moved field
    if let Some(PlaceElem::Field(idx, _)) = place.projection.first() {
        if state.is_field_moved(place.local, *idx) {
            let name = local_decl
                .name
                .map(|s| format!("'{}'", s))
                .unwrap_or_else(|| "<temporary>".to_string());
            gcx.dcx().emit_error(
                format!(
                    "use of partially moved value {} (field already moved)",
                    name
                )
                .into(),
                Some(span),
            );
            return gcx.dcx().ok();
        }
    }

    // Check if we're trying to use a partially moved value as a whole
    if place.projection.is_empty() && state.partial_moves.contains_key(&place.local) {
        let name = local_decl
            .name
            .map(|s| format!("'{}'", s))
            .unwrap_or_else(|| "<temporary>".to_string());
        gcx.dcx().emit_error(
            format!("use of partially moved value {}", name).into(),
            Some(span),
        );
        return gcx.dcx().ok();
    }

    Ok(())
}

/// Collect moves from an rvalue.
fn collect_moves_from_rvalue<'ctx>(
    _gcx: Gcx<'ctx>,
    _body: &Body<'ctx>,
    rvalue: &Rvalue<'ctx>,
    state: &mut MoveState,
) {
    match rvalue {
        Rvalue::Use(op) => collect_move_from_operand(op, state),
        Rvalue::UnaryOp { operand, .. } => collect_move_from_operand(operand, state),
        Rvalue::BinaryOp { lhs, rhs, .. } => {
            collect_move_from_operand(lhs, state);
            collect_move_from_operand(rhs, state);
        }
        Rvalue::Cast { operand, .. } => collect_move_from_operand(operand, state),
        Rvalue::Aggregate { fields, .. } => {
            for op in fields.iter() {
                collect_move_from_operand(op, state);
            }
        }
        Rvalue::Repeat { operand, .. } => collect_move_from_operand(operand, state),
        Rvalue::Ref { .. } | Rvalue::Discriminant { .. } | Rvalue::Alloc { .. } => {}
    }
}

/// Collect moves from a terminator.
fn collect_moves_from_terminator<'ctx>(
    _gcx: Gcx<'ctx>,
    _body: &Body<'ctx>,
    term: &crate::mir::Terminator<'ctx>,
    state: &mut MoveState,
) {
    match &term.kind {
        TerminatorKind::SwitchInt { discr, .. } => {
            collect_move_from_operand(discr, state);
        }
        TerminatorKind::Call { func, args, .. } => {
            collect_move_from_operand(func, state);
            for arg in args {
                collect_move_from_operand(arg, state);
            }
        }
        TerminatorKind::Goto { .. }
        | TerminatorKind::Return
        | TerminatorKind::ResumeUnwind
        | TerminatorKind::Unreachable
        | TerminatorKind::UnresolvedGoto => {}
    }
}

/// Collect a move from an operand.
fn collect_move_from_operand(operand: &Operand, state: &mut MoveState) {
    if let Operand::Move(place) = operand {
        if place.projection.is_empty() {
            // Full move of local
            state.mark_moved(place.local);
        } else if let Some(PlaceElem::Field(idx, _)) = place.projection.first() {
            // Partial move of field
            state.mark_field_moved(place.local, *idx);
        }
    }
}
// ============================================================================
// Borrow Validation
// ============================================================================

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

pub fn validate_borrows<'ctx>(gcx: Gcx<'ctx>, body: &Body<'ctx>) -> CompileResult<()> {
    use crate::mir::analysis::liveness::compute_liveness;

    // 1. Compute Liveness
    let liveness = compute_liveness(body);

    // 2. Track active borrows: BorrowedLocal -> Vec<(BorrowerLocal, Span)>
    // Ideally this should flow sensitive, but for now we can approximate:
    // If a borrow is created, it is "active" as long as the borrower is live.
    // Liveness handles the scope.
    // We just need to know "who borrows whom".
    // Since we don't have alias analysis, we rely on the explicit `_y = &_x` assignment.
    // We collect these relations.
    // Note: A borrower might be reassigned. `_y` borrows `_x`, then `_y` borrows `_z`.
    // Validating strict correctness requires full borrow checking (lifetime inference).
    // BUT, for the specific issue "implicit copy", we just want to catch "move while borrower is live".
    // We can be conservative: identifying that `_y` *might* borrow `_x`.

    // Better approach: Forward dataflow with state `ActiveBorrows`.
    // State: Map<BorrowedLocal, Set<BorrowerLocal>>.
    // On `_y = &_x`: add `_x -> _y` to state.
    // On `_y = ...` (reassign): remove `_y` from all values (it no longer borrows them).
    // On `move _x`: check if any `b` in `state[_x]` is LIVE.

    // We need per-statement liveness.

    let mut visited = FxHashSet::default();
    let mut worklist = vec![body.start_block];

    // Map block -> In-State
    let mut block_in_states: FxHashMap<BasicBlockId, FxHashMap<LocalId, FxHashSet<LocalId>>> =
        FxHashMap::default();
    block_in_states.insert(body.start_block, FxHashMap::default());

    // We reuse a worklist, but we need to verify convergence if we have loops?
    // Borrow sets only grow or shrink on strict kill.
    // Standard dataflow.

    while let Some(bb) = worklist.pop() {
        if !visited.insert(bb) {
            // If already visited, we only re-process if input changed.
            // Simplified: simplified topological walk (Reverse Post Order) is better, but worklist okay.
        }

        // 1. Recompute liveness at each statement for this block
        // Liveness is backward.
        // live_out is known.
        let live_out = &liveness.live_out[bb];
        let mut live_at_stmts = Vec::with_capacity(body.basic_blocks[bb].statements.len() + 1);

        let mut current_live = live_out.clone();
        // Push live_out as the liveness AFTER the last statement (at terminator)
        live_at_stmts.push(current_live.clone());

        // Walk backwards to compute liveness before each stmt
        let statements = &body.basic_blocks[bb].statements;
        for stmt in statements.iter().rev() {
            // Same logic as liveness.rs
            match &stmt.kind {
                StatementKind::Assign(dest, rvalue) => {
                    if dest.projection.is_empty() {
                        current_live.remove(&dest.local);
                    } else {
                        current_live.insert(dest.local);
                    }
                    // Uses
                    match rvalue {
                        Rvalue::Use(op)
                        | Rvalue::UnaryOp { operand: op, .. }
                        | Rvalue::Cast { operand: op, .. }
                        | Rvalue::Repeat { operand: op, .. } => use_operand(op, &mut current_live),
                        Rvalue::BinaryOp { lhs, rhs, .. } => {
                            use_operand(lhs, &mut current_live);
                            use_operand(rhs, &mut current_live);
                        }
                        Rvalue::Ref { place, .. } | Rvalue::Discriminant { place } => {
                            current_live.insert(place.local);
                        }
                        Rvalue::Aggregate { fields, .. } => {
                            for f in fields {
                                use_operand(f, &mut current_live);
                            }
                        }
                        _ => {}
                    }
                }
                StatementKind::SetDiscriminant { place, .. } => {
                    if !place.projection.is_empty() {
                        current_live.insert(place.local);
                    }
                }
                StatementKind::GcSafepoint | StatementKind::Nop => {}
            }
            live_at_stmts.push(current_live.clone());
        }
        live_at_stmts.reverse();
        // Now live_at_stmts[i] is liveness BEFORE statement i.
        // live_at_stmts[len] is liveness AFTER last statement (at terminator).

        // 2. Forward pass for validation
        let entry_borrows = block_in_states.entry(bb).or_default().clone();
        let mut active_borrows = entry_borrows; // Map<Borrowed, Set<Borrower>>

        for (idx, stmt) in statements.iter().enumerate() {
            match &stmt.kind {
                StatementKind::Assign(dest, rvalue) => {
                    // Check for moves in rvalue
                    check_rvalue_moves_borrowed(
                        gcx,
                        rvalue,
                        &active_borrows,
                        &live_at_stmts[idx],
                        stmt.span,
                    )?;

                    // Update state: Dest is overwritten, so it stops borrowing anything
                    if dest.projection.is_empty() {
                        let borrower = dest.local;
                        for borrowers in active_borrows.values_mut() {
                            borrowers.remove(&borrower);
                        }
                    }

                    // If Ref, add borrow
                    if let Rvalue::Ref { place, .. } = rvalue {
                        if dest.projection.is_empty() {
                            active_borrows
                                .entry(place.local)
                                .or_default()
                                .insert(dest.local);
                        }
                    }
                    // Propagate borrows (copy/move): if _y = _z, and _z borrows _x, then _y borrows _x?
                    // Yes, copying a reference copies the borrow.
                    if let Rvalue::Use(op) = rvalue {
                        if let Some(src_local) = operand_local(op) {
                            // If src_local is a borrower of X, then dest becomes borrower of X
                            if dest.projection.is_empty() {
                                let d = dest.local;
                                let mut new_borrows = Vec::new();
                                for (borrowed, borrowers) in &active_borrows {
                                    if borrowers.contains(&src_local) {
                                        new_borrows.push(*borrowed);
                                    }
                                }
                                for b in new_borrows {
                                    active_borrows.entry(b).or_default().insert(d);
                                }
                            }
                        }
                    }
                    if let Rvalue::Aggregate { fields, .. } = rvalue {
                        if dest.projection.is_empty() {
                            let d = dest.local;
                            let mut new_borrows = Vec::new();
                            for field in fields {
                                if let Some(src_local) = operand_local(field) {
                                    for (borrowed, borrowers) in &active_borrows {
                                        if borrowers.contains(&src_local) {
                                            new_borrows.push(*borrowed);
                                        }
                                    }
                                }
                            }
                            for b in new_borrows {
                                active_borrows.entry(b).or_default().insert(d);
                            }
                        }
                    }
                }
                // Check SetDiscriminant? No moves usually.
                _ => {}
            }
        }

        // Check terminator
        if let Some(term) = &body.basic_blocks[bb].terminator {
            check_terminator_moves_borrowed(
                gcx,
                term,
                &active_borrows,
                &live_at_stmts[statements.len()],
                term.span,
            )?;

            // Propagate to successors
            for succ in successors(&term.kind) {
                // Union state? Intersect?
                // Borrow checker is usually strict. If ANY path has a borrow, it exists?
                // Or rather, we are flowing states.
                // If we merge, we should merge sets.
                let succ_state = block_in_states.entry(succ).or_default();
                let mut changed = false;
                for (borrowed, borrowers) in &active_borrows {
                    let entry = succ_state.entry(*borrowed).or_default();
                    for &b in borrowers {
                        if entry.insert(b) {
                            changed = true;
                        }
                    }
                }
                if changed || !visited.contains(&succ) {
                    if !worklist.contains(&succ) {
                        worklist.push(succ);
                    }
                }
            }
        }
    }

    gcx.dcx().ok()
}

fn operand_local(op: &Operand) -> Option<LocalId> {
    match op {
        Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => Some(p.local),
        _ => None,
    }
}

// Reuse helpers from dse/liveness locally
fn use_operand(op: &Operand, live: &mut FxHashSet<LocalId>) {
    match op {
        Operand::Copy(place) | Operand::Move(place) => {
            live.insert(place.local);
        }
        _ => {}
    }
}

fn check_rvalue_moves_borrowed(
    gcx: Gcx,
    rvalue: &Rvalue,
    borrows: &FxHashMap<LocalId, FxHashSet<LocalId>>,
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
            for f in fields {
                check_operand_move_borrowed(gcx, f, borrows, live, span)?;
            }
            return Ok(());
        }
        _ => Ok(()),
    }
}

fn check_terminator_moves_borrowed(
    gcx: Gcx,
    term: &crate::mir::Terminator,
    borrows: &FxHashMap<LocalId, FxHashSet<LocalId>>,
    live: &FxHashSet<LocalId>,
    span: crate::span::Span,
) -> CompileResult<()> {
    match &term.kind {
        TerminatorKind::Call { func, args, .. } => {
            check_operand_move_borrowed(gcx, func, borrows, live, span)?;
            for arg in args {
                check_operand_move_borrowed(gcx, arg, borrows, live, span)?;
            }
            return Ok(());
        }
        TerminatorKind::SwitchInt { discr, .. } => {
            check_operand_move_borrowed(gcx, discr, borrows, live, span)?;
            return Ok(());
        }
        _ => Ok(()),
    }
}

fn check_operand_move_borrowed(
    gcx: Gcx,
    op: &Operand,
    borrows: &FxHashMap<LocalId, FxHashSet<LocalId>>,
    live: &FxHashSet<LocalId>,
    span: crate::span::Span,
) -> CompileResult<()> {
    if let Operand::Move(place) = op {
        // ... (original logic)
        // If we are moving 'place.local', check if it is borrowed
        if let Some(borrowers) = borrows.get(&place.local) {
            for &b in borrowers {
                if live.contains(&b) {
                    // Borrower is live!
                    gcx.dcx().emit_error(
                        format!("cannot move out of borrowed content").into(),
                        Some(span),
                    );
                    return gcx.dcx().ok();
                }
            }
        }
    }
    Ok(())
}
