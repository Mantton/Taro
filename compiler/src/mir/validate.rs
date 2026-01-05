//! MIR validation passes that check for semantic errors.
//!
//! These validations run after MIR building to catch errors that are easier
//! to detect at the MIR level than during type checking.

use crate::{
    compile::context::Gcx,
    error::CompileResult,
    mir::{BasicBlockId, Body, LocalId, Operand, Place, PlaceElem, Rvalue, StatementKind, TerminatorKind},
    sema::models::TyKind,
    thir::FieldIndex,
};
use rustc_hash::{FxHashMap, FxHashSet};

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
        TerminatorKind::Call { target, .. } => vec![*target],
        TerminatorKind::Return | TerminatorKind::Unreachable | TerminatorKind::UnresolvedGoto => {
            vec![]
        }
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
        }
        Operand::Constant(_) => {}
    }
    Ok(())
}

/// Check that a place is not moved.
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
        gcx.dcx().emit_error(
            format!("use of moved value {}", name).into(),
            Some(span),
        );
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
                format!("use of partially moved value {} (field already moved)", name).into(),
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
