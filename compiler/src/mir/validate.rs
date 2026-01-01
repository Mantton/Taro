//! MIR validation passes that check for semantic errors.
//!
//! These validations run after MIR building to catch errors that are easier
//! to detect at the MIR level than during type checking.

use crate::{
    compile::context::Gcx,
    error::CompileResult,
    mir::{Body, PlaceElem, Rvalue, StatementKind},
    sema::models::TyKind,
};

/// Validates that mutable borrows only occur on mutable places.
///
/// This check ensures that code like:
/// ```
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
/// - The base local is declared mutable, AND
/// - All projections through references are to mutable references
fn is_place_mutable<'ctx>(
    _: Gcx<'ctx>,
    body: &Body<'ctx>,
    place: &crate::mir::Place<'ctx>,
) -> bool {
    let local_decl = &body.locals[place.local];

    // Check if the base local is mutable
    if !local_decl.mutable {
        return false;
    }

    // Walk the projection to check for immutable reference dereferences
    let mut current_ty = local_decl.ty;
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
