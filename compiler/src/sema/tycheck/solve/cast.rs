use crate::{
    hir::NodeID,
    sema::{
        error::{ExpectedFound, TypeError},
        models::{Ty, TyKind},
        tycheck::utils::is_type_layout_compatible,
    },
    span::{Span, Spanned},
};

use super::{ConstraintSolver, SolverResult};

impl<'ctx> ConstraintSolver<'ctx> {
    pub fn solve_cast(
        &mut self,
        location: Span,
        _node_id: NodeID,
        from: Ty<'ctx>,
        to: Ty<'ctx>,
        is_unsafe: bool,
    ) -> SolverResult<'ctx> {
        let from = self.structurally_resolve(from);
        let to = self.structurally_resolve(to);

        if from.is_error() || to.is_error() {
            return SolverResult::Solved(vec![]);
        }

        // Defer if types are not fully known yet
        if from.is_ty_var() || to.is_ty_var() {
            return SolverResult::Deferred;
        }

        // Helper for numeric integer casts (includes rune and IntVars).
        let is_numeric_int_like = |ty: Ty<'ctx>| {
            matches!(
                ty.kind(),
                TyKind::Int(_)
                    | TyKind::UInt(_)
                    | TyKind::Rune
                    | TyKind::Infer(crate::sema::models::InferTy::IntVar(_))
            )
        };

        // 1. Integer <-> Integer
        if is_numeric_int_like(from) && is_numeric_int_like(to) {
            return SolverResult::Solved(vec![]);
        }

        // 2. TODO: Float <-> Float

        // Pointer-int casts keep prior restrictions (rune is excluded here).
        let is_ptr_int_like = |ty: Ty<'ctx>| {
            matches!(
                ty.kind(),
                TyKind::Int(_)
                    | TyKind::UInt(_)
                    | TyKind::Infer(crate::sema::models::InferTy::IntVar(_))
            )
        };

        // 3. Pointer <-> Pointer
        // 4. Pointer <-> Integer
        let from_is_ptr = from.is_pointer();
        let to_is_ptr = to.is_pointer();

        let is_ptr_cast = from_is_ptr && to_is_ptr;
        let is_ptr_int_cast =
            (from_is_ptr && is_ptr_int_like(to)) || (is_ptr_int_like(from) && to_is_ptr);

        if is_ptr_cast || is_ptr_int_cast {
            if !is_type_layout_compatible(from, to) {
                let error = Spanned::new(
                    TypeError::LayoutIncompatibleCast(ExpectedFound::new(to, from)),
                    location,
                );
                return SolverResult::Error(vec![error]);
            }

            // Must be unsafe
            if !is_unsafe {
                let error = Spanned::new(TypeError::UnsafePtrCastNeedsUnsafeBlock, location);
                return SolverResult::Error(vec![error]);
            }

            // If unsafe, we allow it.
            return SolverResult::Solved(vec![]);
        }

        // Fallback: type equality (identity cast)
        // TODO: Interface Casts
        self.solve_equality(location, to, from)
    }
}
