use super::ConstraintSolver;
use crate::{
    sema::{
        error::TypeError,
        models::TyKind,
        tycheck::solve::{DerefGoalData, SolverResult},
    },
    span::Spanned,
};

impl<'ctx> ConstraintSolver<'ctx> {
    pub fn solve_deref(&mut self, data: DerefGoalData<'ctx>) -> SolverResult<'ctx> {
        let DerefGoalData {
            node_id: _,
            operand_node: _,
            operand_ty,
            result_ty,
            span,
        } = data;

        // Resolve the operand type
        let operand_ty = self.structurally_resolve(operand_ty);

        match operand_ty.kind() {
            TyKind::Pointer(inner, _) | TyKind::Reference(inner, _) => {
                // Successfully dereferenced - unify result with inner type
                self.solve_equality(span, result_ty, inner)
            }
            TyKind::Infer(_) => {
                // Operand is still an inference variable - defer until it's resolved
                SolverResult::Deferred
            }
            TyKind::Error => {
                // Error type - propagate error
                SolverResult::Solved(vec![])
            }
            _ => {
                // Cannot dereference this type
                let error = Spanned::new(TypeError::CannotDereference { ty: operand_ty }, span);
                SolverResult::Error(vec![error])
            }
        }
    }
}
