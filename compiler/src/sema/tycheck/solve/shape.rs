use crate::{
    hir::NodeID,
    sema::{
        models::Ty,
        tycheck::solve::{ConstraintSolver, Goal, Obligation, Shape, ShapeKind, SolverResult},
    },
    span::Span,
};

impl<'ctx> ConstraintSolver<'ctx> {
    pub fn solve_shape(
        &mut self,
        scrutinee: Ty<'ctx>,
        shape: Shape<'ctx>,
        location: Span,
    ) -> SolverResult<'ctx> {
        let ty = self.structurally_resolve(scrutinee);

        if ty.is_ty_var() {
            return SolverResult::Deferred;
        }

        self.check_shape_kind(shape.kind, scrutinee, shape.id, location)
    }
}

impl<'ctx> ConstraintSolver<'ctx> {
    fn check_shape_kind(
        &self,
        shape: ShapeKind<'ctx>,
        scrutinee_ty: Ty<'ctx>,
        id: NodeID,
        location: Span,
    ) -> SolverResult<'ctx> {
        match shape {
            ShapeKind::Typed(shape_ty) => self.check_typed_shape(shape_ty, scrutinee_ty, location),
            _ => {
                todo!()
            }
        }
    }

    fn check_typed_shape(
        &self,
        provided: Ty<'ctx>,
        expectation: Ty<'ctx>,
        location: Span,
    ) -> SolverResult<'ctx> {
        let obligation = Obligation {
            location,
            goal: Goal::Equal(expectation, provided),
        };

        return SolverResult::Solved(vec![obligation]);
    }
}
