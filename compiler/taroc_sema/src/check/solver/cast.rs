use crate::{
    check::solver::{SolverDelegate, SolverResult},
    error::TypeError,
    ty::Ty,
};
use taroc_span::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CastGoal<'ctx> {
    pub span: Span,
    pub from_ty: Ty<'ctx>,
    pub to_ty: Ty<'ctx>,
    pub optional: bool,
}

impl<'icx, 'ctx, 'rcx> SolverDelegate<'icx, 'ctx, 'rcx> {
    pub fn solve_cast(&mut self, goal: CastGoal<'ctx>) -> SolverResult<'ctx> {
        let from_ty = self.structurally_resolve(goal.from_ty);
        let to_ty = self.structurally_resolve(goal.to_ty);

        if from_ty.is_infer() || to_ty.is_infer() {
            return SolverResult::Deferred;
        }

        // TODO: Casting
        // SolverResult::Error(TypeError::CannotCast(from_ty, to_ty))
        SolverResult::Solved(vec![])
    }
}
