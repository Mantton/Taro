use taroc_span::Span;

use crate::{
    check::solver::{SolverDelegate, SolverResult},
    error::TypeError,
    ty::Ty,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CastGoal<'ctx> {
    pub span: Span,
    pub from_ty: Ty<'ctx>,
    pub to_ty: Ty<'ctx>,
    pub optional: bool,
}

impl<'icx, 'ctx, 'rcx> SolverDelegate<'icx, 'ctx, 'rcx> {
    pub fn solve_cast(&mut self, goal: CastGoal<'ctx>) -> SolverResult<'ctx> {
        // TODO: Casting
        SolverResult::Error(TypeError::CannotCast(goal.from_ty, goal.to_ty))
    }
}
