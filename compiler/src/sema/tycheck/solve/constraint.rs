use crate::sema::{
    error::{ExpectedFound, TypeError},
    models::Ty,
    tycheck::solve::solver::{SolverDelegate, SolverResult},
};

impl<'ctx> SolverDelegate<'ctx> {
    pub fn solve_equality(&mut self, lhs: Ty<'ctx>, rhs: Ty<'ctx>) -> SolverResult<'ctx> {
        if lhs == rhs {
            return SolverResult::Solved(vec![]);
        }
        return SolverResult::Error(TypeError::TyMismatch(ExpectedFound::new(lhs, rhs)));
    }
}
