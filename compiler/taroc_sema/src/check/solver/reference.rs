use taroc_span::Span;

use crate::{
    check::solver::{DerefGoal, Goal, Obligation, ReferenceGoal, SolverDelegate, SolverResult},
    error::TypeError,
    ty::{Constraint, TyKind},
};

impl<'icx, 'ctx> SolverDelegate<'icx, 'ctx> {
    pub fn solve_ref(&mut self, goal: ReferenceGoal<'ctx>, location: Span) -> SolverResult<'ctx> {
        let ty = self.structurally_resolve(goal.ty);
        let res = self.gcx().mk_ty(TyKind::Reference(ty, goal.mutability));
        let goal = Goal::Constraint(Constraint::TypeEquality(res, goal.alpha));
        return SolverResult::Solved(vec![Obligation { goal, location }]);
    }
    pub fn solve_deref(&mut self, goal: DerefGoal<'ctx>, location: Span) -> SolverResult<'ctx> {
        let ty = self.structurally_resolve(goal.ty);
        if ty.is_infer() {
            return SolverResult::Deferred;
        }

        match ty.kind() {
            TyKind::Reference(ty, _) | TyKind::Pointer(ty, _) => {
                let goal = Goal::Constraint(Constraint::TypeEquality(ty, goal.alpha));
                return SolverResult::Solved(vec![Obligation { goal, location }]);
            }
            _ => return SolverResult::Error(TypeError::CannotDereference(ty)),
        }
    }
}
