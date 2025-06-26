use crate::{
    check::solver::{SolverDelegate, SolverResult},
    ty::Ty,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PatternResolutionGoal<'ctx> {
    pub pattern: &'ctx taroc_hir::Pattern,
    pub scrutinee_ty: Ty<'ctx>,
}

impl<'icx, 'ctx> SolverDelegate<'icx, 'ctx> {
    pub fn solve_pattern_resolve(
        &mut self,
        goal: PatternResolutionGoal<'ctx>,
    ) -> SolverResult<'ctx> {
        let ty = self.icx.shallow_resolve(goal.scrutinee_ty);
        if ty.is_infer() {
            return SolverResult::Deferred;
        }
        println!("resolve pattern for {}", ty.format(self.gcx()));
        self.gcx()
            .diagnostics
            .info("resolving pattern".into(), goal.pattern.span);
        todo!()
    }
}
