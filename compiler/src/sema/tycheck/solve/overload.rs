use crate::{
    sema::tycheck::solve::{
        BindOverloadGoalData, ConstraintSolver, DisjunctionBranch, Obligation, SolverDriver,
        SolverResult, rank_branches,
    },
    span::{Span, Spanned},
};

impl<'ctx> ConstraintSolver<'ctx> {
    pub fn solve_disjunction(
        &mut self,
        location: Span,
        branches: Vec<DisjunctionBranch<'ctx>>,
    ) -> SolverResult<'ctx> {
        let mut successful = vec![];
        let mut failed = false;

        for branch in branches {
            let probe_goal = branch.goal.clone();
            let probe_result = self.icx.probe(|_| {
                let mut fork = self.fork();
                fork.obligations.push_front(Obligation {
                    location,
                    goal: probe_goal,
                });
                let mut driver = SolverDriver::new(fork);
                driver.solve_to_fixpoint()
            });

            match probe_result {
                Ok(()) => successful.push(branch),
                Err(_) => failed = true,
            }
        }

        if successful.is_empty() {
            if failed {
                // No branch succeeded; surface a generic overload failure.
                return SolverResult::Error(vec![Spanned::new(
                    crate::sema::error::TypeError::NoOverloadMatches,
                    location,
                )]);
            }
            return SolverResult::Deferred;
        }

        if successful.len() == 1 {
            let branch = successful.pop().unwrap();
            return self.solve(Obligation {
                location,
                goal: branch.goal,
            });
        }

        // Ambiguous or needs ranking.
        let ranked = rank_branches(successful);
        let best = ranked.first().cloned();
        let second = ranked.get(1);

        match (best, second) {
            (Some(best), Some(second)) if best.score == second.score => {
                return SolverResult::Error(vec![Spanned::new(
                    crate::sema::error::TypeError::AmbiguousOverload,
                    location,
                )]);
            }
            (Some(best), _) => self.solve(Obligation {
                location,
                goal: best.branch.goal,
            }),
            _ => unreachable!(),
        }
    }

    pub fn solve_bind_overload(
        &mut self,
        location: Span,
        data: BindOverloadGoalData<'ctx>,
    ) -> SolverResult<'ctx> {
        let BindOverloadGoalData {
            var_ty,
            candidate_ty,
            source,
        } = data;

        match self.unify(var_ty, candidate_ty) {
            Ok(_) => {
                self.icx.bind_overload(var_ty, source);
                SolverResult::Solved(vec![])
            }
            Err(e) => {
                let error = Spanned::new(e, location);
                SolverResult::Error(vec![error])
            }
        }
    }
}
