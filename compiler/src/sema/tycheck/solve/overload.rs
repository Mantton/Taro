use crate::{
    sema::tycheck::{
        solve::{
            BindInterfaceMethodGoalData, BindOverloadGoalData, ConstraintSolver,
            DisjunctionBranch, Obligation, SolverDriver, SolverResult, rank_branches,
        },
        utils::instantiate::instantiate_ty_with_args,
    },
    span::{Span, Spanned},
};

impl<'ctx> ConstraintSolver<'ctx> {
    pub fn solve_disjunction(
        &mut self,
        location: Span,
        branches: Vec<DisjunctionBranch<'ctx>>,
    ) -> SolverResult<'ctx> {
        if branches.len() == 1 {
            let branch = branches.into_iter().next().unwrap();
            return self.solve(Obligation {
                location,
                goal: branch.goal,
            });
        }

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
        let ranked = rank_branches(self.gcx(), successful);
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
            node_id,
            var_ty,
            candidate_ty,
            source,
        } = data;

        // Instantiate the candidate type if it has generics
        let generics = self.gcx().generics_of(source);
        let actual_ty = if !generics.is_empty() {
            let args = self.icx.fresh_args_for_def(source, location);
            let instantiated = instantiate_ty_with_args(self.gcx(), candidate_ty, args);
            self.record_instantiation(node_id, args);
            instantiated
        } else {
            candidate_ty
        };

        match self.unify(var_ty, actual_ty) {
            Ok(_) => {
                self.record_overload_source(node_id, source);
                self.icx.bind_overload(var_ty, source);
                SolverResult::Solved(vec![])
            }
            Err(e) => {
                let error = Spanned::new(e, location);
                SolverResult::Error(vec![error])
            }
        }
    }

    pub fn solve_bind_interface_method(
        &mut self,
        location: Span,
        data: BindInterfaceMethodGoalData<'ctx>,
    ) -> SolverResult<'ctx> {
        let BindInterfaceMethodGoalData {
            node_id,
            var_ty,
            candidate_ty,
            call_info,
            instantiation_args,
        } = data;

        match self.unify(var_ty, candidate_ty) {
            Ok(_) => {
                if let Some(args) = instantiation_args {
                    self.record_instantiation(node_id, args);
                }
                self.record_overload_source(node_id, call_info.method_id);
                self.record_interface_call(node_id, call_info);
                SolverResult::Solved(vec![])
            }
            Err(e) => {
                let error = Spanned::new(e, location);
                SolverResult::Error(vec![error])
            }
        }
    }
}
