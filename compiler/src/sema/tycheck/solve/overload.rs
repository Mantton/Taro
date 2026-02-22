use crate::{
    sema::tycheck::{
        solve::{
            BindInterfaceMethodGoalData, BindMethodOverloadGoalData, BindOverloadGoalData,
            ConstraintSolver, DisjunctionBranch, Goal, Obligation, SolverDriver, SolverResult,
            rank_branches,
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
            let obligation = Obligation {
                location,
                goal: branch.goal,
            };
            return self.solve(&obligation);
        }

        // Rank first and probe only the highest-scoring group that can succeed.
        // Lower-scoring groups can never beat a successful higher-scoring group.
        let mut ranked = rank_branches(self.gcx(), branches).into_iter().peekable();
        let mut failed = false;

        while let Some(first) = ranked.next() {
            let score = first.score;
            let mut group = vec![first.branch];

            while matches!(ranked.peek(), Some(next) if next.score == score) {
                let next = ranked.next().expect("peeked item must exist");
                group.push(next.branch);
            }

            let mut winner: Option<DisjunctionBranch<'ctx>> = None;
            for branch in group {
                let probe_goal = branch.goal.clone();
                let probe_result = self.icx.probe(|_| {
                    let mut fork = self.fork_for_probe();
                    fork.obligations.push_front(Obligation {
                        location,
                        goal: probe_goal,
                    });
                    let mut driver = SolverDriver::new(fork);
                    driver.solve_to_fixpoint()
                });

                match probe_result {
                    Ok(()) => {
                        if winner.is_some() {
                            return SolverResult::Error(vec![Spanned::new(
                                crate::sema::error::TypeError::AmbiguousOverload,
                                location,
                            )]);
                        }
                        winner = Some(branch);
                    }
                    Err(_) => failed = true,
                }
            }

            if let Some(winner) = winner {
                let obligation = Obligation {
                    location,
                    goal: winner.goal,
                };
                return self.solve(&obligation);
            }
        }

        if failed {
            // No branch succeeded; surface a generic overload failure.
            return SolverResult::Error(vec![Spanned::new(
                crate::sema::error::TypeError::NoOverloadMatches,
                location,
            )]);
        }

        SolverResult::Deferred
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
            instantiation_args,
        } = data;

        // Instantiate the candidate type if it has generics
        let generics = self.gcx().generics_of(source);
        let (actual_ty, instantiation_args) = if !generics.is_empty() {
            let args =
                self.instantiate_generic_args_with_defaults(source, instantiation_args, location);
            let instantiated = instantiate_ty_with_args(self.gcx(), candidate_ty, args);
            self.record_instantiation(node_id, args);
            (instantiated, Some(args))
        } else {
            (candidate_ty, None)
        };

        match self.unify(var_ty, actual_ty) {
            Ok(_) => {
                self.record_overload_source(node_id, source);
                self.icx.bind_overload(var_ty, source);
                let obligations = self.constraints_for_def(source, instantiation_args, location);
                SolverResult::Solved(obligations)
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

        // Instantiate interface method generics only for the selected branch.
        // This avoids leaking unconstrained inference vars from rejected candidates.
        let generics = self.gcx().generics_of(call_info.method_id);
        let (actual_ty, instantiation_args) = if !generics.is_empty() {
            let args = self.instantiate_generic_args_with_defaults(
                call_info.method_id,
                instantiation_args,
                location,
            );
            let instantiated = instantiate_ty_with_args(self.gcx(), candidate_ty, args);
            self.record_instantiation(node_id, args);
            (instantiated, Some(args))
        } else {
            (candidate_ty, None)
        };

        match self.unify(var_ty, actual_ty) {
            Ok(_) => {
                self.record_overload_source(node_id, call_info.method_id);
                self.icx.bind_overload(var_ty, call_info.method_id);
                self.record_interface_call(node_id, call_info);
                let obligations =
                    self.constraints_for_def(call_info.method_id, instantiation_args, location);
                SolverResult::Solved(obligations)
            }
            Err(e) => {
                let error = Spanned::new(e, location);
                SolverResult::Error(vec![error])
            }
        }
    }

    /// Solve a method overload binding with associated receiver adjustments.
    /// This combines the overload binding with adjustment recording so that
    /// each branch of a disjunction can carry its own receiver type and adjustments.
    pub fn solve_bind_method_overload(
        &mut self,
        location: Span,
        data: BindMethodOverloadGoalData<'ctx>,
    ) -> SolverResult<'ctx> {
        let BindMethodOverloadGoalData {
            node_id,
            receiver_node_id,
            var_ty,
            candidate_ty,
            receiver_ty,
            receiver_ty_var,
            source,
            instantiation_args,
            adjustments,
        } = data;

        // Instantiate the candidate type if it has generics
        let generics = self.gcx().generics_of(source);
        let (actual_ty, instantiation_args) = if !generics.is_empty() {
            let args =
                self.instantiate_generic_args_with_defaults(source, instantiation_args, location);
            let instantiated = instantiate_ty_with_args(self.gcx(), candidate_ty, args);
            self.record_instantiation(node_id, args);
            (instantiated, Some(args))
        } else {
            (candidate_ty, None)
        };

        match self.unify(var_ty, actual_ty) {
            Ok(_) => {
                self.record_overload_source(node_id, source);
                self.icx.bind_overload(var_ty, source);
                // Record the receiver adjustments when this overload is selected
                self.record_adjustments(receiver_node_id, adjustments);

                // Constrain the receiver type variable to match the receiver type.
                // We do NOT instantiate receiver_ty because it comes from the actual receiver
                // expression and carries the specific types we want to unify with.
                let mut obligations = vec![Obligation {
                    location,
                    goal: Goal::Equal(receiver_ty_var, receiver_ty),
                }];

                obligations.extend(self.constraints_for_def(source, instantiation_args, location));
                SolverResult::Solved(obligations)
            }
            Err(e) => {
                let error = Spanned::new(e, location);
                SolverResult::Error(vec![error])
            }
        }
    }
}
