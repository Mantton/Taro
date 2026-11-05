use crate::sema::{
    impl_engine::ref_ops::{InterfaceRefMatch, interface_ref_matches},
    models::TyKind,
};
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

        // Rank first and probe only the highest-priority group that can succeed.
        // Lower-priority groups can never beat a successful higher-scoring group.
        let mut ranked = rank_branches(self.gcx(), branches).into_iter().peekable();
        let mut failed = false;

        while let Some(first) = ranked.next() {
            let score = first.score;
            let mut group = vec![first.branch];

            while matches!(ranked.peek(), Some(next) if next.score == score) {
                let next = ranked.next().expect("peeked item must exist");
                group.push(next.branch);
            }

            let mut winner: Option<(DisjunctionBranch<'ctx>, (u32, bool))> = None;
            let mut tied = false;
            let mut interface_instances = rustc_hash::FxHashSet::default();
            for branch in group {
                let probe_goal = branch.goal.clone();
                fn binding_node(goal: &Goal<'_>) -> Option<crate::hir::NodeID> {
                    match goal {
                        Goal::BindOverload(data) => Some(data.node_id),
                        Goal::BindInterfaceMethod(data) => Some(data.node_id),
                        Goal::BindMethodOverload(data) => binding_node(&data.binding),
                        _ => None,
                    }
                }
                let node = binding_node(&probe_goal);
                let probe_result = self.icx.probe(|_| {
                    let mut fork = self.fork_for_probe(node);
                    fork.obligations.push_front(Obligation {
                        location,
                        goal: probe_goal,
                    });
                    let mut driver = SolverDriver::new(fork);
                    driver.solve_to_fixpoint().map(|()| {
                        // A declared bound and a blanket template can discover
                        // the same requirement instance. Compare only resolved
                        // arguments: probe-local variables cannot escape here.
                        let instance = node.and_then(|node| {
                            let call = driver.solver.interface_calls.get(&node)?;
                            let args = *driver.solver.instantiation_args.get(&node)?;
                            let args = driver.solver.icx.resolve_args_if_possible(args);
                            (!args.iter().any(crate::sema::tycheck::utils::unresolved::generic_arg_contains_unresolved_inference))
                                .then_some((call.method_id, args))
                        });
                        (driver.solver.coercions, instance)
                    })
                });

                let generic = branch
                    .source
                    .is_some_and(|source| !self.gcx().generics_of(source).parameters.is_empty());
                let probe_result = probe_result.map(|(cost, instance)| ((cost, generic), instance));
                match probe_result {
                    Ok((cost, instance)) => {
                        if instance.is_some_and(|instance| !interface_instances.insert(instance)) {
                            continue;
                        }
                        match &winner {
                            None => {
                                winner = Some((branch, cost));
                                tied = false;
                            }
                            Some((_, best)) if cost < *best => {
                                winner = Some((branch, cost));
                                tied = false;
                            }
                            Some((_, best)) if cost == *best => tied = true,
                            _ => {}
                        }
                    }
                    Err(_) => failed = true,
                }
            }

            if let Some((winner, _)) = winner {
                if tied {
                    return SolverResult::Error(vec![Spanned::new(
                        crate::sema::error::TypeError::AmbiguousOverload,
                        location,
                    )]);
                }
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
            static_owner,
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

        if let Some(owner) = static_owner {
            if let Some((target, ancestor)) =
                crate::sema::tycheck::utils::members::static_target(self.gcx(), owner, source)
            {
                let target = if let Some(arguments) = instantiation_args {
                    instantiate_ty_with_args(self.gcx(), target, arguments)
                } else {
                    target
                };
                if let Err(error) = self.unify(target, ancestor) {
                    return SolverResult::Error(vec![Spanned::new(error, location)]);
                }
            }
        }

        match self.unify(var_ty, actual_ty) {
            Ok(_) => {
                self.record_overload_source(node_id, source);
                self.icx.bind_overload(var_ty, source);
                let obligations = self.constraints_for_def_at_call(
                    source,
                    instantiation_args,
                    location,
                    Some(node_id),
                );
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

        let existential_dispatch = instantiation_args
            .and_then(|args| args.first().copied())
            .and_then(|arg| arg.ty())
            .and_then(|ty| match ty.kind() {
                TyKind::BoxedExistential { interfaces } => interfaces
                    .get(call_info.table_index)
                    .copied()
                    .map(|root| (ty, root)),
                _ => None,
            });

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

        if existential_dispatch.is_some()
            && (crate::sema::tycheck::utils::erased_self::has_free_self(actual_ty)
                || instantiation_args.is_some_and(|args| {
                    crate::sema::tycheck::utils::erased_self::method_has_unsupported_payload_types(
                        self.gcx(),
                        call_info.method_id,
                        args,
                    )
                }))
        {
            return SolverResult::Error(vec![Spanned::new(
                crate::sema::error::TypeError::ErasedMethodUsesHiddenType,
                location,
            )]);
        }
        match self.unify(var_ty, actual_ty) {
            Ok(_) => {
                self.record_overload_source(node_id, call_info.method_id);
                self.icx.bind_overload(var_ty, call_info.method_id);
                self.record_interface_call(node_id, call_info);
                let mut obligations =
                    self.constraints_for_def(call_info.method_id, instantiation_args, location);
                if let Some((self_ty, root)) = existential_dispatch {
                    // The witness table proves these receiver requirements for
                    // the hidden payload. It does not make the owning box Copy.
                    // Keep associated-type and additional method requirements.
                    let provided = self.collect_interface_with_supers(root);
                    let declared = self.gcx().definition_parent(call_info.method_id)
                        .zip(instantiation_args).map(|(parent, args)| {
                            self.gcx().canonical_constraints_of(parent).into_iter().map(|constraint| {
                                crate::sema::tycheck::utils::instantiate::instantiate_constraint_with_args(
                                    self.gcx(), constraint.value, args,
                                )
                            }).collect::<Vec<_>>()
                        }).unwrap_or_default();
                    obligations.retain(|obligation| {
                        // The interface witness also proves its declared bounds
                        // on hidden generic arguments. Additional method-only
                        // requirements still need an independent caller proof.
                        if declared
                            .iter()
                            .any(|constraint| match (constraint, &obligation.goal) {
                                (
                                    crate::sema::models::Constraint::Bound {
                                        ty: a,
                                        interface: x,
                                    },
                                    Goal::Conforms {
                                        ty: b,
                                        interface: y,
                                    },
                                ) => a == b && x == y,
                                (
                                    crate::sema::models::Constraint::TypeEquality(a, b),
                                    Goal::ConstraintEqual(x, y),
                                ) => a == x && b == y,
                                _ => false,
                            })
                        {
                            return false;
                        }
                        match obligation.goal {
                            Goal::Conforms { ty, interface } if ty == self_ty => {
                                !provided.iter().any(|bound| {
                                    interface_ref_matches(
                                        interface,
                                        *bound,
                                        InterfaceRefMatch::Logical,
                                    )
                                })
                            }
                            _ => true,
                        }
                    });
                }
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
            binding,
            receiver_node_id,
            receiver_constraint,
            adjustments,
        } = data;
        let result = self.solve(&Obligation {
            location,
            goal: *binding,
        });
        if let SolverResult::Solved(mut obligations) = result {
            self.record_adjustments(receiver_node_id, adjustments);
            if let Some((variable, actual)) = receiver_constraint {
                obligations.push(Obligation {
                    location,
                    goal: Goal::Equal(variable, actual),
                });
            }
            SolverResult::Solved(obligations)
        } else {
            result
        }
    }
}
