use super::{ConstraintSolver, Goal, MethodCallData, Obligation, SolverResult};
use crate::{
    hir::Mutability,
    sema::{
        error::TypeError,
        models::{Ty, TyKind},
        resolve::models::DefinitionID,
        tycheck::{
            solve::{
                Adjustment, ApplyArgument, ApplyGoalData, BindOverloadGoalData, DisjunctionBranch,
            },
            utils::AutoReference,
        },
    },
    span::{Spanned, Symbol},
};

impl<'ctx> ConstraintSolver<'ctx> {
    pub fn solve_method_call(&mut self, data: MethodCallData<'ctx>) -> SolverResult<'ctx> {
        let MethodCallData {
            node_id,
            receiver,
            reciever_node,
            reciever_span,
            name,
            arguments,
            result,
            span,
            method_ty,
            expect_ty,
            ..
        } = data;

        let rec_candidates = self.reciever_candidates(receiver);
        for (candidate_ty, deref_steps) in rec_candidates {
            for r in [
                AutoReference::None,
                AutoReference::Immutable,
                AutoReference::Mutable,
            ] {
                let reciever_ty = match r {
                    AutoReference::None => candidate_ty,
                    AutoReference::Mutable => Ty::new(
                        TyKind::Reference(candidate_ty, Mutability::Mutable),
                        self.gcx(),
                    ),
                    AutoReference::Immutable => Ty::new(
                        TyKind::Reference(candidate_ty, Mutability::Immutable),
                        self.gcx(),
                    ),
                };
                let candidates =
                    self.lookup_instance_candidates_method(candidate_ty, reciever_ty, name.symbol);
                let Some(candidates) = candidates else {
                    continue;
                };

                if candidates.is_empty() {
                    continue;
                }

                let mut adjustments = vec![];
                for _ in 0..deref_steps {
                    adjustments.push(Adjustment::Dereference);
                }
                match r {
                    AutoReference::None => {}
                    AutoReference::Immutable => adjustments.push(Adjustment::BorrowImmutable),
                    AutoReference::Mutable => adjustments.push(Adjustment::BorrowMutable),
                }

                let mut branches = vec![];
                for candidate in candidates {
                    let branch = DisjunctionBranch {
                        goal: Goal::BindOverload(BindOverloadGoalData {
                            node_id,
                            var_ty: method_ty,
                            candidate_ty: self.gcx().get_type(candidate),
                            source: candidate,
                        }),
                        source: Some(candidate),
                    };
                    branches.push(branch);
                }

                let disjuction_goal = Obligation {
                    location: name.span,
                    goal: Goal::Disjunction(branches),
                };

                let mut args = arguments.clone();
                args.insert(
                    0,
                    ApplyArgument {
                        id: reciever_node,
                        label: None,
                        ty: reciever_ty,
                        span: reciever_span,
                    },
                );

                let apply_goal = Obligation {
                    location: span,
                    goal: Goal::Apply(ApplyGoalData {
                        call_span: span,
                        callee_ty: method_ty,
                        callee_source: None,
                        result_ty: result,
                        expect_ty,
                        arguments: args,
                    }),
                };

                self.record_adjustments(reciever_node, adjustments);
                return SolverResult::Solved(vec![disjuction_goal, apply_goal]);
            }
        }
        return SolverResult::Error(vec![Spanned::new(
            TypeError::NoSuchMember {
                name: name.symbol,
                on: self.structurally_resolve(receiver),
            },
            name.span,
        )]);
    }

    fn reciever_candidates(&self, base_ty: Ty<'ctx>) -> Vec<(Ty<'ctx>, usize)> {
        let mut base = vec![];
        let mut derefs = 0;

        let mut autoderef = self.autoderef(base_ty);
        while let Some(nx) = autoderef.next() {
            base.push((nx, derefs));
            derefs += 1;
        }

        base
    }

    pub fn lookup_instance_candidates_method(
        &self,
        candidate: Ty<'ctx>,
        reciever: Ty<'ctx>,
        name: Symbol,
    ) -> Option<Vec<DefinitionID>> {
        let head = self.type_head_from_type(candidate)?;
        let all_candidates = self.gcx().with_session_type_database(|db| {
            db.type_head_to_members
                .get(&head)
                .and_then(|idx| idx.instance_functions.get(&name))
                .map(|set| set.members.clone())
        })?;

        let mut matching = vec![];
        for candidate in all_candidates.into_iter() {
            let ty = self.gcx().get_type(candidate);
            let fn_reciever = match ty.kind() {
                TyKind::FnPointer { inputs, .. } => inputs.first().cloned(),
                _ => None,
            };

            let Some(fn_reciever) = fn_reciever else {
                continue;
            };

            if reciever == fn_reciever {
                matching.push(candidate);
            }
        }

        return Some(matching);
    }
}
