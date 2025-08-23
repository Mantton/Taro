use crate::infer::{OverloadCallKind, OverloadResolution};
use crate::{
    GlobalContext,
    check::{
        nodes::utils::associated_operators_for_ty,
        solver::{
            BinaryOperatorGoal, Goal, MethodCallGoal, Obligation, OverloadArgument, OverloadGoal,
            SolverDelegate, SolverResult, UnaryOperatorGoal,
        },
    },
    error::TypeError,
    ty::{Constraint, InferTy, Ty, TyKind},
};
use taroc_hir::{BinaryOperator, DefinitionID, OperatorKind};
use taroc_span::{Identifier, Span};

impl<'icx, 'ctx> SolverDelegate<'icx, 'ctx> {
    pub fn solve_unary(&mut self, goal: UnaryOperatorGoal<'ctx>) -> SolverResult<'ctx> {
        self.solve_unary_via_operator(goal)
    }

    fn solve_unary_via_operator(&mut self, goal: UnaryOperatorGoal<'ctx>) -> SolverResult<'ctx> {
        let ty = self.structurally_resolve(goal.operand_ty);
        if ty.is_infer() {
            return SolverResult::Deferred;
        }
        let kind = OperatorKind::from_unary(goal.operator);
        let candidates = self.collect_all_operator_candidates(ty, goal.span, kind);

        if candidates.is_empty() {
            return SolverResult::Error(TypeError::NoUnaryOperator(ty, kind));
        }

        if let [candidate] = candidates.as_slice() {
            let obligations = self.select_fn_for_method(
                *candidate,
                ty,
                &unary_goal_to_method_goal(goal),
                Some(OverloadCallKind::Unary(goal.operator)),
            );
            return SolverResult::Solved(obligations);
        }

        let mut valid = vec![];
        for &candidate in &candidates {
            if self.evaluate_method_candidate(candidate, ty, &unary_goal_to_method_goal(goal)) {
                valid.push(candidate);
            }
        }

        if let [candidate] = valid.as_slice() {
            let obligations = self.select_fn_for_method(
                *candidate,
                ty,
                &unary_goal_to_method_goal(goal),
                Some(OverloadCallKind::Unary(goal.operator)),
            );
            return SolverResult::Solved(obligations);
        }

        if valid.is_empty() {
            return SolverResult::Error(TypeError::NoOverloadCandidateMatch);
        }

        SolverResult::Deferred
    }
}

fn unary_goal_to_method_goal<'ctx>(goal: UnaryOperatorGoal<'ctx>) -> MethodCallGoal<'ctx> {
    MethodCallGoal {
        call_span: goal.span,
        method: Identifier::emtpy(goal.span.file),
        receiver_ty: goal.operand_ty,
        result_var: goal.result_var,
        expected_result_ty: goal.expectation,
        arguments: &[],
        label_agnostic: true,
    }
}

impl<'icx, 'ctx> SolverDelegate<'icx, 'ctx> {
    pub fn solve_binary(&mut self, goal: BinaryOperatorGoal<'ctx>) -> SolverResult<'ctx> {
        let gcx = self.gcx();
        let lhs = self.structurally_resolve(goal.lhs);
        let rhs = self.structurally_resolve(goal.rhs);
        if lhs.is_infer() {
            return SolverResult::Deferred;
        }

        if let BinaryOperator::PtrEq = goal.operator {
            match (lhs.kind(), rhs.kind()) {
                (
                    TyKind::Pointer(..) | TyKind::Reference(..),
                    TyKind::Pointer(..) | TyKind::Reference(..),
                ) => {
                    let location = goal.span;
                    let goal = Goal::Constraint(Constraint::TypeEquality(
                        gcx.store.common_types.bool,
                        goal.rho,
                    ));
                    return SolverResult::Solved(vec![Obligation { goal, location }]);
                }
                _ => return SolverResult::Error(TypeError::InvalidPointerEquality(lhs)),
            }
        }

        // Try intrinsic resolution first (e.g., u8 + u8, bool && bool)
        if let Some(obligations) = self.solve_binary_intrinsic(&goal, lhs, rhs) {
            // Mark as intrinsic dispatch
            self.icx().record_overload_call(
                goal.span,
                OverloadCallKind::Binary(goal.operator),
                OverloadResolution::Intrinsic,
            );
            return SolverResult::Solved(obligations);
        }

        let mut obligations = vec![];
        let is_infer = matches!(
            rhs.kind(),
            TyKind::Infer(InferTy::TyVar(..) | InferTy::IntVar(..) | InferTy::FloatVar(..))
        );

        if is_infer {
            obligations.push(Obligation {
                location: goal.span,
                goal: Goal::Constraint(Constraint::TypeEquality(lhs, rhs)),
            });
        }

        let kind = if !goal.assigning {
            OperatorKind::from_binary(goal.operator)
        } else {
            OperatorKind::assign_from_binary(goal.operator).expect("Assign Op")
        };
        let candidates = self.collect_all_operator_candidates(lhs, goal.span, kind);

        if candidates.is_empty() {
            return SolverResult::Error(TypeError::NoBinaryOperator(lhs, rhs, kind));
        }

        if let [candidate] = candidates.as_slice() {
            obligations.extend(self.select_fn_for_method(
                *candidate,
                lhs,
                &binary_goal_to_method_goal(goal, gcx),
                Some(OverloadCallKind::Binary(goal.operator)),
            ));
            return SolverResult::Solved(obligations);
        }

        let mut valid = vec![];
        for &candidate in &candidates {
            if self.evaluate_method_candidate(
                candidate,
                lhs,
                &binary_goal_to_method_goal(goal, gcx),
            ) {
                valid.push(candidate);
            }
        }

        if let [candidate] = valid.as_slice() {
            obligations.extend(self.select_fn_for_method(
                *candidate,
                lhs,
                &binary_goal_to_method_goal(goal, gcx),
                Some(OverloadCallKind::Binary(goal.operator)),
            ));
            return SolverResult::Solved(obligations);
        }

        if valid.is_empty() {
            return SolverResult::Error(TypeError::NoOverloadCandidateMatch);
        }

        SolverResult::Deferred
    }
}

impl<'icx, 'ctx> SolverDelegate<'icx, 'ctx> {
    /// Try to resolve “intrinsic” binary operations on primitives without invoking overloads.
    /// Returns Some(obligations) if handled intrinsically; None to fall back to overload search.
    fn solve_binary_intrinsic(
        &self,
        goal: &BinaryOperatorGoal<'ctx>,
        lhs: Ty<'ctx>,
        rhs: Ty<'ctx>,
    ) -> Option<Vec<Obligation<'ctx>>> {
        use BinaryOperator::*;
        use TyKind::*;

        let gcx = self.gcx();

        let mut obligations = vec![];

        let numeric_same = |a: Ty<'ctx>, b: Ty<'ctx>| -> bool {
            match (a.kind(), b.kind()) {
                (Int(ka), Int(kb)) => ka == kb,
                (UInt(ka), UInt(kb)) => ka == kb,
                (Float(ka), Float(kb)) => ka == kb,
                _ => false,
            }
        };

        match goal.operator {
            Add | Sub | Mul | Div | Rem => {
                if numeric_same(lhs, rhs) {
                    obligations.push(Obligation {
                        location: goal.span,
                        goal: Goal::Constraint(Constraint::TypeEquality(goal.rho, lhs)),
                    });
                    if let Some(exp) = goal.expectation {
                        obligations.push(Obligation {
                            location: goal.span,
                            goal: Goal::Coerce {
                                from: goal.rho,
                                to: exp,
                            },
                        });
                    }
                    return Some(obligations);
                }
            }
            BitAnd | BitOr | BitXor | BitShl | BitShr => {
                match (lhs.kind(), rhs.kind()) {
                    (Int(ka), Int(kb)) if ka == kb => {
                        obligations.push(Obligation {
                            location: goal.span,
                            goal: Goal::Constraint(Constraint::TypeEquality(goal.rho, lhs)),
                        });
                        return Some(obligations);
                    }
                    (UInt(ka), UInt(kb)) if ka == kb => {
                        obligations.push(Obligation {
                            location: goal.span,
                            goal: Goal::Constraint(Constraint::TypeEquality(goal.rho, lhs)),
                        });
                        return Some(obligations);
                    }
                    // For shifts, allow any integer width on RHS, but still exact match for LHS result
                    (Int(_), Int(_) | UInt(_)) | (UInt(_), Int(_) | UInt(_))
                        if matches!(goal.operator, BitShl | BitShr) =>
                    {
                        obligations.push(Obligation {
                            location: goal.span,
                            goal: Goal::Constraint(Constraint::TypeEquality(goal.rho, lhs)),
                        });
                        return Some(obligations);
                    }
                    _ => {}
                }
            }
            BoolAnd | BoolOr => {
                if matches!(lhs.kind(), Bool) && matches!(rhs.kind(), Bool) {
                    obligations.push(Obligation {
                        location: goal.span,
                        goal: Goal::Constraint(Constraint::TypeEquality(
                            goal.rho,
                            gcx.store.common_types.bool,
                        )),
                    });
                    return Some(obligations);
                }
            }
            Eql | Neq | Lt | Gt | Leq | Geq => {
                // Simple numeric comparisons: require same numeric type; result is bool.
                if numeric_same(lhs, rhs) {
                    obligations.push(Obligation {
                        location: goal.span,
                        goal: Goal::Constraint(Constraint::TypeEquality(
                            goal.rho,
                            gcx.store.common_types.bool,
                        )),
                    });
                    return Some(obligations);
                }
            }
            PtrEq => unreachable!(),
        }

        None
    }
}

impl<'icx, 'ctx> SolverDelegate<'icx, 'ctx> {
    pub fn collect_all_operator_candidates(
        &self,
        recv_ty: Ty<'ctx>,
        recv_span: Span,
        operator: OperatorKind,
    ) -> Vec<DefinitionID> {
        let mut candidates = vec![];
        let mut autoderef = self.autoderef(recv_span, recv_ty);
        while let Some(recv) = autoderef.next() {
            let recv_candidates =
                associated_operators_for_ty(operator, recv, self.gcx(), recv_span.file);
            candidates.extend(recv_candidates);
        }
        candidates.dedup();
        candidates
    }
}

fn binary_goal_to_method_goal<'ctx>(
    goal: BinaryOperatorGoal<'ctx>,
    gcx: GlobalContext<'ctx>,
) -> MethodCallGoal<'ctx> {
    let arguments = gcx.store.interners.intern_slice(&[OverloadArgument {
        ty: if goal.rhs.is_infer() {
            goal.lhs
        } else {
            goal.rhs
        },
        span: goal.span,
        label: None,
    }]);
    MethodCallGoal {
        call_span: goal.span,
        method: Identifier::emtpy(goal.span.file),
        receiver_ty: goal.lhs,
        result_var: goal.rho,
        expected_result_ty: goal.expectation,
        arguments,
        label_agnostic: true,
    }
}

impl<'icx, 'ctx> SolverDelegate<'icx, 'ctx> {
    pub fn solve_subscript(&mut self, goal: OverloadGoal<'ctx>) -> SolverResult<'ctx> {
        let lhs = self.structurally_resolve(goal.callee_var);
        if lhs.is_infer() {
            return SolverResult::Deferred;
        }

        let candidates =
            self.collect_all_operator_candidates(lhs, goal.callee_span, OperatorKind::Index);
        if candidates.is_empty() {
            return SolverResult::Error(TypeError::NoOverloadCandidateMatch);
        }

        if let [candidate] = candidates.as_slice() {
            let obligations = self.select_fn_for_method(
                *candidate,
                lhs,
                &overload_goal_to_method_goal(goal, lhs),
                Some(OverloadCallKind::Index),
            );
            return SolverResult::Solved(obligations);
        }

        let mut valid = vec![];
        for &candidate in &candidates {
            if self.evaluate_method_candidate(
                candidate,
                lhs,
                &overload_goal_to_method_goal(goal, lhs),
            ) {
                valid.push(candidate);
            }
        }

        if let [candidate] = valid.as_slice() {
            let obligations = self.select_fn_for_method(
                *candidate,
                lhs,
                &overload_goal_to_method_goal(goal, lhs),
                Some(OverloadCallKind::Index),
            );
            return SolverResult::Solved(obligations);
        }

        if valid.is_empty() {
            return SolverResult::Error(TypeError::NoOverloadCandidateMatch);
        }

        SolverResult::Deferred
    }
}

fn overload_goal_to_method_goal<'ctx>(
    goal: OverloadGoal<'ctx>,
    rec: Ty<'ctx>,
) -> MethodCallGoal<'ctx> {
    MethodCallGoal {
        call_span: goal.expr_span,
        method: Identifier::emtpy(goal.callee_span.file),
        receiver_ty: rec,
        result_var: goal.result_var,
        expected_result_ty: goal.expected_result_ty,
        arguments: goal.arguments,
        label_agnostic: false,
    }
}
