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
    ty::{Constraint, Ty, TyKind},
};
use taroc_ast_ir::UnaryOperator;
use taroc_hir::{BinaryOperator, Mutability, OperatorKind};
use taroc_span::Identifier;

impl<'icx, 'ctx, 'rcx> SolverDelegate<'icx, 'ctx, 'rcx> {
    pub fn solve_unary(&mut self, goal: UnaryOperatorGoal<'ctx>) -> SolverResult<'ctx> {
        match goal.operator {
            UnaryOperator::Reference(mutability) => self.solve_ref(goal, mutability),
            UnaryOperator::Dereference => self.solve_deref(goal),
            UnaryOperator::LogicalNot => self.solve_unary_via_operator(goal),
            UnaryOperator::Negate => self.solve_unary_via_operator(goal),
            UnaryOperator::BitwiseNot => self.solve_unary_via_operator(goal),
        }
    }

    fn solve_ref(
        &mut self,
        goal: UnaryOperatorGoal<'ctx>,
        mutability: Mutability,
    ) -> SolverResult<'ctx> {
        let ty = self.icx().shallow_resolve(goal.operand_ty);
        let location = goal.span;
        let res = self.gcx().mk_ty(TyKind::Reference(ty, mutability));
        let goal = Goal::Constraint(Constraint::TypeEquality(goal.result_var, res));
        return SolverResult::Solved(vec![Obligation { goal, location }]);
    }
    fn solve_deref(&mut self, goal: UnaryOperatorGoal<'ctx>) -> SolverResult<'ctx> {
        let ty = self.icx().shallow_resolve(goal.operand_ty);
        if ty.is_infer() {
            return SolverResult::Deferred;
        }
        let location = goal.span;

        match ty.kind() {
            TyKind::Reference(ty, _) | TyKind::Pointer(ty, _) => {
                let goal = Goal::Constraint(Constraint::TypeEquality(goal.result_var, ty));
                return SolverResult::Solved(vec![Obligation { goal, location }]);
            }
            _ => return SolverResult::Error(TypeError::CannotDereference(ty)),
        }
    }

    fn solve_unary_via_operator(&mut self, goal: UnaryOperatorGoal<'ctx>) -> SolverResult<'ctx> {
        let gcx = self.gcx();
        let ty = self.icx().shallow_resolve(goal.operand_ty);
        if ty.is_infer() {
            return SolverResult::Deferred;
        }
        let kind = OperatorKind::from_unary(goal.operator);
        let candidates = associated_operators_for_ty(kind, ty, gcx, goal.span.file);

        if candidates.is_empty() {
            return SolverResult::Error(TypeError::NoUnaryOperator(ty, kind));
        }

        if let [candidate] = candidates.as_slice() {
            let obligations =
                self.select_fn_for_method(*candidate, ty, &unary_goal_to_method_goal(goal));
            return SolverResult::Solved(obligations);
        }

        let mut valid = vec![];
        for &candidate in &candidates {
            if self.evaluate_method_candidate(candidate, ty, &unary_goal_to_method_goal(goal)) {
                valid.push(candidate);
            }
        }

        if let [candidate] = valid.as_slice() {
            let obligations =
                self.select_fn_for_method(*candidate, ty, &unary_goal_to_method_goal(goal));
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

impl<'icx, 'ctx, 'rcx> SolverDelegate<'icx, 'ctx, 'rcx> {
    pub fn solve_binary(&mut self, goal: BinaryOperatorGoal<'ctx>) -> SolverResult<'ctx> {
        let gcx = self.gcx();
        let lhs = self.icx().shallow_resolve(goal.lhs);
        let rhs = self.icx().shallow_resolve(goal.rhs);
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
                        goal.rho,
                        gcx.store.common_types.bool,
                    ));
                    return SolverResult::Solved(vec![Obligation { goal, location }]);
                }
                _ => return SolverResult::Error(TypeError::InvalidPointerEquality(lhs)),
            }
        }

        let kind = if !goal.assigning {
            OperatorKind::from_binary(goal.operator)
        } else {
            OperatorKind::assign_from_binary(goal.operator).expect("Assign Op")
        };
        let candidates = associated_operators_for_ty(kind, lhs, gcx, goal.span.file);

        if candidates.is_empty() {
            return SolverResult::Error(TypeError::NoBinaryOperator(lhs, rhs, kind));
        }

        if let [candidate] = candidates.as_slice() {
            let obligations =
                self.select_fn_for_method(*candidate, lhs, &binary_goal_to_method_goal(goal, gcx));
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
            let obligations =
                self.select_fn_for_method(*candidate, lhs, &binary_goal_to_method_goal(goal, gcx));
            return SolverResult::Solved(obligations);
        }

        if valid.is_empty() {
            return SolverResult::Error(TypeError::NoOverloadCandidateMatch);
        }

        SolverResult::Deferred
    }
}

fn binary_goal_to_method_goal<'ctx>(
    goal: BinaryOperatorGoal<'ctx>,
    gcx: GlobalContext<'ctx>,
) -> MethodCallGoal<'ctx> {
    let arguments = gcx.store.interners.intern_slice(&[OverloadArgument {
        ty: goal.rhs,
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

impl<'icx, 'ctx, 'rcx> SolverDelegate<'icx, 'ctx, 'rcx> {
    pub fn solve_subscript(&mut self, goal: OverloadGoal<'ctx>) -> SolverResult<'ctx> {
        let gcx = self.gcx();
        let lhs = self.icx().shallow_resolve(goal.callee_var);
        if lhs.is_infer() {
            return SolverResult::Deferred;
        }
        let candidates =
            associated_operators_for_ty(OperatorKind::Index, lhs, gcx, goal.callee_span.file);

        if candidates.is_empty() {
            return SolverResult::Error(TypeError::NoOverloadCandidateMatch);
        }

        if let [candidate] = candidates.as_slice() {
            let obligations = self.select_fn_for_method(
                *candidate,
                lhs,
                &overload_goal_to_method_goal(goal, lhs),
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
