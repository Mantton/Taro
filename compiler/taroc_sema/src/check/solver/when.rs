use crate::{
    check::solver::{BinaryOperatorGoal, Goal, Obligation, SolverDelegate, SolverResult},
    error::TypeError,
    ty::Ty,
};
use taroc_hir::BinaryOperator;
use taroc_span::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct WhenCaseGoal<'ctx> {
    pub span: Span,
    pub scrutinee_ty: Ty<'ctx>,
    pub ty: Ty<'ctx>,
}

impl<'icx, 'ctx> SolverDelegate<'icx, 'ctx> {
    pub fn solve_when_case_goal(&mut self, goal: WhenCaseGoal<'ctx>) -> SolverResult<'ctx> {
        let scrutinee_ty = self.icx.shallow_resolve(goal.scrutinee_ty);
        let expr_ty = self.icx.shallow_resolve(goal.ty);

        if scrutinee_ty.is_infer() {
            return SolverResult::Deferred;
        }

        let coerce_obligation = Obligation {
            location: goal.span,
            goal: Goal::Coerce {
                from: expr_ty,
                to: scrutinee_ty,
            },
        };
        let coerce_succcess = self.icx.probe(|_| {
            let mut ctx = SolverDelegate::new(self.icx, self.param_env);
            ctx.add_obligations(vec![coerce_obligation]);
            ctx.solve_nested_obligations();
            !ctx.has_error
        });

        if coerce_succcess {
            return SolverResult::Solved(vec![coerce_obligation]);
        }

        // Coercion Failed, Try Operator
        let bool_ty = self.icx.gcx.store.common_types.bool;

        let operator_success = self.icx.probe(|_| {
            // Now in main window, add operator obligation
            let binary_goal = BinaryOperatorGoal {
                lhs: scrutinee_ty,
                rhs: expr_ty,
                rho: self.icx.next_ty_var(goal.span),
                expectation: Some(bool_ty),
                operator: BinaryOperator::PatMatch,
                span: goal.span,
                assigning: false,
            };

            let operator_obligation = Obligation {
                location: goal.span,
                goal: Goal::BinaryOperator(binary_goal),
            };
            let mut ctx = SolverDelegate::new(self.icx, self.param_env);
            ctx.add_obligations(vec![operator_obligation]);
            ctx.solve_nested_obligations();
            !ctx.has_error
        });

        if !operator_success {
            return SolverResult::Error(TypeError::CannotMatchAgainst(expr_ty, scrutinee_ty));
        } else {
            // Now in main window, add operator obligation
            let binary_goal = BinaryOperatorGoal {
                lhs: scrutinee_ty,
                rhs: expr_ty,
                rho: self.icx.next_ty_var(goal.span),
                expectation: Some(bool_ty),
                operator: BinaryOperator::PatMatch,
                span: goal.span,
                assigning: false,
            };

            let operator_obligation = Obligation {
                location: goal.span,
                goal: Goal::BinaryOperator(binary_goal),
            };

            return SolverResult::Solved(vec![operator_obligation]);
        }
    }
}
