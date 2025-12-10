use crate::{
    compile::context::Gcx,
    sema::{
        error::{SpannedError, TypeError},
        tycheck::{
            infer::InferCtx,
            solve::{Goal, Obligation},
        },
    },
    span::Spanned,
};
use std::collections::VecDeque;

pub struct SolverDelegate<'icx, 'ctx> {
    infer_cx: &'icx InferCtx<'ctx>,
    nested: VecDeque<Obligation<'ctx>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ObligationState {
    Deferred,
    Solved(bool),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RootOutcome {
    Solved,
    Deferred,
}

pub type ObligationResult<'ctx> = Result<ObligationState, SpannedError<'ctx>>;

pub enum SolverResult<'ctx> {
    Deferred,
    Solved(Vec<Obligation<'ctx>>), // Solved, With Sub-Obligations
    Error(TypeError<'ctx>),        // Failed, With Error
}

impl<'icx, 'ctx> SolverDelegate<'icx, 'ctx> {
    #[inline]
    pub fn icx(&self) -> &'icx InferCtx<'ctx> {
        &self.infer_cx
    }

    #[inline]
    pub fn gcx(&self) -> Gcx<'ctx> {
        self.infer_cx.gcx
    }

    pub fn add_obligation(&mut self, obligation: Obligation<'ctx>) {
        self.nested.push_back(obligation);
    }

    pub fn add_obligations(&mut self, obligations: Vec<Obligation<'ctx>>) {
        for obligation in obligations.into_iter() {
            self.add_obligation(obligation);
        }
    }
}

impl<'icx, 'ctx> SolverDelegate<'icx, 'ctx> {
    pub fn solve_root(
        icx: &'icx InferCtx<'ctx>,
        root: &Obligation<'ctx>,
    ) -> Result<RootOutcome, SpannedError<'ctx>> {
        let mut cx = SolverDelegate {
            infer_cx: icx,
            nested: VecDeque::new(),
        };

        // Solve Root
        let state = cx.solve(root)?;

        match state {
            ObligationState::Deferred => {
                // root was deferred
                // No progress was made
                // mark to be requeued
                Ok(RootOutcome::Deferred)
            }
            ObligationState::Solved(true) => {
                // root was solved
                // we have pending sub-obligations
                cx.solve_children()
            }
            ObligationState::Solved(false) => {
                // root was solved
                // no sub-obligations
                // mark as completed
                Ok(RootOutcome::Solved)
            }
        }
    }

    fn solve_children(&mut self) -> Result<RootOutcome, SpannedError<'ctx>> {
        let obligations = std::mem::take(&mut self.nested);
        let mut any_deferred = false;

        for obligation in obligations {
            let result = SolverDelegate::solve_root(self.infer_cx, &obligation);
            match result? {
                RootOutcome::Solved => {}
                RootOutcome::Deferred => {
                    any_deferred = true;
                }
            }
        }

        if any_deferred {
            Ok(RootOutcome::Deferred)
        } else {
            Ok(RootOutcome::Solved)
        }
    }

    fn solve(&mut self, obligation: &Obligation<'ctx>) -> ObligationResult<'ctx> {
        let result = self.try_solve(obligation);

        match result {
            SolverResult::Deferred => Ok(ObligationState::Deferred),
            SolverResult::Solved(obligations) => {
                let has_nested = !obligations.is_empty();
                let state = ObligationState::Solved(has_nested);
                self.add_obligations(obligations);
                Ok(state)
            }
            SolverResult::Error(e) => Err(Spanned::new(e, obligation.location)),
        }
    }

    fn try_solve(&mut self, obligation: &Obligation<'ctx>) -> SolverResult<'ctx> {
        let goal = &obligation.goal;
        let _ = obligation.location;
        match goal {
            Goal::Equal(lhs, rhs) => self.solve_equality(*lhs, *rhs),
            Goal::Apply(goal) => self.solve_application(goal),
        }
    }
}
