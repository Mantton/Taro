use std::collections::VecDeque;

use crate::{
    sema::{
        error::TypeError,
        tycheck::solve::{
            Obligation,
            solver::{RootOutcome, SolverDelegate},
        },
    },
    span::Spanned,
};

pub struct ObligationCtx<'ctx> {
    pub obligations: VecDeque<Obligation<'ctx>>,
}

impl<'ctx> ObligationCtx<'ctx> {
    pub fn new() -> ObligationCtx<'ctx> {
        ObligationCtx {
            obligations: Default::default(),
        }
    }

    pub fn add_obligation(&mut self, obligation: Obligation<'ctx>) {
        self.obligations.push_back(obligation);
    }
}

impl<'ctx> ObligationCtx<'ctx> {
    pub fn solve_all(&mut self) -> Vec<Spanned<TypeError<'ctx>>> {
        let mut errors = vec![];

        // Fixpoint loop
        'outer: loop {
            if self.obligations.is_empty() {
                break;
            }

            let obligations = std::mem::take(&mut self.obligations);
            let mut made_progress = false;

            for obligation in obligations {
                let mut delegate = SolverDelegate::new(obligation);
                match delegate.solve_root() {
                    Ok(RootOutcome::Solved) => {
                        made_progress = true;
                        // obligation fully discharged
                    }
                    Ok(RootOutcome::Deferred) => {
                        // couldn’t (fully) solve now; requeue the root
                        self.add_obligation(obligation);
                    }
                    Err(e) => {
                        errors.push(e);
                    }
                }
            }

            if !made_progress {
                // Stuck: everything that was requeued got deferred again.
                break 'outer;
            }
        }

        errors
    }
}
