use std::ops::Deref;

use crate::{
    GlobalContext,
    error::TypeError,
    infer::InferCtx,
    ty::{Constraint, Ty},
};
use taroc_span::{Identifier, Span};

mod apply;
mod coerce;
mod constraint;
mod unify;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Goal<'ctx> {
    Constraint(Constraint<'ctx>),
    Coerce { from: Ty<'ctx>, to: Ty<'ctx> },
    Apply(OverloadGoal<'ctx>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct OverloadGoal<'ctx> {
    pub callee_var: Ty<'ctx>,                      // α
    pub result_var: Ty<'ctx>,                      // ρ
    pub expected_result_ty: Option<Ty<'ctx>>,      // ⟂ or τctx
    pub arguments: &'ctx [OverloadArgument<'ctx>], // β₀ … βₙ
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct OverloadArgument<'ctx> {
    pub ty: Ty<'ctx>,
    pub span: Span,
    pub label: Option<Identifier>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Obligation<'ctx> {
    pub location: Span,
    pub goal: Goal<'ctx>,
}

pub struct ObligationCollector<'ctx> {
    pending_obligations: Vec<Obligation<'ctx>>,
}

impl<'ctx> ObligationCollector<'ctx> {
    pub fn new() -> ObligationCollector<'ctx> {
        ObligationCollector {
            pending_obligations: vec![],
        }
    }
}

impl<'ctx> ObligationCollector<'ctx> {
    pub fn add_obligation(&mut self, obligation: Obligation<'ctx>) {
        self.pending_obligations.push(obligation);
    }

    pub fn count(&self) -> usize {
        self.pending_obligations.len()
    }

    pub fn take(&mut self) -> Vec<Obligation<'ctx>> {
        std::mem::take(&mut self.pending_obligations)
    }
}

pub struct ObligationSolver<'icx, 'ctx> {
    icx: &'icx InferCtx<'ctx>,
    pending_obligations: Vec<Obligation<'ctx>>,
}

impl<'icx, 'ctx> ObligationSolver<'icx, 'ctx> {
    pub fn new(
        icx: &'icx InferCtx<'ctx>,
        obligations: Vec<Obligation<'ctx>>,
    ) -> ObligationSolver<'icx, 'ctx> {
        ObligationSolver {
            icx,
            pending_obligations: obligations,
        }
    }

    pub fn gcx(&self) -> GlobalContext<'ctx> {
        return self.icx.gcx;
    }
}

impl<'icx, 'ctx> ObligationSolver<'icx, 'ctx> {
    pub fn solve(&mut self) {
        const ITER_LIMIT: usize = 2; // safeguard against runaway loops
        let mut iter = 0;

        // Keep iterating while there is still work to do.
        while self.solve_internal() {
            iter += 1;
            if iter >= ITER_LIMIT {
                // You could surface something more structured than `dummy()`.
                self.gcx().diagnostics.error(
                    "obligation solver: iteration limit reached".into(),
                    Span::module(),
                );
                break;
            }
        }
    }

    pub fn solve_internal(&mut self) -> bool {
        let pending = std::mem::take(&mut self.pending_obligations);
        let mut requeued = vec![];

        for obligation in pending.into_iter() {
            let result = self.try_solve(obligation);

            match result {
                Ok(requeue) => {
                    if requeue {
                        requeued.push(obligation);
                    }
                }
                Err(err) => self
                    .gcx()
                    .diagnostics
                    .error("encountered error".into(), obligation.location),
            }
        }

        // Put back anything that still needs another attempt.
        let has_more_work = !requeued.is_empty();
        self.pending_obligations = requeued;
        has_more_work
    }

    fn try_solve(&self, obligation: Obligation<'ctx>) -> Result<bool, TypeError<'ctx>> {
        match obligation.goal {
            Goal::Constraint(constraint) => {
                self.solve_constraint(constraint)?;
            }
            Goal::Coerce { from, to } => {
                let output = self.coerce(from, to)?;
                if output.requeue() {
                    return Ok(true);
                }
            }
            Goal::Apply(goal) => {
                self.resolve_application(goal)?;
            }
        };

        return Ok(false);
    }
}
