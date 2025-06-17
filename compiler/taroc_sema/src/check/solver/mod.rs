use crate::{
    GlobalContext,
    error::TypeError,
    infer::InferCtx,
    ty::{Constraint, ParamEnv, Ty},
};
use std::collections::VecDeque;
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
    pub callee_span: Span,
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

pub enum SolverResult<'ctx> {
    Deferred,
    Solved(Vec<Obligation<'ctx>>), // New Obligations Spawned
    Error(TypeError<'ctx>),
}

type PendingObligations<'ctx> = VecDeque<(Obligation<'ctx>, Option<bool>)>;

#[derive(Default)]
pub struct ObligationStore<'ctx> {
    pending: PendingObligations<'ctx>,
}
impl<'ctx> ObligationStore<'ctx> {
    fn add(&mut self, obligation: Obligation<'ctx>) {
        self.pending.push_back((obligation, None));
    }

    fn drain_pending(
        &mut self,
        cond: impl Fn(&Obligation<'ctx>) -> bool,
    ) -> PendingObligations<'ctx> {
        let (unstalled, pending) = std::mem::take(&mut self.pending)
            .into_iter()
            .partition(|(o, _)| cond(o));
        self.pending = pending;
        unstalled
    }
}

pub struct ObligationSolver<'ctx> {
    obligations: ObligationStore<'ctx>,
}

impl<'ctx> ObligationSolver<'ctx> {
    pub fn new() -> ObligationSolver<'ctx> {
        ObligationSolver {
            obligations: Default::default(),
        }
    }

    pub fn add_obligation(&mut self, obligation: Obligation<'ctx>) {
        self.obligations.add(obligation);
    }
}

impl<'ctx> ObligationSolver<'ctx> {
    pub fn solve(&mut self, icx: &InferCtx<'ctx>, param_env: ParamEnv<'ctx>) {
        if self.obligations.pending.is_empty() {
            return;
        }

        loop {
            let mut progress = false;

            for (obligation, _) in self.obligations.drain_pending(|_| true) {
                let mut delegate = SolverDelegate::new(icx, param_env);
                let result = delegate.solve(obligation);
                match result {
                    0 => {
                        self.obligations.add(obligation);
                    }
                    1 => {
                        delegate.solve_nested_obligations();
                        progress = true
                    }
                    2 => progress = true,
                    _ => unreachable!(),
                }
            }

            if !progress {
                break;
            }
        }
    }
}

pub struct SolverDelegate<'icx, 'ctx> {
    icx: &'icx InferCtx<'ctx>,
    param_env: ParamEnv<'ctx>,
    nested_obligations: Vec<Obligation<'ctx>>,
    has_error: bool,
}

impl<'icx, 'ctx> SolverDelegate<'icx, 'ctx> {
    pub fn new(icx: &'icx InferCtx<'ctx>, param_env: ParamEnv<'ctx>) -> SolverDelegate<'icx, 'ctx> {
        SolverDelegate {
            icx,
            param_env,
            nested_obligations: vec![],
            has_error: false,
        }
    }

    pub fn gcx(&self) -> GlobalContext<'ctx> {
        return self.icx.gcx;
    }
}

impl<'icx, 'ctx> SolverDelegate<'icx, 'ctx> {
    pub fn add_obligation(&mut self, obligation: Obligation<'ctx>) {
        self.nested_obligations.push(obligation);
    }

    pub fn add_obligations(&mut self, obligations: Vec<Obligation<'ctx>>) {
        for obligation in obligations.into_iter() {
            self.add_obligation(obligation);
        }
    }

    fn solve_nested_obligations(&mut self) {
        for obligation in self.nested_obligations.iter() {
            let mut delegate = SolverDelegate::new(self.icx, self.param_env);
            delegate.solve(*obligation);
            delegate.solve_nested_obligations();
            if delegate.has_error {
                self.has_error = true;
            }
        }
    }
}

impl<'icx, 'ctx> SolverDelegate<'icx, 'ctx> {
    fn solve(&mut self, obligation: Obligation<'ctx>) -> usize {
        let result = self.try_solve(obligation);
        match result {
            SolverResult::Deferred => 0,
            SolverResult::Solved(obligations) => {
                self.add_obligations(obligations);
                1
            }
            SolverResult::Error(_) => {
                self.has_error = true;
                2
            }
        }
    }
    fn try_solve(&mut self, obligation: Obligation<'ctx>) -> SolverResult<'ctx> {
        match obligation.goal {
            Goal::Constraint(constraint) => {
                return self.solve_constraint(constraint, obligation.location);
            }
            Goal::Coerce { from, to } => {
                let result = self.coerce(from, to);

                match result {
                    Ok(defer) => {
                        if defer.requeue() {
                            return SolverResult::Deferred;
                        } else {
                            return SolverResult::Solved(vec![]);
                        }
                    }
                    Err(err) => return SolverResult::Error(err),
                }
            }
            Goal::Apply(goal) => {
                return self.solve_application(goal);
            }
        };
    }
}
