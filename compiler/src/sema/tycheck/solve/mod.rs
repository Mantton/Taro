use crate::{
    compile::context::Gcx,
    sema::{error::TypeError, models::Ty, tycheck::infer::InferCtx},
    span::{Span, Spanned},
};
pub use models::*;
use std::{collections::VecDeque, rc::Rc};

mod models;
mod unify;

pub struct ConstraintSystem<'ctx> {
    infer_cx: Rc<InferCtx<'ctx>>,
    obligations: VecDeque<Obligation<'ctx>>,
}

impl<'ctx> ConstraintSystem<'ctx> {
    pub fn new(context: Gcx<'ctx>) -> ConstraintSystem<'ctx> {
        ConstraintSystem {
            infer_cx: Rc::new(InferCtx::new(context)),
            obligations: Default::default(),
        }
    }
}

impl<'ctx> ConstraintSystem<'ctx> {
    pub fn equal(&mut self, lhs: Ty<'ctx>, rhs: Ty<'ctx>, location: Span) {
        if lhs == rhs {
            return;
        }
        let obligation = Obligation {
            location,
            goal: Goal::Equal(lhs, rhs),
        };
        self.obligations.push_back(obligation);
    }
}

impl<'ctx> ConstraintSystem<'ctx> {
    pub fn solve_all(&mut self) {
        let solver = ConstraintSolver {
            icx: self.infer_cx.clone(),
            obligations: std::mem::take(&mut self.obligations),
        };

        let result = solver.solve_all();

        let gcx = self.infer_cx.gcx;
        match result {
            Ok(_) => {}
            Err(e) => {
                gcx.dcx().emit_error(e.value.format(gcx), Some(e.span));
            }
        }
    }
}

struct ConstraintSolver<'ctx> {
    pub icx: Rc<InferCtx<'ctx>>,
    obligations: VecDeque<Obligation<'ctx>>,
}

impl<'ctx> ConstraintSolver<'ctx> {
    pub fn gcx(&self) -> Gcx<'ctx> {
        self.icx.gcx
    }
}

impl<'ctx> ConstraintSolver<'ctx> {
    fn solve_all(mut self) -> Result<(), Spanned<TypeError<'ctx>>> {
        while let Some(obligation) = self.obligations.pop_front() {
            let location = obligation.location;
            let result = self.solve(obligation);

            match result {
                SolverResult::Deferred => todo!("deferred obligation"),
                SolverResult::Solved(obligations) => {
                    for obligation in obligations {
                        self.obligations.push_front(obligation);
                    }
                }
                SolverResult::Error(e) => return Err(Spanned::new(e, location)),
            }
        }

        return Ok(());
    }

    fn solve(&mut self, obligation: Obligation<'ctx>) -> SolverResult<'ctx> {
        let goal = obligation.goal;

        match goal {
            Goal::Equal(lhs, rhs) => match self.unify(lhs, rhs) {
                Ok(_) => SolverResult::Solved(vec![]),
                Err(e) => SolverResult::Error(e),
            },
        }
    }
}
