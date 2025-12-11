use crate::{
    compile::context::Gcx,
    sema::{error::SpannedErrorList, models::Ty, tycheck::infer::InferCtx},
    span::{Span, Spanned},
};
pub use models::*;
use std::{cmp::Reverse, collections::VecDeque, rc::Rc};

mod apply;
mod models;
mod unify;

pub struct ConstraintSystem<'ctx> {
    pub infer_cx: Rc<InferCtx<'ctx>>,
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

    pub fn add_goal(&mut self, goal: Goal<'ctx>, location: Span) {
        self.obligations.push_back(Obligation { location, goal });
    }
}

impl<'ctx> ConstraintSystem<'ctx> {
    pub fn solve_all(&mut self) {
        let solver = ConstraintSolver {
            icx: self.infer_cx.clone(),
            obligations: std::mem::take(&mut self.obligations),
        };

        let mut driver = SolverDriver::new(solver);
        let result = driver.solve_to_fixpoint();

        let Err(errors) = result else {
            return;
        };

        let gcx = self.infer_cx.gcx;
        let dcx = gcx.dcx();
        for error in errors {
            dcx.emit_error(error.value.format(gcx), Some(error.span));
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
    fn solve(&mut self, obligation: Obligation<'ctx>) -> SolverResult<'ctx> {
        let location = obligation.location;
        let goal = obligation.goal;
        match goal {
            Goal::Equal(lhs, rhs) => self.solve_equality(location, lhs, rhs),
            Goal::Apply(data) => self.solve_apply(data),
            Goal::BindOverload(data) => self.solve_bind_overload(location, data),
            Goal::Disjunction(branches) => self.solve_disjunction(location, branches),
        }
    }

    fn solve_equality(
        &mut self,
        location: Span,
        lhs: Ty<'ctx>,
        rhs: Ty<'ctx>,
    ) -> SolverResult<'ctx> {
        match self.unify(lhs, rhs) {
            Ok(_) => SolverResult::Solved(vec![]),
            Err(e) => {
                let error = Spanned::new(e, location);
                let errors = vec![error];
                SolverResult::Error(errors)
            }
        }
    }

    fn fork(&self) -> ConstraintSolver<'ctx> {
        ConstraintSolver {
            icx: self.icx.clone(),
            obligations: self.obligations.clone(),
        }
    }

    fn solve_disjunction(
        &mut self,
        location: Span,
        branches: Vec<DisjunctionBranch<'ctx>>,
    ) -> SolverResult<'ctx> {
        let mut successful = vec![];
        let mut failed = false;

        for branch in branches {
            let probe_goal = branch.goal.clone();
            let probe_result = self.icx.probe(|_| {
                let mut fork = self.fork();
                fork.obligations.push_front(Obligation {
                    location,
                    goal: probe_goal,
                });
                let mut driver = SolverDriver::new(fork);
                driver.solve_to_fixpoint()
            });

            match probe_result {
                Ok(()) => successful.push(branch),
                Err(_) => failed = true,
            }
        }

        if successful.is_empty() {
            if failed {
                // No branch succeeded; surface a generic overload failure.
                return SolverResult::Error(vec![Spanned::new(
                    crate::sema::error::TypeError::NoOverloadMatches,
                    location,
                )]);
            }
            return SolverResult::Deferred;
        }

        if successful.len() == 1 {
            let branch = successful.pop().unwrap();
            return self.solve(Obligation {
                location,
                goal: branch.goal,
            });
        }

        // Ambiguous or needs ranking.
        let ranked = rank_branches(successful);
        let best = ranked.first().cloned();
        let second = ranked.get(1);

        match (best, second) {
            (Some(best), Some(second)) if best.score == second.score => {
                return SolverResult::Error(vec![Spanned::new(
                    crate::sema::error::TypeError::AmbiguousOverload,
                    location,
                )]);
            }
            (Some(best), _) => self.solve(Obligation {
                location,
                goal: best.branch.goal,
            }),
            _ => unreachable!(),
        }
    }

    fn solve_bind_overload(
        &mut self,
        location: Span,
        data: BindOverloadGoalData<'ctx>,
    ) -> SolverResult<'ctx> {
        let BindOverloadGoalData {
            var_ty,
            candidate_ty,
            source,
        } = data;

        match self.unify(var_ty, candidate_ty) {
            Ok(_) => {
                self.icx.bind_overload(var_ty, source);
                SolverResult::Solved(vec![])
            }
            Err(e) => {
                let error = Spanned::new(e, location);
                SolverResult::Error(vec![error])
            }
        }
    }
}

#[derive(Clone)]
struct RankedBranch<'ctx> {
    branch: DisjunctionBranch<'ctx>,
    score: u32,
}

fn rank_branches<'ctx>(branches: Vec<DisjunctionBranch<'ctx>>) -> Vec<RankedBranch<'ctx>> {
    let mut ranked: Vec<RankedBranch<'ctx>> = branches
        .into_iter()
        .map(|branch| RankedBranch { branch, score: 0 })
        .collect();

    ranked.sort_by_key(|b| Reverse(b.score));
    ranked
}

struct SolverDriver<'ctx> {
    solver: ConstraintSolver<'ctx>,
    deferred: VecDeque<Obligation<'ctx>>,
    errors: SpannedErrorList<'ctx>,
    defaulted: bool,
}

impl<'ctx> SolverDriver<'ctx> {
    fn new(solver: ConstraintSolver<'ctx>) -> SolverDriver<'ctx> {
        SolverDriver {
            solver,
            deferred: VecDeque::new(),
            errors: vec![],
            defaulted: false,
        }
    }

    fn solve_to_fixpoint(&mut self) -> Result<(), SpannedErrorList<'ctx>> {
        loop {
            let made_progress = self.drain_queue();

            if !self.errors.is_empty() {
                return Err(std::mem::take(&mut self.errors));
            }

            if !self.solver.obligations.is_empty() {
                continue;
            }

            if !self.defaulted {
                self.defaulted = true;
                self.solver.icx.default_numeric_vars();
                if !self.deferred.is_empty() {
                    self.solver.obligations.append(&mut self.deferred);
                }
                continue;
            }

            if !self.deferred.is_empty() {
                if made_progress {
                    self.solver.obligations.append(&mut self.deferred);
                    continue;
                }

                todo!("deferred obligations remaining after defaulting");
            }

            return Ok(());
        }
    }

    fn drain_queue(&mut self) -> bool {
        let mut made_progress = false;
        while let Some(obligation) = self.solver.obligations.pop_front() {
            match self.solver.solve(obligation.clone()) {
                SolverResult::Deferred => self.deferred.push_back(obligation),
                SolverResult::Solved(mut obligations) => {
                    made_progress = true;
                    for obligation in obligations.drain(..) {
                        self.solver.obligations.push_front(obligation);
                    }
                }
                SolverResult::Error(errs) => self.errors.extend(errs),
            }
        }

        made_progress
    }
}
