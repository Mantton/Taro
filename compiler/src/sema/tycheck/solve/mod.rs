use crate::{
    compile::context::Gcx,
    hir::NodeID,
    sema::{error::SpannedErrorList, models::Ty, tycheck::infer::InferCtx},
    span::{Span, Spanned},
};
pub use models::*;
use rustc_hash::FxHashMap;
use std::{cmp::Reverse, collections::VecDeque, rc::Rc};

mod apply;
mod models;
mod op;
mod overload;
mod unify;

pub struct ConstraintSystem<'ctx> {
    pub infer_cx: Rc<InferCtx<'ctx>>,
    obligations: VecDeque<Obligation<'ctx>>,
    expr_tys: FxHashMap<NodeID, Ty<'ctx>>,
}

impl<'ctx> ConstraintSystem<'ctx> {
    pub fn new(context: Gcx<'ctx>) -> ConstraintSystem<'ctx> {
        ConstraintSystem {
            infer_cx: Rc::new(InferCtx::new(context)),
            obligations: Default::default(),
            expr_tys: Default::default(),
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

    pub fn record_expr_ty(&mut self, id: NodeID, ty: Ty<'ctx>) {
        self.expr_tys.insert(id, ty);
    }

    pub fn expr_ty(&self, id: NodeID) -> Option<Ty<'ctx>> {
        self.expr_tys.get(&id).copied()
    }

    pub fn resolved_expr_types(&self) -> FxHashMap<NodeID, Ty<'ctx>> {
        let gcx = self.infer_cx.gcx;
        self.expr_tys
            .iter()
            .map(|(&id, &ty)| {
                let resolved = self.infer_cx.resolve_vars_if_possible(ty);
                let resolved = if resolved.is_infer() {
                    Ty::error(gcx)
                } else {
                    resolved
                };
                (id, resolved)
            })
            .collect()
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
            Goal::UnaryOp(data) => self.solve_unary(data),
            Goal::BinaryOp(data) => self.solve_binary(data),
            Goal::Coerce { from, to } => self.solve_coerce(location, from, to),
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

    fn solve_coerce(
        &mut self,
        location: Span,
        from: Ty<'ctx>,
        to: Ty<'ctx>,
    ) -> SolverResult<'ctx> {
        // Minimal coercion: just equality for now.
        self.solve_equality(location, from, to)
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
