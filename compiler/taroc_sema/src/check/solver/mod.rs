use crate::{
    GlobalContext,
    check::{
        context::func::FnCtx,
        solver::{cast::CastGoal, shape::Shape},
    },
    error::TypeError,
    infer::InferCtx,
    ty::{Constraint, ParamEnv, Ty},
    utils::autoderef::Autoderef,
};
use std::{collections::VecDeque, vec};
use taroc_hir::{BinaryOperator, Mutability, UnaryOperator};
use taroc_span::{Identifier, Span, Spanned};

mod apply;
pub mod cast;
mod coerce;
mod constraint;
mod field;
mod method;
mod op;
mod reference;
pub mod shape;
mod unify;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Goal<'ctx> {
    Constraint(Constraint<'ctx>),
    Coerce {
        from: Ty<'ctx>,
        to: Ty<'ctx>,
    },
    Apply(OverloadGoal<'ctx>),
    FieldAccess(FieldAccessGoal<'ctx>),
    TupleAccess(TupleAccessGoal<'ctx>),
    MethodCall(MethodCallGoal<'ctx>),
    UnaryOperator(UnaryOperatorGoal<'ctx>),
    BinaryOperator(BinaryOperatorGoal<'ctx>),
    IndexOperator(OverloadGoal<'ctx>),
    Cast(CastGoal<'ctx>),
    RecieverCoerce {
        from: Ty<'ctx>,
        to: Ty<'ctx>,
    },
    Shape {
        scrutinee_ty: Ty<'ctx>,
        shape: Shape<'ctx>,
    },
    Ref(ReferenceGoal<'ctx>),
    Deref(DerefGoal<'ctx>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct OverloadGoal<'ctx> {
    pub callee_span: Span,
    pub expr_span: Span,
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
pub struct FieldAccessGoal<'ctx> {
    pub base_ty: Ty<'ctx>,
    pub field: Identifier,
    pub result_var: Ty<'ctx>,
    pub field_span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TupleAccessGoal<'ctx> {
    pub base_ty: Ty<'ctx>,
    pub index: usize,
    pub result_var: Ty<'ctx>,
    pub index_span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MethodCallGoal<'ctx> {
    pub call_span: Span,
    pub method: Identifier,
    pub receiver_ty: Ty<'ctx>,
    pub result_var: Ty<'ctx>,
    pub expected_result_ty: Option<Ty<'ctx>>,
    pub arguments: &'ctx [OverloadArgument<'ctx>],
    pub label_agnostic: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct UnaryOperatorGoal<'ctx> {
    pub operand_ty: Ty<'ctx>,
    pub result_var: Ty<'ctx>,
    pub expectation: Option<Ty<'ctx>>,
    pub operator: UnaryOperator,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BinaryOperatorGoal<'ctx> {
    pub lhs: Ty<'ctx>,
    pub rhs: Ty<'ctx>,
    pub rho: Ty<'ctx>,
    pub expectation: Option<Ty<'ctx>>,
    pub operator: BinaryOperator,
    pub span: Span,
    pub assigning: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ReferenceGoal<'ctx> {
    pub ty: Ty<'ctx>,
    pub mutability: Mutability,
    pub alpha: Ty<'ctx>, // resulting type
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DerefGoal<'ctx> {
    pub ty: Ty<'ctx>,
    pub alpha: Ty<'ctx>,
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
    pub fn solve(
        &mut self,
        fcx: &FnCtx<'_, 'ctx>,
        param_env: ParamEnv<'ctx>,
    ) -> Vec<Spanned<TypeError<'ctx>>> {
        if self.obligations.pending.is_empty() {
            return vec![];
        }

        let mut errors = vec![];

        loop {
            let mut progress = false;

            for (obligation, _) in self.obligations.drain_pending(|_| true) {
                let mut delegate = SolverDelegate::new(fcx, param_env);
                let result = delegate.solve_root_goal(obligation.goal, obligation.location);
                let GoalResult {
                    certainty,
                    progressed,
                } = match result {
                    Ok(i) => i,
                    Err(err) => {
                        errors.push(err);
                        continue;
                    }
                };
                // println!("{:?}", result.ok().unwrap());

                progress |= progressed;
                match certainty {
                    Certainty::Yes => {}
                    Certainty::Maybe => {
                        // deferred
                        self.obligations.add(obligation);
                    }
                }
            }

            if !progress {
                break;
            }
        }

        errors
    }
}

pub struct SolverDelegate<'icx, 'ctx> {
    _icx: &'icx InferCtx<'ctx>,
    param_env: ParamEnv<'ctx>,
    nested_obligations: Vec<Obligation<'ctx>>,
}

impl<'icx, 'ctx> SolverDelegate<'icx, 'ctx> {
    pub fn new(icx: &'icx InferCtx<'ctx>, param_env: ParamEnv<'ctx>) -> SolverDelegate<'icx, 'ctx> {
        SolverDelegate {
            _icx: icx,
            param_env,
            nested_obligations: vec![],
        }
    }

    #[inline]
    pub fn gcx(&self) -> GlobalContext<'ctx> {
        return self.icx().gcx;
    }

    #[inline]
    pub fn icx(&self) -> &'icx InferCtx<'ctx> {
        return &self._icx;
    }

    #[inline]
    pub fn autoderef(&self, span: Span, ty: Ty<'ctx>) -> Autoderef<'icx, 'ctx> {
        Autoderef::new(self.icx(), ty, span)
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
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GoalResult {
    certainty: Certainty,
    progressed: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Certainty {
    Yes,
    Maybe,
}

impl<'icx, 'ctx> SolverDelegate<'icx, 'ctx> {
    fn solve_root_goal(
        &mut self,
        goal: Goal<'ctx>,
        span: Span,
    ) -> Result<GoalResult, Spanned<TypeError<'ctx>>> {
        let result = self.solve(goal, span)?;

        if let Certainty::Yes = result.certainty {
            let result = self.solve_nested_goals()?;
            return Ok(GoalResult {
                certainty: result.certainty,
                progressed: true,
            });
        }

        Ok(result)
    }

    pub fn solve_nested_goals(&mut self) -> Result<GoalResult, Spanned<TypeError<'ctx>>> {
        let mut progressed = false;
        let mut certainty = Certainty::Yes;

        for obligation in self.nested_obligations.iter() {
            let mut delegate = SolverDelegate::new(self.icx(), self.param_env);
            let result = delegate.solve_root_goal(obligation.goal, obligation.location)?;

            progressed |= result.progressed;
            if let Certainty::Maybe = result.certainty {
                certainty = result.certainty;
                break;
            }
        }

        Ok(GoalResult {
            certainty,
            progressed,
        })
    }
}

impl<'icx, 'ctx> SolverDelegate<'icx, 'ctx> {
    fn solve(
        &mut self,
        goal: Goal<'ctx>,
        location: Span,
    ) -> Result<GoalResult, Spanned<TypeError<'ctx>>> {
        let result = self.try_solve(goal, location);
        match result {
            SolverResult::Deferred => Ok(GoalResult {
                certainty: Certainty::Maybe,
                progressed: false,
            }),
            SolverResult::Solved(obligations) => {
                self.add_obligations(obligations);
                Ok(GoalResult {
                    certainty: Certainty::Yes,
                    progressed: true,
                })
            }
            SolverResult::Error(err) => Err(Spanned::new(err, location)),
        }
    }

    fn try_solve(&mut self, goal: Goal<'ctx>, location: Span) -> SolverResult<'ctx> {
        match goal {
            Goal::Constraint(constraint) => self.solve_constraint(constraint, location),
            Goal::Coerce { from, to, .. } => self.solve_coerce(from, to),
            Goal::Apply(goal) => self.solve_application(goal),
            Goal::FieldAccess(goal) => self.solve_field_access(goal),
            Goal::TupleAccess(goal) => self.solve_tuple_access(goal),
            Goal::MethodCall(goal) => self.solve_method_call(goal),
            Goal::UnaryOperator(goal) => self.solve_unary(goal),
            Goal::BinaryOperator(goal) => self.solve_binary(goal),
            Goal::IndexOperator(goal) => self.solve_subscript(goal),
            Goal::Cast(goal) => self.solve_cast(goal),
            Goal::Shape {
                scrutinee_ty,
                shape,
            } => self.solve_shape(shape, scrutinee_ty, location),
            Goal::RecieverCoerce { from, to } => self.solve_reciever_coerce(from, to, location),
            Goal::Ref(goal) => self.solve_ref(goal, location),
            Goal::Deref(goal) => self.solve_deref(goal, location),
        }
    }
}
