use crate::{
    compile::context::Gcx,
    hir::NodeID,
    sema::{
        error::SpannedErrorList,
        models::{GenericArguments, Ty},
        tycheck::infer::InferCtx,
    },
    span::{Span, Spanned},
};
pub use models::*;
use rustc_hash::FxHashMap;
use std::{cell::RefCell, cmp::Reverse, collections::VecDeque, rc::Rc};

mod adt;
mod apply;
mod member;
mod method;
mod models;
mod op;
mod overload;
mod tuple;
mod unify;

pub struct ConstraintSystem<'ctx> {
    pub infer_cx: Rc<InferCtx<'ctx>>,
    obligations: VecDeque<Obligation<'ctx>>,
    expr_tys: FxHashMap<NodeID, Ty<'ctx>>,
    adjustments: FxHashMap<NodeID, Vec<Adjustment<'ctx>>>,
    pub locals: RefCell<FxHashMap<NodeID, Ty<'ctx>>>,
    pub field_indices: FxHashMap<NodeID, usize>,
    overload_sources: FxHashMap<NodeID, crate::sema::resolve::models::DefinitionID>,
    instantiation_args: FxHashMap<NodeID, GenericArguments<'ctx>>,
    current_def: crate::sema::resolve::models::DefinitionID,
}

impl<'ctx> ConstraintSystem<'ctx> {
    pub fn new(
        context: Gcx<'ctx>,
        current_def: crate::sema::resolve::models::DefinitionID,
    ) -> ConstraintSystem<'ctx> {
        ConstraintSystem {
            infer_cx: Rc::new(InferCtx::new(context)),
            obligations: Default::default(),
            expr_tys: Default::default(),
            locals: Default::default(),
            adjustments: Default::default(),
            field_indices: Default::default(),
            overload_sources: Default::default(),
            instantiation_args: Default::default(),
            current_def,
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

    pub fn resolved_local_types(&self) -> FxHashMap<NodeID, Ty<'ctx>> {
        let gcx = self.infer_cx.gcx;
        self.locals
            .borrow()
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

    pub fn resolved_adjustments(&self) -> FxHashMap<NodeID, Vec<Adjustment<'ctx>>> {
        self.adjustments.clone()
    }

    pub fn resolved_field_indices(&self) -> FxHashMap<NodeID, usize> {
        self.field_indices.clone()
    }

    pub fn resolved_overload_sources(
        &self,
    ) -> FxHashMap<NodeID, crate::sema::resolve::models::DefinitionID> {
        self.overload_sources.clone()
    }

    pub fn record_instantiation(&mut self, node_id: NodeID, args: GenericArguments<'ctx>) {
        self.instantiation_args.insert(node_id, args);
    }

    pub fn resolved_instantiations(&self) -> FxHashMap<NodeID, GenericArguments<'ctx>> {
        use crate::sema::models::GenericArgument;

        let gcx = self.infer_cx.gcx;
        self.instantiation_args
            .iter()
            .map(|(&id, &args)| {
                let resolved: Vec<GenericArgument<'ctx>> = args
                    .iter()
                    .map(|arg| match arg {
                        GenericArgument::Type(ty) => {
                            let resolved = self.infer_cx.resolve_vars_if_possible(*ty);
                            GenericArgument::Type(resolved)
                        }
                        GenericArgument::Const(c) => GenericArgument::Const(*c),
                    })
                    .collect();
                let interned = gcx.store.interners.intern_generic_args(resolved);
                (id, interned)
            })
            .collect()
    }
}

impl<'ctx> ConstraintSystem<'ctx> {
    pub fn solve_all(&mut self) {
        let solver = ConstraintSolver {
            icx: self.infer_cx.clone(),
            obligations: std::mem::take(&mut self.obligations),
            adjustments: std::mem::take(&mut self.adjustments),
            field_indices: std::mem::take(&mut self.field_indices),
            overload_sources: std::mem::take(&mut self.overload_sources),
            instantiation_args: std::mem::take(&mut self.instantiation_args),
            current_def: self.current_def,
        };

        let mut driver = SolverDriver::new(solver);
        let result = driver.solve_to_fixpoint();
        // Pull adjustments back out of the solver/driver.
        let (adjustments, field_indices, overload_sources, instantiation_args) =
            driver.into_parts();
        self.adjustments = adjustments;
        self.field_indices = field_indices;
        self.overload_sources = overload_sources;
        self.instantiation_args = instantiation_args;

        let Err(errors) = result else {
            // Only check for unresolved vars when solving succeeded
            // If there are unresolved vars with no errors, it's a bug
            self.check_unresolved_vars();
            return;
        };

        let gcx = self.infer_cx.gcx;

        let dcx = gcx.dcx();
        for error in errors {
            dcx.emit_error(error.value.format(gcx), Some(error.span));
        }
    }

    /// Check for unresolved type variables after solving completes successfully.
    /// If there are unresolved vars when no errors occurred, it indicates a bug.
    fn check_unresolved_vars(&self) {
        use crate::sema::models::{InferTy, TyKind};

        let gcx = self.infer_cx.gcx;
        for (var_id, origin) in self.infer_cx.all_type_var_origins() {
            let var_ty = Ty::new(TyKind::Infer(InferTy::TyVar(var_id)), gcx);
            let resolved = self.infer_cx.resolve_vars_if_possible(var_ty);
            if resolved.is_infer() {
                panic!(
                    "ICE: unresolved type var {:?} at {:?} with no errors",
                    var_id, origin.location
                );
            }
        }
    }
}

struct ConstraintSolver<'ctx> {
    pub icx: Rc<InferCtx<'ctx>>,
    obligations: VecDeque<Obligation<'ctx>>,
    adjustments: FxHashMap<NodeID, Vec<Adjustment<'ctx>>>,
    pub field_indices: FxHashMap<NodeID, usize>,
    overload_sources: FxHashMap<NodeID, crate::sema::resolve::models::DefinitionID>,
    instantiation_args: FxHashMap<NodeID, GenericArguments<'ctx>>,
    current_def: crate::sema::resolve::models::DefinitionID,
}

impl<'ctx> ConstraintSolver<'ctx> {
    pub fn gcx(&self) -> Gcx<'ctx> {
        self.icx.gcx
    }

    pub fn record_field_index(&mut self, id: NodeID, index: usize) {
        self.field_indices.insert(id, index);
    }

    pub fn record_overload_source(
        &mut self,
        node_id: NodeID,
        source: crate::sema::resolve::models::DefinitionID,
    ) {
        self.overload_sources.insert(node_id, source);
    }

    pub fn record_instantiation(&mut self, node_id: NodeID, args: GenericArguments<'ctx>) {
        self.instantiation_args.insert(node_id, args);
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
            Goal::AssignOp(data) => self.solve_assign_op(data),
            Goal::Coerce { from, to } => self.solve_coerce(location, from, to),
            Goal::Member(data) => self.solve_member(data),
            Goal::MethodCall(data) => self.solve_method_call(data),
            Goal::StructLiteral(data) => self.solve_struct_literal(data),
            Goal::TupleAccess(data) => self.solve_tuple_access(data),
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
            adjustments: self.adjustments.clone(),
            field_indices: self.field_indices.clone(),
            overload_sources: self.overload_sources.clone(),
            instantiation_args: self.instantiation_args.clone(),
            current_def: self.current_def,
        }
    }

    fn solve_coerce(&mut self, location: Span, from: Ty<'ctx>, to: Ty<'ctx>) -> SolverResult<'ctx> {
        // Minimal coercion: just equality for now.
        self.solve_equality(location, from, to)
    }
}

#[derive(Clone)]
struct RankedBranch<'ctx> {
    branch: DisjunctionBranch<'ctx>,
    score: u32,
}

fn rank_branches<'ctx>(
    gcx: Gcx<'ctx>,
    branches: Vec<DisjunctionBranch<'ctx>>,
) -> Vec<RankedBranch<'ctx>> {
    let mut ranked: Vec<RankedBranch<'ctx>> = branches
        .into_iter()
        .map(|branch| {
            let score = match branch.source {
                Some(def_id) if gcx.generics_of(def_id).is_empty() => 1,
                _ => 0,
            };
            RankedBranch { branch, score }
        })
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

    fn into_parts(
        self,
    ) -> (
        FxHashMap<NodeID, Vec<Adjustment<'ctx>>>,
        FxHashMap<NodeID, usize>,
        FxHashMap<NodeID, crate::sema::resolve::models::DefinitionID>,
        FxHashMap<NodeID, GenericArguments<'ctx>>,
    ) {
        (
            self.solver.adjustments,
            self.solver.field_indices,
            self.solver.overload_sources,
            self.solver.instantiation_args,
        )
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
                    for obligation in obligations.drain(..).rev() {
                        self.solver.obligations.push_front(obligation);
                    }
                }
                SolverResult::Error(errs) => self.errors.extend(errs),
            }
        }

        made_progress
    }
}
