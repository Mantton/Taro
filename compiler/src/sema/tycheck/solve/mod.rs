use crate::{
    compile::context::Gcx,
    hir::NodeID,
    sema::{
        error::SpannedErrorList,
        models::{
            AliasKind, Constraint, GenericArgument, GenericArguments, InterfaceReference, Ty, TyKind,
        },
        tycheck::infer::InferCtx,
        tycheck::{
            constraints::canonical_constraints_of,
            utils::{instantiate::instantiate_constraint_with_args, normalize_ty},
        },
    },
    span::{Span, Spanned},
};
pub use models::*;
use rustc_hash::{FxHashMap, FxHashSet};
use std::{cell::RefCell, cmp::Reverse, collections::VecDeque, rc::Rc};

mod adt;
mod apply;
mod coerce;
mod interface;
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
    interface_calls: FxHashMap<NodeID, InterfaceCallInfo>,
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
        let mut cs = ConstraintSystem {
            infer_cx: Rc::new(InferCtx::new(context)),
            obligations: Default::default(),
            expr_tys: Default::default(),
            locals: Default::default(),
            adjustments: Default::default(),
            interface_calls: Default::default(),
            field_indices: Default::default(),
            overload_sources: Default::default(),
            instantiation_args: Default::default(),
            current_def,
        };

        let def_span = context.definition_ident(current_def).span;
        cs.add_constraints_for_def(current_def, None, def_span);
        cs
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

    pub fn add_constraints_for_def(
        &mut self,
        def_id: crate::sema::resolve::models::DefinitionID,
        args: Option<GenericArguments<'ctx>>,
        location: Span,
    ) {
        let gcx = self.infer_cx.gcx;
        let constraints = canonical_constraints_of(gcx, def_id);
        for constraint in constraints {
            let constraint = match args {
                Some(args) => instantiate_constraint_with_args(gcx, constraint.value, args),
                None => constraint.value,
            };
            self.add_constraint(constraint, location);
        }
    }

    fn add_constraint(&mut self, constraint: Constraint<'ctx>, location: Span) {
        match constraint {
            Constraint::TypeEquality(lhs, rhs) => {
                self.add_goal(Goal::ConstraintEqual(lhs, rhs), location);
            }
            Constraint::Bound { ty, interface } => {
                self.add_goal(Goal::Conforms { ty, interface }, location);
            }
        }
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
                let resolved = normalize_ty(gcx, resolved);
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
                let resolved = normalize_ty(gcx, resolved);
                (id, resolved)
            })
            .collect()
    }

    pub fn resolved_adjustments(&self) -> FxHashMap<NodeID, Vec<Adjustment<'ctx>>> {
        self.adjustments.clone()
    }

    pub fn resolved_interface_calls(&self) -> FxHashMap<NodeID, InterfaceCallInfo> {
        self.interface_calls.clone()
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
            interface_calls: std::mem::take(&mut self.interface_calls),
            field_indices: std::mem::take(&mut self.field_indices),
            overload_sources: std::mem::take(&mut self.overload_sources),
            instantiation_args: std::mem::take(&mut self.instantiation_args),
            current_def: self.current_def,
        };

        let mut driver = SolverDriver::new(solver);
        let result = driver.solve_to_fixpoint();
        // Pull adjustments back out of the solver/driver.
        let (adjustments, interface_calls, field_indices, overload_sources, instantiation_args) =
            driver.into_parts();
        self.adjustments = adjustments;
        self.interface_calls = interface_calls;
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
    /// Emit user-friendly errors for unresolved type parameters.
    fn check_unresolved_vars(&self) {
        use crate::sema::models::{InferTy, TyKind};

        let gcx = self.infer_cx.gcx;
        for (var_id, origin) in self.infer_cx.all_type_var_origins() {
            let var_ty = Ty::new(TyKind::Infer(InferTy::TyVar(var_id)), gcx);
            let resolved = self.infer_cx.resolve_vars_if_possible(var_ty);
            if resolved.is_infer() {
                let msg = if let Some(name) = origin.param_name {
                    format!(
                        "generic parameter '{}' could not be inferred",
                        name.as_str()
                    )
                } else {
                    "type annotations needed: unable to infer type".into()
                };
                gcx.dcx().emit_error(msg.into(), Some(origin.location));
            }
        }
    }
}

struct ConstraintSolver<'ctx> {
    pub icx: Rc<InferCtx<'ctx>>,
    obligations: VecDeque<Obligation<'ctx>>,
    adjustments: FxHashMap<NodeID, Vec<Adjustment<'ctx>>>,
    interface_calls: FxHashMap<NodeID, InterfaceCallInfo>,
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

    pub fn record_interface_call(&mut self, node_id: NodeID, info: InterfaceCallInfo) {
        self.interface_calls.insert(node_id, info);
    }
}

impl<'ctx> ConstraintSolver<'ctx> {
    fn constraints_for_def(
        &self,
        def_id: crate::sema::resolve::models::DefinitionID,
        args: Option<GenericArguments<'ctx>>,
        location: Span,
    ) -> Vec<Obligation<'ctx>> {
        let gcx = self.gcx();
        let constraints = canonical_constraints_of(gcx, def_id);
        constraints
            .into_iter()
            .map(|constraint| {
                let constraint = match args {
                    Some(args) => instantiate_constraint_with_args(gcx, constraint.value, args),
                    None => constraint.value,
                };
                let goal = match constraint {
                    Constraint::TypeEquality(lhs, rhs) => Goal::ConstraintEqual(lhs, rhs),
                    Constraint::Bound { ty, interface } => Goal::Conforms { ty, interface },
                };
                Obligation { location, goal }
            })
            .collect()
    }

    fn constraints_in_scope(&self) -> Vec<Constraint<'ctx>> {
        canonical_constraints_of(self.gcx(), self.current_def)
            .into_iter()
            .map(|c| c.value)
            .collect()
    }

    fn equivalent_types_in_scope(&self, ty: Ty<'ctx>) -> FxHashSet<Ty<'ctx>> {
        let ty = self.structurally_resolve(ty);
        let constraints = self.constraints_in_scope();
        let mut edges = Vec::new();
        for constraint in constraints {
            if let Constraint::TypeEquality(a, b) = constraint {
                edges.push((a, b));
            }
        }

        let mut seen: FxHashSet<Ty<'ctx>> = FxHashSet::default();
        let mut stack = vec![ty];
        seen.insert(ty);

        while let Some(cur) = stack.pop() {
            for (a, b) in edges.iter() {
                if *a == cur && seen.insert(*b) {
                    stack.push(*b);
                } else if *b == cur && seen.insert(*a) {
                    stack.push(*a);
                }
            }
        }

        seen
    }

    fn in_scope_equal(&self, a: Ty<'ctx>, b: Ty<'ctx>) -> bool {
        let a = self.structurally_resolve(a);
        let b = self.structurally_resolve(b);
        if a == b {
            return true;
        }
        self.equivalent_types_in_scope(a).contains(&b)
    }

    fn bounds_for_type_in_scope(&self, ty: Ty<'ctx>) -> Vec<InterfaceReference<'ctx>> {
        let eq_set = self.equivalent_types_in_scope(ty);
        let mut out: FxHashSet<InterfaceReference<'ctx>> = FxHashSet::default();

        for constraint in self.constraints_in_scope() {
            if let Constraint::Bound { ty, interface } = constraint {
                if eq_set.contains(&ty) {
                    out.insert(interface);
                }
            }
        }

        out.into_iter().collect()
    }

    fn solve(&mut self, obligation: Obligation<'ctx>) -> SolverResult<'ctx> {
        let location = obligation.location;
        let goal = obligation.goal;
        match goal {
            Goal::Equal(lhs, rhs) => self.solve_equality(location, lhs, rhs),
            Goal::ConstraintEqual(lhs, rhs) => self.solve_constraint_equality(location, lhs, rhs),
            Goal::Conforms { ty, interface } => self.solve_conforms(location, ty, interface),
            Goal::Apply(data) => self.solve_apply(data),
            Goal::BindOverload(data) => self.solve_bind_overload(location, data),
            Goal::BindInterfaceMethod(data) => self.solve_bind_interface_method(location, data),
            Goal::Disjunction(branches) => self.solve_disjunction(location, branches),
            Goal::UnaryOp(data) => self.solve_unary(data),
            Goal::BinaryOp(data) => self.solve_binary(data),
            Goal::AssignOp(data) => self.solve_assign_op(data),
            Goal::Coerce { node_id, from, to } => self.solve_coerce(location, node_id, from, to),
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

    fn solve_constraint_equality(
        &mut self,
        location: Span,
        lhs: Ty<'ctx>,
        rhs: Ty<'ctx>,
    ) -> SolverResult<'ctx> {
        let lhs = self.structurally_resolve(lhs);
        let rhs = self.structurally_resolve(rhs);

        if matches!(lhs.kind(), TyKind::Parameter(_))
            || matches!(rhs.kind(), TyKind::Parameter(_))
        {
            return SolverResult::Solved(vec![]);
        }
        if contains_projection(lhs) || contains_projection(rhs) {
            return SolverResult::Solved(vec![]);
        }

        self.solve_equality(location, lhs, rhs)
    }

    fn fork(&self) -> ConstraintSolver<'ctx> {
        ConstraintSolver {
            icx: self.icx.clone(),
            obligations: self.obligations.clone(),
            adjustments: self.adjustments.clone(),
            interface_calls: self.interface_calls.clone(),
            field_indices: self.field_indices.clone(),
            overload_sources: self.overload_sources.clone(),
            instantiation_args: self.instantiation_args.clone(),
            current_def: self.current_def,
        }
    }
}

fn contains_projection<'ctx>(ty: Ty<'ctx>) -> bool {
    match ty.kind() {
        TyKind::Alias {
            kind: AliasKind::Projection,
            ..
        } => true,
        TyKind::Alias { args, .. } | TyKind::Adt(_, args) => args.iter().any(|arg| match arg {
            GenericArgument::Type(ty) => contains_projection(*ty),
            GenericArgument::Const(c) => contains_projection(c.ty),
        }),
        TyKind::Pointer(inner, _) | TyKind::Reference(inner, _) => contains_projection(inner),
        TyKind::Array { element, .. } => contains_projection(element),
        TyKind::Tuple(items) => items.iter().any(|ty| contains_projection(*ty)),
        TyKind::FnPointer { inputs, output } => {
            inputs.iter().any(|ty| contains_projection(*ty)) || contains_projection(output)
        }
        TyKind::BoxedExistential { interfaces } => interfaces.iter().any(|iface| {
            iface.arguments.iter().any(|arg| match arg {
                GenericArgument::Type(ty) => contains_projection(*ty),
                GenericArgument::Const(c) => contains_projection(c.ty),
            })
        }),
        _ => false,
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
        FxHashMap<NodeID, InterfaceCallInfo>,
        FxHashMap<NodeID, usize>,
        FxHashMap<NodeID, crate::sema::resolve::models::DefinitionID>,
        FxHashMap<NodeID, GenericArguments<'ctx>>,
    ) {
        (
            self.solver.adjustments,
            self.solver.interface_calls,
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
