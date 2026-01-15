use crate::{
    compile::context::Gcx,
    hir::{NodeID, Resolution},
    sema::{
        error::SpannedErrorList,
        models::{
            AliasKind, Constraint, GenericArgument, GenericArguments, InterfaceReference, Ty,
            TyKind,
        },
        resolve::models::DefinitionID,
        tycheck::{
            constraints::canonical_constraints_of,
            infer::InferCtx,
            utils::{
                ParamEnv, instantiate::instantiate_constraint_with_args,
                instantiate::instantiate_ty_with_args, normalize_ty,
            },
        },
    },
    span::{Span, Spanned},
};
pub use models::*;
use rustc_hash::{FxHashMap, FxHashSet};
use std::{cell::RefCell, cmp::Reverse, collections::VecDeque, rc::Rc};

mod adt;
mod apply;
mod cast;
mod coerce;
mod deref;
mod interface;
mod member;
mod method;
mod models;
mod op;
mod overload;
mod tuple;
mod unify;

/// Collect all traits (interfaces) that are visible in the scope of the given definition.
/// This includes:
/// - Interfaces defined in the current module and parent modules
/// - Interfaces explicitly imported via `import` statements
/// - Interfaces from glob imports (`import some.module.*`)
fn collect_visible_traits(gcx: Gcx, def_id: DefinitionID) -> FxHashSet<DefinitionID> {
    use crate::sema::resolve::models::{DefinitionKind, Resolution, ScopeEntryKind};

    let mut visible = FxHashSet::default();
    let pkg = def_id.package();
    let resolution_output = gcx.resolution_output(pkg);

    // Get the scope for this definition
    let mut current_scope = resolution_output
        .definition_scope_mapping
        .get(&def_id)
        .copied();

    // Walk up the scope chain
    while let Some(scope) = current_scope {
        let table = scope.table.borrow();

        // Collect interfaces from this scope
        for name_entry in table.values() {
            if let Some(type_entry) = &name_entry.ty {
                match &type_entry.kind {
                    ScopeEntryKind::Resolution(Resolution::Definition(id, kind)) => {
                        if *kind == DefinitionKind::Interface {
                            visible.insert(*id);
                        }
                    }
                    ScopeEntryKind::Usage { used_entry, .. } => {
                        // Follow the usage chain to the actual definition
                        if let ScopeEntryKind::Resolution(Resolution::Definition(id, kind)) =
                            &used_entry.kind
                        {
                            if *kind == DefinitionKind::Interface {
                                visible.insert(*id);
                            }
                        }
                    }
                    _ => {
                        // Other resolution types (PrimaryType, SelfTypeAlias, etc.) are not interfaces
                    }
                }
            }
        }

        // Also check glob imports
        let glob_imports = scope.glob_imports.borrow();
        for _usage in glob_imports.iter() {
            // For glob imports, we need to look at what they bring into scope
            // This is a simplified version - glob imports should already be resolved into the scope table
        }

        drop(table);
        drop(glob_imports);

        // Move to parent scope
        current_scope = scope.parent;
    }

    visible
}

pub struct ConstraintSystem<'ctx> {
    pub infer_cx: Rc<InferCtx<'ctx>>,
    obligations: VecDeque<Obligation<'ctx>>,
    expr_tys: FxHashMap<NodeID, Ty<'ctx>>,
    adjustments: FxHashMap<NodeID, Vec<Adjustment<'ctx>>>,
    interface_calls: FxHashMap<NodeID, InterfaceCallInfo>,
    pub locals: RefCell<FxHashMap<NodeID, Ty<'ctx>>>,
    pub field_indices: FxHashMap<NodeID, usize>,
    overload_sources: FxHashMap<NodeID, crate::sema::resolve::models::DefinitionID>,
    value_resolutions: FxHashMap<NodeID, Resolution>,
    instantiation_args: FxHashMap<NodeID, GenericArguments<'ctx>>,
    current_def: crate::sema::resolve::models::DefinitionID,
    env: ParamEnv<'ctx>,
    /// Traits (interfaces) visible in the current scope (for trait method lookup)
    visible_traits: FxHashSet<DefinitionID>,
    error_count_at_start: usize,
}

impl<'ctx> ConstraintSystem<'ctx> {
    pub fn new(
        context: Gcx<'ctx>,
        current_def: crate::sema::resolve::models::DefinitionID,
    ) -> ConstraintSystem<'ctx> {
        Self::with_infer_ctx(context, current_def, Rc::new(InferCtx::new(context)))
    }

    pub fn with_infer_ctx(
        context: Gcx<'ctx>,
        current_def: crate::sema::resolve::models::DefinitionID,
        infer_cx: Rc<InferCtx<'ctx>>,
    ) -> ConstraintSystem<'ctx> {
        let visible_traits = collect_visible_traits(context, current_def);
        let error_count_at_start = context.dcx().error_count();

        ConstraintSystem {
            infer_cx,
            obligations: Default::default(),
            expr_tys: Default::default(),
            locals: Default::default(),
            adjustments: Default::default(),
            interface_calls: Default::default(),
            field_indices: Default::default(),
            overload_sources: Default::default(),
            value_resolutions: Default::default(),
            instantiation_args: Default::default(),
            current_def,
            env: ParamEnv::new(
                canonical_constraints_of(context, current_def)
                    .into_iter()
                    .map(|c| c.value)
                    .collect(),
            ),
            visible_traits,
            error_count_at_start,
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

    pub fn record_adjustments(&mut self, node_id: NodeID, adjustments: Vec<Adjustment<'ctx>>) {
        if adjustments.is_empty() {
            return;
        }
        self.adjustments.insert(node_id, adjustments);
    }

    pub fn expr_ty(&self, id: NodeID) -> Option<Ty<'ctx>> {
        self.expr_tys.get(&id).copied()
    }

    pub fn resolved_expr_types(&self) -> FxHashMap<NodeID, Ty<'ctx>> {
        let gcx = self.infer_cx.gcx;
        self.expr_tys
            .iter()
            .map(|(&id, &ty)| {
                let resolved = self.structurally_resolve(ty);
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
                let resolved = self.structurally_resolve(ty);
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

    pub fn resolved_value_resolutions(&self) -> FxHashMap<NodeID, Resolution> {
        self.value_resolutions.clone()
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
                            let resolved = self.structurally_resolve(*ty);
                            GenericArgument::Type(resolved)
                        }
                        GenericArgument::Const(c) => {
                            GenericArgument::Const(self.infer_cx.resolve_const_if_possible(*c))
                        }
                    })
                    .collect();
                let interned = gcx.store.interners.intern_generic_args(resolved);
                (id, interned)
            })
            .collect()
    }

    fn structurally_resolve(&self, ty: Ty<'ctx>) -> Ty<'ctx> {
        let ty = self.infer_cx.resolve_vars_if_possible(ty);
        normalize_ty(self.infer_cx.clone(), ty, &self.env)
    }

    pub fn merge(&mut self, other: ConstraintSystem<'ctx>) {
        self.obligations.extend(other.obligations);
        self.expr_tys.extend(other.expr_tys);
        self.adjustments.extend(other.adjustments);
        self.interface_calls.extend(other.interface_calls);
        self.locals.borrow_mut().extend(other.locals.into_inner());
        self.field_indices.extend(other.field_indices);
        self.overload_sources.extend(other.overload_sources);
        self.value_resolutions.extend(other.value_resolutions);
        self.instantiation_args.extend(other.instantiation_args);
    }
}

impl<'ctx> ConstraintSystem<'ctx> {
    pub fn solve_all(&mut self) {
        self.solve_internal(true);
    }

    pub fn solve_intermediate(&mut self) {
        self.solve_internal(false);
    }

    fn solve_internal(&mut self, check_unresolved: bool) {
        let param_env = ParamEnv::new(
            canonical_constraints_of(self.infer_cx.gcx, self.current_def)
                .into_iter()
                .map(|c| c.value)
                .collect(),
        );

        let solver = ConstraintSolver {
            icx: self.infer_cx.clone(),
            obligations: std::mem::take(&mut self.obligations),
            adjustments: std::mem::take(&mut self.adjustments),
            interface_calls: std::mem::take(&mut self.interface_calls),
            field_indices: std::mem::take(&mut self.field_indices),
            overload_sources: std::mem::take(&mut self.overload_sources),
            value_resolutions: std::mem::take(&mut self.value_resolutions),
            instantiation_args: std::mem::take(&mut self.instantiation_args),
            current_def: self.current_def,
            param_env,
            visible_traits: self.visible_traits.clone(),
        };

        let mut driver = SolverDriver::new(solver);
        let result = driver.solve_to_fixpoint();
        // Pull adjustments back out of the solver/driver.
        let (
            adjustments,
            interface_calls,
            field_indices,
            overload_sources,
            value_resolutions,
            instantiation_args,
        ) = driver.into_parts();
        self.adjustments = adjustments;
        self.interface_calls = interface_calls;
        self.field_indices = field_indices;
        self.overload_sources = overload_sources;
        self.value_resolutions = value_resolutions;
        self.instantiation_args = instantiation_args;

        let gcx = self.infer_cx.gcx;

        if result.is_ok() {
            if check_unresolved && gcx.dcx().error_count() == self.error_count_at_start {
                self.check_unresolved_vars();
            }
            return;
        }

        let Err(errors) = result else { unreachable!() };

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
                panic!("Uninferred type parameter")
            }
        }

        for (var_id, origin) in self.infer_cx.all_const_var_origins() {
            if matches!(
                self.infer_cx.const_var_binding(var_id),
                crate::sema::tycheck::infer::keys::ConstVarValue::Unknown
            ) {
                let msg = if let Some(name) = origin.param_name {
                    format!("const parameter '{}' could not be inferred", name.as_str())
                } else {
                    "const value could not be inferred".into()
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
    value_resolutions: FxHashMap<NodeID, Resolution>,
    instantiation_args: FxHashMap<NodeID, GenericArguments<'ctx>>,
    current_def: crate::sema::resolve::models::DefinitionID,
    param_env: ParamEnv<'ctx>,
    visible_traits: FxHashSet<DefinitionID>,
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

    pub fn record_value_resolution(&mut self, node_id: NodeID, resolution: Resolution) {
        self.value_resolutions.insert(node_id, resolution);
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

    pub(crate) fn bounds_for_type_in_scope(&self, ty: Ty<'ctx>) -> Vec<InterfaceReference<'ctx>> {
        self.param_env.bounds_for(self.structurally_resolve(ty))
    }

    pub(crate) fn filter_extension_candidates(
        &self,
        candidates: Vec<crate::sema::resolve::models::DefinitionID>,
        receiver: Ty<'ctx>,
        span: Span,
    ) -> Vec<crate::sema::resolve::models::DefinitionID> {
        candidates
            .into_iter()
            .filter(|candidate| {
                let Some(parent) = self.gcx().definition_parent(*candidate) else {
                    return true;
                };

                if self.gcx().definition_kind(parent)
                    != crate::sema::resolve::models::DefinitionKind::Impl
                {
                    return true;
                }

                self.extension_target_matches(parent, receiver, span)
            })
            .collect()
    }

    pub(crate) fn extension_target_matches(
        &self,
        extension_id: crate::sema::resolve::models::DefinitionID,
        receiver: Ty<'ctx>,
        span: Span,
    ) -> bool {
        let Some(target_ty) = self.gcx().get_impl_target_ty(extension_id) else {
            return true;
        };

        if target_ty.is_error() || receiver.is_error() {
            return true;
        }

        self.icx.probe(|_| {
            let args = self.icx.fresh_args_for_def(extension_id, span);
            let instantiated = instantiate_ty_with_args(self.gcx(), target_ty, args);
            self.unify(receiver, instantiated).is_ok()
        })
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
            Goal::BindMethodOverload(data) => self.solve_bind_method_overload(location, data),
            Goal::Disjunction(branches) => self.solve_disjunction(location, branches),
            Goal::UnaryOp(data) => self.solve_unary(data),
            Goal::BinaryOp(data) => self.solve_binary(data),
            Goal::AssignOp(data) => self.solve_assign_op(data),
            Goal::Coerce { node_id, from, to } => self.solve_coerce(location, node_id, from, to),
            Goal::Cast {
                node_id,
                from,
                to,
                is_unsafe,
            } => self.solve_cast(location, node_id, from, to, is_unsafe),
            Goal::Member(data) => self.solve_member(data),
            Goal::InferredStaticMember(data) => self.solve_inferred_static_member(data),
            Goal::MethodCall(data) => self.solve_method_call(data),
            Goal::StructLiteral(data) => self.solve_struct_literal(data),
            Goal::TupleAccess(data) => self.solve_tuple_access(data),
            Goal::Deref(data) => self.solve_deref(data),
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
        // Resolve inference variables first
        let lhs = self.structurally_resolve(lhs);
        let rhs = self.structurally_resolve(rhs);

        // If either side has an unresolvable projection (projection on an inference var),
        // defer until the inference var is bound.
        if has_unresolvable_projection(&self.icx, lhs)
            || has_unresolvable_projection(&self.icx, rhs)
        {
            return SolverResult::Deferred;
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
            value_resolutions: self.value_resolutions.clone(),
            instantiation_args: self.instantiation_args.clone(),
            current_def: self.current_def,
            param_env: self.param_env.clone(),
            visible_traits: self.visible_traits.clone(),
        }
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
            // Higher score = better
            // Start with a base score of 100 for all candidates
            let mut score: i32 = 100;

            // Bonus for non-generic methods (prefer concrete over generic)
            if let Some(def_id) = branch.source {
                if gcx.generics_of(def_id).is_empty() {
                    score += 50;
                }
            }

            // Huge bonus for matching expectation (especially mutability)
            if branch.matches_expectation {
                score += 1000;
            }

            // Subtract autoref_cost: prefer None (0) over Immutable (1) over Mutable (2)
            // This ensures that when we have at(&self) and at(&mut self), and the receiver
            // is immutable, we prefer at(&self) which has lower autoref_cost.
            // Multiply by 10 to make it significant.
            let autoref_penalty = branch.autoref_cost as i32 * 10;
            score -= autoref_penalty;

            // Subtract deref_steps penalty: prefer fewer dereferences (closer to original type)
            // e.g. prefer impl on &T (0 derefs) over impl on T (1 deref) when calling on &T
            let deref_penalty = branch.deref_steps as i32 * 5;
            score -= deref_penalty;

            RankedBranch {
                branch,
                score: score.max(0) as u32,
            }
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
        FxHashMap<NodeID, Resolution>,
        FxHashMap<NodeID, GenericArguments<'ctx>>,
    ) {
        (
            self.solver.adjustments,
            self.solver.interface_calls,
            self.solver.field_indices,
            self.solver.overload_sources,
            self.solver.value_resolutions,
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

                // No progress after defaulting; let unresolved inference vars report errors.
                return Ok(());
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

/// Check if a type contains a projection whose self-type is an unresolved inference variable.
/// Such projections cannot be normalized and need to be deferred.
fn has_unresolvable_projection<'ctx>(icx: &InferCtx<'ctx>, ty: Ty<'ctx>) -> bool {
    match ty.kind() {
        TyKind::Alias {
            kind: AliasKind::Projection,
            args,
            ..
        } => {
            // Check if the Self type (first arg) is still an inference variable
            if let Some(GenericArgument::Type(self_ty)) = args.get(0) {
                let resolved = icx.resolve_vars_if_possible(*self_ty);
                if resolved.is_infer() {
                    return true;
                }
            }
            // Also check nested types in args
            args.iter().any(|arg| match arg {
                GenericArgument::Type(t) => has_unresolvable_projection(icx, *t),
                GenericArgument::Const(c) => has_unresolvable_projection(icx, c.ty),
            })
        }
        TyKind::Alias { args, .. } | TyKind::Adt(_, args) => args.iter().any(|arg| match arg {
            GenericArgument::Type(t) => has_unresolvable_projection(icx, *t),
            GenericArgument::Const(c) => has_unresolvable_projection(icx, c.ty),
        }),
        TyKind::Pointer(inner, _) | TyKind::Reference(inner, _) => {
            has_unresolvable_projection(icx, inner)
        }
        TyKind::Array { element, .. } => has_unresolvable_projection(icx, element),
        TyKind::Tuple(items) => items.iter().any(|t| has_unresolvable_projection(icx, *t)),
        TyKind::FnPointer { inputs, output } => {
            inputs.iter().any(|t| has_unresolvable_projection(icx, *t))
                || has_unresolvable_projection(icx, output)
        }
        TyKind::BoxedExistential { interfaces } => interfaces.iter().any(|iface| {
            iface.arguments.iter().any(|arg| match arg {
                GenericArgument::Type(t) => has_unresolvable_projection(icx, *t),
                GenericArgument::Const(c) => has_unresolvable_projection(icx, c.ty),
            })
        }),
        _ => false,
    }
}
