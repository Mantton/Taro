use crate::{
    compile::context::Gcx,
    hir::{NodeID, Resolution},
    sema::{
        error::SpannedErrorList,
        models::{
            AliasKind, ConstKind, Constraint, GenericArgument, GenericArguments,
            GenericParameterDefinition, GenericParameterDefinitionKind, InferTy,
            InterfaceReference, Ty, TyKind, TyVarID,
        },
        resolve::models::DefinitionID,
        tycheck::{
            constraints::canonical_constraints_of,
            infer::{InferCtx, NumericVar},
            lower::{DefTyLoweringCtx, TypeLowerer},
            utils::generics::GenericsBuilder,
            utils::{
                ParamEnv, instantiate::instantiate_const_with_args,
                instantiate::instantiate_constraint_with_args,
                instantiate::instantiate_ty_with_args, normalize_ty,
            },
        },
    },
    span::{Span, Spanned},
};
pub use models::*;
use rustc_hash::{FxHashMap, FxHashSet};
use std::{cell::RefCell, cmp::Reverse, collections::VecDeque, rc::Rc};

#[cfg(test)]
mod g30_tests;

mod adt;
mod apply;
mod cast;
mod coerce;
mod collection_span;
mod conformance_inference;
mod deref;
mod early_interface;
mod index;
mod interface;
mod member;
mod method;
mod method_value;
mod models;
mod op;
mod overload;
mod tuple;
mod unify;

#[derive(Clone)]
pub(super) struct PendingMemberValue<'ctx> {
    pub member: Rc<crate::hir::Expression>,
    pub selection: Ty<'ctx>,
    pub value: Ty<'ctx>,
}

pub(super) struct PendingEnumPattern<'ctx> {
    pub pattern: crate::hir::Pattern,
    pub scrutinee: Ty<'ctx>,
    pub autoderef: bool,
}

pub struct ConstraintSystem<'ctx> {
    pub infer_cx: Rc<InferCtx<'ctx>>,
    obligations: VecDeque<Obligation<'ctx>>,
    expr_tys: FxHashMap<NodeID, Ty<'ctx>>,
    integer_literals: FxHashMap<NodeID, i128>,
    adjustments: FxHashMap<NodeID, Vec<Adjustment<'ctx>>>,
    interface_calls: FxHashMap<NodeID, InterfaceCallInfo>,
    pub locals: RefCell<FxHashMap<NodeID, Ty<'ctx>>>,
    pub field_indices: FxHashMap<NodeID, usize>,
    pub property_reads: FxHashMap<NodeID, ResolvedPropertyRead>,
    overload_sources: FxHashMap<NodeID, crate::sema::resolve::models::DefinitionID>,
    /// Unwrapped call arguments selected for a `@lazy` parameter by overload resolution.
    lazy_argument_targets: FxHashMap<NodeID, Ty<'ctx>>,
    deferred_return_scopes: Vec<DeferredReturnScope<'ctx>>,
    result_propagation_conversions:
        FxHashMap<NodeID, crate::sema::tycheck::results::ResultPropagationConversion<'ctx>>,
    value_resolutions: FxHashMap<NodeID, Resolution>,
    instantiation_args: FxHashMap<NodeID, GenericArguments<'ctx>>,
    opening_calls: FxHashSet<NodeID>,
    current_def: crate::sema::resolve::models::DefinitionID,
    /// Canonical interface-selection view of bounds declared by the definition
    /// being checked. Unlike `env`, this is not extended with callee requirements.
    assumption_constraints: &'ctx [Constraint<'ctx>],
    env: ParamEnv<'ctx>,
    /// Traits (interfaces) visible in the current scope (for trait method lookup)
    visible_traits: Rc<FxHashSet<DefinitionID>>,
    error_count_at_start: usize,
    isolated_goals: bool,
    /// Closures whose capture types belong to this inference context.
    pub(super) capturing_closures: Vec<DefinitionID>,
    /// Member selections that may need a captured receiver once the lookup resolves.
    pub(super) pending_member_values: VecDeque<PendingMemberValue<'ctx>>,
    /// Shorthand constructors whose expected enum comes from an enclosing call.
    pub(super) pending_enum_patterns: Vec<PendingEnumPattern<'ctx>>,
    /// Receiver conformances that early-bound interface calls still prove.
    receiver_proofs: Vec<early_interface::ReceiverProof<'ctx>>,
}

struct SolverOutputs<'ctx> {
    obligations: VecDeque<Obligation<'ctx>>,
    adjustments: FxHashMap<NodeID, Vec<Adjustment<'ctx>>>,
    interface_calls: FxHashMap<NodeID, InterfaceCallInfo>,
    field_indices: FxHashMap<NodeID, usize>,
    property_reads: FxHashMap<NodeID, ResolvedPropertyRead>,
    overload_sources: FxHashMap<NodeID, crate::sema::resolve::models::DefinitionID>,
    lazy_argument_targets: FxHashMap<NodeID, Ty<'ctx>>,
    result_propagation_conversions:
        FxHashMap<NodeID, crate::sema::tycheck::results::ResultPropagationConversion<'ctx>>,
    value_resolutions: FxHashMap<NodeID, Resolution>,
    instantiation_args: FxHashMap<NodeID, GenericArguments<'ctx>>,
    receiver_proofs: Vec<early_interface::ReceiverProof<'ctx>>,
}

impl<'ctx> ConstraintSystem<'ctx> {
    pub fn new(
        context: Gcx<'ctx>,
        current_def: crate::sema::resolve::models::DefinitionID,
    ) -> ConstraintSystem<'ctx> {
        Self::with_infer_ctx(
            context,
            current_def,
            Rc::new(InferCtx::new(context)),
            context.visible_traits(current_def),
        )
    }

    pub fn with_infer_ctx(
        context: Gcx<'ctx>,
        current_def: crate::sema::resolve::models::DefinitionID,
        infer_cx: Rc<InferCtx<'ctx>>,
        visible_traits: Rc<FxHashSet<DefinitionID>>,
    ) -> ConstraintSystem<'ctx> {
        let error_count_at_start = context.dcx().error_count();

        let assumptions = Self::build_param_env(context, current_def);
        let assumption_constraints = context
            .store
            .arenas
            .global
            .alloc_slice_copy(&assumptions.constraints());
        ConstraintSystem {
            infer_cx,
            obligations: Default::default(),
            expr_tys: Default::default(),
            integer_literals: Default::default(),
            locals: Default::default(),
            adjustments: Default::default(),
            interface_calls: Default::default(),
            field_indices: Default::default(),
            property_reads: Default::default(),
            overload_sources: Default::default(),
            lazy_argument_targets: Default::default(),
            deferred_return_scopes: Default::default(),
            result_propagation_conversions: Default::default(),
            value_resolutions: Default::default(),
            instantiation_args: Default::default(),
            opening_calls: Default::default(),
            current_def,
            assumption_constraints,
            env: assumptions,
            visible_traits,
            error_count_at_start,
            isolated_goals: false,
            capturing_closures: vec![],
            pending_member_values: VecDeque::new(),
            pending_enum_patterns: Vec::new(),
            receiver_proofs: Vec::new(),
        }
    }

    /// Build the parameter environment for typechecking a definition.
    ///
    /// For methods inside interfaces, also includes constraints from sibling
    /// associated types. This ensures type equalities arising from associated
    /// type bindings (e.g., `type Iterator: Iterator[Element = Self.Element]`
    /// producing `TypeEquality(Self.Iterator.Element, Self.Element)`) are
    /// visible when typechecking default method bodies.
    fn build_param_env(
        context: Gcx<'ctx>,
        current_def: crate::sema::resolve::models::DefinitionID,
    ) -> ParamEnv<'ctx> {
        let mut constraints: Vec<_> = canonical_constraints_of(context, current_def)
            .into_iter()
            .map(|c| c.value)
            .collect();

        // Include sibling associated type constraints for interface methods.
        use crate::sema::resolve::models::DefinitionKind;
        if let Some(parent) = context.definition_parent(current_def) {
            if context.definition_kind(current_def) == DefinitionKind::AssociatedFunction
                && context.definition_kind(parent) == DefinitionKind::Interface
            {
                if let Some(assoc_types) = context.with_type_database(parent.package(), |db| {
                    db.def_to_iface_def
                        .get(&parent)
                        .map(|def| def.assoc_types.clone())
                }) {
                    for (_, assoc_id) in &assoc_types {
                        for c in context.constraints_of(*assoc_id) {
                            constraints.push(c.value);
                        }
                    }
                }
            }
        }

        ParamEnv::new(constraints)
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
        self.add_constraints_for_def_with_call(def_id, args, location, None, false);
    }

    /// The existential's hidden Self is checked when a concrete value is
    /// boxed, not as an unrelated generic parameter of its enclosing function.
    pub fn add_constraints_for_existential(
        &mut self,
        interface: InterfaceReference<'ctx>,
        location: Span,
    ) {
        self.add_constraints_for_def_with_call(
            interface.id,
            Some(interface.arguments),
            location,
            None,
            true,
        );
    }

    pub fn add_constraints_for_def_at_call(
        &mut self,
        def_id: crate::sema::resolve::models::DefinitionID,
        args: Option<GenericArguments<'ctx>>,
        location: Span,
        call_node_id: NodeID,
    ) {
        self.add_constraints_for_def_with_call(def_id, args, location, Some(call_node_id), false);
    }

    fn add_constraints_for_def_with_call(
        &mut self,
        def_id: crate::sema::resolve::models::DefinitionID,
        args: Option<GenericArguments<'ctx>>,
        location: Span,
        call_node_id: Option<NodeID>,
        abstract_self: bool,
    ) {
        let gcx = self.infer_cx.gcx;
        let constraints = canonical_constraints_of(gcx, def_id);
        for constraint in constraints {
            let opening_template = match constraint.value {
                Constraint::Bound { interface, .. } => Some(interface),
                _ => None,
            };
            let constraint = match args {
                Some(args) => instantiate_constraint_with_args(gcx, constraint.value, args),
                None => constraint.value,
            };
            let constraint = self.infer_cx.resolve_vars_if_possible(constraint);
            if let Constraint::Bound { ty, interface } = constraint {
                self.env.add_pending_bound(ty, interface);
            }
            if abstract_self {
                // Defaults may still be inference variables. Keep the witness
                // context until they resolve instead of emitting an ordinary
                // conformance goal that forgets its existential binder.
                self.add_goal(Goal::ExistentialConstraint(constraint), location);
                continue;
            }
            let goal = match constraint {
                Constraint::TypeEquality(lhs, rhs) => Goal::ConstraintEqual(lhs, rhs),
                Constraint::Bound { ty, interface } => {
                    if let Some(arguments) = args
                        && call_node_id.is_some_and(|node| self.opening_calls.contains(&node))
                    {
                        Goal::OpenedConforms {
                            source: def_id,
                            arguments,
                            template: opening_template.unwrap(),
                            ty,
                            interface,
                        }
                    } else {
                        Goal::Conforms { ty, interface }
                    }
                }
            };
            self.add_goal(goal, location);
        }
    }

    pub fn record_expr_ty(&mut self, id: NodeID, ty: Ty<'ctx>) {
        self.expr_tys.insert(id, ty);
    }

    pub fn allow_inferred_opening(&mut self, callee: NodeID) {
        self.opening_calls.insert(callee);
    }

    pub fn record_integer_literal(&mut self, id: NodeID, value: i128) {
        self.integer_literals.insert(id, value);
    }

    pub fn record_adjustments(&mut self, node_id: NodeID, adjustments: Vec<Adjustment<'ctx>>) {
        if adjustments.is_empty() {
            return;
        }
        if let Some(existing) = self.adjustments.get_mut(&node_id) {
            let mut combined = adjustments;
            combined.extend(std::mem::take(existing));
            *existing = combined;
        } else {
            self.adjustments.insert(node_id, adjustments);
        }
    }

    pub(crate) fn receiver_adjustments(&self, node: NodeID) -> Option<Vec<Adjustment<'ctx>>> {
        self.adjustments.get(&node).cloned()
    }

    /// A method-value selection probe must not publish its receiver autoref
    /// into the subsequent direct call's separate receiver adjustment pass.
    pub(crate) fn restore_receiver_adjustments(
        &mut self,
        node: NodeID,
        previous: Option<Vec<Adjustment<'ctx>>>,
    ) {
        match previous {
            Some(previous) => {
                self.adjustments.insert(node, previous);
            }
            None => {
                self.adjustments.remove(&node);
            }
        }
    }

    /// Append a receiver borrow after the member solver's autodereferences.
    pub fn append_adjustments(&mut self, node_id: NodeID, adjustments: Vec<Adjustment<'ctx>>) {
        self.adjustments
            .entry(node_id)
            .or_default()
            .extend(adjustments);
    }

    pub fn expr_ty(&self, id: NodeID) -> Option<Ty<'ctx>> {
        self.expr_tys.get(&id).cloned()
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

    pub fn node_adjustments(&self, node: NodeID) -> &[Adjustment<'ctx>] {
        self.adjustments
            .get(&node)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    pub fn resolved_adjustments(&self) -> FxHashMap<NodeID, Vec<Adjustment<'ctx>>> {
        self.adjustments.clone()
    }

    pub fn resolved_interface_calls(&self) -> FxHashMap<NodeID, InterfaceCallInfo> {
        self.interface_calls.clone()
    }

    pub(super) fn bound_method_source(&self, id: NodeID) -> Option<DefinitionID> {
        if self.field_indices.contains_key(&id) || self.property_reads.contains_key(&id) {
            return None;
        }
        self.overload_sources.get(&id).copied()
    }

    pub fn resolved_field_indices(&self) -> FxHashMap<NodeID, usize> {
        self.field_indices.clone()
    }

    pub fn resolved_property_reads(&self) -> FxHashMap<NodeID, ResolvedPropertyRead> {
        self.property_reads.clone()
    }

    pub fn opaque_return_sites(&self) -> impl Iterator<Item = &DeferredReturnSite<'ctx>> {
        self.deferred_return_scopes
            .iter()
            .filter(|scope| {
                scope.return_var.is_some_and(|ty| {
                    crate::sema::tycheck::opaque::is_owner_return(
                        self.infer_cx.resolve_vars_if_possible(ty),
                        self.current_def,
                    )
                })
            })
            .flat_map(|scope| &scope.returns)
    }

    pub fn register_deferred_return_scope(&mut self, scope: DeferredReturnScope<'ctx>) -> u32 {
        let index = self.deferred_return_scopes.len() as u32;
        self.deferred_return_scopes.push(scope);
        index
    }

    pub fn resolved_result_propagation_conversions(
        &self,
    ) -> FxHashMap<NodeID, crate::sema::tycheck::results::ResultPropagationConversion<'ctx>> {
        self.result_propagation_conversions.clone()
    }

    pub fn take_lazy_argument_targets(&mut self) -> Vec<(NodeID, Ty<'ctx>)> {
        let mut targets: Vec<_> = self.lazy_argument_targets.drain().collect();
        targets.sort_by_key(|(id, _)| *id);
        targets
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

    pub fn instantiation(&self, node_id: NodeID) -> Option<GenericArguments<'ctx>> {
        self.instantiation_args.get(&node_id).copied()
    }

    pub(crate) fn assumptions(&self) -> &'ctx [Constraint<'ctx>] {
        self.assumption_constraints
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

    pub(crate) fn structurally_resolve(&self, ty: Ty<'ctx>) -> Ty<'ctx> {
        let ty = self.infer_cx.resolve_vars_if_possible(ty);
        normalize_ty(self.infer_cx.clone(), ty, &self.env)
    }
}

impl<'ctx> ConstraintSystem<'ctx> {
    pub fn solve_all(&mut self) {
        self.solve_internal(true, None);
    }

    /// Keep an unfinished call's overload binding out of argument elaboration,
    /// while preserving constraints from earlier declarations and complete calls.
    pub fn with_deferred_callee<R>(
        &mut self,
        callee: NodeID,
        action: impl FnOnce(&mut Self) -> R,
    ) -> R {
        fn binds(goal: &Goal<'_>, node: NodeID) -> bool {
            match goal {
                Goal::BindOverload(data) => data.node_id == node,
                Goal::BindInterfaceMethod(data) => data.node_id == node,
                Goal::BindMethodOverload(data) => binds(&data.binding, node),
                Goal::Member(data) => data.node_id == node,
                Goal::BindMethodValue(data) => data.node_id == node,
                Goal::MethodValueSignature(data) => data.node_id == node,
                Goal::InferredStaticMember(data) => data.node_id == node,
                Goal::Disjunction(branches) => {
                    branches.iter().any(|branch| binds(&branch.goal, node))
                }
                _ => false,
            }
        }
        let mut deferred = VecDeque::new();
        let pending = std::mem::take(&mut self.obligations);
        for obligation in pending {
            if binds(&obligation.goal, callee) {
                deferred.push_back(obligation);
            } else {
                self.obligations.push_back(obligation);
            }
        }
        let result = action(self);
        deferred.append(&mut self.obligations);
        self.obligations = deferred;
        result
    }

    /// Member elaboration may resolve earlier local declarations, but must not
    /// choose global numeric/generic defaults before the whole context is known.
    pub fn without_fallbacks<R>(&mut self, action: impl FnOnce(&mut Self) -> R) -> R {
        let was_isolated = self.isolated_goals;
        self.isolated_goals = true;
        let result = action(self);
        self.isolated_goals = was_isolated;
        result
    }

    pub(super) fn defer_member_value(
        &mut self,
        expression: &crate::hir::Expression,
        selection: Ty<'ctx>,
    ) -> Ty<'ctx> {
        let value = self.infer_cx.next_ty_var(expression.span);
        self.pending_member_values.push_back(PendingMemberValue {
            member: Rc::new(expression.clone()),
            selection,
            value,
        });
        value
    }

    pub(super) fn finish_member_value(&mut self, actual: Ty<'ctx>) {
        let pending = self.pending_member_values.pop_front().expect("pending member");
        // Publish the value before retrying consumers. A waiting coercion can
        // now box the closure or wrap it in Optional with the right layout.
        self.obligations.push_front(Obligation {
            location: pending.member.span,
            goal: Goal::Equal(pending.value, actual),
        });
    }

    pub(super) fn pending_member(&mut self, id: NodeID) -> Option<&mut MemberGoalData<'ctx>> {
        self.obligations.iter_mut().find_map(|obligation| match &mut obligation.goal {
            Goal::Member(data) if data.node_id == id => Some(data),
            _ => None,
        })
    }

    /// Unknown integer and float literal variables in `ty`, by root.
    pub fn numeric_vars_in(&self, ty: Ty<'ctx>) -> Vec<NumericVar> {
        numeric_vars_in(&self.infer_cx, ty)
    }

    pub fn solve_intermediate(&mut self) {
        self.solve_internal(false, None);
    }

    /// Default only the literals needed by the operand's producers. Siblings
    /// can still take their type from the enclosing expression.
    fn solve_intermediate_defaulting_only(&mut self, scope: Vec<Ty<'ctx>>) {
        self.solve_internal(false, Some(scope.into()));
    }

    /// Resolve the pending operations that produce a type. For example,
    /// matching a local initialized by a pending method call can require
    /// defaulting the receiver of that call. Walk backwards from the local
    /// through its producers; siblings of the match have no constraints yet.
    pub fn solve_producers(&mut self, ty: Ty<'ctx>) -> Ty<'ctx> {
        self.without_fallbacks(|cs| cs.solve_intermediate());
        let resolved = self.structurally_resolve(ty);
        if !resolved.has_inference_variables() {
            return resolved;
        }
        let roots_in = |ty| {
            crate::sema::tycheck::utils::unresolved::inference_variables(
                self.infer_cx.resolve_vars_if_possible(ty),
            )
            .into_iter()
            .filter_map(|ty| match ty.kind() {
                TyKind::Infer(InferTy::TyVar(id)) => Some(self.infer_cx.ty_var_root(id)),
                _ => None,
            })
        };
        let mut pending: Vec<_> = roots_in(resolved).collect();
        if pending.is_empty() {
            // Optional[{integer}] already has the shape needed by its
            // patterns. Leave its payload open for the surrounding expression.
            return resolved;
        }

        let mut producers: FxHashMap<TyVarID, Vec<Ty<'ctx>>> = FxHashMap::default();
        for obligation in &self.obligations {
            let mut record = |result, input| {
                for root in roots_in(result) {
                    producers.entry(root).or_default().push(input);
                }
            };
            let goal = &obligation.goal;
            if let Some((receiver, arguments)) = receiver_lookup(goal) {
                let result = lookup_result(goal).expect("receiver lookup has a result");
                record(result, receiver);
                if let Some((_, arguments)) = arguments {
                    for arg in arguments {
                        record(result, arg.ty);
                    }
                }
                continue;
            }
            match goal {
                Goal::BinaryOp(data) => {
                    record(data.rho, data.lhs);
                    record(data.rho, data.rhs);
                }
                Goal::UnaryOp(data) => record(data.rho, data.lhs),
                Goal::Apply(data) => {
                    record(data.result_ty, data.callee_ty);
                    for arg in &data.arguments {
                        record(data.result_ty, arg.ty);
                    }
                }
                // A local initialization may be waiting on a projection
                // from a qualified interface method, as in a lowered for loop.
                Goal::Coerce { from, to, .. } => record(*to, *from),
                Goal::ConstraintEqual(a, b) => {
                    record(*a, *b);
                    record(*b, *a);
                }
                Goal::Deref(data) => record(data.result_ty, data.operand_ty),
                Goal::TupleAccess(data) => record(data.result, data.receiver),
                _ => {}
            }
        }
        let mut scope = FxHashSet::default();
        while let Some(root) = pending.pop() {
            if let Some(inputs) = producers.remove(&root) {
                for input in inputs {
                    if scope.insert(input) {
                        pending.extend(roots_in(input));
                    }
                }
            }
        }
        self.solve_intermediate_defaulting_only(scope.into_iter().collect());
        self.structurally_resolve(ty)
    }

    /// Obtain the outer type required by an operation such as Optional
    /// propagation. An associated type can depend on the width of its
    /// receiver even after the call that produced it has been solved.
    pub fn solve_for_structure(&mut self, ty: Ty<'ctx>) -> Ty<'ctx> {
        let ty = self.solve_producers(ty);
        self.resolve_projection_head(ty)
    }

    /// Inspect the outer projection only. For a tuple or enum, a subpattern
    /// may need a projection while an independent payload stays open.
    pub fn resolve_projection_head(&mut self, ty: Ty<'ctx>) -> Ty<'ctx> {
        let is_projection = |ty: Ty<'ctx>| matches!(
            ty.kind(),
            TyKind::Alias { kind: AliasKind::Projection, .. }
        );
        if !is_projection(ty) {
            return ty;
        }
        let ty = self.structurally_resolve(ty);
        if is_projection(ty) && !self.numeric_vars_in(ty).is_empty() {
            self.solve_intermediate_defaulting_only(vec![ty]);
            return self.structurally_resolve(ty);
        }
        ty
    }

    /// Render an already rejected operand with its ordinary numeric defaults
    /// (`5 ?? 1` reports int32) without binding a sibling use during recovery.
    pub fn format_rejected_operand(&self, ty: Ty<'ctx>) -> String {
        self.infer_cx.probe(|_| {
            for var in self.numeric_vars_in(ty) {
                self.infer_cx.default_numeric_var(var);
            }
            self.infer_cx
                .resolve_vars_if_possible(ty)
                .format(self.infer_cx.gcx)
        })
    }

    fn solve_internal(&mut self, check_unresolved: bool, default_scope: Option<Rc<[Ty<'ctx>]>>) {
        let gcx = self.infer_cx.gcx;

        let solver = ConstraintSolver {
            icx: self.infer_cx.clone(),
            coercions: 0,
            boxings: 0,
            obligations: std::mem::take(&mut self.obligations),
            adjustments: std::mem::take(&mut self.adjustments),
            interface_calls: std::mem::take(&mut self.interface_calls),
            integer_literals: self.integer_literals.clone(),
            field_indices: std::mem::take(&mut self.field_indices),
            property_reads: std::mem::take(&mut self.property_reads),
            overload_sources: std::mem::take(&mut self.overload_sources),
            lazy_argument_targets: std::mem::take(&mut self.lazy_argument_targets),
            deferred_return_scopes: Rc::new(self.deferred_return_scopes.clone()),
            result_propagation_conversions: std::mem::take(
                &mut self.result_propagation_conversions,
            ),
            value_resolutions: std::mem::take(&mut self.value_resolutions),
            instantiation_args: std::mem::take(&mut self.instantiation_args),
            opening_calls: self.opening_calls.clone(),
            current_def: self.current_def,
            assumption_constraints: self.assumption_constraints,
            param_env: self.env.clone(),
            visible_traits: self.visible_traits.clone(),
            held_literals: FxHashMap::default(),
            deferred: VecDeque::new(),
            pending_member_values: self.pending_member_values.iter().map(|p| p.value).collect(),
            lookups_have_waiters: false,
            receiver_proofs: std::mem::take(&mut self.receiver_proofs),
            default_scope,
        };

        let mut driver = SolverDriver::new(solver);
        driver.default_collection_literals = check_unresolved;
        driver.allow_fallbacks = !self.isolated_goals;
        let mut result = driver.solve_to_fixpoint();
        if check_unresolved && result.is_ok() {
            let errors = driver.check_receiver_proofs();
            if !errors.is_empty() {
                result = Err(errors);
            }
        }

        // Pull collected outputs back out of the solver/driver.
        let outputs = driver.into_parts();
        if result.is_ok() && !check_unresolved {
            // Intermediate solving is allowed to stop with inference-dependent
            // obligations. Preserve them so a later pass can retry after new
            // constraints bind their variables instead of silently accepting
            // an unproven conformance or projection.
            self.obligations = outputs.obligations;
        }
        self.adjustments = outputs.adjustments;
        self.interface_calls = outputs.interface_calls;
        self.field_indices = outputs.field_indices;
        self.property_reads = outputs.property_reads;
        self.overload_sources = outputs.overload_sources;
        self.lazy_argument_targets = outputs.lazy_argument_targets;
        self.result_propagation_conversions = outputs.result_propagation_conversions;
        self.value_resolutions = outputs.value_resolutions;
        self.instantiation_args = outputs.instantiation_args;
        self.receiver_proofs = outputs.receiver_proofs;

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
    ///
    /// A single unresolved generic parameter typically taints several vars
    /// along the expression path (the call's return-type var, the outer
    /// expression var, the enclosing local's var, ...). We dedup by
    /// unification root and prefer the origin carrying a generic-parameter
    /// name, so the user sees one pointed error instead of a cascade of
    /// "type annotations needed" messages at overlapping spans.
    fn check_unresolved_vars(&self) {
        use crate::sema::models::{InferTy, TyKind, TyVarID};
        use crate::sema::tycheck::infer::keys::TypeVariableOrigin;

        let gcx = self.infer_cx.gcx;

        let mut by_root: FxHashMap<TyVarID, TypeVariableOrigin> = FxHashMap::default();
        for (var_id, origin) in self.infer_cx.all_type_var_origins() {
            let var_ty = Ty::new(TyKind::Infer(InferTy::TyVar(var_id)), gcx);
            let resolved = self.infer_cx.resolve_vars_if_possible(var_ty);
            if !resolved.is_infer() {
                continue;
            }
            let root = self.infer_cx.ty_var_root(var_id);
            by_root
                .entry(root)
                .and_modify(|existing| {
                    if existing.param_name.is_none() && origin.param_name.is_some() {
                        *existing = origin;
                    }
                })
                .or_insert(origin);
        }

        let mut ordered: Vec<_> = by_root.into_values().collect();
        ordered.sort_by_key(|o| {
            (
                o.location.start.line,
                o.location.start.offset,
                o.location.end.line,
                o.location.end.offset,
            )
        });
        for origin in ordered {
            let msg = if let Some(name) = origin.param_name {
                format!(
                    "generic parameter '{}' could not be inferred",
                    gcx.symbol_text(name)
                )
            } else {
                "type annotations needed: unable to infer type".into()
            };
            gcx.dcx().emit_error(msg.into(), Some(origin.location));
        }

        use crate::sema::models::ConstVarID;
        use crate::sema::tycheck::infer::keys::ConstVariableOrigin;
        let mut const_by_root: FxHashMap<ConstVarID, ConstVariableOrigin> = FxHashMap::default();
        for (var_id, origin) in self.infer_cx.all_const_var_origins() {
            if !matches!(
                self.infer_cx.const_var_binding(var_id),
                crate::sema::tycheck::infer::keys::ConstVarValue::Unknown
            ) {
                continue;
            }
            let root = self.infer_cx.const_var_root(var_id);
            const_by_root
                .entry(root)
                .and_modify(|existing| {
                    if existing.param_name.is_none() && origin.param_name.is_some() {
                        *existing = origin;
                    }
                })
                .or_insert(origin);
        }

        let mut const_ordered: Vec<_> = const_by_root.into_values().collect();
        const_ordered.sort_by_key(|o| {
            (
                o.location.start.line,
                o.location.start.offset,
                o.location.end.line,
                o.location.end.offset,
            )
        });
        for origin in const_ordered {
            let msg = if let Some(name) = origin.param_name {
                format!(
                    "const parameter '{}' could not be inferred",
                    gcx.symbol_text(name)
                )
            } else {
                "const value could not be inferred".into()
            };
            gcx.dcx().emit_error(msg.into(), Some(origin.location));
        }
    }
}

struct ConstraintSolver<'ctx> {
    pub icx: Rc<InferCtx<'ctx>>,
    /// Tie-break equally ranked overloads by the number of argument conversions.
    coercions: u32,
    /// How many of those conversions boxed a concrete value into an
    /// existential. Among overloads that need as many conversions, the one
    /// that erases fewer argument types wins. See `solve_disjunction`.
    boxings: u32,
    obligations: VecDeque<Obligation<'ctx>>,
    adjustments: FxHashMap<NodeID, Vec<Adjustment<'ctx>>>,
    interface_calls: FxHashMap<NodeID, InterfaceCallInfo>,
    integer_literals: FxHashMap<NodeID, i128>,
    pub field_indices: FxHashMap<NodeID, usize>,
    pub property_reads: FxHashMap<NodeID, ResolvedPropertyRead>,
    overload_sources: FxHashMap<NodeID, crate::sema::resolve::models::DefinitionID>,
    lazy_argument_targets: FxHashMap<NodeID, Ty<'ctx>>,
    deferred_return_scopes: Rc<Vec<DeferredReturnScope<'ctx>>>,
    result_propagation_conversions:
        FxHashMap<NodeID, crate::sema::tycheck::results::ResultPropagationConversion<'ctx>>,
    value_resolutions: FxHashMap<NodeID, Resolution>,
    instantiation_args: FxHashMap<NodeID, GenericArguments<'ctx>>,
    opening_calls: FxHashSet<NodeID>,
    current_def: crate::sema::resolve::models::DefinitionID,
    assumption_constraints: &'ctx [Constraint<'ctx>],
    param_env: ParamEnv<'ctx>,
    visible_traits: Rc<FxHashSet<DefinitionID>>,
    /// The input literals of goals that were still waiting when numeric
    /// defaults were chosen, keyed by the goal's node. See
    /// `SolverDriver::hold_literals`.
    held_literals: FxHashMap<NodeID, Vec<NumericVar>>,
    /// Waiting obligations stay visible to nested overload probes. In
    /// particular, probing the consumer of a lookup needs its producer.
    deferred: VecDeque<Obligation<'ctx>>,
    /// Values produced by the checker once a pending receiver capture is known.
    pending_member_values: Vec<Ty<'ctx>>,
    /// Some coercion has waited for a lookup here or in the solver this one
    /// probes for. See `SolverDriver::take_coercions_awaiting`.
    lookups_have_waiters: bool,
    /// Receiver conformances that early-bound interface calls still prove.
    /// See `early_interface`.
    receiver_proofs: Vec<early_interface::ReceiverProof<'ctx>>,
    /// The types whose unknown literals this solve may default, or `None`
    /// when it may default any. See
    /// `ConstraintSystem::solve_intermediate_defaulting_only`.
    default_scope: Option<Rc<[Ty<'ctx>]>>,
}

impl<'ctx> ConstraintSolver<'ctx> {
    pub fn gcx(&self) -> Gcx<'ctx> {
        self.icx.gcx
    }

    pub fn record_field_index(&mut self, id: NodeID, index: usize) {
        self.field_indices.insert(id, index);
    }

    pub fn record_property_read(&mut self, id: NodeID, info: ResolvedPropertyRead) {
        self.property_reads.insert(id, info);
    }

    pub fn record_overload_source(
        &mut self,
        node_id: NodeID,
        source: crate::sema::resolve::models::DefinitionID,
    ) {
        self.overload_sources.insert(node_id, source);
    }

    pub fn record_lazy_argument_target(&mut self, node_id: NodeID, param_ty: Ty<'ctx>) {
        self.lazy_argument_targets.insert(node_id, param_ty);
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

    pub fn integer_literal_value(&self, id: NodeID) -> Option<i128> {
        self.integer_literals.get(&id).copied()
    }
}

impl<'ctx> ConstraintSolver<'ctx> {
    fn constraints_for_def(
        &mut self,
        def_id: crate::sema::resolve::models::DefinitionID,
        args: Option<GenericArguments<'ctx>>,
        location: Span,
    ) -> Vec<Obligation<'ctx>> {
        self.constraints_for_def_at_call(def_id, args, location, None)
    }

    fn constraints_for_def_at_call(
        &mut self,
        def_id: crate::sema::resolve::models::DefinitionID,
        args: Option<GenericArguments<'ctx>>,
        location: Span,
        call_node_id: Option<NodeID>,
    ) -> Vec<Obligation<'ctx>> {
        let gcx = self.gcx();
        let constraints = canonical_constraints_of(gcx, def_id);
        constraints
            .into_iter()
            .map(|constraint| {
                let opening_template = match constraint.value {
                    Constraint::Bound { interface, .. } => Some(interface),
                    _ => None,
                };
                let constraint = match args {
                    Some(args) => instantiate_constraint_with_args(gcx, constraint.value, args),
                    None => constraint.value,
                };
                // Argument unification happens before call-site obligations are
                // materialized. Resolve those bindings now so the ParamEnv and
                // its associated-type equalities refer to the caller's actual
                // types rather than stale inference variables.
                let constraint = self.icx.resolve_vars_if_possible(constraint);
                if let Constraint::Bound { ty, interface } = constraint {
                    self.param_env.add_pending_bound(ty, interface);
                }
                let goal = match constraint {
                    Constraint::TypeEquality(lhs, rhs) => Goal::ConstraintEqual(lhs, rhs),
                    Constraint::Bound { ty, interface } => {
                        if let Some(arguments) = args
                            && call_node_id.is_some_and(|node| self.opening_calls.contains(&node))
                        {
                            Goal::OpenedConforms {
                                source: def_id,
                                arguments,
                                template: opening_template.unwrap(),
                                ty,
                                interface,
                            }
                        } else {
                            Goal::Conforms { ty, interface }
                        }
                    }
                };
                Obligation { location, goal }
            })
            .collect()
    }

    /// A call introduces requirements to prove. Only the caller's declared
    /// bounds supply members, including when an argument reads a member of
    /// the same interface as the callee.
    fn bounds_for_member_lookup(&self, ty: Ty<'ctx>) -> Vec<InterfaceReference<'ctx>> {
        let declared = ParamEnv::new(self.assumption_constraints.to_vec());
        self.bounds_for_type(ty, &declared)
    }

    fn bounds_for_type(&self, ty: Ty<'ctx>, env: &ParamEnv<'ctx>) -> Vec<InterfaceReference<'ctx>> {
        let ty = self.structurally_resolve(ty);
        env.bounds_for_type(self.gcx(), ty, |bound_ty| {
            let bound_ty = self.structurally_resolve(bound_ty);
            bound_ty == ty || self.icx.probe(|_| self.unify(bound_ty, ty).is_ok())
        })
    }

    /// Probe a single implementation header without letting it choose a width for
    /// a literal in the original receiver (which may be a derived class).
    fn match_extension_header(
        &self,
        extension: DefinitionID,
        owner: Ty<'ctx>,
        receiver: Ty<'ctx>,
        span: Span,
    ) -> ExtensionHeaderMatch {
        let Some(target) = self.gcx().get_impl_target_ty(extension) else {
            return ExtensionHeaderMatch::Mismatch;
        };
        let before = if receiver.contains_inference() {
            numeric_vars_in(&self.icx, receiver)
        } else {
            Vec::new()
        };
        self.icx.probe(|_| {
            let args = self.icx.fresh_args_for_def(extension, span);
            let target = instantiate_ty_with_args(self.gcx(), target, args);
            if self.unify(owner, target).is_err() {
                return ExtensionHeaderMatch::Mismatch;
            }
            // A same-type clause can spell the same specialization as a
            // concrete argument in the header. Leave unresolved projections
            // to the ordinary obligations on the selected declaration.
            for clause in canonical_constraints_of(self.gcx(), extension) {
                if let Constraint::TypeEquality(left, right) =
                    instantiate_constraint_with_args(self.gcx(), clause.value, args)
                {
                    let left = self.structurally_resolve(left);
                    let right = self.structurally_resolve(right);
                    if !has_unresolvable_projection(&self.icx, left)
                        && !has_unresolvable_projection(&self.icx, right)
                        && self.unify(left, right).is_err()
                    {
                        return ExtensionHeaderMatch::Mismatch;
                    }
                }
            }
            if before.is_empty() {
                return ExtensionHeaderMatch::Independent;
            }
            let after = numeric_vars_in(&self.icx, receiver);
            if after.len() == before.len() && before.iter().all(|var| after.contains(var)) {
                ExtensionHeaderMatch::Independent
            } else {
                ExtensionHeaderMatch::NeedsLiteralType
            }
        })
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
                || self
                    .gcx()
                    .class_ancestry(receiver)
                    .into_iter()
                    .any(|ancestor| {
                        self.icx
                            .probe(|_| self.unify(ancestor, instantiated).is_ok())
                    })
        })
    }

    fn instantiate_generic_args_with_defaults(
        &mut self,
        def_id: DefinitionID,
        provided: Option<GenericArguments<'ctx>>,
        span: Span,
    ) -> GenericArguments<'ctx> {
        let gcx = self.gcx();
        let provided = provided.unwrap_or(GenericArguments::empty());
        let erased_context = gcx
            .erased_access_context(def_id)
            .map(|context| GenericsBuilder::identity_for_item(gcx, context));
        GenericsBuilder::for_item(gcx, def_id, |param, current_args| {
            if let Some(arg) = provided.get(param.index) {
                return *arg;
            }
            if param.index < gcx.generics_of(def_id).parent_count
                && let Some(argument) =
                    erased_context.and_then(|arguments| arguments.get(param.index).copied())
            {
                return argument;
            }
            self.instantiate_missing_generic_arg(def_id, param, current_args, span)
        })
    }

    fn instantiate_missing_generic_arg(
        &mut self,
        def_id: DefinitionID,
        param: &GenericParameterDefinition,
        current_args: &[GenericArgument<'ctx>],
        span: Span,
    ) -> GenericArgument<'ctx> {
        let gcx = self.gcx();
        let owner = gcx.definition_parent(param.id).unwrap_or(def_id);
        let lower_ctx = DefTyLoweringCtx::new(owner, gcx);
        let current_args = gcx.store.interners.intern_generic_args_slice(current_args);

        match &param.kind {
            GenericParameterDefinitionKind::Type {
                default: Some(default),
                ..
            } => {
                let infer_var = self.icx.var_for_generic_param(param, span);
                let mut default_ty = gcx
                    .try_generic_type_default(param.id)
                    .unwrap_or_else(|| lower_ctx.lowerer().lower_type(default));
                default_ty = instantiate_ty_with_args(gcx, default_ty, current_args);
                self.push_default_fallback_goal(infer_var, GenericArgument::Type(default_ty), span);
                infer_var
            }
            GenericParameterDefinitionKind::Type { default: None, .. } => {
                self.icx.var_for_generic_param(param, span)
            }
            GenericParameterDefinitionKind::Const {
                ty,
                default: Some(default),
            } => {
                let expected_ty = gcx
                    .try_generic_const_param_ty(param.id)
                    .unwrap_or_else(|| lower_ctx.lowerer().lower_type(ty));
                let infer_var = self.icx.var_for_generic_param(param, span);
                let mut default_const =
                    gcx.try_generic_const_default(param.id).unwrap_or_else(|| {
                        lower_ctx
                            .lowerer()
                            .lower_const_argument(expected_ty, default)
                    });
                default_const = instantiate_const_with_args(gcx, default_const, current_args);
                self.push_default_fallback_goal(
                    infer_var,
                    GenericArgument::Const(default_const),
                    span,
                );
                infer_var
            }
            GenericParameterDefinitionKind::Const { default: None, .. } => {
                self.icx.var_for_generic_param(param, span)
            }
        }
    }

    fn push_default_fallback_goal(
        &mut self,
        infer_var: GenericArgument<'ctx>,
        default: GenericArgument<'ctx>,
        span: Span,
    ) {
        self.obligations.push_back(Obligation {
            location: span,
            goal: Goal::DefaultFallback(DefaultFallbackGoalData {
                infer_var,
                default,
                span,
            }),
        });
    }

    fn solve(&mut self, obligation: &Obligation<'ctx>) -> SolverResult<'ctx> {
        let location = obligation.location;
        match &obligation.goal {
            Goal::Equal(lhs, rhs) => self.solve_equality(location, *lhs, *rhs),
            Goal::ConstructorResult(output, target) => {
                let output = self.structurally_resolve(*output);
                if output.is_infer() {
                    SolverResult::Deferred
                } else {
                    self.solve_equality(location, self.gcx().constructor_value(output), *target)
                }
            }
            Goal::InitializerStatement(output, expression) => {
                let output = self.structurally_resolve(*output);
                if output.is_infer() {
                    SolverResult::Deferred
                } else {
                    self.solve_equality(
                        location,
                        self.gcx().constructor_result(output, self.gcx().types.void),
                        *expression,
                    )
                }
            }
            Goal::ConstraintEqual(lhs, rhs) => self.solve_constraint_equality(location, *lhs, *rhs),
            Goal::ExistentialConstraint(constraint) => {
                let constraint = self.icx.resolve_vars_if_possible(*constraint);
                match constraint {
                    Constraint::Bound { ty, interface } => {
                        if ty.contains_inference() {
                            SolverResult::Deferred
                        } else if crate::sema::tycheck::utils::erased_self::has_free_self(ty) {
                            SolverResult::Solved(vec![])
                        } else {
                            self.solve_conforms(location, ty, interface)
                        }
                    }
                    Constraint::TypeEquality(lhs, rhs) => {
                        if crate::sema::tycheck::utils::erased_self::has_free_self(lhs)
                            || crate::sema::tycheck::utils::erased_self::has_free_self(rhs)
                        {
                            SolverResult::Solved(vec![])
                        } else {
                            self.solve_constraint_equality(location, lhs, rhs)
                        }
                    }
                }
            }
            Goal::Conforms { ty, interface } => self.solve_conforms(location, *ty, *interface),
            Goal::OpenedConforms {
                source,
                arguments,
                template,
                ty,
                interface,
            } => self
                .solve_opened_conforms(location, *source, *arguments, *template, *ty, *interface),
            Goal::ValidateOpening { source, arguments } => {
                self.solve_validate_opening(location, *source, *arguments)
            }
            Goal::Apply(data) => self.solve_apply(data.clone()),
            Goal::BindOverload(data) => self.solve_bind_overload(location, data.clone()),
            Goal::BindInterfaceMethod(data) => {
                self.solve_bind_interface_method(location, data.clone())
            }
            Goal::BindMethodOverload(data) => {
                self.solve_bind_method_overload(location, data.clone())
            }
            Goal::Disjunction(branches) => self.solve_disjunction(location, branches.clone()),
            Goal::UnaryOp(data) => self.solve_unary(*data),
            Goal::BinaryOp(data) => self.solve_binary(*data),
            Goal::AssignOp(data) => self.solve_assign_op(*data),
            Goal::Coerce { node_id, from, to } => self.solve_coerce(location, *node_id, *from, *to),
            Goal::AssignOptional {
                node_id,
                target,
                value,
            } => self.solve_assign_optional(location, *node_id, *target, *value),
            Goal::Cast {
                node_id,
                from,
                to,
                is_unsafe,
            } => self.solve_cast(location, *node_id, *from, *to, *is_unsafe),
            Goal::Member(data) => self.solve_member(data.clone()),
            Goal::BindMethodValue(data) => self.solve_bind_method_value(location, data.clone()),
            Goal::MethodValueSignature(data) => {
                self.solve_method_value_signature(location, data.clone())
            }
            Goal::InferredStaticMember(data) => self.solve_inferred_static_member(data.clone()),
            Goal::MethodCall(data) => self.solve_method_call(data.clone()),
            Goal::IndexAccess(data) => self.solve_index_access(data.clone()),
            Goal::StructLiteral(data) => self.solve_struct_literal(data.clone()),
            Goal::SpreadShape {
                result,
                element,
                scalars,
                sources,
                contextual,
            } => {
                self.solve_spread_shape(location, *result, *element, *scalars, sources, *contextual)
            }
            Goal::CollectionLiteral { ty, element, len } => {
                self.solve_collection_literal(location, *ty, *element, *len)
            }
            Goal::TupleAccess(data) => self.solve_tuple_access(data.clone()),
            Goal::Deref(data) => self.solve_deref(data.clone()),
            Goal::DefaultFallback(_) => SolverResult::Deferred,
            Goal::ValidateReturn { site, target } => {
                let target = self.icx.resolve_vars_if_possible(*target);
                if target.is_infer() {
                    return SolverResult::Deferred;
                }
                if crate::sema::tycheck::opaque::is_owner_return(target, self.current_def) {
                    // Hidden-type inference uses only committed return sites.
                    return SolverResult::Solved(vec![]);
                }
                let goal = site.coerce_to(self.gcx(), target);
                SolverResult::Solved(vec![Obligation { location, goal }])
            }
            Goal::ValidatePropagation {
                node_id,
                err_ty,
                return_ty,
            } => self.solve_validate_propagation(location, *node_id, *err_ty, *return_ty),
            Goal::ReleaseHeldLiterals(node) => {
                self.finish_holding(*node);
                SolverResult::Solved(vec![])
            }
        }
    }

    /// The goal at `node` has stopped waiting and has given its inputs what
    /// type it could. Its held literals that are still unknown take their
    /// defaults, except those that another goal still waiting holds too: that
    /// goal may yet give them a type.
    fn finish_holding(&mut self, node: NodeID) {
        let Some(vars) = self.held_literals.remove(&node) else {
            return;
        };
        let scope = self.defaultable_numeric_vars();
        for var in vars {
            if !self.holds_numeric_root(self.icx.numeric_var_root(var)) {
                self.default_numeric_var_in(scope.as_ref(), var);
            }
        }
    }

    /// Default the held literals of the goal at `node` that are still
    /// unknown. Overload selection has verified that its candidates can
    /// accept those defaults.
    pub(super) fn release_held_literals(&mut self, node: NodeID) {
        if let Some(vars) = self.held_literals.remove(&node) {
            let scope = self.defaultable_numeric_vars();
            for var in vars {
                self.default_numeric_var_in(scope.as_ref(), var);
            }
        }
    }

    fn release_all_held_literals(&mut self) {
        let scope = self.defaultable_numeric_vars();
        for (_, vars) in std::mem::take(&mut self.held_literals) {
            for var in vars {
                self.default_numeric_var_in(scope.as_ref(), var);
            }
        }
    }

    /// The unknown literals, by root, that this solve may default, or `None`
    /// when it may default any.
    fn defaultable_numeric_vars(&self) -> Option<FxHashSet<NumericVar>> {
        let scope = self.default_scope.as_ref()?;
        Some(
            scope
                .iter()
                .flat_map(|ty| numeric_vars_in(&self.icx, *ty))
                .collect(),
        )
    }

    fn default_numeric_var_in(&self, scope: Option<&FxHashSet<NumericVar>>, var: NumericVar) {
        if scope.is_none_or(|scope| scope.contains(&self.icx.numeric_var_root(var))) {
            self.icx.default_numeric_var(var);
        }
    }

    /// Whether a type variable is the result of a member lookup that has not
    /// resolved yet, either still queued or deferred until its receiver is
    /// known (`Box { v: 0 }.takeIt(3)` waits for the literal's default), or
    /// of an operator that waits for its operands (`list.count() + 1`).
    /// That goal will give the variable its type.
    pub(super) fn awaits_lookup(&self, var: TyVarID) -> bool {
        let root = self.icx.ty_var_root(var);
        let is_root = |ty: Ty<'ctx>| match self.icx.shallow_resolve(ty).kind() {
            TyKind::Infer(InferTy::TyVar(other)) => self.icx.ty_var_root(other) == root,
            _ => false,
        };
        self.deferred
            .iter()
            .chain(&self.obligations)
            .filter_map(|obligation| lookup_result(&obligation.goal))
            .chain(self.pending_member_values.iter().copied())
            .any(is_root)
    }

    fn is_held_literal(&self, ty: Ty<'ctx>) -> bool {
        self.icx
            .unresolved_numeric_var(ty)
            .is_some_and(|root| self.holds_numeric_root(root))
    }

    fn holds_numeric_root(&self, root: NumericVar) -> bool {
        // Literals can unify after a hold is recorded.
        self.held_literals
            .values()
            .flatten()
            .any(|var| self.icx.numeric_var_root(*var) == root)
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

        if lhs == rhs {
            return SolverResult::Solved(vec![]);
        }
        // Resolve independent parts before waiting on a projection. For
        // Result[T, T::Error], the first argument supplies the T required by
        // the second; deferring the entire type would discard that context.
        if has_unresolvable_projection(&self.icx, lhs)
            || has_unresolvable_projection(&self.icx, rhs)
        {
            let projection = if lhs.is_ty_var() {
                Some((lhs, rhs))
            } else if rhs.is_ty_var() {
                Some((rhs, lhs))
            } else {
                None
            };
            if let Some((variable, source)) = projection
                && let Some(published) = self.publish_projection_equality(source, location)
            {
                return self.solve_equality(location, variable, published);
            }
            let mut pairs = Vec::new();
            match (lhs.kind(), rhs.kind()) {
                (TyKind::Adt(a, left), TyKind::Adt(b, right))
                    if a.id == b.id && left.len() == right.len() =>
                {
                    for (left, right) in left.iter().zip(right.iter()) {
                        match (*left, *right) {
                            (GenericArgument::Type(a), GenericArgument::Type(b)) => {
                                pairs.push((a, b))
                            }
                            (GenericArgument::Const(a), GenericArgument::Const(b))
                                if self.unify_const(a, b).is_ok() =>
                            {
                                pairs.push((a.ty, b.ty))
                            }
                            _ => return self.solve_equality(location, lhs, rhs),
                        }
                    }
                }
                (TyKind::Tuple(left), TyKind::Tuple(right)) if left.len() == right.len() => {
                    pairs.extend(left.iter().copied().zip(right.iter().copied()))
                }
                (TyKind::Reference(a), TyKind::Reference(b)) => pairs.push((a, b)),
                (TyKind::Pointer(a, am), TyKind::Pointer(b, bm)) if am == bm => pairs.push((a, b)),
                (
                    TyKind::Array {
                        element: a,
                        len: al,
                    },
                    TyKind::Array {
                        element: b,
                        len: bl,
                    },
                ) if self.unify_const(al, bl).is_ok() => pairs.push((a, b)),
                (
                    TyKind::FnPointer {
                        effects: ae,
                        inputs: ai,
                        output: ao,
                    },
                    TyKind::FnPointer {
                        effects: be,
                        inputs: bi,
                        output: bo,
                    },
                ) if ae == be && ai.len() == bi.len() => {
                    pairs.extend(ai.iter().copied().zip(bi.iter().copied()));
                    pairs.push((ao, bo));
                }
                _ => return SolverResult::Deferred,
            }
            return SolverResult::Solved(
                pairs
                    .into_iter()
                    .map(|(a, b)| Obligation {
                        location,
                        goal: Goal::ConstraintEqual(a, b),
                    })
                    .collect(),
            );
        }

        self.solve_equality(location, lhs, rhs)
    }

    fn fork_for_probe(&self, binding_node: Option<NodeID>) -> ConstraintSolver<'ctx> {
        let mut obligations = self.obligations.clone();
        for obligation in &mut obligations {
            if let Goal::Apply(data) = &mut obligation.goal
                && data.input_only_selection
                && Some(data.call_node_id) == binding_node
            {
                data.result_ty = self.icx.next_ty_var(data.call_span);
                data.input_only_selection = false;
            }
        }
        ConstraintSolver {
            obligations,
            // Retry pending producers in the probe. Its argument coercions
            // can then see the same result types as the enclosing solve.
            deferred: self
                .deferred
                .iter()
                .filter(|obligation| lookup_result(&obligation.goal).is_some())
                .cloned()
                .collect(),
            ..self.fork_for_lookup()
        }
    }

    /// Test one lookup in the caller's environment without importing other
    /// work from the surrounding expression.
    fn fork_for_lookup(&self) -> ConstraintSolver<'ctx> {
        ConstraintSolver {
            icx: self.icx.clone(),
            coercions: self.coercions,
            boxings: self.boxings,
            obligations: VecDeque::new(),
            deferred: VecDeque::new(),
            // Probes need satisfiability and weakening costs, not collected outputs.
            adjustments: FxHashMap::default(),
            interface_calls: FxHashMap::default(),
            integer_literals: self.integer_literals.clone(),
            field_indices: FxHashMap::default(),
            property_reads: FxHashMap::default(),
            overload_sources: FxHashMap::default(),
            lazy_argument_targets: FxHashMap::default(),
            deferred_return_scopes: self.deferred_return_scopes.clone(),
            result_propagation_conversions: FxHashMap::default(),
            value_resolutions: FxHashMap::default(),
            instantiation_args: FxHashMap::default(),
            opening_calls: self.opening_calls.clone(),
            current_def: self.current_def,
            assumption_constraints: self.assumption_constraints,
            param_env: self.param_env.clone(),
            visible_traits: self.visible_traits.clone(),
            // The caller supplies the literal types to probe. Holds belong to
            // goals in the caller's queue.
            held_literals: FxHashMap::default(),
            pending_member_values: self.pending_member_values.clone(),
            lookups_have_waiters: self.lookups_have_waiters,
            // A probe defaults no more than the solve it probes for.
            default_scope: self.default_scope.clone(),
            // A probe's calls are bound again in the solver it probes for.
            receiver_proofs: Vec::new(),
        }
    }
}

#[derive(Clone)]
struct RankedBranch<'ctx> {
    branch: DisjunctionBranch<'ctx>,
    score: (bool, bool, Reverse<u8>, Reverse<usize>),
}

/// An applicable inherent declaration wins before interface overloads.
fn inherent_method(gcx: Gcx<'_>, source: DefinitionID) -> bool {
    if gcx.is_builtin_clone(source) || gcx.is_primitive_operator(source) {
        return false;
    }
    let Some(parent) = gcx.definition_parent(source) else {
        return true;
    };
    gcx.definition_kind(parent) != crate::hir::DefinitionKind::Interface
        && gcx
            .conformance_records_for_extension(parent.package(), parent)
            .is_empty()
}

fn rank_branches<'ctx>(
    gcx: Gcx<'ctx>,
    branches: Vec<DisjunctionBranch<'ctx>>,
) -> Vec<RankedBranch<'ctx>> {
    let mut ranked: Vec<_> = branches
        .into_iter()
        .map(|branch| RankedBranch {
            score: (
                branch
                    .source
                    .is_none_or(|source| inherent_method(gcx, source)),
                branch.matches_async_preference,
                Reverse(branch.autoref_cost),
                Reverse(branch.deref_steps),
            ),
            branch,
        })
        .collect();
    ranked.sort_by_key(|branch| Reverse(branch.score));
    ranked
}

struct SolverDriver<'ctx> {
    solver: ConstraintSolver<'ctx>,
    errors: SpannedErrorList<'ctx>,
    defaulted: bool,
    default_collection_literals: bool,
    /// Isolated subexpressions share inference variables with outer goals;
    /// defaulting those variables before their constraints run loses context.
    allow_fallbacks: bool,
}

impl<'ctx> SolverDriver<'ctx> {
    fn new(solver: ConstraintSolver<'ctx>) -> SolverDriver<'ctx> {
        SolverDriver {
            solver,
            errors: vec![],
            defaulted: false,
            default_collection_literals: false,
            allow_fallbacks: true,
        }
    }

    fn into_parts(mut self) -> SolverOutputs<'ctx> {
        let mut obligations = std::mem::take(&mut self.solver.obligations);
        obligations.append(&mut self.solver.deferred);
        SolverOutputs {
            obligations,
            adjustments: self.solver.adjustments,
            interface_calls: self.solver.interface_calls,
            field_indices: self.solver.field_indices,
            property_reads: self.solver.property_reads,
            overload_sources: self.solver.overload_sources,
            lazy_argument_targets: self.solver.lazy_argument_targets,
            result_propagation_conversions: self.solver.result_propagation_conversions,
            value_resolutions: self.solver.value_resolutions,
            instantiation_args: self.solver.instantiation_args,
            receiver_proofs: self.solver.receiver_proofs,
        }
    }

    fn solve_to_fixpoint(&mut self) -> Result<(), SpannedErrorList<'ctx>> {
        loop {
            // Drain pending fallbacks from lowering
            let pending = if self.allow_fallbacks {
                self.solver.icx.take_pending_fallbacks()
            } else {
                vec![]
            };
            for data in pending {
                self.solver.obligations.push_back(Obligation {
                    location: data.span,
                    goal: Goal::DefaultFallback(data),
                });
            }

            let made_progress = self.drain_queue();

            if !self.errors.is_empty() {
                self.remove_dependent_conformance_errors();
                return Err(std::mem::take(&mut self.errors));
            }

            if !self.solver.obligations.is_empty() {
                continue;
            }

            if !self.defaulted {
                // Use constraints learned during this round before choosing
                // defaults. A deferred literal may now have a concrete context.
                if made_progress && !self.solver.deferred.is_empty() {
                    self.requeue_deferred();
                    continue;
                }
                self.defaulted = true;
                // Closure checking and overload probes can run before the
                // enclosing call has supplied a collection's element type.
                let awaiting_collection_context = !self.default_collection_literals
                    && self.solver.deferred.iter().any(|obligation| {
                        matches!(obligation.goal, Goal::CollectionLiteral { ty, .. } | Goal::SpreadShape { result: ty, .. }
                            if self.solver.icx.resolve_vars_if_possible(ty).is_infer()
                                || has_unresolvable_projection(&self.solver.icx, ty))
                    });
                if self.allow_fallbacks {
                    if !awaiting_collection_context {
                        let scope = self.solver.defaultable_numeric_vars();
                        let held = self.hold_literals(scope.as_ref());
                        match scope {
                            None => self.solver.icx.default_numeric_vars_except(&held),
                            Some(scope) => {
                                for var in scope {
                                    if !held.contains(&var) {
                                        self.solver.icx.default_numeric_var(var);
                                    }
                                }
                            }
                        }
                    }
                    self.apply_default_fallbacks();
                }
                if !self.solver.deferred.is_empty() {
                    self.requeue_deferred();
                }
                continue;
            }

            if !self.solver.deferred.is_empty() && made_progress {
                self.requeue_deferred();
                continue;
            }

            // A producer-only solve can run before its surrounding application
            // supplies the missing operand. Leave its held inputs open for the
            // next pass. A complete solve can exhaust the remaining defaults.
            if !self.solver.held_literals.is_empty() && self.solver.default_scope.is_none() {
                self.solver.release_all_held_literals();
                self.requeue_deferred();
                continue;
            }

            // No progress after defaulting; let unresolved inference vars report errors.
            return Ok(());
        }
    }

    /// At fallback, default the literals needed to unblock a goal before
    /// defaulting the inputs that goal can type. In `[1, 2].map(f).count() + 1`,
    /// the array needs an element type for lookup, but the addend can take
    /// its type from the count. A literal used in both roles is a prerequisite.
    fn hold_literals(&mut self, scope: Option<&FxHashSet<NumericVar>>) -> FxHashSet<NumericVar> {
        let icx = &self.solver.icx;
        let mut prerequisites = FxHashSet::default();
        let mut by_node: FxHashMap<NodeID, Vec<NumericVar>> = FxHashMap::default();
        let mut needs = |ty| prerequisites.extend(numeric_vars_in(icx, ty));
        let mut input = |node, ty| {
            for var in numeric_vars_in(icx, ty) {
                if scope.is_none_or(|scope| scope.contains(&var)) {
                    let vars = by_node.entry(node).or_default();
                    if !vars.contains(&var) {
                        vars.push(var);
                    }
                }
            }
        };
        for obligation in &self.solver.deferred {
            if let Some((receiver, call)) = receiver_lookup(&obligation.goal) {
                needs(receiver);
                if let Some((node, arguments)) = call {
                    for arg in arguments {
                        input(node, arg.ty);
                    }
                }
                continue;
            }
            let (node, lhs, rhs) = match &obligation.goal {
                Goal::BinaryOp(data) => (data.node_id, data.lhs, data.rhs),
                Goal::AssignOp(data) => (data.node_id, data.lhs, data.rhs),
                Goal::UnaryOp(data) => {
                    needs(data.lhs);
                    continue;
                }
                _ => continue,
            };
            // Both a binary operator and an intrinsic compound write can
            // type either operand once the other operand's producer resolves.
            let awaits_type = |ty| {
                self.solver
                    .operand_awaits_type(self.solver.structurally_resolve(ty))
            };
            match (awaits_type(lhs), awaits_type(rhs)) {
                (true, false) => {
                    needs(lhs);
                    input(node, rhs);
                }
                (false, true) => {
                    needs(rhs);
                    input(node, lhs);
                }
                _ => {
                    needs(lhs);
                    needs(rhs);
                }
            }
        }
        let mut held = FxHashSet::default();
        by_node.retain(|_, vars| {
            vars.retain(|var| !prerequisites.contains(var));
            held.extend(vars.iter().copied());
            !vars.is_empty()
        });
        self.solver.held_literals = by_node;
        held
    }

    /// If an operand already failed a bound required to form a nominal type,
    /// reporting a failed use of that ill-formed type in the enclosing
    /// expression adds no information (e.g. RangeIterator[double]: Iterator).
    fn remove_dependent_conformance_errors(&mut self) {
        use crate::sema::error::TypeError;
        if self.errors.len() < 2 {
            return;
        }
        let failed: Vec<_> = self
            .errors
            .iter()
            .filter_map(|error| match error.value {
                TypeError::NonConformance { ty, interface } => Some((ty, interface, error.span)),
                _ => None,
            })
            .collect();
        let gcx = self.solver.gcx();
        self.errors.retain(|error| {
            let TypeError::NonConformance { ty, .. } = error.value else {
                return true;
            };
            let TyKind::Adt(def, args) = ty.kind() else {
                return true;
            };
            if args.len() != gcx.generics_of(def.id).total_count() {
                return true;
            }
            !canonical_constraints_of(gcx, def.id)
                .into_iter()
                .any(|bound| {
                    let Constraint::Bound {
                        ty: subject,
                        interface,
                    } = instantiate_constraint_with_args(gcx, bound.value, args)
                    else {
                        return false;
                    };
                    args.iter().any(|arg| arg.ty() == Some(subject))
                        && failed.iter().any(|&(other, required, span)| {
                            let pos = |p: crate::span::Position| (p.line, p.offset);
                            subject == other
                                && interface == required
                                && span.file == error.span.file
                                && pos(error.span.start) <= pos(span.start)
                                && pos(span.end) <= pos(error.span.end)
                        })
                })
        });
    }

    fn drain_queue(&mut self) -> bool {
        let mut made_progress = false;
        let dcx = self.solver.gcx().dcx();
        while let Some(obligation) = self.solver.obligations.pop_front() {
            dcx.cancellation_point();
            let mut result = self.solver.solve(&obligation);
            if let SolverResult::Solved(obligations) = &mut result
                && self.solver.lookups_have_waiters
                && let Some(lookup) = lookup_result(&obligation.goal)
            {
                obligations.extend(self.take_coercions_awaiting(lookup));
            }
            if let SolverResult::Solved(obligations) = &mut result
                && !self.solver.held_literals.is_empty()
                && let Some(node) = holding_node(&obligation.goal)
                && self.solver.held_literals.contains_key(&node)
            {
                obligations.push(Obligation {
                    location: obligation.location,
                    goal: Goal::ReleaseHeldLiterals(node),
                });
            }
            match result {
                SolverResult::Deferred => self.solver.deferred.push_back(obligation),
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

    /// Queue the deferred goals again. Their lookups are found in the queue now.
    fn requeue_deferred(&mut self) {
        self.solver.obligations.append(&mut self.solver.deferred);
    }

    /// Take the boxing and wrapping coercions that wait for a lookup's
    /// result, so they run right after the lookup's own goals, where binding
    /// the result to the target type used to run. Its overloads are then
    /// probed with the coercion in view, and its argument literals are not
    /// released before the coercion has seen the result.
    fn take_coercions_awaiting(&mut self, lookup: Ty<'ctx>) -> Vec<Obligation<'ctx>> {
        let icx = self.solver.icx.clone();
        let gcx = self.solver.gcx();
        let waits = |to| coerce::lookup_dependent_target(gcx, icx.shallow_resolve(to));
        let root_of = |ty: Ty<'ctx>| match icx.shallow_resolve(ty).kind() {
            TyKind::Infer(InferTy::TyVar(var)) => Some(icx.ty_var_root(var)),
            _ => None,
        };
        let Some(root) = root_of(lookup) else {
            return vec![];
        };
        let awaits = |obligation: &Obligation<'ctx>| {
            matches!(obligation.goal, Goal::Coerce { from, to, .. }
                if root_of(from) == Some(root) && waits(to))
        };
        let mut taken = vec![];
        for queue in [&mut self.solver.deferred, &mut self.solver.obligations] {
            if !queue.iter().any(awaits) {
                continue;
            }
            let (waiting, rest): (VecDeque<_>, VecDeque<_>) =
                std::mem::take(queue).into_iter().partition(awaits);
            *queue = rest;
            taken.extend(waiting);
        }
        taken
    }

    fn apply_default_fallbacks(&mut self) {
        let mut remaining = VecDeque::new();
        while let Some(obligation) = self.solver.deferred.pop_front() {
            let goal = obligation.goal;
            let location = obligation.location;
            if self.default_collection_literals
                && let Goal::CollectionLiteral { ty, element, len } = &goal
                && self.solver.icx.resolve_vars_if_possible(*ty).is_infer()
            {
                let array = Ty::new(
                    TyKind::Array {
                        element: *element,
                        len: *len,
                    },
                    self.solver.gcx(),
                );
                if let SolverResult::Error(errors) =
                    self.solver.solve_equality(location, *ty, array)
                {
                    self.errors.extend(errors);
                }
                remaining.push_back(Obligation { goal, location });
            } else if self.default_collection_literals
                && let Goal::SpreadShape {
                    result,
                    element,
                    scalars,
                    sources,
                    ..
                } = &goal
                && self.solver.icx.resolve_vars_if_possible(*result).is_infer()
            {
                if let SolverResult::Error(errors) = self
                    .solver
                    .solve_spread_shape(location, *result, *element, *scalars, sources, false)
                {
                    self.errors.extend(errors);
                }
                remaining.push_back(Obligation { goal, location });
            } else if let Goal::DefaultFallback(data) = goal {
                self.attempt_default_fallback(data, location);
            } else {
                remaining.push_back(Obligation { goal, location });
            }
        }
        self.solver.deferred = remaining;
    }

    fn attempt_default_fallback(&mut self, data: DefaultFallbackGoalData<'ctx>, span: Span) {
        match (data.infer_var, data.default) {
            (GenericArgument::Type(var), GenericArgument::Type(default)) => {
                let resolved = self.solver.icx.resolve_vars_if_possible(var);
                // Without holding, this literal would already have its numeric
                // default here, and the fallback would not apply.
                if resolved.is_infer() && !self.solver.is_held_literal(resolved) {
                    let _ = self.solver.solve_equality(span, var, default);
                }
            }
            (GenericArgument::Const(var), GenericArgument::Const(default)) => {
                let resolved = self.solver.icx.resolve_const_if_possible(var);
                if matches!(resolved.kind, ConstKind::Infer(_)) {
                    let _ = self.solver.unify_const(var, default);
                }
            }
            _ => {}
        }
    }
}

/// The receiver of a goal that looks a member up on it, and for calls, the
/// call node and its arguments (without the receiver).
fn receiver_lookup<'a, 'ctx>(
    goal: &'a Goal<'ctx>,
) -> Option<(Ty<'ctx>, Option<(NodeID, &'a [ApplyArgument<'ctx>])>)> {
    match goal {
        Goal::MethodCall(data) => Some((data.receiver, Some((data.node_id, &data.arguments)))),
        Goal::IndexAccess(data) => Some((data.receiver, Some((data.nodes.call, &data.keys)))),
        Goal::Member(data) => Some((data.receiver, None)),
        _ => None,
    }
}

/// The node of a goal that can hold input literals: a call, a subscript or
/// an operator. An operator's node is the node of its operator method call
/// too (`solve_operator_method`).
fn holding_node(goal: &Goal<'_>) -> Option<NodeID> {
    match goal {
        Goal::MethodCall(data) => Some(data.node_id),
        Goal::IndexAccess(data) => Some(data.nodes.call),
        Goal::BinaryOp(data) => Some(data.node_id),
        Goal::AssignOp(data) => Some(data.node_id),
        _ => None,
    }
}

/// The type that a `receiver_lookup` goal gives its result, or that an
/// operator gives its own. An operator waits for an unresolved operand, such
/// as a lookup's result (`list.count() + 1`), and only then gives its result
/// a type; binding that result to a coercion's target first would reject
/// the operator's actual result.
fn lookup_result<'ctx>(goal: &Goal<'ctx>) -> Option<Ty<'ctx>> {
    match goal {
        Goal::MethodCall(data) => Some(data.result),
        Goal::IndexAccess(data) => Some(data.output),
        Goal::Member(data) => Some(data.result),
        Goal::BinaryOp(data) => Some(data.rho),
        Goal::UnaryOp(data) => Some(data.rho),
        _ => None,
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ExtensionHeaderMatch {
    Mismatch,
    Independent,
    NeedsLiteralType,
}

/// Unknown integer and float literal variables in a type, by root.
fn numeric_vars_in<'ctx>(icx: &InferCtx<'ctx>, ty: Ty<'ctx>) -> Vec<NumericVar> {
    use crate::sema::tycheck::visit::{TypeSuperVisitable, TypeVisitable, TypeVisitor};
    struct Collect<'a, 'ctx> {
        icx: &'a InferCtx<'ctx>,
        vars: Vec<NumericVar>,
    }
    impl<'ctx> TypeVisitor<'ctx> for Collect<'_, 'ctx> {
        fn visit_ty(&mut self, ty: Ty<'ctx>) -> bool {
            if let Some(var) = self.icx.unresolved_numeric_var(ty) {
                if !self.vars.contains(&var) {
                    self.vars.push(var);
                }
                return false;
            }
            ty.super_visit_with(self)
        }
    }
    let mut collect = Collect {
        icx,
        vars: Vec::new(),
    };
    icx.resolve_vars_if_possible(ty).visit_with(&mut collect);
    collect.vars
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
            // Every interface argument can determine an associated type,
            // including Into's destination even when Self is already known.
            args.iter().any(|argument| {
                crate::sema::tycheck::utils::unresolved::generic_arg_contains_unresolved_inference(
                    &icx.resolve_vars_if_possible(*argument),
                )
            })
        }
        TyKind::Alias { args, .. } | TyKind::Adt(_, args) => args.iter().any(|arg| match arg {
            GenericArgument::Type(t) => has_unresolvable_projection(icx, *t),
            GenericArgument::Const(c) => has_unresolvable_projection(icx, c.ty),
        }),
        TyKind::Pointer(inner, _) | TyKind::Reference(inner) => {
            has_unresolvable_projection(icx, inner)
        }
        TyKind::Array { element, .. } => has_unresolvable_projection(icx, element),
        TyKind::Tuple(items) => items.iter().any(|t| has_unresolvable_projection(icx, *t)),
        TyKind::FnPointer { inputs, output, .. } => {
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
