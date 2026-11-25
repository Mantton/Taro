use crate::{
    compile::context::Gcx,
    hir::StdItem,
    sema::{
        models::{
            AliasKind, CandidateSource, ConformanceRecord, ConformanceRecordId, Constraint,
            GenericArgument, GenericArguments, GoalResult, InterfaceGoal, InterfaceReference,
            SelectedImpl, SelectionError, SelectionMode, SelectionResult, Ty, TyKind,
        },
        resolve::models::TypeHead,
        tycheck::{
            infer::InferCtx,
            utils::{
                ParamEnv,
                instantiate::{
                    instantiate_constraint_with_args, instantiate_interface_ref_with_args,
                    instantiate_ty_with_args,
                },
                normalize_aliases, normalize_ty, type_head_from_value_ty,
                unify::TypeUnifier,
                unresolved::{
                    generic_arg_contains_unresolved_inference, ty_contains_unresolved_inference,
                },
            },
        },
    },
};
use rustc_hash::FxHashSet;
use std::rc::Rc;

use super::{
    candidate::ConfirmedCandidate,
    canonical::goal_key,
    goal::{interface_ref_matches_goal, interface_ref_to_goal},
};

pub fn prove_interface_goal<'ctx>(
    gcx: Gcx<'ctx>,
    goal: InterfaceGoal<'ctx>,
    mode: SelectionMode,
) -> GoalResult {
    match select_interface_impl(gcx, goal, mode) {
        SelectionResult::Selected(_) => GoalResult::Proven,
        SelectionResult::NoSolution(_) => GoalResult::NoSolution,
        SelectionResult::Ambiguous(_) => GoalResult::Ambiguous,
    }
}

pub fn select_interface_impl<'ctx>(
    gcx: Gcx<'ctx>,
    goal: InterfaceGoal<'ctx>,
    mode: SelectionMode,
) -> SelectionResult<'ctx> {
    let mut selector = Selector::new(gcx, mode);
    selector.select(goal)
}

pub(crate) fn deduce_impl_subst<'ctx>(
    gcx: Gcx<'ctx>,
    extension_id: crate::hir::DefinitionID,
    self_ty: Ty<'ctx>,
) -> Option<GenericArguments<'ctx>> {
    let generics = gcx.generics_of(extension_id);
    if generics.is_empty() {
        return Some(GenericArguments::empty());
    }

    let pattern_self = extension_self_ty(gcx, extension_id)?;

    let icx = Rc::new(InferCtx::new(gcx));
    let span = crate::span::Span::empty(crate::span::FileID::from_usize(0));
    let fresh_args = icx.fresh_args_for_def(extension_id, span);
    let instantiated =
        normalize_aliases(gcx, instantiate_ty_with_args(gcx, pattern_self, fresh_args));
    let self_ty = normalize_aliases(gcx, self_ty);
    let unifier = TypeUnifier::new(icx.clone());
    if unifier.unify(instantiated, self_ty).is_err() {
        return None;
    }

    let resolved = icx.resolve_args_if_possible(fresh_args);
    if generic_args_contain_infer(resolved) {
        return None;
    }

    Some(resolved)
}

/// Recover an interface header for discovery, not a conformance proof.
/// Parameters absent from Self may be inferred from the selected method's
/// arguments or result. Return only the resolved argument prefix: binding the
/// selected requirement creates its remaining variables in the caller's context.
/// Never export inference variables from this temporary context.
pub(crate) fn deduce_conformance_interface<'ctx>(
    gcx: Gcx<'ctx>,
    record: &ConformanceRecord<'ctx>,
    self_ty: Ty<'ctx>,
) -> Option<crate::sema::models::InterfaceReference<'ctx>> {
    if self_ty.contains_inference() {
        return None;
    }
    if gcx.generics_of(record.extension).is_empty() {
        return Some(record.interface);
    }
    let pattern = extension_self_ty(gcx, record.extension)?;
    let icx = Rc::new(InferCtx::new(gcx));
    let arguments = icx.fresh_args_for_def(record.extension, record.location);
    let pattern = normalize_aliases(gcx, instantiate_ty_with_args(gcx, pattern, arguments));
    TypeUnifier::new(icx.clone())
        .unify(pattern, normalize_aliases(gcx, self_ty))
        .ok()?;
    let interface = crate::sema::tycheck::utils::instantiate::instantiate_interface_ref_with_args(
        gcx,
        record.interface,
        icx.resolve_args_if_possible(arguments),
    );
    let prefix: Vec<_> = interface
        .arguments
        .iter()
        .copied()
        .take_while(|argument| !generic_arg_contains_unresolved_inference(argument))
        .collect();
    if !crate::sema::tycheck::utils::unresolved::interface_ref_contains_unresolved_inference(
        interface,
    ) {
        return Some(interface);
    }
    // Self is fixed by the receiver; only trailing interface arguments may be
    // supplied later. Associated bindings are checked by conformance selection.
    if prefix.is_empty() {
        return None;
    }
    Some(InterfaceReference {
        id: interface.id,
        arguments: gcx.store.interners.intern_generic_args(prefix),
        bindings: &[],
    })
}

struct Selector<'ctx> {
    gcx: Gcx<'ctx>,
    mode: SelectionMode,
    visiting: FxHashSet<crate::sema::models::CanonicalGoalKey<'ctx>>,
}

impl<'ctx> Selector<'ctx> {
    fn new(gcx: Gcx<'ctx>, mode: SelectionMode) -> Self {
        Self {
            gcx,
            mode,
            visiting: FxHashSet::default(),
        }
    }

    fn select(&mut self, goal: InterfaceGoal<'ctx>) -> SelectionResult<'ctx> {
        if goal_has_unresolved_types(goal) {
            return SelectionResult::NoSolution(vec![SelectionError::NoCandidates(goal)]);
        }

        crate::sema::tycheck::ensure_conformance_headers(self.gcx, goal.self_ty, goal.interface_id);
        let key = goal_key(self.gcx, goal, self.mode);
        if let Some(cached) = self.gcx.get_selection_cache(self.gcx.package_index(), key) {
            return cached;
        }

        if !self.visiting.insert(key) {
            // Ordinary interface proofs are inductive. A where-clause cannot
            // prove its own goal, nor does such a cycle create two candidates.
            return SelectionResult::NoSolution(vec![SelectionError::NoCandidates(goal)]);
        }

        let (mut candidates, saw_ambiguous_obligation) = self.collect_candidates(goal);
        let mut viable = Vec::new();
        viable.append(&mut candidates);

        self.visiting.remove(&key);

        viable.sort_by_key(|candidate| match candidate.source {
            CandidateSource::Impl(id) => (id.package.index(), id.index as usize),
            CandidateSource::ParamEnv => (usize::MAX - 5, 0),
            CandidateSource::BuiltinTuple => (usize::MAX - 4, 0),
            CandidateSource::BuiltinTupleConformance => (usize::MAX - 3, 0),
            CandidateSource::BuiltinCallable => (usize::MAX - 2, 0),
            CandidateSource::BuiltinClone => (usize::MAX - 1, 0),
            CandidateSource::BuiltinOperator => (usize::MAX, 0),
            CandidateSource::BuiltinAnyObject => (usize::MAX, 1),
        });

        let result = match viable.len() {
            0 if saw_ambiguous_obligation => SelectionResult::Ambiguous(Vec::new()),
            0 => SelectionResult::NoSolution(vec![SelectionError::NoCandidates(goal)]),
            1 => {
                let candidate = viable.pop().expect("length checked");
                SelectionResult::Selected(SelectedImpl {
                    source: candidate.source,
                    extension_id: candidate.extension_id,
                    record_id: candidate.record_id,
                    subst: candidate.subst,
                    obligations: candidate.obligations,
                })
            }
            _ => {
                let selected = viable
                    .into_iter()
                    .map(|candidate| SelectedImpl {
                        source: candidate.source,
                        extension_id: candidate.extension_id,
                        record_id: candidate.record_id,
                        subst: candidate.subst,
                        obligations: candidate.obligations,
                    })
                    .collect();
                SelectionResult::Ambiguous(selected)
            }
        };

        self.gcx
            .put_selection_cache(self.gcx.package_index(), key, result.clone());
        result
    }

    fn collect_candidates(
        &mut self,
        goal: InterfaceGoal<'ctx>,
    ) -> (Vec<ConfirmedCandidate<'ctx>>, bool) {
        let mut out = Vec::new();
        let mut saw_ambiguous_obligation = false;

        // Codec field checks can assume the struct conformance currently being
        // derived. A matching assumption already establishes these capability-
        // only interfaces (which have no associated bindings); rediscovering
        // its implementation would create a second candidate or recurse.
        if [StdItem::Encodable, StdItem::Decodable]
            .iter()
            .any(|item| self.gcx.std_item_def(*item) == Some(goal.interface_id))
            && let Some(candidate) = self.param_env_candidate(goal)
        {
            return (vec![candidate], false);
        }

        // Only class identities can establish this capability. A source impl
        // assertion cannot turn an inline value or a borrowed handle into one.
        if self.gcx.std_item_def(StdItem::AnyObject) == Some(goal.interface_id) {
            if self.gcx.uses_native_class_handle(goal.self_ty)
                || self
                    .gcx
                    .existential_requires_interface(goal.self_ty, StdItem::AnyObject)
            {
                out.push(ConfirmedCandidate {
                    source: CandidateSource::BuiltinAnyObject,
                    extension_id: None,
                    record_id: None,
                    subst: GenericArguments::empty(),
                    obligations: Vec::new(),
                });
            } else if matches!(
                normalize_aliases(self.gcx, goal.self_ty).kind(),
                TyKind::Parameter(_) | TyKind::Alias { .. } | TyKind::ExistentialSelf(_)
            ) && let Some(candidate) = self.param_env_candidate(goal)
            {
                out.push(candidate);
            }
            return (out, false);
        }

        if let Some(candidate) = self.builtin_tuple_candidate(goal) {
            out.push(candidate);
        }

        if let Some(candidate) =
            self.builtin_tuple_conformance_candidate(goal, &mut saw_ambiguous_obligation)
        {
            out.push(candidate);
        }

        if crate::mir::primitive_operators::item_for_goal(self.gcx, goal).is_some() {
            out.push(ConfirmedCandidate {
                source: CandidateSource::BuiltinOperator,
                extension_id: None,
                record_id: None,
                subst: GenericArguments::empty(),
                obligations: Vec::new(),
            });
        }

        if let Some(candidate) = self.builtin_callable_candidate(goal) {
            out.push(candidate);
        }

        if let Some(candidate) = self.builtin_clone_candidate(goal, &mut saw_ambiguous_obligation) {
            out.push(candidate);
        }

        if let Some(candidate) = self.param_env_candidate(goal) {
            out.push(candidate);
        }

        out.extend(self.collect_declared_candidates(goal, &mut saw_ambiguous_obligation));

        (out, saw_ambiguous_obligation)
    }

    fn collect_declared_candidates(
        &mut self,
        goal: InterfaceGoal<'ctx>,
        saw_ambiguous_obligation: &mut bool,
    ) -> Vec<ConfirmedCandidate<'ctx>> {
        let mut out = Vec::new();
        let mut head = type_head_from_value_ty(goal.self_ty);
        if head.is_none() {
            let normalized = normalize_aliases(self.gcx, goal.self_ty);
            if normalized != goal.self_ty {
                head = type_head_from_value_ty(normalized);
            }
        }
        // Inherited conformances retain the base's resolved interface arguments
        // (including defaults). Only the receiver is projected to its actual
        // base instantiation for implementation matching; substituting Derived
        // into every occurrence of Base would invent PartialEq[Derived].
        let mut owners = vec![(head, goal.self_ty)];
        owners.extend(
            self.gcx
                .class_ancestry(goal.self_ty)
                .into_iter()
                .skip(1)
                .map(|owner| (type_head_from_value_ty(owner), owner)),
        );
        let mut records: Vec<(ConformanceRecordId, ConformanceRecord<'ctx>, Ty<'ctx>)> = self
            .gcx
            .conformance_ownership_packages(goal.interface_id, goal.self_ty, goal.interface_args)
            .into_iter()
            .flat_map(|package| {
                self.gcx.with_type_database(package, |db| {
                    db.conformance_by_interface
                        .get(&goal.interface_id)
                        .into_iter()
                        .flat_map(|ids| ids.iter())
                        .filter_map(|id| {
                            let record = db.conformance_records.get(id)?;
                            let owner = if record.target.is_blanket() {
                                goal.self_ty
                            } else {
                                owners
                                    .iter()
                                    .find(|(head, _)| *head == Some(record.target))?
                                    .1
                            };
                            Some((*id, *record, owner))
                        })
                        .collect::<Vec<_>>()
                })
            })
            .collect();
        records.sort_by_key(|(id, _, _)| (id.package.index(), id.index));
        let mut seen_ids = FxHashSet::default();

        let mut nearest_class = None;
        for (record_id, record, owner) in records {
            if !seen_ids.insert(record_id) {
                continue;
            }
            if let Some(candidate) = self.confirm_record_candidate(
                InterfaceGoal {
                    self_ty: owner,
                    ..goal
                },
                record_id,
                record,
                saw_ambiguous_obligation,
            ) {
                let depth = (!record.target.is_blanket() && self.gcx.is_class_type(owner))
                    .then(|| owners.iter().position(|(_, ty)| *ty == owner).unwrap());
                if let Some(depth) = depth {
                    nearest_class = Some(nearest_class.map_or(depth, |old: usize| old.min(depth)));
                }
                out.push((depth, candidate));
            }
        }
        // A subclass block customizes one inherited conformance. It is not a
        // second competing implementation; unrelated blanket candidates still
        // participate in ordinary coherence/ambiguity checks.
        out.into_iter()
            .filter(|(depth, _)| depth.is_none() || *depth == nearest_class)
            .map(|(_, candidate)| candidate)
            .collect()
    }

    fn param_env_candidate(&self, goal: InterfaceGoal<'ctx>) -> Option<ConfirmedCandidate<'ctx>> {
        if goal.param_env.is_empty() && !matches!(goal.self_ty.kind(), TyKind::Alias { .. }) {
            return None;
        }
        let env = ParamEnv::new(goal.param_env.to_vec());
        for bound in env.bounds_for_type(self.gcx, goal.self_ty, |ty| ty == goal.self_ty) {
            if super::ref_ops::collect_interface_with_superfaces(self.gcx, bound)
                .into_iter()
                .any(|interface| interface_ref_matches_goal(self.gcx, interface, goal))
            {
                return Some(ConfirmedCandidate {
                    source: CandidateSource::ParamEnv,
                    extension_id: None,
                    record_id: None,
                    subst: GenericArguments::empty(),
                    obligations: Vec::new(),
                });
            }
        }
        None
    }

    fn builtin_tuple_candidate(
        &self,
        goal: InterfaceGoal<'ctx>,
    ) -> Option<ConfirmedCandidate<'ctx>> {
        let TypeHead::Tuple(_) = type_head_from_value_ty(goal.self_ty)? else {
            return None;
        };
        let tuple_id = self.gcx.std_item_def(StdItem::Tuple)?;
        if goal.interface_id != tuple_id {
            return None;
        }
        Some(ConfirmedCandidate {
            source: CandidateSource::BuiltinTuple,
            extension_id: None,
            record_id: None,
            subst: GenericArguments::empty(),
            obligations: Vec::new(),
        })
    }

    fn builtin_tuple_conformance_candidate(
        &mut self,
        goal: InterfaceGoal<'ctx>,
        saw_ambiguous_obligation: &mut bool,
    ) -> Option<ConfirmedCandidate<'ctx>> {
        let item = crate::mir::tuple_conformances::CONFORMANCE_ITEMS
            .iter()
            .copied()
            .find(|&item| self.gcx.std_item_def(item) == Some(goal.interface_id))?;
        if !goal.bindings.is_empty() {
            return None;
        }
        let ty = normalize_aliases(self.gcx, goal.self_ty);
        let TyKind::Tuple(fields) = ty.kind() else {
            return None;
        };
        if crate::mir::tuple_conformances::is_rhs_parameterized(item) {
            if goal.interface_args.len() > 1 {
                return None;
            }
            if let Some(arg) = goal.interface_args.first().copied() {
                let GenericArgument::Type(rhs) = arg else {
                    return None;
                };
                let rhs = normalize_aliases(self.gcx, rhs);
                if rhs != ty {
                    if rhs.is_infer()
                        || (matches!(rhs.kind(), TyKind::Tuple(rhs_fields) if rhs_fields.len() == fields.len())
                            && rhs.contains_inference())
                    {
                        *saw_ambiguous_obligation = true;
                    }
                    return None;
                }
            }
        } else if !goal.interface_args.is_empty() {
            return None;
        }

        let obligations: Vec<_> = fields
            .iter()
            .copied()
            .map(|field| {
                let interface_args = if crate::mir::tuple_conformances::is_rhs_parameterized(item) {
                    self.gcx
                        .store
                        .interners
                        .intern_generic_args(vec![GenericArgument::Type(field)])
                } else {
                    GenericArguments::empty()
                };
                InterfaceGoal {
                    interface_id: goal.interface_id,
                    self_ty: field,
                    interface_args,
                    bindings: &[],
                    param_env: goal.param_env,
                }
            })
            .collect();

        match self.obligations_satisfied(&obligations) {
            GoalSatisfaction::Satisfied => {}
            GoalSatisfaction::Ambiguous => {
                *saw_ambiguous_obligation = true;
                return None;
            }
            GoalSatisfaction::Unsatisfied => return None,
        }

        Some(ConfirmedCandidate {
            source: CandidateSource::BuiltinTupleConformance,
            extension_id: None,
            record_id: None,
            subst: GenericArguments::empty(),
            obligations,
        })
    }

    fn builtin_clone_candidate(
        &mut self,
        goal: InterfaceGoal<'ctx>,
        saw_ambiguous_obligation: &mut bool,
    ) -> Option<ConfirmedCandidate<'ctx>> {
        if self.gcx.std_item_def(StdItem::Clone) != Some(goal.interface_id) {
            return None;
        }
        let ty = normalize_aliases(self.gcx, goal.self_ty);
        let obligations = if builtin_copy_clone(self.gcx, ty) {
            Vec::new()
        } else {
            let components = match ty.kind() {
                TyKind::Tuple(fields) => fields.to_vec(),
                TyKind::Array { element, .. } => vec![element],
                TyKind::Closure { .. } => closure_clone_fields(self.gcx, ty)?,
                _ => return None,
            };
            components
                .into_iter()
                .map(|self_ty| InterfaceGoal { self_ty, ..goal })
                .collect()
        };
        match self.obligations_satisfied(&obligations) {
            GoalSatisfaction::Satisfied => {}
            GoalSatisfaction::Ambiguous => {
                *saw_ambiguous_obligation = true;
                return None;
            }
            GoalSatisfaction::Unsatisfied => return None,
        }
        Some(ConfirmedCandidate {
            source: CandidateSource::BuiltinClone,
            extension_id: None,
            record_id: None,
            subst: GenericArguments::empty(),
            obligations,
        })
    }

    fn builtin_callable_candidate(
        &self,
        goal: InterfaceGoal<'ctx>,
    ) -> Option<ConfirmedCandidate<'ctx>> {
        let (kind, inputs, output) = crate::sema::models::callable_signature(goal.self_ty)?;

        let allowed = crate::sema::models::callable_kind(self.gcx, goal.interface_id) == Some(kind);
        if !allowed {
            return None;
        }

        if goal.interface_args.len() != 2 {
            return None;
        }

        let args_ty = crate::sema::models::callable_args_ty(self.gcx, inputs);

        let Some(GenericArgument::Type(actual_args_ty)) = goal.interface_args.get(0).copied()
        else {
            return None;
        };
        let Some(GenericArgument::Type(actual_output_ty)) = goal.interface_args.get(1).copied()
        else {
            return None;
        };

        if actual_args_ty != args_ty || actual_output_ty != output {
            return None;
        }

        Some(ConfirmedCandidate {
            source: CandidateSource::BuiltinCallable,
            extension_id: None,
            record_id: None,
            subst: GenericArguments::empty(),
            obligations: Vec::new(),
        })
    }

    fn confirm_record_candidate(
        &mut self,
        goal: InterfaceGoal<'ctx>,
        record_id: ConformanceRecordId,
        record: ConformanceRecord<'ctx>,
        saw_ambiguous_obligation: &mut bool,
    ) -> Option<ConfirmedCandidate<'ctx>> {
        // Declaration headers can ask before witness checking populates the
        // canonical constraint cache. A missing entry cannot prove a bound.
        if self.gcx.store.collecting_constant_headers.get()
            && record.extension.package() == self.gcx.package_index()
        {
            crate::sema::tycheck::constraints::canonical_constraints_of(self.gcx, record.extension);
        }
        let subst = self.deduce_record_subst(goal, record)?;
        let instantiated = if subst.is_empty() {
            record.interface
        } else {
            instantiate_interface_ref_with_args(self.gcx, record.interface, subst)
        };

        let constraints: Vec<_> = self
            .gcx
            .canonical_constraints_of(record.extension)
            .into_iter()
            .map(|constraint| instantiate_constraint_with_args(self.gcx, constraint.value, subst))
            .collect();
        let env = ParamEnv::new(constraints.clone());

        if !interface_header_matches_goal(self.gcx, instantiated, goal, &env) {
            return None;
        }

        let mut obligations = Vec::new();
        if let Some(fields) = crate::sema::tycheck::derive::conditional_fields(self.gcx, record) {
            let caller_env = ParamEnv::new(goal.param_env.to_vec());
            let mut field_assumptions = goal.param_env.to_vec();
            if [StdItem::Encodable, StdItem::Decodable]
                .iter()
                .any(|item| self.gcx.std_item_def(*item) == Some(goal.interface_id))
                && matches!(record.target, TypeHead::Nominal(id)
                    if self.gcx.try_get_struct_definition(id).is_some() || self.gcx.try_get_enum_definition(id).is_some())
            {
                // Recursive fields may use the conformance under construction,
                // but unrelated leaves must still prove their own capability.
                // Scope this assumption to structural fields: declared where
                // clauses below retain the original, inductive environment.
                // Including it in param_env also keeps assumption-dependent
                // selection-cache entries separate from ordinary proofs.
                field_assumptions.push(Constraint::Bound {
                    ty: goal.self_ty,
                    interface: instantiated,
                });
            }
            let field_assumptions = self
                .gcx
                .store
                .arenas
                .global
                .alloc_slice_copy(&field_assumptions);
            let icx = Rc::new(InferCtx::new(self.gcx));
            for field in fields {
                let field = instantiate_ty_with_args(self.gcx, field, subst);
                let field = normalize_ty(icx.clone(), field, &caller_env);
                let arguments = crate::sema::tycheck::derive::component_interface_arguments(
                    self.gcx,
                    goal.interface_id,
                    field,
                );
                obligations.push(InterfaceGoal {
                    self_ty: field,
                    interface_args: arguments,
                    bindings: &[],
                    param_env: field_assumptions,
                    ..goal
                });
            }
            // Conditional synthesis cannot claim a derived interface while
            // its resolved super-conformances are unavailable on this type.
            for interface in
                super::ref_ops::collect_interface_with_superfaces(self.gcx, instantiated)
                    .into_iter()
                    .skip(1)
            {
                obligations.push(interface_ref_to_goal(
                    self.gcx,
                    interface,
                    goal.param_env,
                    goal.self_ty,
                ));
            }
        }
        for constraint in constraints {
            match constraint {
                Constraint::Bound { ty, interface } => {
                    let obligation = interface_ref_to_goal(self.gcx, interface, goal.param_env, ty);
                    obligations.push(obligation);
                }
                Constraint::TypeEquality(lhs, rhs) => {
                    if !constraint_type_equality_holds(self.gcx, lhs, rhs, &env) {
                        return None;
                    }
                }
            }
        }

        match self.obligations_satisfied(&obligations) {
            GoalSatisfaction::Satisfied => {}
            GoalSatisfaction::Ambiguous => {
                *saw_ambiguous_obligation = true;
                return None;
            }
            GoalSatisfaction::Unsatisfied => return None,
        }

        Some(ConfirmedCandidate {
            source: CandidateSource::Impl(record_id),
            extension_id: Some(record.extension),
            record_id: Some(record_id),
            subst,
            obligations,
        })
    }

    fn deduce_record_subst(
        &self,
        goal: InterfaceGoal<'ctx>,
        record: ConformanceRecord<'ctx>,
    ) -> Option<GenericArguments<'ctx>> {
        let generics = self.gcx.generics_of(record.extension);
        if generics.is_empty() {
            return Some(GenericArguments::empty());
        }

        let pattern_self = extension_self_ty(self.gcx, record.extension)?;
        let icx = Rc::new(InferCtx::new(self.gcx));
        let span = crate::span::Span::empty(crate::span::FileID::from_usize(0));
        let fresh_args = icx.fresh_args_for_def(record.extension, span);
        let unifier = TypeUnifier::new(icx.clone());

        let instantiated_self = instantiate_ty_with_args(self.gcx, pattern_self, fresh_args);
        let instantiated_self = normalize_aliases(self.gcx, instantiated_self);
        let normalized_goal_self = normalize_aliases(self.gcx, goal.self_ty);
        if unifier
            .unify(instantiated_self, normalized_goal_self)
            .is_err()
        {
            return None;
        }

        let instantiated_iface =
            instantiate_interface_ref_with_args(self.gcx, record.interface, fresh_args);
        let expected_iface = expand_goal_interface_ref(self.gcx, goal);
        if instantiated_iface.id != expected_iface.id
            || instantiated_iface.arguments.len() != expected_iface.arguments.len()
        {
            return None;
        }

        let instantiated_constraints = self
            .gcx
            .canonical_constraints_of(record.extension)
            .into_iter()
            .map(|constraint| {
                instantiate_constraint_with_args(self.gcx, constraint.value, fresh_args)
            })
            .collect();
        let env = ParamEnv::new(instantiated_constraints);

        for (lhs, rhs) in instantiated_iface
            .arguments
            .iter()
            .zip(expected_iface.arguments.iter())
        {
            if !unify_generic_argument(self.gcx, icx.clone(), &env, &unifier, *lhs, *rhs) {
                return None;
            }
        }

        if !instantiated_iface.bindings.is_empty() {
            for rhs in goal.bindings {
                let Some(lhs) = instantiated_iface
                    .bindings
                    .iter()
                    .find(|lhs| lhs.name == rhs.name)
                else {
                    return None;
                };
                if unifier.unify(lhs.ty, rhs.ty).is_err() {
                    return None;
                }
            }
        }

        let resolved = icx.resolve_args_if_possible(fresh_args);
        if !generic_args_contain_infer(resolved) {
            return Some(resolved);
        }

        refine_impl_args_from_constraints(
            self.gcx,
            icx.clone(),
            self.mode,
            record.extension,
            fresh_args,
            goal.param_env,
        );
        let resolved = icx.resolve_args_if_possible(fresh_args);
        if generic_args_contain_infer(resolved) {
            return None;
        }

        Some(resolved)
    }

    fn obligations_satisfied(&mut self, obligations: &[InterfaceGoal<'ctx>]) -> GoalSatisfaction {
        let mut saw_ambiguous = false;
        for goal in obligations.iter().copied() {
            match self.goal_is_satisfied(goal) {
                GoalSatisfaction::Satisfied => {}
                GoalSatisfaction::Ambiguous => saw_ambiguous = true,
                GoalSatisfaction::Unsatisfied => return GoalSatisfaction::Unsatisfied,
            }
        }

        if saw_ambiguous {
            GoalSatisfaction::Ambiguous
        } else {
            GoalSatisfaction::Satisfied
        }
    }

    fn goal_is_satisfied(&mut self, goal: InterfaceGoal<'ctx>) -> GoalSatisfaction {
        match self.select(goal) {
            SelectionResult::Selected(_) => GoalSatisfaction::Satisfied,
            SelectionResult::Ambiguous(_) => GoalSatisfaction::Ambiguous,
            SelectionResult::NoSolution(_) => GoalSatisfaction::Unsatisfied,
        }
    }
}

pub(crate) fn closure_clone_fields<'ctx>(gcx: Gcx<'ctx>, ty: Ty<'ctx>) -> Option<Vec<Ty<'ctx>>> {
    let TyKind::Closure {
        closure_def_id,
        captured_generics,
        ..
    } = ty.kind()
    else {
        return None;
    };
    let captures = gcx.get_closure_captures(closure_def_id)?;
    Some(
        captures
            .captures
            .iter()
            .map(|capture| capture.storage_ty(gcx, captured_generics))
            .collect(),
    )
}

/// Only intrinsic representations whose Clone operation is defined to be a
/// copy qualify. A user's Copy conformance says nothing about Clone, including
/// inside a tuple or fixed array. Nominal Clone always comes from a declaration.
pub(crate) fn builtin_copy_clone<'ctx>(gcx: Gcx<'ctx>, ty: Ty<'ctx>) -> bool {
    match normalize_aliases(gcx, ty).kind() {
        TyKind::Bool
        | TyKind::Rune
        | TyKind::String
        | TyKind::Int(_)
        | TyKind::UInt(_)
        | TyKind::Float(_)
        | TyKind::Pointer(..)
        | TyKind::Reference(_)
        | TyKind::FnPointer { .. }
        | TyKind::Never => true,
        TyKind::Tuple(fields) => fields.iter().all(|field| builtin_copy_clone(gcx, *field)),
        TyKind::Array { element, .. } => builtin_copy_clone(gcx, element),
        _ => false,
    }
}

enum GoalSatisfaction {
    Satisfied,
    Ambiguous,
    Unsatisfied,
}

fn interface_header_matches_goal<'ctx>(
    gcx: Gcx<'ctx>,
    interface: InterfaceReference<'ctx>,
    goal: InterfaceGoal<'ctx>,
    env: &ParamEnv<'ctx>,
) -> bool {
    let mut expected = goal.to_interface_ref(gcx);
    let expected_count = gcx.generics_of(goal.interface_id).total_count();
    if expected.arguments.len() < expected_count {
        let mut args = expected.arguments.to_vec();
        while args.len() < expected_count {
            args.push(GenericArgument::Type(goal.self_ty));
        }
        expected.arguments = gcx.store.interners.intern_generic_args(args);
    }

    if interface.id != expected.id || interface.arguments.len() != expected.arguments.len() {
        return false;
    }

    let icx = Rc::new(InferCtx::new(gcx));
    let unifier = TypeUnifier::new(icx.clone());
    interface
        .arguments
        .iter()
        .zip(expected.arguments.iter())
        .all(|(lhs, rhs)| unify_generic_argument(gcx, icx.clone(), env, &unifier, *lhs, *rhs))
}

fn refine_impl_args_from_constraints<'ctx>(
    gcx: Gcx<'ctx>,
    icx: Rc<InferCtx<'ctx>>,
    mode: SelectionMode,
    impl_id: crate::hir::DefinitionID,
    impl_args: GenericArguments<'ctx>,
    caller_assumptions: &'ctx [Constraint<'ctx>],
) {
    let constraints = gcx.canonical_constraints_of(impl_id);
    if constraints.is_empty() {
        return;
    }

    let instantiated: Vec<_> = constraints
        .into_iter()
        .map(|constraint| instantiate_constraint_with_args(gcx, constraint.value, impl_args))
        .collect();
    let env = ParamEnv::new(instantiated.clone());
    let caller_env = ParamEnv::new(caller_assumptions.to_vec());
    let unifier = TypeUnifier::new(icx.clone());

    let passes = instantiated.len().max(1) * 2;
    for _ in 0..passes {
        for constraint in &instantiated {
            match *constraint {
                Constraint::TypeEquality(lhs, rhs) => {
                    let lhs = normalize_ty(icx.clone(), lhs, &env);
                    let rhs = normalize_ty(icx.clone(), rhs, &env);
                    let _ = unifier.unify(lhs, rhs);
                }
                Constraint::Bound { ty: _, interface } => {
                    let resolved_interface_args = icx.resolve_args_if_possible(interface.arguments);
                    if generic_args_contain_infer(resolved_interface_args) {
                        continue;
                    }

                    let self_ty = match resolved_interface_args.get(0).copied() {
                        Some(GenericArgument::Type(self_ty)) => self_ty,
                        _ => continue,
                    };
                    let interface_args = if resolved_interface_args.len() > 1 {
                        gcx.store
                            .interners
                            .intern_generic_args_slice(&resolved_interface_args[1..])
                    } else {
                        GenericArguments::empty()
                    };
                    // An associated binding can constrain an impl parameter
                    // to a symbolic projection of a caller parameter. Asking
                    // for a concrete witness first loses this case (the caller
                    // has only a generic bound). Infer with the caller's
                    // assumptions, not the impl's own circular equality.
                    // This chooses substitutions only: confirmation below
                    // still proves every conformance obligation separately.
                    if let Some(requirements) = gcx.get_interface_requirements(interface.id) {
                        for binding in interface.bindings {
                            let Some(requirement) = requirements
                                .types
                                .iter()
                                .find(|requirement| requirement.name == binding.name)
                            else {
                                continue;
                            };
                            let projection = Ty::new(
                                TyKind::Alias {
                                    kind: AliasKind::Projection,
                                    def_id: requirement.id,
                                    args: resolved_interface_args,
                                },
                                gcx,
                            );
                            let actual = normalize_ty(icx.clone(), projection, &caller_env);
                            let expected = icx.resolve_vars_if_possible(binding.ty);
                            let _ = unifier.unify(expected, actual);
                        }
                    }
                    let goal = InterfaceGoal {
                        interface_id: interface.id,
                        self_ty,
                        interface_args,
                        // Build a witness from the interface header first, then
                        // use declared bindings below to refine unresolved impl args.
                        bindings: &[],
                        param_env: caller_assumptions,
                    };

                    let Ok(witness) = gcx.build_conformance_witness(goal, mode) else {
                        continue;
                    };
                    let Some(requirements) = gcx.get_interface_requirements(interface.id) else {
                        continue;
                    };

                    for binding in interface.bindings {
                        let Some(req) = requirements
                            .types
                            .iter()
                            .find(|req| req.name == binding.name)
                        else {
                            continue;
                        };
                        let Some(actual_ty) = witness.type_witnesses.get(&req.id).copied() else {
                            continue;
                        };
                        let expected_ty = normalize_ty(icx.clone(), binding.ty, &env);
                        let actual_ty = normalize_ty(icx.clone(), actual_ty, &env);
                        let _ = unifier.unify(expected_ty, actual_ty);
                    }
                }
            }
        }
    }
}

fn extension_self_ty<'ctx>(
    gcx: Gcx<'ctx>,
    extension_id: crate::hir::DefinitionID,
) -> Option<Ty<'ctx>> {
    if let Some(ty) = gcx.get_impl_self_ty(extension_id) {
        return Some(ty);
    }

    match gcx.definition_kind(extension_id) {
        crate::sema::resolve::models::DefinitionKind::Struct
        | crate::sema::resolve::models::DefinitionKind::Enum => Some(gcx.get_type(extension_id)),
        _ => None,
    }
}

fn constraint_type_equality_holds<'ctx>(
    gcx: Gcx<'ctx>,
    lhs: Ty<'ctx>,
    rhs: Ty<'ctx>,
    env: &ParamEnv<'ctx>,
) -> bool {
    let icx = Rc::new(InferCtx::new(gcx));
    let unifier = TypeUnifier::new(icx.clone());
    let lhs = normalize_ty(icx.clone(), lhs, env);
    let rhs = normalize_ty(icx.clone(), rhs, env);
    unifier.unify(lhs, rhs).is_ok()
}

fn generic_args_contain_infer(args: GenericArguments<'_>) -> bool {
    args.iter().any(generic_arg_contains_unresolved_inference)
}

fn goal_has_unresolved_types(goal: InterfaceGoal<'_>) -> bool {
    if ty_contains_unresolved_inference(goal.self_ty) {
        return true;
    }

    if goal
        .interface_args
        .iter()
        .any(generic_arg_contains_unresolved_inference)
    {
        return true;
    }

    goal.bindings
        .iter()
        .any(|binding| ty_contains_unresolved_inference(binding.ty))
}

fn unify_generic_argument<'ctx>(
    _gcx: Gcx<'ctx>,
    icx: Rc<InferCtx<'ctx>>,
    env: &ParamEnv<'ctx>,
    unifier: &TypeUnifier<'ctx, '_>,
    lhs: GenericArgument<'ctx>,
    rhs: GenericArgument<'ctx>,
) -> bool {
    match (lhs, rhs) {
        (GenericArgument::Type(lhs), GenericArgument::Type(rhs)) => {
            let lhs = icx.resolve_vars_if_possible(lhs);
            let rhs = icx.resolve_vars_if_possible(rhs);
            let lhs = normalize_ty(icx.clone(), lhs, env);
            let rhs = normalize_ty(icx.clone(), rhs, env);
            unifier.unify(lhs, rhs).is_ok()
        }
        (GenericArgument::Const(lhs), GenericArgument::Const(rhs)) => {
            let lhs = icx.resolve_const_if_possible(lhs);
            let rhs = icx.resolve_const_if_possible(rhs);
            unifier.unify_const(lhs, rhs).is_ok()
        }
        _ => false,
    }
}

fn expand_goal_interface_ref<'ctx>(
    gcx: Gcx<'ctx>,
    goal: InterfaceGoal<'ctx>,
) -> crate::sema::models::InterfaceReference<'ctx> {
    let mut iface = goal.to_interface_ref(gcx);
    let expected = gcx.generics_of(goal.interface_id).total_count();
    if iface.arguments.len() < expected {
        let mut args = iface.arguments.to_vec();
        while args.len() < expected {
            args.push(GenericArgument::Type(goal.self_ty));
        }
        iface.arguments = gcx.store.interners.intern_generic_args(args);
    }
    iface
}

#[cfg(test)]
mod recursive_proof_tests {
    #[test]
    fn blanket_requirements_cannot_prove_themselves_directly_or_indirectly() {
        for declarations in [
            "interface P {}\nconform[T] T to P where T: P {}",
            "interface P {}\ninterface Q {}\nconform[T] T to P where T: Q {}\nconform[T] T to Q where T: P {}",
        ] {
            let source = format!(
                "{declarations}\nstruct Counter {{}}\nfunc main() {{ var value: any P = Counter {{}}; }}"
            );
            let diagnostics = crate::test_support::analyze_script_diagnostics(&source);
            assert!(
                diagnostics
                    .iter()
                    .any(|d| d.message.contains("does not conform")),
                "{source}\n{diagnostics:#?}"
            );
            assert!(
                !diagnostics
                    .iter()
                    .any(|d| d.message.contains("ambiguous conformance")),
                "{diagnostics:#?}"
            );
        }
    }
}
