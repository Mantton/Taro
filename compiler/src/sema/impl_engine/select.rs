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

/// Return whether one declared conformance (rather than a synthesized builtin)
/// proves this goal. Sendable's structural fallback uses this to respect the
/// trust boundary of explicit marker impls on raw-storage owner types.
pub fn prove_declared_interface_goal<'ctx>(
    gcx: Gcx<'ctx>,
    goal: InterfaceGoal<'ctx>,
    mode: SelectionMode,
) -> GoalResult {
    if goal_has_unresolved_types(goal) {
        return GoalResult::NoSolution;
    }

    let mut selector = Selector::new(gcx, mode);
    let key = goal_key(gcx, goal, mode);
    if !selector.visiting.insert(key) {
        return GoalResult::Ambiguous;
    }
    let mut saw_ambiguous_obligation = false;
    let candidates = selector.collect_declared_candidates(goal, &mut saw_ambiguous_obligation);
    selector.visiting.remove(&key);

    match candidates.len() {
        0 if saw_ambiguous_obligation => GoalResult::Ambiguous,
        0 => GoalResult::NoSolution,
        1 => GoalResult::Proven,
        _ => GoalResult::Ambiguous,
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
    let instantiated = instantiate_ty_with_args(gcx, pattern_self, fresh_args);
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

        let key = goal_key(self.gcx, goal, self.mode);
        if let Some(cached) = self.gcx.get_selection_cache(self.gcx.package_index(), key) {
            return cached;
        }

        if !self.visiting.insert(key) {
            return SelectionResult::Ambiguous(Vec::new());
        }

        let (mut candidates, saw_ambiguous_obligation) = self.collect_candidates(goal);
        let mut viable = Vec::new();
        viable.append(&mut candidates);

        self.visiting.remove(&key);

        viable.sort_by_key(|candidate| match candidate.source {
            CandidateSource::Impl(id) => (id.package.index(), id.index as usize),
            CandidateSource::ParamEnv => (usize::MAX - 4, 0),
            CandidateSource::BuiltinTuple => (usize::MAX - 3, 0),
            CandidateSource::BuiltinClosure => (usize::MAX - 2, 0),
            CandidateSource::BuiltinClone => (usize::MAX - 1, 0),
            CandidateSource::BuiltinCopy => (usize::MAX, 0),
            CandidateSource::BuiltinSendable => (usize::MAX, 1),
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

        if let Some(candidate) = self.builtin_tuple_candidate(goal) {
            out.push(candidate);
        }

        if let Some(candidate) = self.builtin_closure_candidate(goal) {
            out.push(candidate);
        }

        if let Some(candidate) = self.builtin_clone_candidate(goal) {
            out.push(candidate);
        }

        if let Some(candidate) = self.builtin_copy_candidate(goal) {
            out.push(candidate);
        }

        if let Some(candidate) = self.builtin_sendable_candidate(goal) {
            out.push(candidate);
        }

        if let Some(candidate) = self.param_env_candidate(goal) {
            out.push(candidate);
        }

        out.extend(self.collect_declared_candidates(goal, &mut saw_ambiguous_obligation));

        if self.gcx.std_item_def(StdItem::Sendable) == Some(goal.interface_id)
            && out
                .iter()
                .any(|candidate| matches!(candidate.source, CandidateSource::Impl(_)))
        {
            // Sendable has a structural builtin candidate, but an explicit
            // marker impl is the type author's trust boundary for hidden raw
            // storage (for example List's managed buffer pointer). Once such
            // an impl applies, keeping both candidates would report a false
            // ambiguity for every structurally-Sendable instantiation of a
            // conditional container like Result[T, E]. Coherence still checks
            // overlaps between declared impls; only the synthesized fallback
            // is suppressed here.
            out.retain(|candidate| candidate.source != CandidateSource::BuiltinSendable);
        }

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
        let mut records: Vec<(ConformanceRecordId, ConformanceRecord<'ctx>)> =
            self.gcx.collect_from_databases(|db| {
                db.conformance_by_interface
                    .get(&goal.interface_id)
                    .into_iter()
                    .flat_map(|ids| ids.iter())
                    .filter_map(|id| {
                        let record = db.conformance_records.get(id)?;
                        (record.target.is_blanket() || head == Some(record.target))
                            .then_some((*id, *record))
                    })
                    .collect()
            });
        records.sort_by_key(|(id, _)| (id.package.index(), id.index));
        let mut seen_ids = FxHashSet::default();

        for (record_id, record) in records {
            if !seen_ids.insert(record_id) {
                continue;
            }
            if let Some(candidate) =
                self.confirm_record_candidate(goal, record_id, record, saw_ambiguous_obligation)
            {
                out.push(candidate);
            }
        }
        out
    }

    fn param_env_candidate(&self, goal: InterfaceGoal<'ctx>) -> Option<ConfirmedCandidate<'ctx>> {
        for constraint in goal.param_env {
            let Constraint::Bound { ty, interface } = *constraint else {
                continue;
            };

            if ty != goal.self_ty {
                continue;
            }

            if interface_ref_matches_goal(self.gcx, interface, goal)
                && self.param_env_satisfies_goal_bindings(goal)
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

    fn builtin_copy_candidate(
        &self,
        goal: InterfaceGoal<'ctx>,
    ) -> Option<ConfirmedCandidate<'ctx>> {
        let copy_id = self.gcx.std_item_def(StdItem::Copy)?;
        if goal.interface_id != copy_id || !self.gcx.is_type_builtin_copyable(goal.self_ty) {
            return None;
        }
        Some(ConfirmedCandidate {
            source: CandidateSource::BuiltinCopy,
            extension_id: None,
            record_id: None,
            subst: GenericArguments::empty(),
            obligations: Vec::new(),
        })
    }

    fn builtin_clone_candidate(
        &self,
        goal: InterfaceGoal<'ctx>,
    ) -> Option<ConfirmedCandidate<'ctx>> {
        let clone_id = self.gcx.std_item_def(StdItem::Clone)?;
        if goal.interface_id != clone_id || !self.gcx.is_type_copyable(goal.self_ty) {
            return None;
        }
        Some(ConfirmedCandidate {
            source: CandidateSource::BuiltinClone,
            extension_id: None,
            record_id: None,
            subst: GenericArguments::empty(),
            obligations: Vec::new(),
        })
    }

    fn builtin_sendable_candidate(
        &self,
        goal: InterfaceGoal<'ctx>,
    ) -> Option<ConfirmedCandidate<'ctx>> {
        let sendable_id = self.gcx.std_item_def(StdItem::Sendable)?;
        if goal.interface_id != sendable_id || !self.gcx.is_type_sendable(goal.self_ty) {
            return None;
        }
        Some(ConfirmedCandidate {
            source: CandidateSource::BuiltinSendable,
            extension_id: None,
            record_id: None,
            subst: GenericArguments::empty(),
            obligations: Vec::new(),
        })
    }

    fn builtin_closure_candidate(
        &self,
        goal: InterfaceGoal<'ctx>,
    ) -> Option<ConfirmedCandidate<'ctx>> {
        let TyKind::Closure {
            kind,
            inputs,
            output,
            ..
        } = goal.self_ty.kind()
        else {
            return None;
        };

        let fn_id = self.gcx.std_item_def(StdItem::Fn);
        let fn_mut_id = self.gcx.std_item_def(StdItem::FnMut);
        let fn_once_id = self.gcx.std_item_def(StdItem::FnOnce);
        let async_fn_id = self.gcx.std_item_def(StdItem::AsyncFn);
        let async_fn_mut_id = self.gcx.std_item_def(StdItem::AsyncFnMut);
        let async_fn_once_id = self.gcx.std_item_def(StdItem::AsyncFnOnce);
        let allowed = if fn_id == Some(goal.interface_id) {
            matches!(kind, crate::sema::models::ClosureKind::Fn)
        } else if fn_mut_id == Some(goal.interface_id) {
            matches!(
                kind,
                crate::sema::models::ClosureKind::Fn | crate::sema::models::ClosureKind::FnMut
            )
        } else if fn_once_id == Some(goal.interface_id) {
            matches!(
                kind,
                crate::sema::models::ClosureKind::Fn
                    | crate::sema::models::ClosureKind::FnMut
                    | crate::sema::models::ClosureKind::FnOnce
            )
        } else if async_fn_id == Some(goal.interface_id) {
            matches!(kind, crate::sema::models::ClosureKind::AsyncFn)
        } else if async_fn_mut_id == Some(goal.interface_id) {
            matches!(
                kind,
                crate::sema::models::ClosureKind::AsyncFn
                    | crate::sema::models::ClosureKind::AsyncFnMut
            )
        } else if async_fn_once_id == Some(goal.interface_id) {
            matches!(
                kind,
                crate::sema::models::ClosureKind::AsyncFn
                    | crate::sema::models::ClosureKind::AsyncFnMut
                    | crate::sema::models::ClosureKind::AsyncFnOnce
            )
        } else {
            false
        };
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
            source: CandidateSource::BuiltinClosure,
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
        for constraint in constraints {
            match constraint {
                Constraint::Bound { ty, interface } => {
                    let obligation = interface_ref_to_goal(self.gcx, interface, goal.param_env, ty);
                    if obligation.interface_id == goal.interface_id
                        && obligation.self_ty == goal.self_ty
                        && obligation.interface_args == goal.interface_args
                        && obligation.bindings == goal.bindings
                    {
                        continue;
                    }
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
            SelectionResult::Ambiguous(_) if self.mode == SelectionMode::Coherence => {
                GoalSatisfaction::Satisfied
            }
            SelectionResult::Ambiguous(_) => GoalSatisfaction::Ambiguous,
            SelectionResult::NoSolution(_) => GoalSatisfaction::Unsatisfied,
        }
    }

    fn param_env_satisfies_goal_bindings(&self, goal: InterfaceGoal<'ctx>) -> bool {
        if goal.bindings.is_empty() {
            return true;
        }

        let Some(requirements) = self.gcx.get_interface_requirements(goal.interface_id) else {
            return false;
        };
        let env = ParamEnv::new(goal.param_env.to_vec());
        let iface = goal.to_interface_ref(self.gcx);
        let icx = Rc::new(InferCtx::new(self.gcx));
        let unifier = TypeUnifier::new(icx.clone());

        for binding in goal.bindings {
            let Some(assoc) = requirements
                .types
                .iter()
                .find(|assoc| assoc.name == binding.name)
            else {
                return false;
            };

            let projection = Ty::new(
                TyKind::Alias {
                    kind: AliasKind::Projection,
                    def_id: assoc.id,
                    args: iface.arguments,
                },
                self.gcx,
            );
            let expected = normalize_ty(icx.clone(), projection, &env);
            let actual = normalize_ty(icx.clone(), binding.ty, &env);

            if unifier.unify(expected, actual).is_err() {
                return false;
            }
        }

        true
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
                    let goal = InterfaceGoal {
                        interface_id: interface.id,
                        self_ty,
                        interface_args,
                        // Build a witness from the interface header first, then
                        // use declared bindings below to refine unresolved impl args.
                        bindings: &[],
                        param_env: &[],
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

    goal.bindings.iter().any(|binding| {
        ty_contains_unresolved_inference(binding.ty) || binding.ty.needs_instantiation()
    })
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
