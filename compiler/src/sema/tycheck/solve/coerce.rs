use crate::{
    hir::{Mutability, NodeID},
    sema::{
        error::TypeError,
        models::{
            AliasKind, GenericArgument, InferTy, InterfaceReference, SelectionError, SelectionMode,
            Ty, TyKind,
        },
        tycheck::utils::unresolved::ty_contains_unresolved_inference,
    },
    span::{Span, Spanned},
};

use super::{Adjustment, ConstraintSolver, Goal, Obligation, SolverResult};

#[cfg(test)]
mod nil_pointer_tests {
    #[test]
    fn nil_pointer_returns_and_locals_have_resolved_mir_types() {
        let errors = crate::test_support::analyze_script_mir_diagnostics(
            r#"
func nullConst() -> *const int32 { nil }
func nullMut() -> *mut int32 { nil }
func nullGeneric[T]() -> *const T { nil }
func identity[T](_ value: T) -> T { value }
func main() {
    var pointer: *const int32 = nil
    var mutable: *mut int32 = nil
    pointer = nullConst()
    mutable = nullMut()
    var generic = nullGeneric[bool]()
    var contextual: *const int32 = identity({ nil })
}
"#,
        );
        assert!(errors.is_empty(), "{errors:#?}");
    }
}

impl<'ctx> ConstraintSolver<'ctx> {
    pub(super) fn solve_opened_conforms(
        &mut self,
        location: Span,
        source: crate::hir::DefinitionID,
        arguments: crate::sema::models::GenericArguments<'ctx>,
        template: InterfaceReference<'ctx>,
        ty: Ty<'ctx>,
        interface: InterfaceReference<'ctx>,
    ) -> SolverResult<'ctx> {
        let ty = self.structurally_resolve(ty);
        let (interface, unresolved) = self.resolve_interface_ref(interface);
        if ty_contains_unresolved_inference(ty) {
            return SolverResult::Deferred;
        }
        if let TyKind::BoxedExistential { interfaces } = ty.kind() {
            let arguments = self.icx.resolve_vars_if_possible(arguments);
            if let Ok(Some(plan)) =
                crate::sema::lowering::erased_opening::plan(self.gcx(), source, arguments)
                && plan.erased == ty
            {
                let expected =
                    crate::sema::tycheck::utils::erased_self::bind(self.gcx(), interface, ty);
                let mut provided = Vec::new();
                for root in interfaces {
                    for raw in self.collect_interface_with_supers(*root) {
                        if !crate::sema::lowering::erased_opening::relative_self_matches_template(
                            self.gcx(),
                            template,
                            raw,
                            plan.parameter,
                        ) {
                            continue;
                        }
                        let candidate =
                            crate::sema::tycheck::utils::erased_self::bind(self.gcx(), raw, ty);
                        if !provided.contains(&candidate)
                            && self.existential_interface_ref_matches_with_mode(
                                expected, candidate, unresolved, false,
                            )
                        {
                            provided.push(candidate);
                        }
                    }
                }
                if provided.len() == 1
                    && self.existential_interface_ref_matches_with_mode(
                        expected,
                        provided[0],
                        unresolved,
                        true,
                    )
                {
                    return SolverResult::Solved(vec![Obligation {
                        location,
                        goal: Goal::ValidateOpening { source, arguments },
                    }]);
                }
                if provided.len() > 1 {
                    return SolverResult::Error(vec![Spanned::new(
                        TypeError::AmbiguousOverload,
                        location,
                    )]);
                }
            }
        }
        self.solve_conforms(location, ty, interface)
    }

    pub(super) fn solve_validate_opening(
        &mut self,
        location: Span,
        source: crate::hir::DefinitionID,
        arguments: crate::sema::models::GenericArguments<'ctx>,
    ) -> SolverResult<'ctx> {
        let arguments = self.icx.resolve_vars_if_possible(arguments);
        if arguments.iter().any(|argument| match argument {
            GenericArgument::Type(ty) => ty.contains_inference(),
            GenericArgument::Const(value) => {
                matches!(value.kind, crate::sema::models::ConstKind::Infer(_))
                    || value.ty.contains_inference()
            }
        }) {
            return SolverResult::Deferred;
        }
        match crate::sema::lowering::erased_opening::plan(self.gcx(), source, arguments) {
            Ok(_) => SolverResult::Solved(vec![]),
            Err(_) => SolverResult::Error(vec![Spanned::new(
                TypeError::ErasedMethodUsesHiddenType,
                location,
            )]),
        }
    }

    pub fn solve_coerce(
        &mut self,
        location: Span,
        node_id: NodeID,
        from: Ty<'ctx>,
        to: Ty<'ctx>,
    ) -> SolverResult<'ctx> {
        let from = self.structurally_resolve(from);
        let to = self.structurally_resolve(to);

        if from == to || matches!(from.kind(), TyKind::Never) {
            return SolverResult::Solved(vec![]);
        }

        let ancestor = |source, target: Ty<'ctx>| {
            let TyKind::Adt(target_def, _) = target.kind() else {
                return None;
            };
            self.gcx()
                .class_ancestry(source)
                .into_iter()
                .find(|ty| matches!(ty.kind(),TyKind::Adt(def,_) if def.id == target_def.id))
        };
        if from != to
            && let Some(base) = ancestor(from, to)
            && base != from
        {
            self.coercions += 1;
            self.append_adjustments(node_id, vec![Adjustment::ClassUpcast { to }]);
            return self.solve_constraint_equality(location, base, to);
        }
        if let Some(result) = self.solve_existential_upcast(location, node_id, from, to) {
            if matches!(result, SolverResult::Solved(_)) {
                self.coercions += 1;
            }
            return result;
        }

        if let Some(result) = self.solve_boxing_coercion(location, node_id, from, to) {
            if matches!(result, SolverResult::Solved(_)) {
                self.coercions += 1;
            }
            return result;
        }

        if let Some(result) = self.solve_pointer_coercion(location, node_id, from, to) {
            return result;
        }

        // Closure to function pointer coercion: || -> T to fn() -> T
        if let Some(result) = self.solve_closure_to_fn_pointer(location, node_id, from, to) {
            if matches!(result, SolverResult::Solved(_)) {
                self.coercions += 1;
            }
            return result;
        }

        // Closure to type parameter with Fn bound coercion
        if let Some(result) = self.solve_callable_to_fn_bound_param(location, from, to) {
            return result;
        }

        // Nil coercion: NilVar -> Optional[T] or NilVar -> *T
        if let Some(result) = self.solve_nil_coercion(location, node_id, from, to) {
            if matches!(result, SolverResult::Solved(_)) {
                self.coercions += 1;
            }
            return result;
        }

        // Optional wrapping: T -> Optional[T]
        if let Some(result) = self.solve_optional_wrapping(location, node_id, from, to) {
            if matches!(result, SolverResult::Solved(_)) {
                self.coercions += 1;
            }
            return result;
        }

        // A known Result is never implicitly nested or unwrapped. Ordinary
        // Result equality below still infers its generic arguments normally.
        if let Some(result) = self.solve_result_success_wrapping(location, node_id, from, to) {
            if matches!(result, SolverResult::Solved(_)) {
                self.coercions += 1;
            }
            return result;
        }

        // Minimal coercion: fall back to constraint-equality so unresolved
        // projections (e.g. `T.Item` with unresolved `T`) defer instead of
        // producing an early hard mismatch.
        self.solve_constraint_equality(location, to, from)
    }

    fn solve_boxing_coercion(
        &mut self,
        location: Span,
        node_id: NodeID,
        from: Ty<'ctx>,
        to: Ty<'ctx>,
    ) -> Option<SolverResult<'ctx>> {
        let TyKind::BoxedExistential { interfaces } = to.kind() else {
            return None;
        };

        // When the source type is an inference variable and we're coercing to an
        // existential, bind the variable directly to the existential type.
        // This handles function return type inference: `let x = makeSomething()`
        // where `makeSomething()` returns `any Interface`.
        if from.is_infer() {
            return Some(match from.kind() {
                // Keep existing behavior for general type inference variables.
                TyKind::Infer(InferTy::TyVar(_)) => self.solve_equality(location, from, to),
                // Let numeric inference resolve to a concrete numeric type before
                // checking existential conformance (e.g. `printf("%d", 1)`).
                TyKind::Infer(InferTy::IntVar(_) | InferTy::FloatVar(_)) => SolverResult::Deferred,
                // Preserve prior behavior for remaining inference kinds.
                _ => self.solve_equality(location, from, to),
            });
        }

        // Existential-to-existential: use equality check for compatible interfaces
        if matches!(from.kind(), TyKind::BoxedExistential { .. }) {
            return Some(self.solve_equality(location, to, from));
        }

        // Every source uses the conformance engine, including conditional ADT
        // implementations. Bind erased Self before checking receiver-relative
        // defaults instead of matching only a nominal type head.
        let obligations = interfaces
            .iter()
            .map(|interface| {
                let interface = crate::sema::impl_engine::ref_ops::interface_ref_with_self(
                    self.gcx(),
                    from,
                    *interface,
                );
                Obligation {
                    location,
                    goal: Goal::Conforms {
                        ty: from,
                        interface,
                    },
                }
            })
            .collect();
        self.record_adjustments(
            node_id,
            vec![Adjustment::BoxExistential { from, interfaces }],
        );
        Some(SolverResult::Solved(obligations))
    }

    fn solve_existential_upcast(
        &mut self,
        location: Span,
        node_id: NodeID,
        from: Ty<'ctx>,
        to: Ty<'ctx>,
    ) -> Option<SolverResult<'ctx>> {
        let TyKind::BoxedExistential {
            interfaces: from_ifaces,
        } = from.kind()
        else {
            return None;
        };
        let TyKind::BoxedExistential {
            interfaces: to_ifaces,
        } = to.kind()
        else {
            return None;
        };

        if from == to {
            return Some(SolverResult::Solved(vec![]));
        }

        if let Some(matches) = self.collect_existential_matches(from_ifaces, to_ifaces, false, true)
        {
            let obligations = self.interface_match_obligations(location, &matches);
            self.record_adjustments(node_id, vec![Adjustment::ExistentialUpcast { from, to }]);
            return Some(SolverResult::Solved(obligations));
        }

        if let Some(matches) = self.collect_existential_matches(from_ifaces, to_ifaces, true, true)
        {
            let obligations = self.interface_match_obligations(location, &matches);
            self.record_adjustments(node_id, vec![Adjustment::ExistentialUpcast { from, to }]);
            return Some(SolverResult::Solved(obligations));
        }

        Some(self.solve_equality(location, to, from))
    }

    /// Coerce a non-capturing closure to a function pointer.
    /// This is only valid when the closure captures nothing (empty environment).
    fn solve_closure_to_fn_pointer(
        &mut self,
        location: Span,
        node_id: NodeID,
        from: Ty<'ctx>,
        to: Ty<'ctx>,
    ) -> Option<SolverResult<'ctx>> {
        // Check if source is a closure type
        let TyKind::Closure {
            closure_def_id,
            kind,
            inputs: closure_inputs,
            output: closure_output,
            ..
        } = from.kind()
        else {
            return None;
        };
        if kind != crate::sema::models::ClosureKind::Fn {
            return None;
        }

        // Check if target is a function pointer type
        let TyKind::FnPointer {
            effects,
            inputs: fn_inputs,
            output: fn_output,
        } = to.kind()
        else {
            return None;
        };

        if effects != Default::default() {
            return None;
        }

        // Check if the closure has no captures
        let gcx = self.gcx();
        if let Some(captures) = gcx.get_closure_captures(closure_def_id) {
            if !captures.captures.is_empty() {
                // Closure has captures - cannot coerce to fn pointer
                return None;
            }
        }

        // Check that signatures match (same number of inputs and compatible types)
        if closure_inputs.len() != fn_inputs.len() {
            return None;
        }

        // Build equality constraints for inputs and output
        let mut obligations = Vec::new();
        for (closure_in, fn_in) in closure_inputs.iter().zip(fn_inputs.iter()) {
            obligations.push(super::Obligation {
                location,
                goal: super::Goal::Equal(*closure_in, *fn_in),
            });
        }
        obligations.push(super::Obligation {
            location,
            goal: super::Goal::Equal(closure_output, fn_output),
        });

        // Record the adjustment for codegen
        self.record_adjustments(
            node_id,
            vec![Adjustment::ClosureToFnPointer { closure_def_id }],
        );

        Some(SolverResult::Solved(obligations))
    }

    fn solve_pointer_coercion(
        &mut self,
        location: Span,
        node_id: NodeID,
        from: Ty<'ctx>,
        to: Ty<'ctx>,
    ) -> Option<SolverResult<'ctx>> {
        // Raw pointer coercion: *mut T -> *T
        if let (
            TyKind::Pointer(from_inner, Mutability::Mutable),
            TyKind::Pointer(to_inner, Mutability::Immutable),
        ) = (from.kind(), to.kind())
        {
            self.coercions += 1;
            self.record_adjustments(node_id, vec![Adjustment::PointerToConst]);
            return Some(self.solve_equality(location, to_inner, from_inner));
        }

        None
    }

    fn collect_existential_matches(
        &self,
        from_ifaces: &'ctx [InterfaceReference<'ctx>],
        to_ifaces: &'ctx [InterfaceReference<'ctx>],
        include_supers: bool,
        infer: bool,
    ) -> Option<Vec<(InterfaceReference<'ctx>, InterfaceReference<'ctx>)>> {
        let mut matches_out = Vec::with_capacity(to_ifaces.len());

        for target in to_ifaces {
            let mut matched = None;

            for source in from_ifaces {
                if self.existential_interface_ref_matches_with_mode(*target, *source, infer, false)
                {
                    matched = Some(*source);
                    break;
                }

                if include_supers {
                    for candidate in self
                        .collect_interface_with_supers(*source)
                        .into_iter()
                        .skip(1)
                    {
                        if self.existential_interface_ref_matches_with_mode(
                            *target, candidate, infer, false,
                        ) {
                            matched = Some(candidate);
                            break;
                        }
                    }
                }

                if matched.is_some() {
                    break;
                }
            }

            let actual = matched?;
            matches_out.push((*target, actual));
        }

        Some(matches_out)
    }

    fn interface_match_obligations(
        &self,
        location: Span,
        matches: &[(InterfaceReference<'ctx>, InterfaceReference<'ctx>)],
    ) -> Vec<Obligation<'ctx>> {
        let mut obligations = Vec::new();

        for (expected, actual) in matches {
            let expected_args = if expected.arguments.len() > 0 {
                &expected.arguments[1..]
            } else {
                &expected.arguments
            };
            let actual_args = if actual.arguments.len() > 0 {
                &actual.arguments[1..]
            } else {
                &actual.arguments
            };

            for (expected_arg, actual_arg) in expected_args.iter().zip(actual_args.iter()) {
                match (expected_arg, actual_arg) {
                    (GenericArgument::Type(expected_ty), GenericArgument::Type(actual_ty)) => {
                        obligations.push(Obligation {
                            location,
                            goal: Goal::ConstraintEqual(*expected_ty, *actual_ty),
                        });
                    }
                    (
                        GenericArgument::Const(expected_const),
                        GenericArgument::Const(actual_const),
                    ) => {
                        let _ = self.unify_const(*expected_const, *actual_const);
                    }
                    _ => {}
                }
            }
        }

        obligations
    }

    fn interface_args_match_with_inference(
        &self,
        expected: InterfaceReference<'ctx>,
        actual: InterfaceReference<'ctx>,
    ) -> bool {
        let expected_args = if expected.arguments.len() > 0 {
            &expected.arguments[1..]
        } else {
            &expected.arguments
        };
        let actual_args = if actual.arguments.len() > 0 {
            &actual.arguments[1..]
        } else {
            &actual.arguments
        };

        if expected_args.len() != actual_args.len() {
            return false;
        }

        expected_args
            .iter()
            .zip(actual_args.iter())
            .all(|(expected_arg, actual_arg)| {
                self.unify_interface_args_with_inference(*expected_arg, *actual_arg)
            })
    }

    fn unify_interface_args_with_inference(
        &self,
        expected: GenericArgument<'ctx>,
        actual: GenericArgument<'ctx>,
    ) -> bool {
        match (expected, actual) {
            (GenericArgument::Type(expected_ty), GenericArgument::Type(actual_ty)) => {
                self.unify(expected_ty, actual_ty).is_ok()
            }
            (GenericArgument::Const(expected_const), GenericArgument::Const(actual_const)) => {
                self.unify_const(expected_const, actual_const).is_ok()
            }
            _ => false,
        }
    }

    fn existential_interface_ref_matches_with_mode(
        &self,
        expected: InterfaceReference<'ctx>,
        actual: InterfaceReference<'ctx>,
        infer: bool,
        commit: bool,
    ) -> bool {
        if !infer {
            return self.existential_interface_ref_matches(expected, actual);
        }

        let matches = self
            .icx
            .probe(|_| self.existential_interface_ref_matches_with_inference(expected, actual));
        if !matches {
            return false;
        }

        if commit {
            return self.existential_interface_ref_matches_with_inference(expected, actual);
        }

        true
    }

    fn existential_interface_ref_matches_with_inference(
        &self,
        expected: InterfaceReference<'ctx>,
        actual: InterfaceReference<'ctx>,
    ) -> bool {
        expected.id == actual.id
            && self.interface_args_match_with_inference(expected, actual)
            && self.interface_bindings_match_with_inference(expected, actual)
    }

    fn interface_ref_matches(
        &self,
        expected: InterfaceReference<'ctx>,
        actual: InterfaceReference<'ctx>,
    ) -> bool {
        crate::sema::impl_engine::ref_ops::interface_ref_matches(
            expected,
            actual,
            crate::sema::impl_engine::ref_ops::InterfaceRefMatch::Header,
        )
    }

    fn existential_interface_ref_matches(
        &self,
        expected: InterfaceReference<'ctx>,
        actual: InterfaceReference<'ctx>,
    ) -> bool {
        crate::sema::impl_engine::ref_ops::interface_ref_matches(
            expected,
            actual,
            crate::sema::impl_engine::ref_ops::InterfaceRefMatch::Logical,
        )
    }

    fn interface_bindings_match_with_inference(
        &self,
        expected: InterfaceReference<'ctx>,
        actual: InterfaceReference<'ctx>,
    ) -> bool {
        expected.bindings.iter().all(|expected_binding| {
            actual.bindings.iter().any(|actual_binding| {
                expected_binding.name == actual_binding.name
                    && self.unify(expected_binding.ty, actual_binding.ty).is_ok()
            })
        })
    }

    pub fn solve_conforms(
        &mut self,
        location: Span,
        ty: Ty<'ctx>,
        interface: InterfaceReference<'ctx>,
    ) -> SolverResult<'ctx> {
        let ty = self.structurally_resolve(ty);
        let (interface, has_infer) = self.resolve_interface_ref(interface);
        // Generic defaults may resolve only after the boxing goal was built.
        // Rebind their erased Self now, rather than leaving a newly resolved
        // receiver-relative argument as an unrelated hidden type.
        let interface = crate::sema::tycheck::utils::erased_self::bind(
            self.gcx(),
            interface,
            interface.self_ty().unwrap_or(ty),
        );

        if ty.is_error() {
            return SolverResult::Solved(vec![]);
        }

        // Special case: closures implicitly implement Fn/AsyncFn.
        // Check this BEFORE deferring on has_infer, because the Equal obligations
        // we generate will bind any inference variables in the interface (like output type U).
        if let Some(result) = self.solve_callable_fn_conformance(location, ty, interface) {
            return result;
        }

        // Now defer if interface has unresolved inference variables
        // (except for closure conformance which we already handled)
        if has_infer {
            if let Some(obligations) = self.infer_conformance_arguments(ty, interface, location) {
                return SolverResult::Solved(obligations);
            }
            return SolverResult::Deferred;
        }

        match ty.kind() {
            TyKind::Infer(_) => return SolverResult::Deferred,
            TyKind::Parameter(_) => {
                let bounds = self.bounds_for_type_in_scope(ty);
                let directly_bounded = bounds.iter().any(|bound| {
                    // Bounds can enter the parameter environment before call
                    // inference finishes. Resolve their arguments at the point
                    // of comparison so a known bound such as `SameAs[?T]`, with
                    // `?T = Concrete`, is not mistaken for a missing bound.
                    let (bound, _) = self.resolve_interface_ref(*bound);
                    self.interface_ref_matches(interface, bound)
                        || self
                            .collect_interface_with_supers(bound)
                            .into_iter()
                            .skip(1)
                            .any(|candidate| self.interface_ref_matches(interface, candidate))
                });
                if directly_bounded {
                    return SolverResult::Solved(vec![]);
                }
                // A different bound may imply this interface through a
                // conditional blanket impl, so let declared selection below
                // attempt that proof. Treating every parameter as conforming
                // made recursive or entirely missing bounds silently succeed.
            }
            TyKind::Adt(def, _)
                if self
                    .gcx()
                    .std_item_def(crate::hir::StdItem::Iterable)
                    .is_some_and(|iterable_id| interface.id == iterable_id)
                    && self
                        .gcx()
                        .std_item_def(crate::hir::StdItem::Range)
                        .is_some_and(|range_id| def.id == range_id)
                    || self
                        .gcx()
                        .std_item_def(crate::hir::StdItem::Iterable)
                        .is_some_and(|iterable_id| interface.id == iterable_id)
                        && self
                            .gcx()
                            .std_item_def(crate::hir::StdItem::ClosedRange)
                            .is_some_and(|range_id| def.id == range_id) =>
            {
                // Range syntax diagnostics already report element Step issues; avoid emitting
                // a second cascading "not Iterable" diagnostic for the same source expression.
                return SolverResult::Solved(vec![]);
            }
            TyKind::Adt(def, args)
                if args.is_empty() && !self.gcx().generics_of(def.id).is_empty() =>
            {
                // During declaration-time checks we can see generic ADTs without explicit
                // substitution args (e.g. `Foo[T]` represented as `Foo`). This malformed
                // representation is validated elsewhere (conformance collection/derive checks).
                // Defer instead of reporting solved so we do not drop conformance obligations.
                return SolverResult::Deferred;
            }
            TyKind::Adt(def, args)
                if def.id == self.current_def
                    && args.iter().any(generic_arg_needs_instantiation) =>
            {
                // Declaration-time self conformance checks for generic nominal types
                // (e.g. `struct S[T]: Hashable`) can carry unresolved declaration
                // parameters that are validated via the type's own generic bounds.
                // Defer instead of marking solved so use-site obligations are still
                // forced through concrete proof once instantiations are known.
                return SolverResult::Deferred;
            }
            TyKind::Alias {
                kind: AliasKind::Projection | AliasKind::Opaque,
                ..
            } => {
                // A projection on a generic parameter is ready for a bound
                // check. Only actual inference variables justify deferring.
                if ty_contains_unresolved_inference(ty) {
                    return SolverResult::Deferred;
                }

                let mut satisfied = self
                    .bounds_for_type_in_scope(ty)
                    .into_iter()
                    .any(|bound| self.interface_ref_matches(interface, bound));

                if !satisfied {
                    satisfied = self.bounds_for_type_in_scope(ty).into_iter().any(|bound| {
                        self.collect_interface_with_supers(bound)
                            .into_iter()
                            .skip(1)
                            .any(|candidate| self.interface_ref_matches(interface, candidate))
                    });
                }

                if satisfied {
                    return SolverResult::Solved(vec![]);
                }
            }
            TyKind::BoxedExistential { .. } => {
                if self.gcx().std_item_def(crate::hir::StdItem::AnyObject) == Some(interface.id)
                    && self
                        .gcx()
                        .existential_requires_interface(ty, crate::hir::StdItem::AnyObject)
                {
                    return SolverResult::Solved(vec![]);
                }
                // Its witness proves conformance of the hidden payload only.
                // A direct generic call can open that payload through the
                // separate OpenedConforms goal; no general any-P:P rule exists.
                let error = Spanned::new(TypeError::NonConformance { ty, interface }, location);
                return SolverResult::Error(vec![error]);
            }
            _ => {}
        }

        let self_ty = interface.self_ty().unwrap_or(ty);
        // Conditional conformances can introduce recursive obligations over a
        // caller parameter (for example `Wrapper[T]: Input where T: Reader`).
        // Passing an empty environment here discarded the in-scope `T: Reader`
        // proof, so the declared conformance was incorrectly rejected inside
        // generic function bodies. Pass the definition's canonical assumptions
        // so selection can discharge those obligations through ParamEnv.
        // Only definition-level assumptions belong here. Requirements from a
        // generic callee are added to `param_env` as obligations during call
        // checking; treating those as assumptions would let an invalid call
        // prove its own required conformance.
        let goal = interface.to_goal_with_self_ty(self.gcx(), self.assumption_constraints, self_ty);
        // A definition-level bound proves conformance even when its subject
        // is compound (&T, for example). Its concrete methods are selected
        // after specialization; requesting a concrete witness here rejects
        // valid generic bodies. Pending call requirements are not assumptions.
        if matches!(
            self.gcx()
                .select_interface_impl(goal, SelectionMode::Typecheck),
            crate::sema::models::SelectionResult::Selected(crate::sema::models::SelectedImpl {
                source: crate::sema::models::CandidateSource::ParamEnv,
                ..
            })
        ) {
            return SolverResult::Solved(vec![]);
        }
        match self
            .gcx()
            .build_conformance_witness(goal, SelectionMode::Typecheck)
        {
            Ok(_) => return SolverResult::Solved(vec![]),
            Err(SelectionError::Ambiguous(_)) => {
                self.gcx().dcx().emit_error(
                    format!(
                        "ambiguous conformance: multiple impls satisfy '{}' for '{}'",
                        interface.format(self.gcx()),
                        ty.format(self.gcx())
                    ),
                    None,
                );
            }
            Err(SelectionError::NoCandidates(_)) | Err(SelectionError::ObligationFailed { .. }) => {
            }
        }

        let error = Spanned::new(TypeError::NonConformance { ty, interface }, location);
        SolverResult::Error(vec![error])
    }

    /// Coerce NilVar to Optional[T] or *T
    fn solve_nil_coercion(
        &mut self,
        _location: Span,
        node_id: NodeID,
        from: Ty<'ctx>,
        to: Ty<'ctx>,
    ) -> Option<SolverResult<'ctx>> {
        use crate::sema::models::InferTy;

        let TyKind::Infer(InferTy::NilVar(nil_id)) = from.kind() else {
            return None;
        };

        // A generic/overloaded call may supply the nullable target later.
        // Binding its type variable to NilVar would lose that concrete ABI.
        if to.is_ty_var() {
            return Some(SolverResult::Deferred);
        }

        // Check if target is Optional[T]
        if let Some((args, _inner)) = self.unwrap_optional_type(to) {
            self.record_adjustments(
                node_id,
                vec![Adjustment::OptionalWrap {
                    is_some: false,
                    generic_args: args,
                }],
            );
            self.icx.mark_nil_var_bound(nil_id);
            return Some(SolverResult::Solved(vec![]));
        }

        // Check if target is pointer (nil -> null pointer)
        if let TyKind::Pointer(_, _) = to.kind() {
            // Nil variables track validity rather than unifying with a target.
            // Preserve the selected pointer type for THIR/MIR lowering.
            self.record_adjustments(node_id, vec![Adjustment::NullPointer { to }]);
            self.icx.mark_nil_var_bound(nil_id);
            return Some(SolverResult::Solved(vec![]));
        }

        None
    }

    /// Coerce T to Optional[T] by wrapping in some
    fn solve_optional_wrapping(
        &mut self,
        location: Span,
        node_id: NodeID,
        from: Ty<'ctx>,
        to: Ty<'ctx>,
    ) -> Option<SolverResult<'ctx>> {
        use crate::sema::models::InferTy;

        let (args, inner_ty) = self.unwrap_optional_type(to)?;

        // If from is an unresolved TyVar, let equality handle it.
        // TyVar could become anything (including Optional), so we can't decide yet.
        // IntVar/FloatVar will resolve to concrete types that CAN be wrapped.
        if matches!(from.kind(), TyKind::Infer(InferTy::TyVar(_))) {
            return None;
        }

        // Don't apply if from is already Optional
        if self.unwrap_optional_type(from).is_some() {
            return None;
        }

        // Don't apply to NilVar (handled by solve_nil_coercion)
        if matches!(from.kind(), TyKind::Infer(InferTy::NilVar(_))) {
            return None;
        }

        // Resolve the payload coercion before appending the wrapper. In
        // particular, a class upcast or existential box must operate on T,
        // never on the completed Optional/Result enum.
        let result = self.solve_coerce(location, node_id, from, inner_ty);
        if matches!(result, SolverResult::Solved(_)) {
            self.append_adjustments(
                node_id,
                vec![Adjustment::OptionalWrap {
                    is_some: true,
                    generic_args: args,
                }],
            );
        }
        Some(result)
    }

    fn solve_result_success_wrapping(
        &mut self,
        location: Span,
        node_id: NodeID,
        from: Ty<'ctx>,
        to: Ty<'ctx>,
    ) -> Option<SolverResult<'ctx>> {
        let (success, _) = self.gcx().result_parts(to)?;
        if self.gcx().result_parts(from).is_some() || self.gcx().result_parts(success).is_some() {
            return None;
        }
        // An unknown producer may itself return a Result. Keep ordinary
        // equality inference (as for Optional) instead of forcing its payload
        // type or blocking contextual generic calls such as identity(.err(e)).
        if matches!(from.kind(), TyKind::Infer(InferTy::TyVar(_))) {
            return None;
        }
        let TyKind::Adt(_, generic_args) = to.kind() else {
            unreachable!()
        };
        let result = self.solve_coerce(location, node_id, from, success);
        if matches!(result, SolverResult::Solved(_)) {
            self.append_adjustments(node_id, vec![Adjustment::ResultOkWrap { generic_args }]);
        }
        Some(result)
    }

    /// Check if ty is Optional[T] and return (generic_args, inner_ty)
    pub(crate) fn unwrap_optional_type(
        &self,
        ty: Ty<'ctx>,
    ) -> Option<(crate::sema::models::GenericArguments<'ctx>, Ty<'ctx>)> {
        let TyKind::Adt(def, args) = ty.kind() else {
            return None;
        };
        let opt_id = self.gcx().std_item_def(crate::hir::StdItem::Optional)?;
        if def.id != opt_id {
            return None;
        }
        let inner = (*args.first()?).ty()?;
        Some((args, inner))
    }

    /// Constrain the safe callable signature against Fn/AsyncFn arguments.
    fn solve_callable_fn_conformance(
        &mut self,
        location: Span,
        ty: Ty<'ctx>,
        interface: InterfaceReference<'ctx>,
    ) -> Option<SolverResult<'ctx>> {
        let (kind, closure_inputs, closure_output) = crate::sema::models::callable_signature(ty)?;

        let gcx = self.gcx();

        let allowed = crate::sema::models::callable_kind(gcx, interface.id) == Some(kind);
        if !allowed {
            return None;
        }

        // Get the interface's Args and Output type parameters.
        // Raw interface refs still carry `Self` as the first argument.
        if interface.arguments.len() < 3 {
            return None;
        }

        let expected_args_ty = interface.arguments[1].ty()?;
        let expected_output_ty = interface.arguments[2].ty()?;

        let closure_args_ty = crate::sema::models::callable_args_ty(gcx, closure_inputs);

        self.register_callable_adapter(ty);

        // Create obligations to match Args and Output
        let mut obligations = vec![];

        obligations.push(super::Obligation {
            location,
            goal: super::Goal::Equal(closure_args_ty, expected_args_ty),
        });

        obligations.push(super::Obligation {
            location,
            goal: super::Goal::Equal(closure_output, expected_output_ty),
        });

        Some(SolverResult::Solved(obligations))
    }

    /// Constrain a concrete callable immediately against a generic callable bound.
    fn solve_callable_to_fn_bound_param(
        &mut self,
        location: Span,
        from: Ty<'ctx>,
        to: Ty<'ctx>,
    ) -> Option<SolverResult<'ctx>> {
        if crate::sema::models::callable_signature(from).is_none() {
            return None;
        }

        // Generic call parameters have fresh inference variables at the call
        // site. Prove their callable bound using the same rules as boxing.
        for bound in self.param_env.bounds_for(to) {
            if let Some(mut result) = self.solve_callable_fn_conformance(location, from, bound) {
                if let SolverResult::Solved(obligations) = &mut result {
                    if to.is_infer() {
                        obligations.push(Obligation {
                            location,
                            goal: Goal::Equal(from, to),
                        });
                    }
                }
                return Some(result);
            }
        }
        None
    }

    /// Register the concrete callable adapter while type checking still has a
    /// chance to synthesize and serialize its THIR/MIR. Generic callable calls
    /// are specialized later, after THIR construction, which is too late to
    /// create a missing `call` body on demand.
    fn register_callable_adapter(&self, closure_ty: Ty<'ctx>) {
        let gcx = self.gcx();
        let Some(interface) = crate::sema::models::callable_interface_ref(gcx, closure_ty) else {
            return;
        };
        // A closure may be erased inside generic code and then dynamically cast
        // to any interface it implements. Demand its strongest interface and
        // inherited adapters before THIR synthesis; codegen cannot create bodies.
        for interface in self.collect_interface_with_supers(interface) {
            if let Some(goal) = interface.to_goal(gcx, &[]) {
                let _ = gcx.build_conformance_witness(goal, SelectionMode::Typecheck);
            }
        }
    }
}

fn generic_arg_needs_instantiation(arg: &crate::sema::models::GenericArgument<'_>) -> bool {
    match arg {
        crate::sema::models::GenericArgument::Type(ty) => ty.needs_instantiation(),
        crate::sema::models::GenericArgument::Const(c) => {
            matches!(
                c.kind,
                crate::sema::models::ConstKind::Param(_) | crate::sema::models::ConstKind::Infer(_)
            ) || c.ty.needs_instantiation()
        }
    }
}
