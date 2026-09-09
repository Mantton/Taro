use crate::{
    hir::{Mutability, NodeID},
    sema::{
        error::{ExpectedFound, TypeError},
        models::{
            AliasKind, GenericArgument, InferTy, InterfaceReference, SelectionError, SelectionMode,
            Ty, TyKind,
        },
        resolve::models::TypeHead,
        tycheck::utils::{type_head_from_value_ty, unresolved::ty_contains_unresolved_inference},
    },
    span::{Span, Spanned},
};

use super::{Adjustment, ConstraintSolver, Goal, Obligation, SolverResult};

impl<'ctx> ConstraintSolver<'ctx> {
    pub fn solve_coerce(
        &mut self,
        location: Span,
        node_id: NodeID,
        from: Ty<'ctx>,
        to: Ty<'ctx>,
    ) -> SolverResult<'ctx> {
        let from = self.structurally_resolve(from);
        let to = self.structurally_resolve(to);

        if matches!(from.kind(), TyKind::Never) {
            return SolverResult::Solved(vec![]);
        }

        if let Some(result) = self.solve_existential_upcast(location, node_id, from, to) {
            return result;
        }

        if let Some(result) = self.solve_boxing_coercion(location, node_id, from, to) {
            return result;
        }

        if let Some(result) = self.solve_pointer_coercion(location, from, to) {
            return result;
        }

        // Closure to function pointer coercion: || -> T to fn() -> T
        if let Some(result) = self.solve_closure_to_fn_pointer(location, node_id, from, to) {
            return result;
        }

        // Closure to type parameter with Fn bound coercion
        if let Some(result) = self.solve_closure_to_fn_bound_param(location, from, to) {
            return result;
        }

        // Nil coercion: NilVar -> Optional[T] or NilVar -> *T
        if let Some(result) = self.solve_nil_coercion(location, node_id, from, to) {
            return result;
        }

        // Optional wrapping: T -> Optional[T]
        if let Some(result) = self.solve_optional_wrapping(location, node_id, from, to) {
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

        if matches!(
            from.kind(),
            TyKind::Closure { .. }
                | TyKind::Parameter(_)
                | TyKind::Alias {
                    kind: AliasKind::Opaque,
                    ..
                }
        ) {
            let obligations = interfaces
                .iter()
                .map(|interface| {
                    let mut arguments = interface.arguments.to_vec();
                    if let Some(first) = arguments.first_mut() {
                        *first = GenericArgument::Type(from);
                    } else {
                        arguments.push(GenericArgument::Type(from));
                    }
                    let interface = InterfaceReference {
                        id: interface.id,
                        arguments: self.gcx().store.interners.intern_generic_args(arguments),
                        bindings: interface.bindings,
                    };
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
            return Some(SolverResult::Solved(obligations));
        }

        let Some(head) = type_head_from_value_ty(from) else {
            let error = Spanned::new(
                TypeError::TyMismatch(ExpectedFound::new(to, from)),
                location,
            );
            return Some(SolverResult::Error(vec![error]));
        };

        if let Some(matches) = self.collect_head_conformance_matches(head, interfaces, true) {
            let obligations = self.interface_match_obligations(location, &matches);
            self.record_adjustments(
                node_id,
                vec![Adjustment::BoxExistential { from, interfaces }],
            );
            return Some(SolverResult::Solved(obligations));
        }

        let missing = self.missing_conformances(head, interfaces);
        let errors = missing
            .into_iter()
            .map(|interface| {
                Spanned::new(
                    TypeError::NonConformance {
                        ty: from,
                        interface,
                    },
                    location,
                )
            })
            .collect();

        Some(SolverResult::Error(errors))
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
            inputs: fn_inputs,
            output: fn_output,
        } = to.kind()
        else {
            return None;
        };

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
        from: Ty<'ctx>,
        to: Ty<'ctx>,
    ) -> Option<SolverResult<'ctx>> {
        // Reference coercion: &mut T -> &T
        if let (
            TyKind::Reference(from_inner, Mutability::Mutable),
            TyKind::Reference(to_inner, Mutability::Immutable),
        ) = (from.kind(), to.kind())
        {
            return Some(self.solve_equality(location, to_inner, from_inner));
        }

        // Raw pointer coercion: *mut T -> *T
        if let (
            TyKind::Pointer(from_inner, Mutability::Mutable),
            TyKind::Pointer(to_inner, Mutability::Immutable),
        ) = (from.kind(), to.kind())
        {
            return Some(self.solve_equality(location, to_inner, from_inner));
        }

        None
    }

    fn missing_conformances(
        &self,
        head: TypeHead,
        interfaces: &'ctx [InterfaceReference<'ctx>],
    ) -> Vec<InterfaceReference<'ctx>> {
        let gcx = self.gcx();

        // Collect conformance records from all visible packages
        let records = gcx.collect_from_databases(|db| {
            db.conformance_by_head
                .get(&head)
                .map_or_else(Vec::new, |ids| {
                    ids.iter()
                        .filter_map(|id| db.conformance_records.get(id).copied())
                        .collect()
                })
        });

        let mut missing = Vec::new();
        for iface in interfaces {
            let mut satisfied = false;
            for record in &records {
                if self.interface_ref_matches_with_mode(*iface, record.interface, true, false) {
                    satisfied = true;
                    break;
                }

                let mut supers = self.collect_interface_with_supers(record.interface);
                if supers.drain(1..).any(|candidate| {
                    self.interface_ref_matches_with_mode(*iface, candidate, true, false)
                }) {
                    satisfied = true;
                    break;
                }
            }
            if !satisfied {
                missing.push(*iface);
            }
        }

        missing
    }

    fn collect_head_conformance_matches(
        &self,
        head: TypeHead,
        interfaces: &'ctx [InterfaceReference<'ctx>],
        infer: bool,
    ) -> Option<Vec<(InterfaceReference<'ctx>, InterfaceReference<'ctx>)>> {
        let gcx = self.gcx();
        let records = gcx.collect_from_databases(|db| {
            db.conformance_by_head
                .get(&head)
                .map_or_else(Vec::new, |ids| {
                    ids.iter()
                        .filter_map(|id| db.conformance_records.get(id).copied())
                        .collect()
                })
        });

        let mut matches_out = Vec::with_capacity(interfaces.len());
        for iface in interfaces {
            let mut matched = None;
            for record in &records {
                if self.interface_ref_matches_with_mode(*iface, record.interface, infer, false) {
                    matched = Some(record.interface);
                    break;
                }

                for candidate in self
                    .collect_interface_with_supers(record.interface)
                    .into_iter()
                    .skip(1)
                {
                    if self.interface_ref_matches_with_mode(*iface, candidate, infer, false) {
                        matched = Some(candidate);
                        break;
                    }
                }
                if matched.is_some() {
                    break;
                }
            }

            let actual = matched?;
            matches_out.push((*iface, actual));
        }

        Some(matches_out)
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

    fn interface_ref_matches_with_mode(
        &self,
        expected: InterfaceReference<'ctx>,
        actual: InterfaceReference<'ctx>,
        infer: bool,
        commit: bool,
    ) -> bool {
        if !infer {
            return self.interface_ref_matches(expected, actual);
        }

        let matches = self
            .icx
            .probe(|_| self.interface_ref_matches_with_inference(expected, actual));
        if !matches {
            return false;
        }

        if commit {
            return self.interface_ref_matches_with_inference(expected, actual);
        }

        true
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

    fn interface_ref_matches_with_inference(
        &self,
        expected: InterfaceReference<'ctx>,
        actual: InterfaceReference<'ctx>,
    ) -> bool {
        expected.id == actual.id && self.interface_args_match_with_inference(expected, actual)
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

        if ty.is_error() {
            return SolverResult::Solved(vec![]);
        }

        // Special case: closures implicitly implement Fn/AsyncFn.
        // Check this BEFORE deferring on has_infer, because the Equal obligations
        // we generate will bind any inference variables in the interface (like output type U).
        if let Some(result) = self.solve_closure_fn_conformance(location, ty, interface) {
            return result;
        }

        // Now defer if interface has unresolved inference variables
        // (except for closure conformance which we already handled)
        if has_infer {
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
            TyKind::BoxedExistential { interfaces } => {
                // The payload may implement Copy, but the owning existential
                // box itself is not Copy. Do not let dynamic interface
                // membership bypass representation checks or generic bounds,
                // including bounds on interfaces that inherit Copy.
                let copy_id = self.gcx().std_item_def(crate::hir::StdItem::Copy);
                if self
                    .collect_interface_with_supers(interface)
                    .iter()
                    .any(|required| Some(required.id) == copy_id)
                {
                    return SolverResult::Error(vec![Spanned::new(
                        TypeError::NonConformance { ty, interface },
                        location,
                    )]);
                }
                let mut satisfied = interfaces
                    .iter()
                    .any(|source| self.existential_interface_ref_matches(interface, *source));

                if !satisfied {
                    satisfied = interfaces.iter().any(|source| {
                        self.collect_interface_with_supers(*source)
                            .into_iter()
                            .skip(1)
                            .any(|candidate| {
                                self.existential_interface_ref_matches(interface, candidate)
                            })
                    });
                }

                if satisfied {
                    return SolverResult::Solved(vec![]);
                }

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

        self.record_adjustments(
            node_id,
            vec![Adjustment::OptionalWrap {
                is_some: true,
                generic_args: args,
            }],
        );

        // Recursively coerce inner: from -> inner_ty
        Some(SolverResult::Solved(vec![super::Obligation {
            location,
            goal: super::Goal::Coerce {
                node_id,
                from,
                to: inner_ty,
            },
        }]))
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

    /// Check if a closure type conforms to one of the callable interfaces.
    fn solve_closure_fn_conformance(
        &mut self,
        location: Span,
        ty: Ty<'ctx>,
        interface: InterfaceReference<'ctx>,
    ) -> Option<SolverResult<'ctx>> {
        use crate::hir::StdItem;

        // Check if ty is a closure
        let TyKind::Closure {
            kind,
            inputs: closure_inputs,
            output: closure_output,
            ..
        } = ty.kind()
        else {
            return None;
        };

        let gcx = self.gcx();

        let fn_def = gcx.std_item_def(StdItem::Fn);
        let fn_mut_def = gcx.std_item_def(StdItem::FnMut);
        let fn_once_def = gcx.std_item_def(StdItem::FnOnce);
        let async_fn_def = gcx.std_item_def(StdItem::AsyncFn);
        let async_fn_mut_def = gcx.std_item_def(StdItem::AsyncFnMut);
        let async_fn_once_def = gcx.std_item_def(StdItem::AsyncFnOnce);
        if fn_def != Some(interface.id)
            && fn_mut_def != Some(interface.id)
            && fn_once_def != Some(interface.id)
            && async_fn_def != Some(interface.id)
            && async_fn_mut_def != Some(interface.id)
            && async_fn_once_def != Some(interface.id)
        {
            return None;
        }
        let allowed = if fn_def == Some(interface.id) {
            matches!(kind, crate::sema::models::ClosureKind::Fn)
        } else if fn_mut_def == Some(interface.id) {
            matches!(
                kind,
                crate::sema::models::ClosureKind::Fn | crate::sema::models::ClosureKind::FnMut
            )
        } else if fn_once_def == Some(interface.id) {
            matches!(
                kind,
                crate::sema::models::ClosureKind::Fn
                    | crate::sema::models::ClosureKind::FnMut
                    | crate::sema::models::ClosureKind::FnOnce
            )
        } else if async_fn_def == Some(interface.id) {
            matches!(kind, crate::sema::models::ClosureKind::AsyncFn)
        } else if async_fn_mut_def == Some(interface.id) {
            matches!(
                kind,
                crate::sema::models::ClosureKind::AsyncFn
                    | crate::sema::models::ClosureKind::AsyncFnMut
            )
        } else if async_fn_once_def == Some(interface.id) {
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

        // Get the interface's Args and Output type parameters.
        // Raw interface refs still carry `Self` as the first argument.
        if interface.arguments.len() < 3 {
            return None;
        }

        let expected_args_ty = interface.arguments[1].ty()?;
        let expected_output_ty = interface.arguments[2].ty()?;

        let closure_args_ty = crate::sema::models::callable_args_ty(gcx, closure_inputs);

        self.register_closure_callable_adapter(ty);

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

    /// Coerce a closure to a type that has callable bounds.
    /// This extracts the callable bound and constrains the closure immediately.
    fn solve_closure_to_fn_bound_param(
        &mut self,
        location: Span,
        from: Ty<'ctx>,
        to: Ty<'ctx>,
    ) -> Option<SolverResult<'ctx>> {
        if !matches!(from.kind(), TyKind::Closure { .. }) {
            return None;
        }

        // Generic call parameters have fresh inference variables at the call
        // site. Prove their callable bound using the same rules as boxing.
        for bound in self.param_env.bounds_for(to) {
            if let Some(mut result) = self.solve_closure_fn_conformance(location, from, bound) {
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

    /// Register the concrete closure adapter while type checking still has a
    /// chance to synthesize and serialize its THIR/MIR. Generic callable calls
    /// are specialized later, after THIR construction, which is too late to
    /// create a missing `call`/`callMut`/`callOnce` body on demand.
    fn register_closure_callable_adapter(&self, closure_ty: Ty<'ctx>) {
        let gcx = self.gcx();
        let Some(interface) = crate::sema::models::closure_interface_ref(gcx, closure_ty) else {
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
