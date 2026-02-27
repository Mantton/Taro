use crate::{
    hir::{Mutability, NodeID},
    sema::{
        error::{ExpectedFound, TypeError},
        models::{
            AliasKind, GenericArgument, GenericArguments, InferTy, InterfaceGoal,
            InterfaceReference, SelectionError, SelectionMode, Ty, TyKind,
        },
        resolve::models::TypeHead,
        tycheck::utils::type_head_from_value_ty,
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
            inputs: closure_inputs,
            output: closure_output,
            ..
        } = from.kind()
        else {
            return None;
        };

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
                if self.interface_ref_matches_with_mode(*target, *source, infer, false) {
                    matched = Some(*source);
                    break;
                }

                if include_supers {
                    for candidate in self
                        .collect_interface_with_supers(*source)
                        .into_iter()
                        .skip(1)
                    {
                        if self.interface_ref_matches_with_mode(*target, candidate, infer, false) {
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

    fn interface_args_match(
        &self,
        expected: InterfaceReference<'ctx>,
        actual: InterfaceReference<'ctx>,
    ) -> bool {
        self.interface_args_match_inner(expected, actual, false)
    }

    fn interface_args_match_with_inference(
        &self,
        expected: InterfaceReference<'ctx>,
        actual: InterfaceReference<'ctx>,
    ) -> bool {
        self.interface_args_match_inner(expected, actual, true)
    }

    fn interface_args_match_inner(
        &self,
        expected: InterfaceReference<'ctx>,
        actual: InterfaceReference<'ctx>,
        infer: bool,
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

        if !infer {
            return expected_args
                .iter()
                .zip(actual_args.iter())
                .all(|(a, b)| a == b);
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

    fn interface_ref_matches_with_inference(
        &self,
        expected: InterfaceReference<'ctx>,
        actual: InterfaceReference<'ctx>,
    ) -> bool {
        expected.id == actual.id && self.interface_args_match_with_inference(expected, actual)
    }

    fn interface_ref_matches(
        &self,
        expected: InterfaceReference<'ctx>,
        actual: InterfaceReference<'ctx>,
    ) -> bool {
        expected.id == actual.id && self.interface_args_match(expected, actual)
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

        // Special case: closures implicitly implement Fn/FnMut/FnOnce
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
            TyKind::Parameter(_) => return SolverResult::Solved(vec![]),
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
                // (e.g. `struct S[T: Copy]: Copy`) can carry unresolved declaration
                // parameters that are validated via the type's own generic bounds.
                // Defer instead of marking solved so use-site obligations are still
                // forced through concrete proof once instantiations are known.
                return SolverResult::Deferred;
            }
            TyKind::Alias {
                kind: AliasKind::Projection,
                ..
            } => {
                if ty.contains_inference() {
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
                let mut satisfied = interfaces
                    .iter()
                    .any(|source| self.interface_ref_matches(interface, *source));

                if !satisfied {
                    satisfied = interfaces.iter().any(|source| {
                        self.collect_interface_with_supers(*source)
                            .into_iter()
                            .skip(1)
                            .any(|candidate| self.interface_ref_matches(interface, candidate))
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

        let interface_args = if interface.arguments.len() > 1 {
            self.gcx()
                .store
                .interners
                .intern_generic_args_slice(&interface.arguments[1..])
        } else {
            GenericArguments::empty()
        };
        let self_ty = match interface.arguments.get(0).copied() {
            Some(GenericArgument::Type(self_ty)) => self_ty,
            _ => ty,
        };
        let goal = InterfaceGoal {
            interface_id: interface.id,
            self_ty,
            interface_args,
            bindings: interface.bindings,
            param_env: &[],
        };
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

        // Special case: primitives implicitly satisfy Copy (no explicit conformance record)
        if let Some(copy_def) = self.gcx().std_item_def(crate::hir::StdItem::Copy) {
            if interface.id == copy_def && self.gcx().is_type_copyable(ty) {
                return SolverResult::Solved(vec![]);
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
    fn unwrap_optional_type(
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

    /// Check if a closure type conforms to Fn, FnMut, or FnOnce interfaces.
    /// Closures implicitly implement these traits based on their kind.
    fn solve_closure_fn_conformance(
        &mut self,
        location: Span,
        ty: Ty<'ctx>,
        interface: InterfaceReference<'ctx>,
    ) -> Option<SolverResult<'ctx>> {
        use crate::hir::StdItem;
        use crate::sema::models::ClosureKind;

        // Check if ty is a closure
        let TyKind::Closure {
            inputs: closure_inputs,
            output: closure_output,
            kind: closure_kind,
            ..
        } = ty.kind()
        else {
            return None;
        };

        let gcx = self.gcx();

        // Check which Fn trait is being requested
        let fn_def = gcx.std_item_def(StdItem::Fn);
        let fn_mut_def = gcx.std_item_def(StdItem::FnMut);
        let fn_once_def = gcx.std_item_def(StdItem::FnOnce);

        let required_kind = if fn_def == Some(interface.id) {
            ClosureKind::Fn
        } else if fn_mut_def == Some(interface.id) {
            ClosureKind::FnMut
        } else if fn_once_def == Some(interface.id) {
            ClosureKind::FnOnce
        } else {
            return None; // Not a Fn trait
        };

        // Check if the closure's kind is compatible with the required trait
        // Fn -> can satisfy Fn, FnMut, FnOnce
        // FnMut -> can satisfy FnMut, FnOnce
        // FnOnce -> can only satisfy FnOnce
        let kind_compatible = match (closure_kind, required_kind) {
            (ClosureKind::Fn, _) => true, // Fn closures implement all three
            (ClosureKind::FnMut, ClosureKind::Fn) => false,
            (ClosureKind::FnMut, _) => true, // FnMut implements FnMut and FnOnce
            (ClosureKind::FnOnce, ClosureKind::FnOnce) => true,
            (ClosureKind::FnOnce, _) => false, // FnOnce only implements FnOnce
        };

        if !kind_compatible {
            return None; // Let normal error handling report the failure
        }

        // Get the interface's Args and Output type parameters
        // Fn[Self, Args, Output] - Self is at [0], Args at [1], Output at [2]
        if interface.arguments.len() < 3 {
            return None;
        }

        let expected_args_ty = interface.arguments[1].ty()?;
        let expected_output_ty = interface.arguments[2].ty()?;

        // Build the closure's args type:
        // - Single argument: just the type
        // - Multiple arguments: tuple type
        let closure_args_ty = if closure_inputs.len() == 1 {
            closure_inputs[0]
        } else {
            // Create tuple type for multiple arguments
            Ty::new(TyKind::Tuple(closure_inputs), gcx)
        };

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

    /// Coerce a closure to a type parameter that has Fn/FnMut/FnOnce bounds.
    /// This extracts the Fn bound from the type param and constrains the closure accordingly.
    fn solve_closure_to_fn_bound_param(
        &mut self,
        location: Span,
        from: Ty<'ctx>,
        to: Ty<'ctx>,
    ) -> Option<SolverResult<'ctx>> {
        use crate::hir::StdItem;

        // Check if from is a closure
        let TyKind::Closure {
            inputs: closure_inputs,
            output: closure_output,
            ..
        } = from.kind()
        else {
            return None;
        };

        // Check if to is a type parameter
        let TyKind::Parameter(_) = to.kind() else {
            return None;
        };

        // Get Fn bounds for this type parameter from param_env
        let bounds = self.param_env.bounds_for(to);

        let gcx = self.gcx();
        let fn_def = gcx.std_item_def(StdItem::Fn);
        let fn_mut_def = gcx.std_item_def(StdItem::FnMut);
        let fn_once_def = gcx.std_item_def(StdItem::FnOnce);

        for bound in bounds {
            // Check if this is an Fn trait bound
            let is_fn_trait = fn_def == Some(bound.id)
                || fn_mut_def == Some(bound.id)
                || fn_once_def == Some(bound.id);

            if !is_fn_trait {
                continue;
            }

            // Fn[Args, Output] has Self at [0], Args at [1], Output at [2]
            if bound.arguments.len() < 3 {
                continue;
            }

            let Some(expected_args_ty) = bound.arguments[1].ty() else {
                continue;
            };
            let Some(expected_output_ty) = bound.arguments[2].ty() else {
                continue;
            };

            // Build the closure's args type
            let closure_args_ty = if closure_inputs.len() == 1 {
                closure_inputs[0]
            } else {
                Ty::new(TyKind::Tuple(closure_inputs), gcx)
            };

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

            return Some(SolverResult::Solved(obligations));
        }

        None
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
