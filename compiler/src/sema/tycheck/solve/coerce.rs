use crate::{
    hir::{Mutability, NodeID},
    sema::{
        error::{ExpectedFound, TypeError},
        models::{InterfaceReference, Ty, TyKind},
        resolve::models::TypeHead,
        tycheck::{resolve_conformance_witness, utils::type_head_from_value_ty},
    },
    span::{Span, Spanned},
};

use super::{Adjustment, ConstraintSolver, SolverResult};

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

        // Minimal coercion: just equality for now.
        self.solve_equality(location, to, from)
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

        if from.is_infer() {
            return Some(SolverResult::Deferred);
        }

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

        let missing = self.missing_conformances(head, interfaces);
        if missing.is_empty() {
            self.record_adjustments(
                node_id,
                vec![Adjustment::BoxExistential { from, interfaces }],
            );
            return Some(SolverResult::Solved(vec![]));
        }

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

        if self.interface_subset(from_ifaces, to_ifaces) {
            self.record_adjustments(node_id, vec![Adjustment::ExistentialUpcast { from, to }]);
            return Some(SolverResult::Solved(vec![]));
        }

        if self.interface_superface_upcast(from_ifaces, to_ifaces) {
            self.record_adjustments(node_id, vec![Adjustment::ExistentialUpcast { from, to }]);
            return Some(SolverResult::Solved(vec![]));
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
        let records = gcx
            .collect_from_databases(|db| db.conformances.get(&head).cloned().unwrap_or_default());

        let mut missing = Vec::new();
        for iface in interfaces {
            let mut satisfied = false;
            for record in &records {
                if self.interface_ref_matches(*iface, record.interface) {
                    satisfied = true;
                    break;
                }

                let mut supers = self.collect_interface_with_supers(record.interface);
                if supers
                    .drain(1..)
                    .any(|candidate| self.interface_ref_matches(*iface, candidate))
                {
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

    fn interface_args_match(
        &self,
        expected: InterfaceReference<'ctx>,
        actual: InterfaceReference<'ctx>,
    ) -> bool {
        let expected_args = if expected.arguments.len() > 0 {
            &expected.arguments[1..]
        } else {
            expected.arguments
        };
        let actual_args = if actual.arguments.len() > 0 {
            &actual.arguments[1..]
        } else {
            actual.arguments
        };

        if expected_args.len() != actual_args.len() {
            return false;
        }

        // TODO: Unify/infer interface arguments instead of strict equality.
        expected_args
            .iter()
            .zip(actual_args.iter())
            .all(|(a, b)| a == b)
    }

    fn interface_subset(
        &self,
        from_ifaces: &'ctx [InterfaceReference<'ctx>],
        to_ifaces: &'ctx [InterfaceReference<'ctx>],
    ) -> bool {
        to_ifaces.iter().all(|target| {
            from_ifaces
                .iter()
                .any(|source| self.interface_ref_matches(*target, *source))
        })
    }

    fn interface_superface_upcast(
        &self,
        from_ifaces: &'ctx [InterfaceReference<'ctx>],
        to_ifaces: &'ctx [InterfaceReference<'ctx>],
    ) -> bool {
        to_ifaces.iter().all(|target| {
            from_ifaces.iter().any(|source| {
                if self.interface_ref_matches(*target, *source) {
                    return true;
                }

                self.collect_interface_with_supers(*source)
                    .into_iter()
                    .skip(1)
                    .any(|candidate| self.interface_ref_matches(*target, candidate))
            })
        })
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

        if has_infer {
            return SolverResult::Deferred;
        }

        if ty.is_error() {
            return SolverResult::Solved(vec![]);
        }

        match ty.kind() {
            TyKind::Infer(_) => return SolverResult::Deferred,
            TyKind::Parameter(_) => return SolverResult::Solved(vec![]),
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

        let Some(head) = type_head_from_value_ty(ty) else {
            let error = Spanned::new(TypeError::NonConformance { ty, interface }, location);
            return SolverResult::Error(vec![error]);
        };

        if resolve_conformance_witness(self.gcx(), head, interface).is_some() {
            return SolverResult::Solved(vec![]);
        }

        // Special case: primitives implicitly satisfy Copy (no explicit conformance record)
        if let Some(copy_def) = self.gcx().std_interface_def(crate::hir::StdInterface::Copy) {
            if interface.id == copy_def && self.gcx().is_type_copyable(ty) {
                return SolverResult::Solved(vec![]);
            }
        }

        // Special case: closures implicitly implement Fn/FnMut/FnOnce
        if let Some(result) = self.solve_closure_fn_conformance(location, ty, interface) {
            return result;
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
        let opt_id = self.gcx().find_std_type("Optional")?;
        if def.id != opt_id {
            return None;
        }
        let inner = args.first()?.ty()?;
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
        use crate::hir::StdInterface;
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
        let fn_def = gcx.std_interface_def(StdInterface::Fn);
        let fn_mut_def = gcx.std_interface_def(StdInterface::FnMut);
        let fn_once_def = gcx.std_interface_def(StdInterface::FnOnce);

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
        use crate::hir::StdInterface;

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
        let fn_def = gcx.std_interface_def(StdInterface::Fn);
        let fn_mut_def = gcx.std_interface_def(StdInterface::FnMut);
        let fn_once_def = gcx.std_interface_def(StdInterface::FnOnce);

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
