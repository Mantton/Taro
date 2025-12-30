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

        if let Some(result) = self.solve_existential_upcast(location, node_id, from, to) {
            return result;
        }

        if let Some(result) = self.solve_boxing_coercion(location, node_id, from, to) {
            return result;
        }

        if let Some(result) = self.solve_pointer_coercion(location, from, to) {
            return result;
        }

        if self.in_scope_equal(from, to) {
            return SolverResult::Solved(vec![]);
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

    fn solve_pointer_coercion(
        &mut self,
        location: Span,
        from: Ty<'ctx>,
        to: Ty<'ctx>,
    ) -> Option<SolverResult<'ctx>> {
        let TyKind::Reference(from_inner, Mutability::Mutable) = from.kind() else {
            return None;
        };
        let TyKind::Reference(to_inner, Mutability::Immutable) = to.kind() else {
            return None;
        };

        Some(self.solve_equality(location, to_inner, from_inner))
    }

    fn missing_conformances(
        &self,
        head: TypeHead,
        interfaces: &'ctx [InterfaceReference<'ctx>],
    ) -> Vec<InterfaceReference<'ctx>> {
        let gcx = self.gcx();
        let mut records: Vec<crate::sema::models::ConformanceRecord<'ctx>> = Vec::new();

        let mut collect = |db: &crate::compile::context::TypeDatabase<'ctx>| {
            if let Some(found) = db.conformances.get(&head) {
                records.extend(found.iter().copied());
            }
        };

        gcx.with_session_type_database(|db| collect(db));

        let mapping = gcx.store.package_mapping.borrow();
        let deps: Vec<_> = gcx
            .config
            .dependencies
            .values()
            .filter_map(|ident| mapping.get(ident.as_str()).copied())
            .collect();
        drop(mapping);

        for index in deps {
            gcx.with_type_database(index, |db| collect(db));
        }

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

        let error = Spanned::new(TypeError::NonConformance { ty, interface }, location);
        SolverResult::Error(vec![error])
    }
}
