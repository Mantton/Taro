//! Recover generic arguments from one fully proved concrete conformance. This
//! supplies inference, never an ownership/conformance waiver for a nominal head.
use super::{ConstraintSolver, Goal, Obligation};
use crate::{
    sema::{
        models::{AssociatedTypeBinding, GenericArgument, InterfaceReference, SelectionMode, Ty},
        tycheck::utils::{
            instantiate::instantiate_interface_ref_with_args, type_head_from_value_ty,
            unresolved::interface_ref_contains_unresolved_inference,
        },
    },
    span::Span,
};
use rustc_hash::FxHashSet;

impl<'ctx> ConstraintSolver<'ctx> {
    pub(super) fn infer_conformance_arguments(
        &mut self,
        ty: Ty<'ctx>,
        expected: InterfaceReference<'ctx>,
        span: Span,
    ) -> Option<Vec<Obligation<'ctx>>> {
        if ty.contains_inference() {
            return None;
        }
        let gcx = self.gcx();
        let head = type_head_from_value_ty(ty);
        let mut roots = self.bounds_for_type(ty, &self.param_env);
        // Primitive operator conformances have no source impl record. Their
        // declared contract fixes operand types to this same primitive type.
        for &item in crate::mir::primitive_operators::ITEMS {
            if gcx.std_item_def(item) == Some(expected.id)
                && let Some(interface) =
                    crate::mir::primitive_operators::interface_for_type(gcx, ty, item)
            {
                roots.push(interface);
            }
        }
        let records = gcx.collect_from_databases(|db| {
            db.conformance_by_interface
                .get(&expected.id)
                .into_iter()
                .flatten()
                .filter_map(|id| db.conformance_records.get(id).copied())
                .filter(|record| record.target.is_blanket() || Some(record.target) == head)
                .collect::<Vec<_>>()
        });
        for record in records {
            let Some(args) = crate::sema::impl_engine::deduce_impl_subst(
                gcx,
                record.extension,
                ty,
                self.assumption_constraints,
            ) else {
                continue;
            };
            let interface = instantiate_interface_ref_with_args(gcx, record.interface, args);
            roots.push(crate::sema::impl_engine::ref_ops::interface_ref_with_self(
                gcx, ty, interface,
            ));
        }
        let mut viable = FxHashSet::default();
        for root in roots {
            for mut interface in self.collect_interface_with_supers(root) {
                if interface.id != expected.id
                    || interface_ref_contains_unresolved_inference(interface)
                {
                    continue;
                }
                let goal = interface.to_goal_with_self_ty(gcx, self.assumption_constraints, ty);
                let Ok(witness) = gcx.build_conformance_witness(goal, SelectionMode::Typecheck)
                else {
                    continue;
                };
                // Associated bindings are inferred from their actual witnesses,
                // never by guessing a type or trusting a pending requirement.
                let mut bindings = Vec::new();
                let mut complete = true;
                for binding in expected.bindings {
                    let actual =
                        gcx.get_interface_requirements(interface.id)
                            .and_then(|requirements| {
                                requirements
                                    .types
                                    .iter()
                                    .find(|requirement| requirement.name == binding.name)
                                    .and_then(|requirement| {
                                        witness.type_witnesses.get(&requirement.id)
                                    })
                                    .copied()
                            });
                    let Some(actual) = actual else {
                        complete = false;
                        break;
                    };
                    bindings.push(AssociatedTypeBinding {
                        name: binding.name,
                        ty: actual,
                    });
                }
                if !complete {
                    continue;
                }
                interface.bindings = gcx.store.arenas.global.alloc_slice_clone(&bindings);
                if self
                    .icx
                    .probe(|_| self.unify_conformance_arguments(expected, interface))
                {
                    viable.insert(interface);
                }
            }
        }
        if viable.len() != 1 {
            return None;
        }
        let actual = viable.into_iter().next().unwrap();
        if !self.unify_conformance_arguments(expected, actual) {
            return None;
        }
        Some(vec![Obligation {
            location: span,
            goal: Goal::Conforms {
                ty,
                interface: expected,
            },
        }])
    }

    fn unify_conformance_arguments(
        &self,
        expected: InterfaceReference<'ctx>,
        actual: InterfaceReference<'ctx>,
    ) -> bool {
        if expected.arguments.len() != actual.arguments.len() {
            return false;
        }
        for (expected, actual) in expected.arguments.iter().zip(actual.arguments) {
            let valid = match (*expected, *actual) {
                (GenericArgument::Type(a), GenericArgument::Type(b)) => self.unify(a, b).is_ok(),
                (GenericArgument::Const(a), GenericArgument::Const(b)) => {
                    self.unify_const(a, b).is_ok()
                }
                _ => false,
            };
            if !valid {
                return false;
            }
        }
        expected
            .bindings
            .iter()
            .zip(actual.bindings)
            .all(|(a, b)| a.name == b.name && self.unify(a.ty, b.ty).is_ok())
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn concrete_erasure_infers_generic_and_associated_arguments_from_proved_witnesses() {
        for source in [
            "interface Produce[T] { func produce() -> T; }\nstruct Source {}\nconform Source to Produce[int32] { func produce() -> int32 { 7 }; }\nfunc inspect[T](_ value: any Produce[T]) -> int32 { var _ = value.produce(); 7 }\nfunc main() { var result: int32 = inspect(Source {}); }",
            "interface Produce { type Output; func produce() -> Self::Output; }\nstruct Source {}\nconform Source to Produce { type Output = int32; func produce() -> int32 { 7 }; }\nfunc inspect[T](_ value: any Produce[Output = T]) -> int32 { var _ = value.produce(); 7 }\nfunc main() { var result: int32 = inspect(Source {}); }",
        ] {
            let diagnostics = crate::test_support::analyze_script_diagnostics(source);
            assert!(diagnostics.is_empty(), "{source}\n{diagnostics:#?}");
        }
    }

    #[test]
    fn inference_does_not_guess_between_conformances_or_ignore_where_requirements() {
        for declarations in [
            "struct Source {}\nconform Source to Produce[int32] {}\nconform Source to Produce[bool] {}",
            "interface Missing {}\nstruct Wrapper[T] { value: T }\nconform[T: Missing] Wrapper[T] to Produce[int32] {}\ntype Source = Wrapper[bool]",
        ] {
            let value = if declarations.contains("Wrapper") {
                "Source { value: true }"
            } else {
                "Source {}"
            };
            let source = format!(
                "interface Produce[T] {{}}\n{declarations}\nfunc inspect[T](_ value: any Produce[T]) {{}}\nfunc main() {{ inspect({value}); }}"
            );
            let diagnostics = crate::test_support::analyze_script_diagnostics(&source);
            assert!(
                !diagnostics.is_empty(),
                "unproved inference accepted: {source}"
            );
            assert!(
                !diagnostics.iter().any(|d| d.message.contains("expected")),
                "fixture must reach type inference: {diagnostics:#?}"
            );
        }
    }
}
