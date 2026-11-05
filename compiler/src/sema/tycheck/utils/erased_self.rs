//! Bound Self inside an erased interface is not an outer generic parameter.
//! De Bruijn depths distinguish nested existential binders without source syntax.
use crate::{
    compile::context::Gcx,
    sema::{
        models::{InterfaceReference, Ty, TyKind},
        tycheck::{
            fold::{TypeFoldable, TypeFolder, TypeSuperFoldable},
            visit::{TypeSuperVisitable, TypeVisitable, TypeVisitor},
        },
    },
};

/// The supported covariant erasure case is a direct owned declaration Self,
/// not a defaulted argument that happens to resolve to the payload type.
pub(crate) fn returns_owned_self(gcx: Gcx<'_>, method: crate::hir::DefinitionID) -> bool {
    let output = super::normalize_aliases(gcx, gcx.get_signature(method).output);
    matches!(output.kind(), TyKind::Parameter(parameter) if parameter.index == 0)
}

/// Rebind declaration Self to a hidden marker before inspecting its ABI. Using
/// the public container as Self too early would make &Self look like &any P,
/// although a concrete implementation actually expects &Concrete.
pub(crate) fn method_has_unsupported_payload_types<'ctx>(
    gcx: Gcx<'ctx>,
    method: crate::hir::DefinitionID,
    arguments: crate::sema::models::GenericArguments<'ctx>,
) -> bool {
    let mut hidden = arguments.to_vec();
    let Some(first) = hidden.first_mut() else {
        return false;
    };
    *first = crate::sema::models::GenericArgument::Type(gcx.types.existential_self);
    let hidden = gcx.store.interners.intern_generic_args(hidden);
    let signature = gcx.get_signature(method);
    // A projection such as Self::Output can be independently known through an
    // existential binding. Its resolved type is already checked by the caller.
    // Here inspect direct payload occurrences, without treating that projection's
    // receiver as an exposed payload argument/result.
    struct MaskProjections<'ctx>(Gcx<'ctx>);
    impl<'ctx> TypeFolder<'ctx> for MaskProjections<'ctx> {
        fn gcx(&self) -> Gcx<'ctx> {
            self.0
        }
        fn fold_ty(&mut self, ty: Ty<'ctx>) -> Ty<'ctx> {
            if matches!(
                ty.kind(),
                TyKind::Alias {
                    kind: crate::sema::models::AliasKind::Projection,
                    ..
                }
            ) {
                self.0.types.void
            } else {
                ty.super_fold_with(self)
            }
        }
    }
    let instantiate = |ty: Ty<'ctx>| {
        super::instantiate::instantiate_ty_with_args(
            gcx,
            ty.fold_with(&mut MaskProjections(gcx)),
            hidden,
        )
    };
    signature
        .inputs
        .iter()
        .skip(1)
        .any(|input| has_free_self(instantiate(input.ty)))
        || (!returns_owned_self(gcx, method) && has_free_self(instantiate(signature.output)))
}

/// Shift free erased binders when inserting a type beneath nested existentials.
pub(crate) fn shift<'ctx>(gcx: Gcx<'ctx>, ty: Ty<'ctx>, amount: u32) -> Ty<'ctx> {
    if amount == 0 {
        return ty;
    }
    struct Shift<'ctx> {
        gcx: Gcx<'ctx>,
        cutoff: u32,
        amount: u32,
    }
    impl<'ctx> TypeFolder<'ctx> for Shift<'ctx> {
        fn gcx(&self) -> Gcx<'ctx> {
            self.gcx
        }
        fn fold_ty(&mut self, ty: Ty<'ctx>) -> Ty<'ctx> {
            match ty.kind() {
                TyKind::ExistentialSelf(index) if index >= self.cutoff => {
                    Ty::new(TyKind::ExistentialSelf(index + self.amount), self.gcx)
                }
                TyKind::BoxedExistential { .. } => {
                    self.cutoff += 1;
                    let result = ty.super_fold_with(self);
                    self.cutoff -= 1;
                    result
                }
                _ => ty.super_fold_with(self),
            }
        }
    }
    ty.fold_with(&mut Shift {
        gcx,
        cutoff: 0,
        amount,
    })
}

/// Bind an existential interface's payload Self, including receiver-relative
/// defaults/bindings, without capturing the Self of a nested existential.
pub(crate) fn bind<'ctx>(
    gcx: Gcx<'ctx>,
    interface: InterfaceReference<'ctx>,
    self_ty: Ty<'ctx>,
) -> InterfaceReference<'ctx> {
    struct Bind<'ctx> {
        gcx: Gcx<'ctx>,
        self_ty: Ty<'ctx>,
        depth: u32,
    }
    impl<'ctx> TypeFolder<'ctx> for Bind<'ctx> {
        fn gcx(&self) -> Gcx<'ctx> {
            self.gcx
        }
        fn fold_ty(&mut self, ty: Ty<'ctx>) -> Ty<'ctx> {
            match ty.kind() {
                TyKind::ExistentialSelf(index) if index == self.depth => {
                    shift(self.gcx, self.self_ty, self.depth)
                }
                TyKind::ExistentialSelf(index) if index > self.depth => {
                    Ty::new(TyKind::ExistentialSelf(index - 1), self.gcx)
                }
                TyKind::BoxedExistential { .. } => {
                    self.depth += 1;
                    let result = ty.super_fold_with(self);
                    self.depth -= 1;
                    result
                }
                _ => ty.super_fold_with(self),
            }
        }
    }
    interface.fold_with(&mut Bind {
        gcx,
        self_ty,
        depth: 0,
    })
}

/// Metadata additionally records receiver-relative keys, so a runtime query for
/// `any P` with a default Rhs=Self can match the concrete P[Concrete] witness.
pub(crate) fn abstract_concrete<'ctx>(
    gcx: Gcx<'ctx>,
    interface: InterfaceReference<'ctx>,
    self_ty: Ty<'ctx>,
) -> InterfaceReference<'ctx> {
    struct Abstract<'ctx> {
        gcx: Gcx<'ctx>,
        self_ty: Ty<'ctx>,
        depth: u32,
    }
    impl<'ctx> TypeFolder<'ctx> for Abstract<'ctx> {
        fn gcx(&self) -> Gcx<'ctx> {
            self.gcx
        }
        fn fold_ty(&mut self, ty: Ty<'ctx>) -> Ty<'ctx> {
            if ty == self.self_ty {
                return Ty::new(TyKind::ExistentialSelf(self.depth), self.gcx);
            }
            if matches!(ty.kind(), TyKind::BoxedExistential { .. }) {
                self.depth += 1;
                let result = ty.super_fold_with(self);
                self.depth -= 1;
                return result;
            }
            ty.super_fold_with(self)
        }
    }
    interface.fold_with(&mut Abstract {
        gcx,
        self_ty,
        depth: 0,
    })
}

/// A method signature may contain closed existential types, but cannot expose
/// their hidden payload types as independently usable arguments/results.
pub(crate) fn has_free_self(ty: Ty<'_>) -> bool {
    struct Free {
        depth: u32,
    }
    impl<'ctx> TypeVisitor<'ctx> for Free {
        fn visit_ty(&mut self, ty: Ty<'ctx>) -> bool {
            match ty.kind() {
                TyKind::ExistentialSelf(index) => index >= self.depth,
                TyKind::BoxedExistential { .. } => {
                    self.depth += 1;
                    let found = ty.super_visit_with(self);
                    self.depth -= 1;
                    found
                }
                _ => ty.super_visit_with(self),
            }
        }
    }
    ty.visit_with(&mut Free { depth: 0 })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        hir::DefinitionID, mir::test_support::with_test_gcx, sema::models::GenericArgument,
    };

    fn interface<'ctx>(gcx: Gcx<'ctx>, args: Vec<Ty<'ctx>>) -> InterfaceReference<'ctx> {
        InterfaceReference {
            id: DefinitionID::new(
                crate::span::PackageIndex::new(1),
                crate::sema::resolve::models::DefinitionIndex::from_raw(0),
            ),
            arguments: gcx
                .store
                .interners
                .intern_generic_args(args.into_iter().map(GenericArgument::Type).collect()),
            bindings: &[],
        }
    }
    fn erased<'ctx>(gcx: Gcx<'ctx>, args: Vec<Ty<'ctx>>) -> Ty<'ctx> {
        Ty::new(
            TyKind::BoxedExistential {
                interfaces: gcx
                    .store
                    .arenas
                    .global
                    .alloc_slice_clone(&[interface(gcx, args)]),
            },
            gcx,
        )
    }

    #[test]
    fn default_self_boxes_as_the_actual_payload_type() {
        let diagnostics = crate::test_support::analyze_script_diagnostics(
            "interface Other[Rhs = Self] { func marker() -> int32; }\nstruct Counter {}\nconform Counter to Other { func marker() -> int32 { 7 }; }\nfunc main() { var boxed: any Other = Counter {}; }",
        );
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }

    #[test]
    fn hidden_default_results_reject_but_unrelated_known_results_remain_callable() {
        let diagnostics = crate::test_support::analyze_script_diagnostics(
            "interface Factory[Rhs = Self] { func make() -> Rhs; }\nstruct Counter {}\nconform Counter to Factory { func make() -> Counter { Counter {} }; }\nfunc main() { var boxed: any Factory = Counter {}; hidden := boxed.make(); }",
        );
        assert!(
            diagnostics
                .iter()
                .any(|d| d.message.contains("hidden Self type")),
            "{diagnostics:#?}"
        );
        assert!(
            !diagnostics
                .iter()
                .any(|d| d.message.contains("does not conform")),
            "{diagnostics:#?}"
        );
    }

    #[test]
    fn witness_provides_interface_bounds_without_asserting_extra_method_bounds() {
        for (declaration, accepted) in [
            (
                "interface P[Rhs: Bound = Self] { func known() -> int32; }",
                true,
            ),
            (
                "interface P[Rhs = Self] { func known() -> int32 where Rhs: Bound; }",
                false,
            ),
        ] {
            let source = format!(
                "interface Bound {{}}\n{declaration}\nstruct Counter {{}}\nconform Counter to Bound {{}}\nconform Counter to P {{ func known() -> int32 {{ 7 }}; }}\nfunc main() {{ var boxed: any P = Counter {{}}; result := boxed.known(); }}"
            );
            let diagnostics = crate::test_support::analyze_script_diagnostics(&source);
            if accepted {
                assert!(diagnostics.is_empty(), "{source}\n{diagnostics:#?}");
            } else {
                assert!(
                    diagnostics
                        .iter()
                        .any(|d| d.message.contains("does not conform")),
                    "{source}\n{diagnostics:#?}"
                );
            }
        }
    }

    #[test]
    fn nested_defaults_bind_outer_self_without_capturing_inner_self() {
        with_test_gcx(|gcx| {
            let template = erased(
                gcx,
                vec![gcx.types.existential_self, gcx.types.self_type_parameter],
            );
            let args = gcx
                .store
                .interners
                .intern_generic_args(vec![GenericArgument::Type(gcx.types.existential_self)]);
            let lowered = crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args(
                gcx, template, args,
            );
            let TyKind::BoxedExistential { interfaces } = lowered.kind() else {
                panic!("expected erased type");
            };
            assert_eq!(
                interfaces[0].arguments[0],
                GenericArgument::Type(gcx.types.existential_self)
            );
            assert_eq!(
                interfaces[0].arguments[1],
                GenericArgument::Type(Ty::new(TyKind::ExistentialSelf(1), gcx))
            );
            assert!(has_free_self(lowered));
            let root = interface(gcx, vec![gcx.types.existential_self, lowered]);
            let bound = bind(gcx, root, gcx.types.bool);
            let nested = bound.arguments[1].ty().unwrap();
            assert_eq!(
                nested,
                erased(gcx, vec![gcx.types.existential_self, gcx.types.bool])
            );
            assert!(!has_free_self(nested));
            assert_eq!(abstract_concrete(gcx, bound, gcx.types.bool), root);
        });
    }

    #[test]
    fn inserted_free_binders_shift_but_closed_erased_types_do_not() {
        with_test_gcx(|gcx| {
            let closed = erased(gcx, vec![gcx.types.existential_self]);
            let outer_reference = erased(
                gcx,
                vec![
                    gcx.types.existential_self,
                    Ty::new(TyKind::ExistentialSelf(1), gcx),
                ],
            );
            let root = interface(gcx, vec![gcx.types.existential_self, outer_reference]);
            let bound = bind(gcx, root, closed);
            assert_eq!(bound.arguments[0], GenericArgument::Type(closed));
            assert_eq!(
                bound.arguments[1],
                GenericArgument::Type(erased(gcx, vec![gcx.types.existential_self, closed]))
            );
            let shifted = bind(gcx, root, gcx.types.existential_self);
            assert_eq!(shifted, root);
        });
    }

    #[test]
    fn generic_substitution_shifts_free_self_under_an_erased_binder() {
        with_test_gcx(|gcx| {
            let outer = Ty::new(
                TyKind::Parameter(crate::sema::models::GenericParameter {
                    index: 0,
                    name: gcx.intern_symbol("T"),
                }),
                gcx,
            );
            let template = erased(gcx, vec![gcx.types.existential_self, outer]);
            let arguments = gcx
                .store
                .interners
                .intern_generic_args(vec![GenericArgument::Type(gcx.types.existential_self)]);
            let actual = crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args(
                gcx, template, arguments,
            );
            let expected = erased(
                gcx,
                vec![
                    gcx.types.existential_self,
                    Ty::new(TyKind::ExistentialSelf(1), gcx),
                ],
            );
            assert_eq!(
                actual, expected,
                "a superinterface's outer Self must not bind to the nested interface's own Self"
            );
        });
    }

    #[test]
    fn erased_self_depth_survives_metadata_without_becoming_a_generic_argument() {
        with_test_gcx(|gcx| {
            let ty = Ty::new(TyKind::ExistentialSelf(2), gcx);
            let wire = crate::metadata::wire::ty_to_wire(ty);
            assert_eq!(crate::metadata::wire::ty_from_wire(gcx, &wire), ty);
            let args = gcx
                .store
                .interners
                .intern_generic_args(vec![GenericArgument::Type(gcx.types.bool)]);
            assert_eq!(
                crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args(gcx, ty, args),
                ty
            );
            assert!(
                !crate::sema::tycheck::utils::unresolved::contains_unresolved_generics(
                    closed_for_test(gcx)
                )
            );
        });
    }
    fn closed_for_test(gcx: Gcx<'_>) -> Ty<'_> {
        erased(gcx, vec![gcx.types.existential_self])
    }
}

#[cfg(test)]
mod method_abi_tests {
    #[test]
    fn direct_owned_self_results_are_callable_through_erasure() {
        let diagnostics = crate::test_support::analyze_script_diagnostics(
            r#"
interface Duplicate { func duplicate() -> Self; }
struct Counter { value: int32 }
conform Counter to Duplicate {
    func duplicate() -> Self { Counter { value: self.value } }
}
func main() {
    var value: any Duplicate = Counter { value: 7 };
    var next: any Duplicate = value.duplicate();
}
"#,
        );
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }

    #[test]
    fn payload_parameters_and_nested_or_borrowed_self_results_reject() {
        for (requirement, implementation, call) in [
            (
                "func same(_ other: &Self) -> bool;",
                "func same(_ other: &Self) -> bool { true }",
                "var _ = value.same(other);",
            ),
            (
                "func view() -> &Self;",
                "func view() -> &Self { self }",
                "var _ = value.view();",
            ),
            (
                "func pair() -> (Self, int32);",
                "func pair() -> (Self, int32) { (self, 1) }",
                "var _ = value.pair();",
            ),
        ] {
            let source = format!(
                "interface P {{ {requirement} }}\nfunc inspect(_ value: &any P, _ other: &any P) {{ {call} }}\nfunc main() {{}}"
            );
            let _ = implementation; // No concrete impl is needed to reject this erased ABI.
            let diagnostics = crate::test_support::analyze_script_diagnostics(&source);
            assert!(
                diagnostics
                    .iter()
                    .any(|d| d.message.contains("expose its hidden Self type")),
                "{source}\n{diagnostics:#?}"
            );
        }
    }
}
