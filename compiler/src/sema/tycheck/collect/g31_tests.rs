//! Coherence uses ordered inputs, not just the receiver's constructor.
use super::*;
use crate::{
    hir::Mutability,
    sema::models::{AdtDef, TyKind},
};

fn with_types(test: impl for<'ctx> FnOnce(Gcx<'ctx>, Ty<'ctx>, Ty<'ctx>, Ty<'ctx>)) {
    crate::test_support::analyze_script(
        "struct Local {}\nstruct Wrapper[T] {}\nfunc main() {}",
        |package, gcx| {
            let ty = |name: &str| {
                gcx.get_type(
                    package
                        .root
                        .declarations
                        .iter()
                        .find(|declaration| declaration.identifier.symbol.as_str() == name)
                        .unwrap()
                        .id,
                )
            };
            let local = ty("Local");
            let TyKind::Adt(def, arguments) = ty("Wrapper").kind() else {
                unreachable!()
            };
            let foreign = Ty::new(
                TyKind::Adt(
                    AdtDef {
                        id: DefinitionID::new(PackageIndex::new(2), def.id.index()),
                        ..def
                    },
                    arguments,
                ),
                gcx,
            );
            let GenericArgument::Type(parameter) = arguments[0] else {
                unreachable!()
            };
            test(gcx, local, foreign, parameter);
        },
    );
}

fn allowed<'ctx>(gcx: Gcx<'ctx>, receiver: Ty<'ctx>, inputs: &[Ty<'ctx>]) -> bool {
    let interface = InterfaceReference {
        id: DefinitionID::new(
            PackageIndex::new(2),
            crate::sema::resolve::models::DefinitionIndex::from_raw(999),
        ),
        arguments: gcx.store.interners.intern_generic_args(
            std::iter::once(receiver)
                .chain(inputs.iter().copied())
                .map(GenericArgument::Type)
                .collect(),
        ),
        bindings: &[],
    };
    crate::sema::tycheck::utils::coherence::check_orphan(gcx, interface, gcx.package_index())
        .is_ok()
}

#[test]
fn g31_foreign_receiver_accepts_a_local_interface_input() {
    with_types(|gcx, local, _, _| assert!(allowed(gcx, gcx.types.int32, &[local])));
}

#[test]
fn g31_covered_parameters_before_a_local_input_are_allowed() {
    with_types(|gcx, local, foreign, parameter| {
        for receiver in [
            foreign,
            Ty::new(
                TyKind::Tuple(gcx.store.interners.intern_ty_list(vec![parameter])),
                gcx,
            ),
            Ty::new(TyKind::Pointer(parameter, Mutability::Immutable), gcx),
        ] {
            assert!(
                allowed(gcx, receiver, &[local]),
                "covered constructor before local RHS"
            );
        }
    });
}

#[test]
fn g31_only_references_propagate_locality() {
    with_types(|gcx, local, foreign, _| {
        let reference = Ty::new(TyKind::Reference(local), gcx);
        assert!(allowed(gcx, reference, &[]));
        assert!(!allowed(
            gcx,
            Ty::new(TyKind::Pointer(local, Mutability::Immutable), gcx),
            &[]
        ));
        let TyKind::Adt(def, _) = foreign.kind() else {
            unreachable!()
        };
        let wrapped = Ty::new(
            TyKind::Adt(
                def,
                gcx.store
                    .interners
                    .intern_generic_args(vec![GenericArgument::Type(local)]),
            ),
            gcx,
        );
        assert!(!allowed(gcx, wrapped, &[]));
    });
}

#[test]
fn g31_uncovered_inputs_before_the_first_local_input_are_rejected() {
    with_types(|gcx, local, foreign, parameter| {
        assert!(!allowed(gcx, parameter, &[local]));
        assert!(!allowed(
            gcx,
            Ty::new(TyKind::Reference(parameter), gcx),
            &[local]
        ));
        assert!(!allowed(gcx, gcx.types.int32, &[parameter, local]));
        assert!(allowed(gcx, local, &[parameter]));
        assert!(allowed(gcx, gcx.types.int32, &[foreign, local, parameter]));
    });
}

#[test]
fn g31_argument_owners_are_searched_even_without_a_receiver_owner() {
    with_types(|gcx, _, foreign, _| {
        let TyKind::Adt(def, arguments) = foreign.kind() else {
            unreachable!()
        };
        let owner = PackageIndex::new(3);
        let rhs = Ty::new(
            TyKind::Adt(
                AdtDef {
                    id: DefinitionID::new(owner, def.id.index()),
                    ..def
                },
                arguments,
            ),
            gcx,
        );
        let arguments = gcx
            .store
            .interners
            .intern_generic_args(vec![GenericArgument::Type(Ty::new(
                TyKind::Reference(rhs),
                gcx,
            ))]);
        let interface = DefinitionID::new(PackageIndex::new(2), def.id.index());
        assert!(
            gcx.conformance_ownership_packages(interface, gcx.types.int32, arguments)
                .contains(&owner)
        );
    });
}

#[test]
fn g31_aliases_preserve_reference_but_not_raw_pointer_locality() {
    crate::test_support::analyze_script(
        "struct Local {}\ntype RefAlias = &Local\ntype RawAlias = *const Local\nfunc main() {}",
        |package, gcx| {
            let alias = |name: &str| {
                let id = package
                    .root
                    .declarations
                    .iter()
                    .find(|declaration| declaration.identifier.symbol.as_str() == name)
                    .unwrap()
                    .id;
                Ty::new(
                    TyKind::Alias {
                        kind: crate::sema::models::AliasKind::Weak,
                        def_id: id,
                        args: Default::default(),
                    },
                    gcx,
                )
            };
            assert!(allowed(gcx, alias("RefAlias"), &[]));
            assert!(!allowed(gcx, alias("RawAlias"), &[]));
        },
    );
}

#[test]
fn g31_overlap_is_independent_of_declaration_order_and_missing_positive_bounds() {
    for definitions in [
        "conform[T: Source] Box[T] to Target {}\nconform[T: Other] Box[T] to Target {}",
        "conform[T: Other] Box[T] to Target {}\nconform[T: Source] Box[T] to Target {}",
    ] {
        let source = format!(
            "interface Source {{}}\ninterface Other {{}}\ninterface Target {{}}\nstruct Box[T] {{}}\n{definitions}\nfunc main() {{}}"
        );
        let errors = crate::test_support::analyze_script_diagnostics(&source);
        assert!(
            errors
                .iter()
                .any(|error| error.message.contains("conflicting conformance")),
            "{errors:#?}"
        );
    }
}

#[test]
fn g31_aliases_and_associated_outputs_do_not_distinguish_overlapping_headers() {
    let errors = crate::test_support::analyze_script_diagnostics(
        "interface Target { type Output; }\nstruct Value {}\ntype Alias = Value\nconform Value to Target { type Output = int32; }\nconform Alias to Target { type Output = bool; }\nfunc main() {}",
    );
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("conflicting conformance")),
        "{errors:#?}"
    );
}

#[test]
fn g31_distinct_const_headers_remain_disjoint() {
    let errors = crate::test_support::analyze_script_diagnostics(
        "interface Target {}\nstruct Value[const N: usize] {}\nconform Value[1] to Target {}\nconform Value[2] to Target {}\nfunc main() {}",
    );
    assert!(errors.is_empty(), "{errors:#?}");
}

#[test]
fn g31_generic_alias_conformances_match_the_underlying_target() {
    let errors = crate::test_support::analyze_script_diagnostics(
        "interface Target {}\ntype Alias[T, const N: usize] = [T; N]\nconform[T, const N: usize] Alias[T, N] to Target {}\nfunc require[V: Target](_ value: V) {}\nfunc main() { require([1, 2]); }",
    );
    assert!(errors.is_empty(), "{errors:#?}");
}
