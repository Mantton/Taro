use super::*;
use crate::{
    mir::test_support::{minimal_body, with_test_gcx},
    sema::models::{
        GenericParameterDefinition, GenericParameterDefinitionKind, SyntheticDefinition,
        SyntheticDefinitionKind,
    },
};

#[test]
fn owned_type_extensions_can_read_and_initialize_private_fields() {
    let errors = crate::test_support::analyze_script_mir_diagnostics(
        "struct Secret { private value: int32 }\nextend Secret {\nfunc get() -> int32 { read := () => self.value; read() }\nstatic func create() -> Secret { Secret { value: 7_i32 } }\n}\nfunc main() { secret := Secret::create(); value := secret.get() }",
    );
    assert!(errors.is_empty(), "{errors:#?}");
}

#[test]
fn generic_owned_conformances_can_witness_private_stored_fields() {
    let errors = crate::test_support::analyze_script_mir_diagnostics(
        "interface Read { func read() -> &int32; }\nstruct Secret[T] { private value: int32; extra: T }\nconform[T] Secret[T] to Read {\nfunc read() -> &int32 { &self.value }\n}\nfunc main() {}",
    );
    assert!(errors.is_empty(), "{errors:#?}");
}

#[test]
fn unrelated_extensions_cannot_access_private_representation() {
    let errors = crate::test_support::analyze_script_mir_diagnostics(
        "struct Secret { private value: int32 }\nstruct Other {}\nextend Other {\nfunc expose(_ secret: &Secret) -> int32 { secret.value }\n}\nfunc main() {}",
    );
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("not visible")),
        "{errors:#?}"
    );
}

#[test]
fn free_functions_still_cannot_fabricate_private_fields() {
    let errors = crate::test_support::analyze_script_mir_diagnostics(
        "struct Secret { private value: int32 }\nfunc fabricate() -> Secret { Secret { value: 1_i32 } }\nfunc main() {}",
    );
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("not visible")),
        "{errors:#?}"
    );
}

#[test]
fn imported_synthetic_function_and_parameter_ids_are_reserved_before_fresh_allocation() {
    with_test_gcx(|gcx| {
        let body = minimal_body(gcx);
        let package = body.owner.package();
        let imported = DefinitionID::new(
            package,
            crate::sema::resolve::models::DefinitionIndex::from_raw(0xF000_0000),
        );
        let parameter = DefinitionID::new(
            package,
            crate::sema::resolve::models::DefinitionIndex::from_raw(0xF000_0001),
        );
        let generics = gcx.store.arenas.generics.alloc(Generics {
            parameters: vec![GenericParameterDefinition {
                id: parameter,
                index: 0,
                name: gcx.intern_symbol("T"),
                kind: GenericParameterDefinitionKind::Type { default: None },
            }],
            has_self: false,
            parent: None,
            parent_count: 0,
        });
        let signature = gcx
            .store
            .arenas
            .function_signatures
            .alloc(LabeledFunctionSignature {
                inputs: vec![],
                output: gcx.types.void,
                is_variadic: false,
                abi: None,
            });
        gcx.register_synthetic_definition(
            imported,
            SyntheticDefinition {
                kind: SyntheticDefinitionKind::Ordinary,
                name: gcx.intern_symbol("imported"),
                generics,
                signature,
                span: body.locals[body.return_local].span,
            },
        );
        let fresh = gcx.allocate_synthetic_id(package);
        assert_ne!(
            fresh, imported,
            "fresh synthesis must not overwrite imported declarations"
        );
        assert_ne!(
            fresh, parameter,
            "compiler-generated parameter identities are also reserved"
        );
        assert!(fresh.index().raw() > parameter.index().raw());
    });
}
