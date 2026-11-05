//! A fixed associated binding is distinct from a method's dynamic Self promise.
use crate::sema::models::{GenericArgument, InterfaceReference, SelectionMode};

#[test]
fn g33_associated_defaults_use_the_interface_argument_environment() {
    crate::test_support::analyze_script(
        "interface Value[A] { type Output = A; }\nstruct Source[T] {}\nconform[T] Source[T] to Value[int32] {}\nfunc main() {}",
        |package, gcx| {
            let interface = package.root.declarations[0].id;
            let source = gcx.get_type(package.root.declarations[1].id);
            let args = gcx.store.interners.intern_generic_args(vec![
                GenericArgument::Type(source),
                GenericArgument::Type(gcx.types.int32),
            ]);
            let reference = InterfaceReference {
                id: interface,
                arguments: args,
                bindings: &[],
            };
            let witness = gcx
                .build_conformance_witness(
                    reference.to_goal(gcx, &[]).unwrap(),
                    SelectionMode::Typecheck,
                )
                .unwrap();
            let output = gcx.get_interface_requirements(interface).unwrap().types[0].id;
            assert_eq!(witness.type_witnesses[&output], gcx.types.int32);
        },
    );
}

#[test]
fn g33_fixed_self_associated_results_are_not_dynamic_self_results() {
    for binding in ["type Output = Self;", ""] {
        let source = format!(
            "interface Source {{ type Output = Self; func read() -> Self::Output; }}\nclass Base {{}}\nconform Base to Source {{ {binding} func read() -> Base {{ self }}; }}\nclass Child: Base {{}}\nfunc check(_ value: Child) -> Base {{ value.read() }}\nfunc main() {{}}"
        );
        crate::test_support::analyze_script(&source, |package, gcx| {
            let base = gcx.get_type(package.root.declarations[1].id);
            assert!(
                gcx.class_methods(base)
                    .iter()
                    .all(|method| !method.returns_self)
            );
        });
    }
}

#[test]
fn g33_generic_final_override_cannot_change_an_inherited_binding_when_unused() {
    let diagnostics = crate::test_support::analyze_script_diagnostics(
        "interface Source { type Output; func read() -> int32; }\nclass Base[T] {}\nconform[T] Base[T] to Source { type Output = T; func read() -> int32 { 1 }; }\nfinal class Child[T]: Base[T] {}\nconform[T] Child[T] to Source { type Output = bool; override func read() -> int32 { 2 }; }\nfunc main() {}",
    );
    assert!(
        diagnostics.iter().any(|diagnostic| diagnostic
            .message
            .contains("cannot change inherited associated type bindings")),
        "{diagnostics:#?}"
    );
}

#[test]
fn g33_unknown_associated_results_cannot_be_selected_by_expected_type() {
    for output in ["int32", "any Source"] {
        let source = format!(
            "interface Source {{ type Output; func read() -> Self::Output; }}\nfunc check(_ value: any Source) -> {output} {{ value.read() }}\nfunc main() {{}}"
        );
        let diagnostics = crate::test_support::analyze_script_diagnostics(&source);
        assert!(
            !diagnostics.is_empty(),
            "unknown result was accepted as {output}"
        );
    }
}

#[test]
fn g33_inherited_generic_projections_are_already_in_receiver_coordinates() {
    crate::test_support::analyze_script(
        r#"
interface Read { type Output; func read() -> &Self::Output; }
class Base[A, B] { value: A }
conform[Y, X] Base[X, Y] to Read { type Output = X; func read() -> &X { &self.value }; }
class Child[U, V]: Base[V, U] {}
func check[U, V](_ value: Child[U, V]) -> &V { value.read() }
func main() {}
"#,
        |_, _| {},
    );
}

#[test]
fn g33_associated_default_cycles_are_diagnosed() {
    let diagnostics = crate::test_support::analyze_script_diagnostics(
        "interface Cycle { type Output = Self::Output; }\nstruct Source: Cycle {}\nfunc main() {}",
    );
    assert!(
        !diagnostics.is_empty(),
        "a self-dependent default has no concrete witness"
    );
}

#[test]
fn g33_forward_associated_defaults_resolve_at_the_declaration() {
    crate::test_support::analyze_script(
        "interface Value[A] { type Output = Self::Other; type Other = A; }\nstruct Source: Value[int32] {}\nfunc main() {}",
        |package, gcx| {
            let reference = InterfaceReference {
                id: package.root.declarations[0].id,
                arguments: gcx.store.interners.intern_generic_args(vec![
                    GenericArgument::Type(gcx.get_type(package.root.declarations[1].id)),
                    GenericArgument::Type(gcx.types.int32),
                ]),
                bindings: &[],
            };
            let witness = gcx
                .build_conformance_witness(
                    reference.to_goal(gcx, &[]).unwrap(),
                    SelectionMode::Codegen,
                )
                .unwrap();
            assert!(
                witness
                    .type_witnesses
                    .values()
                    .all(|ty| *ty == gcx.types.int32)
            );
        },
    );
}
