//! Independent conformance families and explicit inherited witness overrides.
#[test]
fn g32_identical_methods_have_independent_families() {
    crate::test_support::analyze_script(
        r#"
interface Left { func read() -> int32 { 1 }; }
interface Right { func read() -> int32 { 2 }; }
class Base: Left, Right {}
extend Base { func read() -> int32 { 3 }; }
class Child: Base {}
extend Child { override func read() -> int32 { 4 }; }
func main() {}
"#,
        |package, gcx| {
            let base = gcx.get_type(package.root.declarations[2].id);
            let child = gcx.get_type(package.root.declarations[4].id);
            let base_methods = gcx.class_methods(base);
            assert_eq!(base_methods.len(), 3);
            let child_methods = gcx.class_methods(child);
            assert_eq!(child_methods.len(), 3);
            assert_eq!(
                child_methods
                    .iter()
                    .filter(|slot| slot.owner == child)
                    .count(),
                1
            );
        },
    );
}

#[test]
fn g32_partial_override_preserves_the_inherited_family() {
    crate::test_support::analyze_script(
        r#"
interface Readable { func read() -> int32; func other() -> int32; }
class Base {}
conform Base to Readable { func read() -> int32 { 1 }; func other() -> int32 { 2 }; }
class Child: Base {}
conform Child to Readable { override func read() -> int32 { 3 }; }
func generic[T: Readable](_ value: T) -> int32 { value.read() + value.other() }
func main() {}
"#,
        |package, gcx| {
            let base = gcx.get_type(package.root.declarations[1].id);
            let child = gcx.get_type(package.root.declarations[3].id);
            for method in gcx.class_methods(base) {
                let selected = gcx.class_method(child, method.family).unwrap();
                assert_eq!(selected.family, method.family);
                assert_eq!(
                    selected.owner == child,
                    gcx.symbol_text(gcx.definition_ident(method.family).symbol).as_str() == "read"
                );
            }
            assert_eq!(gcx.class_methods(child).len(), 2);
        },
    );
}

#[test]
fn g32_inherent_methods_do_not_satisfy_required_witnesses() {
    let diagnostics = crate::test_support::analyze_script_diagnostics(
        "interface Readable { func read() -> int32; }\nclass Base: Readable {}\nextend Base { func read() -> int32 { 1 }; }\nfunc main() {}",
    );
    assert!(
        !diagnostics.is_empty(),
        "an unrelated inherent method must not become a witness"
    );
}

#[test]
fn g32_identical_defaults_require_qualification_at_call_site() {
    crate::test_support::analyze_script(
        "interface Left { func read() -> int32 { 1 }; }\ninterface Right { func read() -> int32 { 2 }; }\nclass Base: Left, Right {}\nfunc check(_ value: Base) -> int32 { Left::read(value) + Right::read(value) }\nfunc main() {}",
        |_, _| {},
    );
    let diagnostics = crate::test_support::analyze_script_diagnostics(
        "interface Left { func read() -> int32 { 1 }; }\ninterface Right { func read() -> int32 { 2 }; }\nclass Base: Left, Right {}\nfunc check(_ value: Base) -> int32 { value.read() }\nfunc main() {}",
    );
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.message.contains("ambiguous")),
        "{diagnostics:#?}"
    );
}

#[test]
fn g32_override_is_scoped_to_the_matching_conformance() {
    for (body, expected) in [
        (
            "conform Child to Left { func read() -> int32 { 3 }; }",
            "requires override",
        ),
        (
            "extend Child { override func read() -> int32 { 3 }; }",
            "override has no inherited",
        ),
        (
            "conform Child to Right { override func read() -> int32 { 3 }; }",
            "override has no inherited",
        ),
    ] {
        let source = format!(
            "interface Left {{ func read() -> int32; }}\ninterface Right {{ func read() -> int32; }}\nclass Base {{}}\nconform Base to Left {{ func read() -> int32 {{ 1 }}; }}\nclass Child: Base {{}}\n{body}\nfunc main() {{}}"
        );
        let diagnostics = crate::test_support::analyze_script_diagnostics(&source);
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message.contains(expected)),
            "{body}: {diagnostics:#?}"
        );
    }
}

#[test]
fn g32_final_generic_subclass_keeps_fixed_instantiations_and_partial_bodies() {
    crate::test_support::analyze_script(
        r#"
interface Readable[A] { func read() -> int32; func echo[T](_ value: T) -> T; }
final class Child[T]: Base[T] {}
conform[T] Child[T] to Readable[int32] { override func read() -> int32 { 3 }; }
class Base[T] {}
conform[T] Base[T] to Readable[int32] { func read() -> int32 { 1 }; func echo[U](_ value: U) -> U { value }; }
conform[T] Base[T] to Readable[bool] { func read() -> int32 { 2 }; func echo[U](_ value: U) -> U { value }; }
func main() {}
"#,
        |package, gcx| {
            let child = gcx.get_type(package.root.declarations[1].id);
            let base = gcx.class_base(child).unwrap();
            let methods = gcx.class_methods(child);
            assert_eq!(methods.len(), 4);
            assert_eq!(methods.iter().filter(|slot| slot.owner == child).count(), 1);
            assert_eq!(gcx.class_methods(base).len(), 4);
        },
    );
}

#[test]
fn g32_override_cannot_change_inherited_associated_binding() {
    for (output, valid) in [("int32", true), ("int64", false)] {
        let source = format!(
            "interface Readable {{ type Output; func read() -> int32; }}\nclass Base {{}}\nconform Base to Readable {{ type Output = int32; func read() -> int32 {{ 1 }}; }}\nclass Child: Base {{}}\nconform Child to Readable {{ type Output = {output}; override func read() -> int32 {{ 2 }}; }}\nfunc main() {{}}"
        );
        let diagnostics = crate::test_support::analyze_script_diagnostics(&source);
        assert_eq!(diagnostics.is_empty(), valid, "{output}: {diagnostics:#?}");
    }
}

#[test]
fn g32_witness_bounds_compare_resolved_associated_bindings() {
    crate::test_support::analyze_script(
        r#"
interface Iterator { type Element; }
interface FromIterator {
    type Element;
    static func fromIter[I: Iterator[Element = Self::Element]](_ iter: &I) -> Self;
}
struct List[T] {}
conform[T] List[T] to FromIterator {
    type Element = T;
    static func fromIter[I: Iterator[Element = T]](_ iter: &I) -> Self { List[T] {} };
}
func main() {}
"#,
        |_, _| {},
    );
}

#[test]
fn g32_partial_overrides_keep_inherited_properties_and_constants() {
    crate::test_support::analyze_script(
        r#"
interface Readable {
    const MAGIC: int32;
    var value: int32 { get };
    func read() -> int32;
}
class Base { data: int32 }
conform Base to Readable {
    const MAGIC: int32 = 7;
    var value: int32 { get { self.data } };
    func read() -> int32 { 1 };
}
class Child: Base {}
conform Child to Readable { override func read() -> int32 { 2 }; }
func main() {}
"#,
        |package, gcx| {
            let child = gcx.get_type(package.root.declarations[3].id);
            let args = gcx
                .store
                .interners
                .intern_generic_args(vec![crate::sema::models::GenericArgument::Type(child)]);
            let reference = crate::sema::models::InterfaceReference {
                id: package.root.declarations[0].id,
                arguments: args,
                bindings: &[],
            };
            let witness = gcx
                .build_conformance_witness(
                    reference.to_goal(gcx, &[]).unwrap(),
                    crate::sema::models::SelectionMode::Codegen,
                )
                .unwrap();
            assert_eq!(witness.constant_witnesses.len(), 1);
            assert_eq!(witness.method_witnesses.len(), 2);
        },
    );
}

#[test]
fn g32_qualified_interface_calls_preserve_explicit_arguments() {
    crate::test_support::analyze_script(
        "interface Reader[A] { func read() -> int32 { 1 }; }\nclass Base: Reader[int32] {}\nfunc check(_ value: Base) -> int32 { Reader[int32]::read(value) }\nfunc main() {}",
        |_, _| {},
    );
}
