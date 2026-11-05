//! Ordinary receiver lookup and overload rules (G30).
use crate::test_support::analyze_script_diagnostics;

#[test]
fn g30_distinct_interface_instantiations_keep_their_own_declarations() {
    let errors = analyze_script_diagnostics(
        "interface Slot[T] { func get() -> T; }\nstruct Value {}\nconform Value to Slot[int32] { func get() -> int32 { 1 }; }\nconform Value to Slot[bool] { func get() -> bool { true }; }\nfunc main() {}",
    );
    assert!(errors.is_empty(), "{errors:#?}");
}

#[test]
fn g30_complete_erased_sets_remain_visible_after_another_method_call() {
    let errors = analyze_script_diagnostics(
        "interface Read { func read() -> int32; }\ninterface Write { func written() -> int32; }\nfunc use(_ value: any Read & Write) -> int32 { value.read() + value.written() }\nfunc main() {}",
    );
    assert!(errors.is_empty(), "{errors:#?}");
}

#[test]
fn g30_blanket_methods_supplement_declared_generic_bounds() {
    let errors = analyze_script_diagnostics(
        "interface Source { func source() -> int32; }\ninterface Adapted { type Output; func adapted() -> Self::Output; }\nconform[T: Source] T to Adapted { type Output = int32; func adapted() -> int32 { self.source() }; }\nfunc use[T: Source](_ value: T) -> int32 { value.adapted() }\nfunc main() {}",
    );
    assert!(errors.is_empty(), "{errors:#?}");
}

#[test]
fn g30_applicable_inherent_methods_precede_interface_methods() {
    for use_site in [
        "value.choose(1)",
        "{ callback := value.choose; callback(1) }",
    ] {
        let source = format!(
            "interface Choose {{ func choose(_ number: int32) -> int32; }}\nstruct Value {{}}\nextend Value {{ func choose(_ number: int32) -> int32 {{ number }}; }}\nconform Value to Choose {{ func choose(_ number: int32) -> int32 {{ number + 1 }}; }}\nfunc main() {{ value := Value {{}}; answer := {use_site}; }}"
        );
        let errors = analyze_script_diagnostics(&source);
        assert!(errors.is_empty(), "{source}\n{errors:#?}");
    }
}

#[test]
fn g30_inapplicable_inherent_methods_allow_interface_defaults() {
    let source = "interface Choose { func choose(_ flag: bool) -> bool { flag }; }\nstruct Value {}\nextend Value { func choose(_ number: int32) -> int32 { number }; }\nconform Value to Choose {}\nfunc main() { value := Value {}; answer := value.choose(true); }";
    let errors = analyze_script_diagnostics(source);
    assert!(errors.is_empty(), "{errors:#?}");
}

#[test]
fn g30_inherited_static_overloads_remain_visible() {
    let source = "class Base {}\nclass Derived: Base {}\nextend Base { static func choose(_ flag: bool) -> bool { flag }; }\nextend Derived { static func choose(_ number: int32) -> int32 { number }; }\nfunc main() { flag := Derived::choose(true); number := Derived::choose(1); }";
    let errors = analyze_script_diagnostics(source);
    assert!(errors.is_empty(), "{errors:#?}");
}

#[test]
fn g30_exact_arguments_precede_class_conversions() {
    let source = "class Base {}\nclass Derived: Base {}\nfunc choose(_ value: Base) -> int32 { 1 }\nfunc choose(_ value: Derived) -> int32 { 2 }\nfunc use(_ value: Derived) -> int32 { choose(value) }\nfunc main() {}";
    let errors = analyze_script_diagnostics(source);
    assert!(errors.is_empty(), "{errors:#?}");
}

#[test]
fn g30_return_only_overloads_are_rejected_without_a_call() {
    for source in [
        "struct Value {}\nextend Value { func choose() -> int32 { 1 }; func choose() -> bool { true }; }\nfunc main() {}",
        "struct Value {}\nextend Value { static func choose() -> int32 { 1 }; static func choose() -> bool { true }; }\nfunc main() {}",
        "func choose() -> int32 { 1 }\nfunc choose() -> bool { true }\nfunc main() {}",
        "interface Choose { func choose() -> int32; func choose() -> bool; }\nfunc main() {}",
    ] {
        let errors = analyze_script_diagnostics(source);
        assert!(
            errors
                .iter()
                .any(|error| error.message.contains("redeclaration")
                    || error.message.contains("return type")),
            "{source}\n{errors:#?}"
        );
    }
}

#[test]
fn g30_exact_arguments_precede_wrapping_and_erasure() {
    for source in [
        "func choose(_ value: int32?) -> int32 { 1 }\nfunc choose(_ value: int32) -> int32 { 2 }\nfunc use(_ value: int32) -> int32 { choose(value) }\nfunc main() {}",
        "interface Tag { func tag() -> int32; }\nstruct Value {}\nconform Value to Tag { func tag() -> int32 { 1 }; }\nfunc choose(_ value: any Tag) -> int32 { 1 }\nfunc choose(_ value: Value) -> int32 { 2 }\nfunc use(_ value: Value) -> int32 { choose(value) }\nfunc main() {}",
    ] {
        let source = format!("enum Optional[T] {{ case none; case some(T); }}\n{source}");
        let errors = crate::test_support::analyze_language_item_script(
            &source,
            false,
            &[(crate::hir::StdItem::Optional, "Optional")],
        );
        assert!(errors.is_empty(), "{source}\n{errors:#?}");
    }
}

#[test]
fn g30_static_lookup_keeps_caller_inference_variables_in_their_context() {
    let errors = analyze_script_diagnostics(
        "struct Container[T] { value: T }\nextend[T] Container[T] { static func make(_ value: T) -> Container[T] { Container[T] { value } }; }\nfunc main() { value := Container::make(1); }",
    );
    assert!(errors.is_empty(), "{errors:#?}");
}

#[test]
fn g30_inherited_static_arguments_preserve_base_specialization() {
    let prefix = "class Base[T] {}\nclass Derived: Base[bool] {}\nextend[T] Base[T] { static func identity(_ value: T) -> T { value }; }\n";
    let valid = analyze_script_diagnostics(&format!(
        "{prefix}func main() {{ value := Derived::identity(true); }}"
    ));
    assert!(valid.is_empty(), "{valid:#?}");
    let invalid = analyze_script_diagnostics(&format!(
        "{prefix}func main() {{ value := Derived::identity(1); }}"
    ));
    assert!(
        !invalid.is_empty(),
        "the inherited method must still require bool"
    );
}

#[test]
fn g30_inherited_static_methods_rebase_reordered_parent_and_own_arguments() {
    let prefix = "class Base[A, B] {}\nclass Derived[X]: Base[bool, X] {}\nextend[L, R] Base[R, L] { static func pick[U](_ value: L, _ other: U) -> L { value }; }\n";
    let valid = analyze_script_diagnostics(&format!(
        "{prefix}func main() {{ value := Derived[int32]::pick[string](1, \"other\"); }}"
    ));
    assert!(valid.is_empty(), "{valid:#?}");
    let invalid = analyze_script_diagnostics(&format!(
        "{prefix}func main() {{ value := Derived[int32]::pick[string](true, \"other\"); }}"
    ));
    assert!(!invalid.is_empty(), "the inherited input must remain int32");
}

#[test]
fn g30_callable_fields_do_not_allocate_an_unused_method_receiver() {
    let source = "interface Fn[Args, Output] { func call(_ args: Args) -> Output; }\nstruct Adapter[F] { callback: F }\nextend[F: Fn[(int32,), bool]] Adapter[F] { func run() -> bool { self.callback(1) }; }\nfunc main() {}";
    let errors = crate::test_support::analyze_language_item_script(
        source,
        false,
        &[(crate::hir::StdItem::Fn, "Fn")],
    );
    assert!(errors.is_empty(), "{errors:#?}");
}

#[test]
fn g30_private_static_overloads_do_not_hide_accessible_base_methods() {
    let errors = analyze_script_diagnostics(
        "class Base {}\nclass Derived: Base {}\nextend Base { public static func pick(_ value: int32) -> int32 { value }; }\nextend Derived { private static func pick(_ value: int32) -> bool { true }; }\nfunc main() { var value: int32 = Derived::pick(1); }",
    );
    assert!(errors.is_empty(), "{errors:#?}");
}

#[test]
fn g30_for_loops_use_language_requirements_before_std_is_built() {
    let source = "enum Optional[T] { case none; case some(T); }\ninterface Iterator { type Element; func next() -> Optional[Self::Element]; }\ninterface Iterable { type Element; type Iterator: Iterator[Element = Self::Element]; func iter() -> Self::Iterator; }\nstruct Cursor {}\nconform Cursor to Iterator { type Element = int32; func next() -> int32? { .none }; }\nstruct Source {}\nconform Source to Iterable { type Element = int32; type Iterator = Cursor; func iter() -> Cursor { Cursor {} }; }\nextend Cursor { func next() -> bool { false }; }\nfunc main() { source := Source {}; for value in source {} }";
    crate::test_support::analyze_native_class_fixture(
        source,
        &[],
        &[
            (crate::hir::StdItem::Optional, "Optional"),
            (crate::hir::StdItem::Iterator, "Iterator"),
            (crate::hir::StdItem::Iterable, "Iterable"),
        ],
        |_, _, _| {},
    );
}
