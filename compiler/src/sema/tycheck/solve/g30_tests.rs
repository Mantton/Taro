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
    let source = "enum Optional[T] { case none; case some(T); }\ninterface Iterator { type Element; func next() -> Optional[Self::Element]; func closeIterator() {}; }\ninterface Iterable { type Element; type Iterator: Iterator[Element = Self::Element]; func iter() -> Self::Iterator; }\nstruct Cursor {}\nconform Cursor to Iterator { type Element = int32; func next() -> int32? { .none }; }\nstruct Source {}\nconform Source to Iterable { type Element = int32; type Iterator = Cursor; func iter() -> Cursor { Cursor {} }; }\nextend Cursor { func next() -> bool { false }; }\nfunc main() { source := Source {}; for value in source {} }";
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

#[test]
fn g30_literal_arguments_take_parameter_types_after_literal_receivers() {
    // The interface method is found only once `Box { v: 0 }` has its default
    // element type; the argument literals still meet the parameter types.
    let source = "struct Box[T] { v: T }\ninterface Takes { func takeIt(_ n: usize) -> usize { n }; func both(_ a: usize, _ b: uint8) -> usize { a }; }\nconform[T] Box[T] to Takes {}\nfunc main() { a := Box { v: 0 }.takeIt(3); b := Box { v: 1.5 }.both(3, 250); c := Box { v: 0 }.takeIt(Box { v: 0 }.takeIt(3)); }";
    let errors = analyze_script_diagnostics(source);
    assert!(errors.is_empty(), "{errors:#?}");
}

#[test]
fn g30_held_literal_arguments_default_before_overload_probes() {
    // With int32 and int64 candidates, the literal keeps its int32 default
    // instead of making the call ambiguous.
    let source = "struct Box[T] { v: T }\ninterface Narrow { func pick(_ n: int32) -> int32 { 32 }; }\ninterface Wide { func pick(_ n: int64) -> int32 { 64 }; }\nconform[T] Box[T] to Narrow {}\nconform[T] Box[T] to Wide {}\nfunc main() { picked := Box { v: 0 }.pick(3); }";
    let errors = analyze_script_diagnostics(source);
    assert!(errors.is_empty(), "{errors:#?}");
}

#[test]
fn g30_existential_arguments_wait_for_deferred_lookup_results() {
    // `Box { v: 0 }.takeIt(3)` resolves only after the receiver's literal
    // default. Its usize result is then boxed for the `any Show` parameter,
    // instead of its type being fixed to `any Show` beforehand.
    let source = "struct Box[T] { v: T }\ninterface Show {}\nconform usize to Show {}\ninterface Takes { func takeIt(_ n: usize) -> usize { n }; }\nconform[T] Box[T] to Takes {}\nfunc show(_ a: any Show, _ b: int32) {}\nfunc pick(_ a: int64, _ b: int32) {}\nfunc pick(_ a: any Show, _ b: int32) {}\nfunc main() { show(Box { v: 0 }.takeIt(3), 1); pick(Box { v: 0 }.takeIt(3), 2); var a: any Show = Box { v: 1.5 }.takeIt(4); if true { total := Box { v: 0 }.takeIt(5); show(total, 3); } }";
    let errors = analyze_script_diagnostics(source);
    assert!(errors.is_empty(), "{errors:#?}");
}

#[test]
fn g30_deferred_lookups_still_see_their_existential_context() {
    // The existential still selects among the lookup's candidates by result
    // type, and a literal argument still takes its type from the
    // existential's argument (int64) rather than its int32 default.
    let source = "struct Box[T] { v: T }\ninterface Show {}\nconform int32 to Show {}\ninterface A { func pick() -> int32 { 1 }; }\ninterface B { func pick() -> any Show { 1 }; }\nconform[T] Box[T] to A {}\nconform[T] Box[T] to B {}\ninterface Holder[V] { func held() -> V; }\nstruct Cell[V] { v: V }\nconform[V] Cell[V] to Holder[V] { func held() -> V { self.v }; }\ninterface Maker { func wrap[U](_ u: U) -> any Holder[U] { Cell[U] { v: u } }; }\nconform[T] Box[T] to Maker {}\nfunc show(_ a: any Show, _ b: int32) {}\nfunc take(_ h: any Holder[int64], _ n: int32) {}\nfunc main() { show(Box { v: 0 }.pick(), 1); take(Box { v: 0 }.wrap(5), 2); }";
    let errors = analyze_script_diagnostics(source);
    assert!(errors.is_empty(), "{errors:#?}");
}

#[test]
fn g30_optional_targets_wait_for_deferred_lookup_results() {
    // `Box { v: 0 }.takeIt(3)` resolves only after the receiver's literal
    // default. Its usize result is then wrapped for the `usize?` parameter,
    // local and return, instead of its type being fixed to `usize?` first.
    let source = "enum Optional[T] { case some(T); case none }\nstruct Box[T] { v: T }\ninterface Takes { func takeIt(_ n: usize) -> usize { n }; }\nconform[T] Box[T] to Takes {}\nfunc pick(_ a: usize?, _ b: int32) {}\nfunc ret() -> usize? { return Box { v: 0 }.takeIt(2) }\nfunc main() { pick(Box { v: 0 }.takeIt(3), 1); var a: usize? = Box { v: 1.5 }.takeIt(4); }";
    let errors = analyze_optional_script(source);
    assert!(errors.is_empty(), "{errors:#?}");
}

#[test]
fn g30_optional_waits_rank_like_concrete_arguments() {
    // The deferred result needs one conversion for either `choose`, and the
    // Optional candidate keeps its concrete type, so it is selected, as for a
    // usize local. `usize` still beats `usize?`. The result types show the
    // selection: `bool` for the Optional candidate, `int32` otherwise.
    let prefix = "enum Optional[T] { case some(T); case none }\nstruct Box[T] { v: T }\ninterface Show {}\nconform usize to Show {}\ninterface Takes { func takeIt(_ n: usize) -> usize { n }; }\nconform[T] Box[T] to Takes {}\nfunc choose(_ a: usize?, _ b: int32) -> bool { false }\nfunc choose(_ a: any Show, _ b: int32) -> int32 { 1 }\nfunc exact(_ a: usize?, _ b: int32) -> bool { false }\nfunc exact(_ a: usize, _ b: int32) -> int32 { 1 }\n";
    for (body, valid) in [
        ("var n: usize = 3; a := choose(n, 1); var b: bool = a;", true),
        ("var n: usize = 3; a := choose(n, 1); var b: int32 = a;", false),
        ("a := choose(Box { v: 0 }.takeIt(3), 1); var b: bool = a;", true),
        ("a := choose(Box { v: 0 }.takeIt(3), 1); var b: int32 = a;", false),
        ("a := exact(Box { v: 0 }.takeIt(3), 1); var b: int32 = a;", true),
    ] {
        let source = format!("{prefix}func main() {{ {body} }}");
        let errors = analyze_optional_script(&source);
        assert_eq!(errors.is_empty(), valid, "{source}\n{errors:#?}");
    }
}

#[test]
fn g30_equal_boxings_stay_ambiguous() {
    // Each candidate wraps one argument and boxes the other.
    let source = "enum Optional[T] { case some(T); case none }\ninterface Show {}\nconform usize to Show {}\nfunc both(_ a: usize?, _ b: any Show) -> int32 { 1 }\nfunc both(_ a: any Show, _ b: usize?) -> int32 { 2 }\nfunc main() { var a: usize = 1; var b: usize = 2; c := both(a, b); }";
    let errors = analyze_optional_script(source);
    assert!(
        errors.iter().any(|error| error.message.contains("ambiguous")),
        "{errors:#?}"
    );
}

fn analyze_optional_script(source: &str) -> Vec<crate::diagnostics::DiagnosticRecord> {
    crate::test_support::analyze_language_item_script(
        source,
        false,
        &[(crate::hir::StdItem::Optional, "Optional")],
    )
}

#[test]
fn g30_coercions_wait_for_operators_on_deferred_lookup_results() {
    // `Box { v: 0 }.width()` resolves only after the receiver's literal
    // default, and `+ one` waits for it. The existential and the Optional take
    // the operator's usize result once known, instead of fixing its type to
    // the target first.
    let source = "enum Optional[T] { case some(T); case none }\nstruct Box[T] { v: T }\ninterface Show {}\nconform usize to Show {}\ninterface Width[U] { func width() -> usize { 4 }; }\nconform Box[int32] to Width[bool] {}\nfunc show(_ a: any Show, _ b: any Show) {}\nfunc main() { var one: usize = 1; var a: any Show = Box { v: 0 }.width() + one; var b: usize? = Box { v: 0 }.width() * one; show(one, Box { v: 0 }.width() - one); }";
    let errors = analyze_optional_script(source);
    assert!(errors.is_empty(), "{errors:#?}");
}
