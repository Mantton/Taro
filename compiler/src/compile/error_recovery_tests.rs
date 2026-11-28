//! Editor analysis keeps checking after errors. Each case is a program the
//! strict pipeline stops on; the recovering pipeline must neither panic nor
//! lose the facts of an unrelated, valid function.

use crate::{
    compile::{analysis_products::AnalysisProduct, config::HarnessMode},
    test_support::{recovering_errors, with_source_compiler},
};

const PROBE: &str = "\nfunc probe(_ value: int32) -> int32 { value }\nfunc main() {}\n";

fn analyze(source: &str) -> AnalysisProduct {
    let source = format!("{source}{PROBE}");
    analyze_exactly(&source)
}

fn analyze_exactly(source: &str) -> AnalysisProduct {
    recovering_errors(|| check_strictly(source))
}

fn check_strictly(source: &str) -> AnalysisProduct {
    with_source_compiler(
        &[("main.tr", source)],
        true,
        HarnessMode::None,
        |compiler| compiler.analyze_partial_owned(1),
    )
}

fn messages(product: &AnalysisProduct) -> Vec<&str> {
    product
        .diagnostics
        .iter()
        .map(|diagnostic| diagnostic.message.as_str())
        .collect()
}

#[track_caller]
fn assert_recovers(source: &str) {
    let product = analyze(source);
    assert!(
        !product.diagnostics.is_empty(),
        "the program should still report its error"
    );
    let strict = check_strictly(&format!("{source}{PROBE}"));
    assert_eq!(
        messages(&product),
        messages(&strict),
        "recovery must not add follow-on errors"
    );
    assert!(!product.complete);
    assert!(
        product
            .occurrences
            .iter()
            .any(|fact| fact.local_declaration.is_some()),
        "the valid function lost its facts: {:?}",
        product.diagnostics
    );
}

#[test]
fn a_script_without_main_keeps_its_facts() {
    let product = analyze_exactly("func probe(_ value: int32) -> int32 { value }");
    assert!(!product.complete);
    assert!(
        product
            .occurrences
            .iter()
            .any(|fact| fact.local_declaration.is_some()),
        "{:?}",
        product.diagnostics
    );
}

#[test]
fn an_unresolved_name_keeps_other_functions_checked() {
    assert_recovers("func broken() -> int32 { missing }");
}

#[test]
fn a_type_error_keeps_other_functions_checked() {
    assert_recovers("func broken() -> int32 { true }");
}

#[test]
fn an_unknown_type_in_a_signature_is_an_error_type() {
    assert_recovers("func broken(_ value: Missing) {}");
}

#[test]
fn an_unknown_conformance_is_skipped() {
    assert_recovers("struct Point: Missing { x: int32 }");
}

#[test]
fn an_unknown_generic_bound_is_skipped() {
    assert_recovers("func share[T: Missing](_ value: T) -> T { value }");
}

#[test]
fn an_unknown_qualified_type_is_an_error_type() {
    assert_recovers("func broken() { var value: missing::Thing = 1 }");
}

#[test]
fn a_nested_type_capturing_generics_is_skipped() {
    assert_recovers("struct Queue[T] { value: T }\nextend[T] Queue[T] {\n    struct Entry(T)\n}");
}

#[test]
fn a_nested_type_in_a_specialized_extension_is_skipped() {
    assert_recovers(
        "struct Queue[T] { value: T }\nextend Queue[int32] {\n    enum State { case ready }\n}",
    );
}

#[test]
fn a_nested_type_through_a_specialized_owner_is_an_error() {
    assert_recovers(
        "struct Queue[T] { value: T }\nextend Queue {\n    struct Entry(int64)\n}\nfunc broken() { var entry = Queue[int32]::Entry(42) }",
    );
}

#[test]
fn an_interface_used_as_a_value_type_is_an_error_type() {
    assert_recovers(
        "@onUnsatisfied(\"{Self} needs an Item witness\")\ninterface Source { type Item; }\nfunc accept(_ source: Source) {}",
    );
}

#[test]
fn a_missing_embedded_asset_is_an_error_expression() {
    assert_recovers("func broken() { var data = #embed(\"missing-asset.txt\") }");
}

#[test]
fn a_discard_read_is_an_error_expression() {
    assert_recovers("func apply(_ f: (int32) -> int32) {}\nfunc broken() { apply(_ => _); }");
}

#[test]
fn a_compound_assignment_to_a_discard_is_an_error_expression() {
    assert_recovers("func broken() { _ += 1; }");
}

#[test]
fn a_cyclic_interface_inheritance_terminates() {
    let (done, finished) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        assert_recovers("interface Recursive[T]: Recursive[(T,)] {}");
        let _ = done.send(());
    });
    finished
        .recv_timeout(std::time::Duration::from_secs(30))
        .expect("analysis of a cyclic interface should finish");
}
