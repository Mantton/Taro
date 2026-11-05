//! Computed getters share ordinary method receiver and value-copy rules.
use crate::test_support::analyze_script_mir_diagnostics;

#[test]
fn g40_computed_value_getters_can_modify_their_receiver_copy() {
    let errors = analyze_script_mir_diagnostics(
        "struct Record { value: int32 }\nextend Record { var next: int32 { get { self.value += 1; self.value } } }\nfunc main() { record := Record { value: 7 }; first := record.next; second := record.next }",
    );
    assert!(errors.is_empty(), "{errors:#?}");
}

#[test]
fn g40_computed_reference_target_getters_use_ordinary_autoref() {
    let errors = analyze_script_mir_diagnostics(
        "struct Record { value: int32 }\nextend &Record { var slot: &int32 { get { &self.value } } }\nfunc main() { var record = Record { value: 7 }; reference := record.slot; *reference = 8; explicit := (&record).slot; *explicit = 9 }",
    );
    assert!(errors.is_empty(), "{errors:#?}");
}

#[test]
fn g40_stored_field_getter_witnesses_need_no_copy_bounds() {
    let errors = analyze_script_mir_diagnostics(
        "interface Value[T] { var value: T { get } }\nstruct Record[T] { readonly value: T }\nconform[T] Record[T] to Value[T] {}\nfunc main() {}",
    );
    assert!(errors.is_empty(), "{errors:#?}");
}

#[test]
fn g40_computed_reference_getters_do_not_implicitly_borrow_returned_values() {
    let source = "struct Record { value: int32 }\nextend &Record { var slot: &int32 { get { &self.value } } }\nfunc record() -> Record { Record { value: 7 } }\n";
    let errors = analyze_script_mir_diagnostics(&format!(
        "{source}func main() {{ reference := record().slot }}"
    ));
    assert!(!errors.is_empty(), "getter invented a writable temporary");
    let errors = analyze_script_mir_diagnostics(&format!(
        "{source}func main() {{ reference := (&record()).slot; *reference = 8 }}"
    ));
    assert!(errors.is_empty(), "explicit reference: {errors:#?}");
}

#[test]
fn g40_generic_reference_getter_results_follow_receiver_substitution() {
    let errors = analyze_script_mir_diagnostics(
        "struct Pair[A, B] { first: A; second: B }\nextend[X, Y] &Pair[Y, X] { var selected: X { get { self.second } } }\nfunc main() { var pair = Pair[int32, bool] { first: 7, second: true }; var selected: bool = pair.selected }",
    );
    assert!(errors.is_empty(), "{errors:#?}");
}
