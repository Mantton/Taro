use crate::test_support::analyze_script_mir_diagnostics;

#[test]
fn hidden_storage_does_not_shadow_visible_borrowed_or_owned_method_values() {
    let errors = analyze_script_mir_diagnostics(
        r#"
struct Counter { private value: int32; private edit: int32; private finish: int32 }
extend Counter {
    static func create() -> Self { Self { value: 1, edit: 2, finish: 3 } }
    func value() -> int32 { self.value }
    func edit() { self.value = self.edit }
    func finish() -> int32 { self.finish }
}
func main() {
    var counter = Counter::create()
    read := counter.value
    var before: int32 = read()
    var edit = counter.edit
    edit()
    finish := counter.finish
    var result: int32 = finish()
}
"#,
    );
    assert!(errors.is_empty(), "{errors:#?}");
}

#[test]
fn hidden_storage_without_a_visible_method_still_reports_field_privacy() {
    let errors = analyze_script_mir_diagnostics(
        r#"
struct Counter { private value: int32; }
extend Counter {
    static func create() -> Self { Self { value: 1 } }
}
func main() {
    counter := Counter::create()
    value := counter.value
}
"#,
    );
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("not visible")),
        "{errors:#?}"
    );
}
