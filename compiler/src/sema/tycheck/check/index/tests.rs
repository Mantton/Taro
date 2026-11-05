//! Native indexing must select declared capabilities, rather than method names.
use crate::test_support::analyze_script_mir_diagnostics;

#[test]
fn g40_native_read_write_and_address_do_not_require_index_conformances() {
    let errors = analyze_script_mir_diagnostics(
        "struct Buffer { value: int32 }\nextend &Buffer { subscript(index: usize) -> int32 { get { self.value } set(value) { self.value = value } address { &self.value } } }\nfunc main() { var buffer = Buffer { value: 7 }; read := buffer[0 as usize]; buffer[0 as usize] = 9; reference := &buffer[0 as usize]; *reference = read }",
    );
    assert!(errors.is_empty(), "{errors:#?}");
}

#[test]
fn g40_native_numeric_compound_assignment_uses_declared_get_set() {
    let errors = analyze_script_mir_diagnostics(
        "struct Buffer { value: int32 }\nextend &Buffer { subscript(index: usize) -> int32 { get { self.value } set(value) { self.value = value } } }\nfunc main() { var buffer = Buffer { value: 7 }; buffer[0 as usize] += 2 }",
    );
    assert!(errors.is_empty(), "{errors:#?}");
}

#[test]
fn g40_native_multi_index_and_range_typed_overloads_reach_mir() {
    let errors = analyze_script_mir_diagnostics(
        "struct Window { start: usize }\nstruct Matrix { value: int32 }\nextend Matrix { subscript(row: usize, column: usize) -> int32 { get { self.value } } subscript(range: Window) -> int32 { get { self.value } } }\nfunc main() { matrix := Matrix { value: 7 }; first := matrix[0 as usize, 1 as usize]; second := matrix[Window { start: 0 as usize }] }",
    );
    assert!(errors.is_empty(), "{errors:#?}");
}

#[test]
fn g40_same_named_methods_do_not_enable_native_indexing() {
    let errors = analyze_script_mir_diagnostics(
        "struct Buffer { value: int32 }\nextend Buffer { func __subscript_get(_ index: usize) -> int32 { self.value } }\nfunc main() { buffer := Buffer { value: 7 }; read := buffer[0 as usize] }",
    );
    assert!(!errors.is_empty(), "ordinary method enabled indexing");
}

const CELLS: &str = "struct Cell { value: int32 }\nextend &Cell { func bump() { self.value += 1 }; }\nstruct Buffer { cell: Cell }\nextend &Buffer { subscript(index: usize) -> Cell { get { self.cell } set(value) { self.cell = value } } }\n";

#[test]
fn g40_get_set_does_not_supply_references_or_nested_struct_writeback() {
    for operation in [
        "reference := &buffer[0 as usize]",
        "buffer[0 as usize].value = 9",
        "buffer[0 as usize].bump()",
        "callback := buffer[0 as usize].bump; callback()",
    ] {
        let errors = analyze_script_mir_diagnostics(&format!(
            "{CELLS}func main() {{ var buffer = Buffer {{ cell: Cell {{ value: 7 }} }}; {operation} }}"
        ));
        assert!(
            errors
                .iter()
                .any(|error| error.message.contains("address accessor")),
            "{operation}: {errors:#?}"
        );
    }
}

#[test]
fn g40_address_supports_nested_fields_and_automatic_reference_receivers() {
    let source = CELLS.replace(
        "set(value) { self.cell = value }",
        "set(value) { self.cell = value } address { &self.cell }",
    );
    let errors = analyze_script_mir_diagnostics(&format!(
        "{source}func main() {{ var buffer = Buffer {{ cell: Cell {{ value: 7 }} }}; buffer[0 as usize].value = 9; buffer[0 as usize].bump(); callback := buffer[0 as usize].bump; callback() }}"
    ));
    assert!(errors.is_empty(), "{errors:#?}");
}

#[test]
fn g40_getter_reference_targets_keep_independent_storage() {
    let errors = analyze_script_mir_diagnostics(
        "struct Cell { value: int32 }\nstruct Buffer { cell: &Cell }\nextend Buffer { subscript(index: usize) -> &Cell { get { self.cell } } }\nfunc main() { var cell = Cell { value: 7 }; buffer := Buffer { cell: &cell }; buffer[0 as usize].value = 9; reference := &buffer[0 as usize].value; *reference = 10 }",
    );
    assert!(errors.is_empty(), "{errors:#?}");
}

#[test]
fn g40_getter_class_targets_can_mutate_without_set_or_address() {
    let errors = crate::test_support::analyze_language_item_script(
        "class Cell { value: int32 }\nstruct Buffer { cell: Cell }\nextend Buffer { subscript(index: usize) -> Cell { get { self.cell } } }\nfunc check(_ buffer: Buffer) { buffer[0 as usize].value = 9; reference := &buffer[0 as usize].value; *reference = 10 }\nfunc main() {}",
        false,
        &[],
    );
    assert!(errors.is_empty(), "{errors:#?}");
}

#[test]
fn g40_getter_only_numeric_assignment_requires_a_write_capability() {
    let errors = analyze_script_mir_diagnostics(
        "struct Buffer { value: int32 }\nextend Buffer { subscript(index: usize) -> int32 { get { self.value } } }\nfunc main() { buffer := Buffer { value: 7 }; buffer[0 as usize] += 2 }",
    );
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("address or set accessor")),
        "{errors:#?}"
    );
}

#[test]
fn g40_expected_element_type_does_not_select_an_index_overload() {
    let errors = analyze_script_mir_diagnostics(
        "struct Buffer {}\nextend Buffer { subscript(index: int32) -> int32 { get { index } } subscript(index: int64) -> bool { get { true } } }\nfunc choose(_ buffer: Buffer) -> bool { buffer[1] }\nfunc main() {}",
    );
    assert!(!errors.is_empty(), "result type selected an index overload");
}
