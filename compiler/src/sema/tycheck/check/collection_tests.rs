use crate::test_support::analyze_script_mir_diagnostics;

const VALUES: &str = r#"
interface Read { func read() -> int32; }
struct First { value: int32 }
struct Second { value: int32 }
conform First to Read { func read() -> int32 { self.value }
}
conform Second to Read { func read() -> int32 { self.value }
}
"#;

#[test]
fn contextual_array_elements_receive_their_ordinary_value_coercions() {
    let errors = analyze_script_mir_diagnostics(&format!(
        r#"{VALUES}
func main() {{
    var values: [any Read; 2] = [First {{ value: 1 }}, Second {{ value: 2 }}]
}}
"#
    ));
    assert!(errors.is_empty(), "{errors:#?}");
}

#[test]
fn contextual_tuple_elements_receive_their_ordinary_value_coercions() {
    let errors = analyze_script_mir_diagnostics(&format!(
        r#"{VALUES}
func main() {{
    var values: (any Read, any Read) = (First {{ value: 1 }}, Second {{ value: 2 }})
}}
"#
    ));
    assert!(errors.is_empty(), "{errors:#?}");
}
