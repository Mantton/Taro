//! Native capabilities must survive interface and class method dispatch.
#[test]
fn g41_native_interface_generic_and_erased_access() {
    let source = r#"
interface Readable[Key] { type Element; subscript(key: Key) -> Self::Element { get } }
struct Buffer { value: int32 }
conform Buffer to Readable[usize] { type Element = int32; subscript(index: usize) -> int32 { get { self.value } } }
func read[T: Readable[usize, Element = int32]](_ value: T) -> int32 { value[0 as usize] }
func erased(_ value: any Readable[usize, Element = int32]) -> int32 { value[0 as usize] }
func main() {}
"#;
    let diagnostics = crate::test_support::analyze_script_mir_diagnostics(source);
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
}

#[test]
fn g41_partial_overrides_keep_inherited_capabilities() {
    let source = r#"
class Base { value: int32 }
extend Base { init(_ value: int32) { self.value = value }; subscript(index: usize) -> int32 { address { &self.value } } }
class Child: Base {}
extend Child { override subscript(index: usize) -> int32 { get { 17 } } }
func use(_ child: Child) { child[0 as usize] = 9; reference := &child[0 as usize]; *reference = 10 }
func main() {}
"#;
    let diagnostics = crate::test_support::analyze_script_diagnostics(source);
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
}

#[test]
fn g41_native_witnesses_cannot_be_ordinary_named_helpers() {
    let source = r#"
interface Readable { subscript(index: usize) -> int32 { get } }
struct Buffer {}
conform Buffer to Readable { func __subscript_get(_ index: usize) -> int32 { 7 }; }
func main() {}
"#;
    let diagnostics = crate::test_support::analyze_script_diagnostics(source);
    assert!(
        !diagnostics.is_empty(),
        "ordinary names must not create native witnesses"
    );
}

#[test]
fn g41_native_interface_overloads_and_extra_concrete_capabilities() {
    let source = r#"
interface Readable {
    subscript(index: usize) -> int32 { get }
    subscript(row: int32, column: int32) -> int32 { get }
}
struct Buffer { value: int32 }
conform &Buffer to Readable {
    subscript(index: usize) -> int32 { address { &self.value } }
    subscript(row: int32, column: int32) -> int32 { get { self.value + row + column } }
}
func use(_ value: &Buffer) { value[0 as usize] = 9; reference := &value[0 as usize]; *reference += 1; copied := value[2 as int32, 3 as int32] }
func main() {}
"#;
    let diagnostics = crate::test_support::analyze_script_mir_diagnostics(source);
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    let source = format!(
        "{source}\nfunc forbidden[T: Readable](_ value: T) {{ reference := &value[0 as usize] }}"
    );
    let diagnostics = crate::test_support::analyze_script_diagnostics(&source);
    assert!(
        diagnostics.iter().any(|item| item
            .message
            .contains("requires a subscript address accessor")),
        "{diagnostics:#?}"
    );
}

#[test]
fn g41_partial_override_generic_ancestors_have_distinct_arguments() {
    let source = r#"
class Base[First, Second] { first: First; second: Second }
extend[First, Second] Base[First, Second] { subscript(index: usize) -> Second { address { &self.second } } }
class Child[Value]: Base[int32, Value] {}
extend[Value] Child[Value] { override subscript(index: usize) -> Value { get { self.second } } }
func use(_ child: Child[int64]) { child[0 as usize] = 9 as int64; reference := &child[0 as usize]; *reference += 1 }
func main() {}
"#;
    let diagnostics = crate::test_support::analyze_script_diagnostics(source);
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
}

#[test]
fn g41_final_partial_overrides_seal_inherited_capabilities() {
    let source = r#"
class Base { value: int32 }
extend Base { subscript(index: usize) -> int32 { address { &self.value } } }
class Child: Base {}
extend Child { final override subscript(index: usize) -> int32 { get { 7 } } }
class Grandchild: Child {}
extend Grandchild { override subscript(index: usize) -> int32 { address { &self.value } } }
func main() {}
"#;
    let diagnostics = crate::test_support::analyze_script_diagnostics(source);
    assert!(
        diagnostics
            .iter()
            .any(|item| item.message.contains("cannot override a final subscript")),
        "{diagnostics:#?}"
    );
}

#[test]
fn g41_subscript_overrides_fix_element_type_and_require_native_identity() {
    for source in [
        "class Base {}; extend Base { subscript(index: usize) -> int32 { get { 1 } } }; class Child: Base {}; extend Child { override subscript(index: usize) -> int64 { get { 1 } } }; func main() {}",
        "class Base {}; extend Base { subscript(index: usize) -> int32 { get { 1 } } }; class Child: Base {}; extend Child { override func __subscript_get(_ index: usize) -> int32 { 1 }; }; func main() {}",
        "interface Readable { subscript(index: usize) -> int32 { get } }; struct Buffer {}; conform Buffer to Readable { subscript(index: usize) -> int32 { get { 7 } }; subscript(index: bool) -> int32 { get { 9 } } }; func main() {}",
    ] {
        let diagnostics = crate::test_support::analyze_script_diagnostics(source);
        assert!(!diagnostics.is_empty(), "{source}");
    }
}

#[test]
fn g41_partial_native_conformance_overrides_inherit_default_families() {
    let source = r#"
interface Storage { type Element; func pointer() -> &Self::Element; subscript(index: usize) -> Self::Element { address { self.pointer() } } }
class Base { first: int32; second: int32 }
conform Base to Storage { type Element = int32; func pointer() -> &int32 { &self.first }; }
class Child: Base {}
conform Child to Storage { override subscript(index: usize) -> int32 { address { &self.second } } }
func use(_ child: Child) { child[0 as usize] = 7; reference := &child[0 as usize] }
func main() {}
"#;
    let diagnostics = crate::test_support::analyze_script_diagnostics(source);
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
}

#[test]
fn g41_added_private_capabilities_do_not_become_public_through_an_inherited_getter() {
    let source = r#"
class Base { value: int32 }
extend Base { public subscript(index: usize) -> int32 { get { self.value } } }
class Child: Base {}
extend Child { private override subscript(index: usize) -> int32 { address { &self.value } } }
func use(_ child: Child) { reference := &child[0 as usize] }
func main() {}
"#;
    let diagnostics = crate::test_support::analyze_script_diagnostics(source);
    assert!(
        diagnostics.iter().any(|item| item
            .message
            .contains("requires a subscript address accessor")),
        "{diagnostics:#?}"
    );
}
