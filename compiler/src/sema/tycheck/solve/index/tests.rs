use crate::{diagnostics::DiagnosticRecord, hir::StdItem};

const TYPES: &str = r#"
interface Access[I] { type Element; subscript(key: I) -> Self::Element { address } }
struct Item { value: int32; }
extend &Item {
 func increment() { self.value += 1 }
}
struct Cell { item: Item; }
conform &Cell to Access[int32] {
    type Element = Item
    subscript(key: int32) -> Item { address { &self.item } }
}
"#;
fn diagnostics(body: &str) -> Vec<DiagnosticRecord> {
    let main = if body.contains("func main(") {
        ""
    } else {
        "\nfunc main() {}"
    };
    crate::test_support::analyze_script_mir_diagnostics(&format!("{TYPES}{body}{main}"))
}

#[test]
fn native_indexing_reads_references_and_updates_storage() {
    let errors = diagnostics(
        r#"
func first[T: Access[int32]](_ value: T) -> &T::Element { &value[0] }
func firstMut[T: Access[int32]](_ value: T) -> &T::Element { &value[0] }
func main() {
    var cell = Cell { item: Item { value: 1 } }
    var index: int32 = 0
    read := &cell[index]
    var value: int32 = read.value
    cell[index] = Item { value: value + 1 }
    cell[index].increment()
    item := first(&cell)
    var observed: int32 = item.value
    mutable := firstMut(&cell)
    mutable.value = observed + 1
}
"#,
    );
    assert!(errors.is_empty(), "{errors:#?}");
}

#[test]
fn indexing_mutates_through_copied_references() {
    let errors =
        diagnostics("func edit(_ cell: &Cell) { saved := cell; saved[0] = Item { value: 2 } }");
    assert!(errors.is_empty(), "{errors:#?}");
}

#[test]
fn nested_native_indices_select_addressable_storage() {
    let errors = diagnostics(
        r#"
struct Row { cell: Cell }
conform &Row to Access[int32] {
    type Element = Cell
    subscript(key: int32) -> Cell { address { &self.cell } }
}
func edit(_ item: &Item) { item.value += 1 }
func main() {
    var row = Row { cell: Cell { item: Item { value: 1 } } }
    edit(&row[0][0])
    row[0][0].increment()
    row[0][0].value += 1
    saved := &row[0][0]
    var observed: int32 = saved.value
}
"#,
    );
    assert!(errors.is_empty(), "{errors:#?}");
}

#[test]
fn native_address_access_supports_independent_reference_values() {
    let errors = diagnostics(
        r#"
struct Reader { item: Item }
conform &Reader to Access[int32] {
    type Element = Item
    subscript(key: int32) -> Item { address { &self.item } }
}
func main() {
    var reader = Reader { item: Item { value: 4 } }
    first := &reader[0]
    second := &reader[0]
    var value: int32 = first.value + second.value
}
"#,
    );
    assert!(errors.is_empty(), "{errors:#?}");
}

#[test]
fn indexing_requires_a_native_declaration() {
    let missing = diagnostics(
        r#"
struct Pretender { value: int32 }
extend Pretender {
    func index(_ key: int32) -> &int32 { &self.value }
}
func main() { value := Pretender { value: 1 }; saved := &value[0] }
"#,
    );
    assert!(
        missing
            .iter()
            .any(|error| error.message.contains("subscript")),
        "{missing:#?}"
    );
}

#[test]
fn indexed_callbacks_preserve_capture_and_erasure_types() {
    let source = format!(
        r#"{TYPES}
interface Tuple {{}}


interface Fn[Args: Tuple, Output]{{
    func call(args: Args) -> Output
}}
struct CallCell[F] {{ callback: F }}
conform[F] &CallCell[F] to Access[int32] {{
    type Element = F
    subscript(key: int32) -> F {{ address {{ &self.callback }} }}
}}
func invoke[F: Fn[(), int32]](_ values: &CallCell[F]) -> int32 {{ values[0]() }}
func read[F: Fn[(), int32]](_ values: &CallCell[F]) -> int32 {{ values[0]() }}
func main() {{
    var count: int32 = 0
    var callback: any Fn[(), int32] = () => {{ count += 1; count }}
    var values = CallCell {{ callback: callback }}
    var first: int32 = values[0]()
    // A wrapper containing an existential cannot be reinterpreted as a
    // wrapper containing its hidden concrete callback. Exercise generic
    // indexing with a concrete callback; the preceding call covers erasure.
    var concrete = CallCell {{ callback: () => {{ count += 1; count }} }}
    var second: int32 = invoke(&concrete)
    readers := CallCell {{ callback: () => 7_i32 }}
    var third: int32 = read(&readers)
}}
"#
    );
    let errors = crate::test_support::analyze_language_item_script(
        &source,
        true,
        &[(StdItem::Tuple, "Tuple"), (StdItem::Fn, "Fn")],
    );
    assert!(errors.is_empty(), "{errors:#?}");
}

#[test]
fn distinct_index_instantiations_keep_their_associated_outputs() {
    let errors = diagnostics(
        r#"
struct Dual { number: int32; flag: bool; }
conform &Dual to Access[int32] {
    type Element = int32
    subscript(key: int32) -> int32 { address { &self.number } }
}
conform &Dual to Access[bool] {
    type Element = bool
    subscript(key: bool) -> bool { address { &self.flag } }
}
func readBool[C: Access[bool, Element=bool]](_ values: C) -> &bool { &values[true] }
func main() {
    value := Dual { number: 7, flag: true }
    var number: int32 = value[0]
    var flag: bool = value[true]
    var borrowed: &bool = readBool(&value)
}
"#,
    );
    assert!(errors.is_empty(), "{errors:#?}");
}

#[test]
fn indexed_existential_methods_wait_for_receiver_before_autoref() {
    let errors = crate::test_support::analyze_script_diagnostics(
        r#"
interface Read { func read() -> int32; }
struct Value { number: int32 }
conform Value to Read {
    func read() -> int32 { self.number }
}
struct Unrelated {}
extend &Unrelated {
    func read(_ enabled: bool) -> int32 { 0 }
}
struct Slot[T] { item: T }
extend[T] &Slot[T] {
    subscript(index: int32) -> T { address { &self.item } }
    subscript(index: bool) -> T { address { &self.item } }
}
func main() {
    var slot = Slot[any Read] { item: Value { number: 1 } }
    var result = slot[0].read() == 1
    bound := slot[0].read
    var throughBound: int32 = bound()
}
"#,
    );
    assert!(errors.is_empty(), "{errors:#?}");
}
