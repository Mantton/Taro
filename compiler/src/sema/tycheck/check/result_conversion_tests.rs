use crate::{hir::StdItem, test_support::analyze_language_item_script};

fn diagnostics(body: &str, mir: bool) -> Vec<crate::diagnostics::Diagnostic> {
    analyze_language_item_script(
        &format!(
            r#"
enum Optional[T] {{ case some(T); case none }}
enum Result[T, E] {{
    case ok(T)
    case err(E)
}}
struct Response {{ status: uint16, body: string }}
extend Response {{
    static func text(_ status: uint16, _ body: string) -> Response {{ Response {{ status, body }} }}
}}
{body}
"#
        ),
        mir,
        &[(StdItem::Optional, "Optional"), (StdItem::Result, "Result")],
    )
}

#[test]
fn contextual_result_conversion_handles_values_factories_and_typed_sites() {
    let errors = diagnostics(
        r#"
func integer() -> Result[int32, string] { 42 }
func response() -> Result[Response, string] { return .text(200, "ok") }
func pass(_ value: Result[int32, string]) -> Result[int32, string] { value }
func generic[T, E](_ value: T) -> Result[T, E] { value }
func main() {
    var value: Result[int32, string] = 1
    value = 2
    var argument = pass(3)
    var branches: Result[int32, string] = if true { 4 } else { .err("failure") }
    var same: Result[int32, int32] = 5
    var nested: Result[Result[int32, string], bool] = .ok(.err("retained"))
    var explicitFailure: Result[int32, string] = .err("failure")
    var forwarded = pass(explicitFailure)
    var factory: Result[Response, string] = .text(201, "created")
    var genericValue = generic[int32, string](6)
}
"#,
        true,
    );
    assert!(errors.is_empty(), "{errors:#?}");
}

#[test]
fn contextual_result_conversion_never_wraps_existing_results_or_bare_errors() {
    for body in [
        "func bad(_ value: Result[int32, string]) -> Result[Result[int32, string], bool] { value }",
        "func bad(_ value: Result[int32, string]) -> Result[int32, bool] { value }",
        "func bad() -> Result[Result[int32, string], bool] { 1 }",
        "func bad() -> Result[int32, string] { \"failure\" }",
        "func bad() -> Result[Response, string] { .unknown(200) }",
    ] {
        let errors = diagnostics(body, false);
        assert!(!errors.is_empty(), "unexpectedly accepted: {body}");
    }
}

#[test]
fn contextual_result_conversion_accepts_explicit_unit_values() {
    let errors = diagnostics(
        r#"
func effect() {}
func explicitUnit() -> Result[(), string] { () }
func voidTail() -> Result[(), string] { effect() }
func main() { var unit: Result[(), string] = () }
"#,
        true,
    );
    assert!(errors.is_empty(), "{errors:#?}");
}

#[test]
fn contextual_result_conversion_keeps_inner_payload_adjustments_in_order() {
    let errors = diagnostics(
        r#"
interface Read { func read() -> int32; }
struct Value { value: int32 }
conform Value to Read { func read() -> int32 { self.value }; }
class Base {}
class Child: Base {}
func boxed(_ value: Value) -> Result[any Read, string] { value }
func optionalBoxed(_ value: Value) -> Result[(any Read)?, string] { value }
func upcast(_ value: Child) -> Result[Base, string] { value }
func optionalUpcast(_ value: Child) -> Result[Base?, string] { value }
func reference(_ value: &int32) -> Result[&int32, string] { value }
func main() {}
"#,
        true,
    );
    assert!(errors.is_empty(), "{errors:#?}");
}

#[test]
fn contextual_result_conversion_defers_producer_types_and_normalizes_associated_outputs() {
    let errors = diagnostics(
        r#"
interface Source { type Output; func get() -> Self::Output; }
func adapt[S: Source](_ source: S) -> Result[S::Output, string] { source.get() }
func identity[T](_ value: T) -> T { value }
func forwarded(_ value: Result[int32, string]) -> Result[int32, string] { identity(value) }
func main() {
    var value: Result[int32, string] = identity(7 as int32)
    var failure: Result[int32, string] = identity(Result[int32, string]::err("retained"))
}
"#,
        true,
    );
    assert!(errors.is_empty(), "{errors:#?}");
}

#[test]
fn contextual_result_conversion_keeps_outer_overloads_authoritative() {
    let errors = diagnostics(
        r#"
extend Response {
    static func choose(_ value: uint16) -> Response { Response { status: value, body: "inner" } }
}
extend Result[Response, string] {
    static func choose(_ value: int32) -> Result[Response, string] { .err("outer integer") }
    static func choose(_ value: bool) -> Result[Response, string] { .err("outer boolean") }
}
func selected() -> Result[Response, string] { .choose(200) }
func main() {}
"#,
        true,
    );
    assert!(errors.is_empty(), "{errors:#?}");
}

#[test]
fn contextual_result_conversion_preserves_generic_contextual_result_inference() {
    let errors = diagnostics(
        r#"
func identity[T](_ value: T) -> T { value }
interface Number {}
conform int32 to Number {}
func constrained[T: Number](_ value: T) -> T { value }
func main() {
    var failed: Result[int32, string] = identity(.err("retained"))
    var successful: Result[int32, string] = identity(.ok(42))
    var number: Result[int32, string] = constrained(7 as int32)
}
"#,
        true,
    );
    assert!(errors.is_empty(), "{errors:#?}");
}
