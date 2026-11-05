use crate::test_support::analyze_script_diagnostics;

const CALLS: &str = r#"
struct Value { value: int32 }
extend Value {
    func unwrap() -> int32 { self.value }
}
func fetch(_ value: int32) async -> Value { Value { value } }
func number(_ value: int32) async -> int32 { value }
func consume(_ value: int32) -> int32 { value }
"#;

#[test]
fn await_scope_covers_chains_arguments_and_multiple_calls() {
    let diagnostics = analyze_script_diagnostics(&format!(
        r#"{CALLS}
func main() async {{
    var first = await fetch(1).unwrap()
    var second = await consume(number(2) + number(3))
    var third = await number(await number(4))
}}
"#
    ));
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
}

#[test]
fn await_scope_does_not_authorize_calls_inside_closures() {
    let diagnostics = analyze_script_diagnostics(&format!(
        r#"{CALLS}
func main() async {{
    var callback = await (() => fetch(1).unwrap())
}}
"#
    ));
    assert!(
        diagnostics.iter().any(|d| d.message.contains("async call")),
        "{diagnostics:#?}"
    );
}

#[test]
fn await_scope_without_async_operations_reports_a_warning() {
    let diagnostics = analyze_script_diagnostics("func main() async { var value = await 1 + 2 }");
    assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
    assert!(
        diagnostics[0].message.contains("no async operations"),
        "{diagnostics:#?}"
    );
    crate::test_support::analyze_script("func main() async { var value = await 1 + 2 }", |_, _| ());
}

#[test]
fn await_scope_lowers_each_async_call_once_before_synchronous_consumers() {
    crate::test_support::analyze_script_built_mir(
        &format!(
            r#"{CALLS}
func main() async {{ var value = await consume(number(1) + number(2)) }}
"#
        ),
        |bodies, gcx| {
            let body = bodies
                .iter()
                .find(|body| {
                    gcx.symbol_text(gcx.definition_symbol_or_fallback(body.owner)) == "main"
                })
                .unwrap();
            let suspensions = body
                .basic_blocks
                .iter()
                .filter(|block| {
                    matches!(
                        block.terminator.as_ref().map(|term| &term.kind),
                        Some(crate::mir::TerminatorKind::Yield { .. })
                    )
                })
                .count();
            assert_eq!(
                suspensions, 2,
                "one suspension per async call, none for consume or the scope marker"
            );
        },
    );
}

#[test]
fn await_scope_redundant_callable_and_overloaded_sync_calls_warn() {
    let diagnostics = analyze_script_diagnostics(
        r#"
func syncCall() -> int32 { 1 }
func main() async {
    var callback: () -> int32 = syncCall
    var value = await callback()
    var other = await syncCall()
}
"#,
    );
    assert_eq!(diagnostics.len(), 2, "{diagnostics:#?}");
    assert!(
        diagnostics
            .iter()
            .all(|d| d.message.contains("no async operations")),
        "{diagnostics:#?}"
    );
}

#[test]
fn await_scope_distinguishes_ready_task_handles_from_implicit_task_awaiting() {
    let prefix =
        "struct Task[T] { value: T }\nfunc task() async -> Task[int32] { Task { value: 1 } }\n";
    let errors = crate::test_support::analyze_language_item_script(
        &format!("{prefix}func main() async {{ var handle = await task() }}"),
        false,
        &[(crate::hir::StdItem::Task, "Task")],
    );
    assert!(errors.is_empty(), "{errors:#?}");
    let errors = crate::test_support::analyze_language_item_script(
        &format!("{prefix}func main(_ handle: Task[int32]) async {{ var value = await handle }}"),
        false,
        &[(crate::hir::StdItem::Task, "Task")],
    );
    assert_eq!(
        errors.len(),
        1,
        "invalid operands must not also warn: {errors:#?}"
    );
    assert!(
        errors.iter().any(|d| d.message.contains("task.result()")),
        "{errors:#?}"
    );
}
