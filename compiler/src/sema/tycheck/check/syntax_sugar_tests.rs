use crate::test_support::analyze_script_mir_diagnostics;

#[test]
fn syntax_sugar_single_parameter_and_ignored_closures() {
    let diagnostics = analyze_script_mir_diagnostics(
        r#"
func apply(_ f: (int32) -> int32) -> int32 { f(3) }
func pair(_ f: (int32, int32) -> int32) -> int32 { f(3, 4) }
func main() {
    var a = apply(value => value + 1)
    var b = apply(_ => 42)
    var c = apply((_: int32) => 42)
    var d = pair((_, value) => value)
    var e = pair((_, _) => 42)
    var f: (int32) -> (int32) -> int32 = x => y => y + 1
}
"#,
    );
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
}

#[test]
fn syntax_sugar_discard_shorthand() {
    let diagnostics = analyze_script_mir_diagnostics(
        "func value() -> int32 { 42 }\nfunc main() { _ := value(); _ := value(); }",
    );
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
}

#[test]
fn syntax_sugar_match_guard_arrows_are_not_closures() {
    let diagnostics = analyze_script_mir_diagnostics(
        r#"
func check(_ f: (int32) -> bool) -> bool { f(1) }
func main() {
    var enabled = true
    var limit = 3
    var a = match 1 { case x if enabled => x; case _ => 0; }
    var b = match 1 { case x if x < limit => x; case _ => 0; }
    var c = match 1 { case x if (enabled) => x; case _ => 0; }
    var d = match 1 { case x if check(value => value > 0) => x; case _ => 0; }
}
"#,
    );
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
}

#[test]
fn syntax_sugar_tuple_assignment_uses_normal_destinations() {
    let diagnostics = analyze_script_mir_diagnostics(
        r#"
struct Point { x: int32; y: int32 }
func main() {
    var (a, b) = (1, 2)
    (a, b) = (b, a)
    (a, (b, _)) = (3, (4, false))
    var point = Point { x: 1, y: 2 }
    var tuple = (3, 4)
    (point.x, tuple.1) = (5, 6)
    var wide: int64 = 0
    (wide, _) = (7, true)
    () = ()
    _ = 1
    (_) = point
}

"#,
    );
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
}

#[test]
fn syntax_sugar_tuple_assignment_rejects_invalid_shapes_and_destinations() {
    for source in [
        "func main() { var (a, b) = (1, 2); (a, b) = (3,); }",
        "func main() { var (a, b) = (1, 2); (a, b) = 3; }",
        "func main() { var a = 1; (a, (a, a)) = (2, 3); }",
        "func main() { var a = 1; (a, 3) = (2, 4); }",
        "struct S { readonly x: int32 }\nfunc main() { var s = S { x: 1 }; (s.x,) = (2,); }",
        "func main() { var (a, b) = (1, 2); (a, b) += (3, 4); }",
        "func main() { var a = 1; (a,) = (false,); }",
        "func main() { (a, b): (int32, int32) := (3, 4); }",
        "func main() { (a, 3) := (2, 4); }",
        "func main() { _ := missingName; }",
        "func apply(_ f: (int32) -> int32) {}\nfunc main() { apply(_ => _); }",
        "func apply(_ f: (int32) -> int32) {}\nfunc main() { apply(value: int32 => value); }",
        "func main() { var (a, b) = (1, 2); (a, b) = (_, 3); }",
    ] {
        let diagnostics = analyze_script_mir_diagnostics(source);
        assert!(!diagnostics.is_empty(), "accepted {source}");
        assert!(
            !diagnostics
                .iter()
                .any(|error| error.message.contains("internal error")),
            "{source}: {diagnostics:#?}"
        );
    }
}

#[test]
fn syntax_sugar_diverging_discard_and_tuple_rhs_have_resolved_types() {
    let diagnostics = analyze_script_mir_diagnostics(
        "func never() -> ! { loop {} }\nfunc discarded() { _ := never(); }\nfunc assigned() { var a = 0; (a, _) = never(); }\nfunc main() {}",
    );
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
}

#[test]
fn loop_break_value_diagnostics_cover_mismatch_mixed_and_while() {
    let mismatch = analyze_script_mir_diagnostics(
        "func f(_ c: bool) { _ := loop { if c { break 1 }; break \"two\" }; }\nfunc main() {}",
    );
    assert!(
        mismatch
            .iter()
            .any(|d| d.message.contains("expected") && d.message.contains("found")),
        "expected type mismatch diagnostic, got: {mismatch:#?}"
    );

    let mixed = analyze_script_mir_diagnostics(
        "func f(_ c: bool) { _ := loop { if c { break }; break 1 }; }\nfunc main() {}",
    );
    assert!(
        mixed
            .iter()
            .any(|d| d.message.contains("cannot mix valueless `break`")),
        "expected mixed break diagnostic, got: {mixed:#?}"
    );

    let in_while = analyze_script_mir_diagnostics(
        "func f(_ c: bool) { while c { break 1 } }\nfunc main() {}",
    );
    assert!(
        in_while
            .iter()
            .any(|d| d.message.contains("only allowed in an unconditional `loop`")),
        "expected while value-break diagnostic, got: {in_while:#?}"
    );
}

#[test]
fn loop_break_value_valid_patterns_typecheck_and_lower_to_mir() {
    let diagnostics = analyze_script_mir_diagnostics(
        r#"
func f(_ c: bool) -> int32 {
    target := 7
    target: loop {
        loop {
            break target
        }
    }
    x := target: loop {
        if c {
            return -1
        }
        loop {
            break
        }
        break (target)
    }
    return x
}
func main() {}
"#,
    );
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
}
