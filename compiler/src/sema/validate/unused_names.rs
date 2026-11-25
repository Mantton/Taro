//! Unused imports and unused locals.
//!
//! The resolver records the facts (`sema::resolve::lint`): the single-name
//! imports of each file and block, the imports a name lookup went through,
//! the locals the author declared and the locals an expression reads. This
//! pass reports what nothing uses, once per name, at the name.
//!
//! An import is used when a lookup resolved through it (a type, a value, a
//! module used as a path prefix, an interface in a conformance list or a
//! bound), when it names an interface whose methods a member lookup found
//! through scope visibility, or when a declaration removed by `@cfg` spells
//! its name. Globs, re-exports, namespace members and the prelude are never
//! reported.
//!
//! A local is used when an expression reads it, including inside a closure or
//! a string interpolation; assigning it with `=` is not a read, so a variable
//! that is only ever assigned is unused. Parameters (of functions, methods,
//! initializers and closures), `self` and names that start with `_` are
//! exempt. Bindings the compiler makes while lowering are never recorded,
//! because the resolver runs on the source as written.

use crate::{compile::context::GlobalContext, span::Span};

pub fn run(gcx: GlobalContext<'_>) {
    if !gcx.config.lint_warnings {
        return;
    }
    let mut warnings: Vec<(Span, String)> = Vec::new();
    {
        let store = gcx.store.lint_facts.borrow();
        let Some(facts) = store.get(&gcx.package_index()) else {
            return;
        };
        let trait_uses = gcx.store.trait_visibility_uses.borrow();

        for import in &facts.imports {
            if facts.used_imports.contains(&import.binding) {
                continue;
            }
            let file = import.target.span.file;
            let removed = facts.cfg_removed_names.get(&file);
            if removed.is_some_and(|names| names.contains(&import.target.symbol)) {
                continue;
            }
            // An interface import may only serve to make its methods
            // callable. Code removed by `@cfg` may call them, too.
            if !import.interfaces.is_empty()
                && (removed.is_some() || import.interfaces.iter().any(|id| trait_uses.contains(id)))
            {
                continue;
            }
            warnings.push((
                import.target.span,
                format!("unused import '{}'", gcx.symbol_text(import.target.symbol)),
            ));
        }

        for local in &facts.locals {
            let name = gcx.symbol_text(local.name.symbol);
            // An initializer's `self` is a local the parser declares.
            if name.starts_with('_') || name == "self" || facts.read_locals.contains(&local.id) {
                continue;
            }
            warnings.push((
                local.name.span,
                format!("unused variable '{name}'; prefix it with '_' if this is intended"),
            ));
        }
    }

    warnings.sort_by_key(|(span, _)| (span.file, span.start.line, span.start.offset));
    for (span, message) in warnings {
        gcx.dcx().emit_warning(message, Some(span));
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        diagnostics::DiagnosticRecord,
        test_support::{
            analyze_package_diagnostics, analyze_package_diagnostics_outside_tests,
            with_lint_warnings,
        },
    };

    const LIBRARY: &[(&str, &str)] = &[
        (
            "shapes/shapes.tr",
            r#"
public struct Point {}
public struct Size {}
public func area() -> int32 { 1 }
public const LIMIT: int32 = 4
public interface Named {
    func name() -> string
}
public interface Greeter {
    func greet() -> string
}
conform int32 to Greeter {
    func greet() -> string { "hi" }
}
"#,
        ),
        (
            "shapes/inner/inner.tr",
            "public func depth() -> int32 { 2 }\n",
        ),
    ];

    /// `(message, line, column)` of each warning, lines counted from one.
    fn warnings(main: &str) -> Vec<(String, usize, usize)> {
        let mut files = LIBRARY.to_vec();
        files.push(("main.tr", main));
        let diagnostics = with_lint_warnings(|| analyze_package_diagnostics(&files));
        diagnostics
            .iter()
            .map(|DiagnosticRecord { message, span }| {
                let span = span.expect("lint warnings carry a span");
                (message.clone(), span.start.line + 1, span.start.offset)
            })
            .collect()
    }

    #[test]
    fn unused_imports_warn_once_at_each_name() {
        let found = warnings(
            r#"import package::shapes::{Point, Size, Named}
import package::shapes::area as measure
import package::shapes::inner
func use(_ point: Point) {}
func scoped() {
    import package::shapes::LIMIT
}
"#,
        );
        assert_eq!(
            found,
            vec![
                ("unused import 'Size'".to_string(), 1, 32),
                ("unused import 'Named'".to_string(), 1, 38),
                ("unused import 'measure'".to_string(), 2, 32),
                ("unused import 'inner'".to_string(), 3, 24),
                ("unused import 'LIMIT'".to_string(), 6, 28),
            ]
        );
    }

    #[test]
    fn every_kind_of_reference_uses_an_import() {
        let found = warnings(
            r#"import package::shapes::{Point, Size, area, LIMIT, Named, Greeter}
import package::shapes::inner
import package::shapes::area as measure
import package::shapes::*
export package::shapes::inner::depth
struct Label {}
conform Label to Named {
    func name() -> string { "label" }
}
func bounded[T: Named](_ value: T) {}
func run() -> int32 {
    var _: Size = Size {}
    var _ = Point {}
    var count: int32 = 3
    _ = count.greet()
    measure() + area() + LIMIT + inner::depth()
}
"#,
        );
        assert!(found.is_empty(), "{found:#?}");
    }

    #[test]
    fn imports_used_only_by_code_removed_for_this_target_are_silent() {
        let found = warnings(
            r#"import package::shapes::{area, Greeter, Point}
@cfg(os("plan9"))
func elsewhere() -> int32 { area() }
"#,
        );
        assert_eq!(
            found,
            vec![("unused import 'Point'".to_string(), 1, 40)],
            "{found:#?}"
        );
    }

    #[test]
    fn imports_used_only_by_tests_are_silent_outside_test_builds() {
        let mut files = LIBRARY.to_vec();
        files.push((
            "main.tr",
            r#"import package::shapes::{Greeter, area, Point}
@test
func greets() {
    var value: int32 = area()
    _ = value.greet()
}
"#,
        ));
        let found = with_lint_warnings(|| analyze_package_diagnostics_outside_tests(&files));
        let found: Vec<_> = found
            .iter()
            .map(|DiagnosticRecord { message, span }| {
                let span = span.expect("lint warnings carry a span");
                (message.clone(), span.start.line + 1, span.start.offset)
            })
            .collect();
        assert_eq!(
            found,
            vec![("unused import 'Point'".to_string(), 1, 40)],
            "{found:#?}"
        );
    }

    /// Unused-variable warnings of a single-file program: `(name, line, column)`.
    fn unused_locals(source: &str) -> Vec<(String, usize, usize)> {
        let diagnostics =
            with_lint_warnings(|| analyze_package_diagnostics(&[("main.tr", source)]));
        diagnostics
            .iter()
            .map(|DiagnosticRecord { message, span }| {
                let name = message
                    .strip_prefix("unused variable '")
                    .and_then(|rest| rest.split('\'').next())
                    .unwrap_or_else(|| panic!("unexpected diagnostic: {message}"));
                let span = span.expect("lint warnings carry a span");
                (name.to_string(), span.start.line + 1, span.start.offset)
            })
            .collect()
    }

    #[test]
    fn unread_locals_warn_once_at_the_binding() {
        let found = unused_locals(
            r#"enum Shape {
    case rect(int32, int32)
    case circle(int32)
}
func area(_ shape: Shape) -> int32 {
    scale := 2
    match shape {
        case .rect(width, height) => width
        case .circle(radius) => radius * radius
    }
}
func assigned() {
    var total = 0
    total = 5
    var (first, second) = (1, 2)
    var a = 0
    var b = 0
    (a, b) = (first, 3)
}
func either(_ shape: Shape) -> int32 {
    match shape {
        case .rect(side, _) | .circle(side) => 1
    }
}
"#,
        );
        assert_eq!(
            found,
            vec![
                ("scale".to_string(), 6, 4),
                ("height".to_string(), 8, 26),
                ("total".to_string(), 13, 8),
                ("second".to_string(), 15, 16),
                ("a".to_string(), 16, 8),
                ("b".to_string(), 17, 8),
                ("side".to_string(), 22, 19),
            ]
        );
    }

    #[test]
    fn reads_parameters_and_underscore_names_are_silent() {
        let found = unused_locals(
            r#"struct Counter {
    value: int32
}
extend Counter {
    init(start: int32) {
        self.value = 0
    }
    func bump(by amount: int32) -> int32 {
        _unused := 4
        var step = 1
        step += 1
        step
    }
}
func run(_ input: int32, _ ignored: int32) -> int32 {
    captured := 3
    read := (x: int32) => x + captured
    var counter = Counter(start: 1)
    counter.value = 2
    var copy = 0
    copy = counter.value
    pending := 5
    var later = 0
    later = pending
    read(input) + copy + later
}
"#,
        );
        assert!(found.is_empty(), "{found:#?}");
    }

    #[test]
    fn tuple_shorthand_destructuring_reports_only_unused_leaves() {
        let found = unused_locals(
            r#"func main() {
    (used, unused) := (1, 2)
    (kept, _, _ignored) := (used, 3, 4)
    _ = kept
}
"#,
        );
        assert_eq!(found, vec![("unused".to_string(), 2, 11)]);
    }
}
