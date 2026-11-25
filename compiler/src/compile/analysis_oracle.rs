//! Cold full-check oracle for comparing editor revisions.

use crate::{
    compile::{config::HarnessMode, context::Gcx},
    hir::{self, HirVisitor},
    sema::tycheck::results::TypeCheckResults,
    span::{Position, Span},
    test_support::with_source_compiler,
};

const DECLARATIONS: &str = include_str!("analysis_oracle/dispatch.tr");
const CALLS: &str = include_str!("analysis_oracle/calls.tr");

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct Location {
    file: String,
    start: Position,
    end: Position,
}

impl Location {
    fn new(context: Gcx<'_>, span: Span) -> Self {
        let file = context.dcx().file_path(span.file).expect("source path");
        let source_root = context.config.src.join("src").canonicalize().unwrap();
        Self {
            file: file
                .strip_prefix(source_root)
                .unwrap()
                .to_str()
                .unwrap()
                .to_owned(),
            start: span.start,
            end: span.end,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Call {
    receiver: String,
    argument: String,
    result: String,
    declaration: Destination,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Destination {
    location: Location,
    signature: String,
}

#[derive(Debug, PartialEq, Eq)]
struct Snapshot {
    succeeded: bool,
    calls: Vec<(Location, Call)>,
    diagnostics: Vec<(Option<Location>, String)>,
}

#[derive(Debug, PartialEq, Eq)]
struct Work {
    parsed_files: usize,
    callable_headers: usize,
    function_bodies: usize,
}

struct Calls<'a, 'ctx> {
    context: Gcx<'ctx>,
    types: &'a TypeCheckResults<'ctx>,
    calls: Vec<(Location, Call)>,
}

impl HirVisitor for Calls<'_, '_> {
    type Result = ();

    fn visit_expression(&mut self, expr: &hir::Expression) {
        if let hir::ExpressionKind::MethodCall {
            receiver,
            name,
            arguments,
            ..
        } = &expr.kind
            && name.symbol.as_str() == "label"
        {
            let context = self.context;
            let definition = self
                .types
                .overload_source(expr.id)
                .expect("selected overload");
            let ident = context.definition_ident(definition);
            let location = Location::new(context, ident.span);
            let ty = |id| self.types.node_type(id).format(context);
            self.calls.push((
                Location::new(context, name.span),
                Call {
                    receiver: ty(receiver.id),
                    argument: ty(arguments[0].expression.id),
                    result: ty(expr.id),
                    declaration: Destination {
                        location,
                        signature: context
                            .get_signature(definition)
                            .format_for_display(context),
                    },
                },
            ));
        }
        hir::walk_expression(self, expr);
    }
}

fn full_check(declarations: &str, calls: &str) -> (Snapshot, Work) {
    with_source_compiler(
        &[("dispatch.tr", declarations), ("calls.tr", calls)],
        false,
        HarnessMode::None,
        |compiler| {
            let context = compiler.context;
            let analysis = compiler.analyze();
            let succeeded = analysis.is_ok();
            let mut calls = Vec::new();
            if let Ok((package, types)) = analysis {
                let mut visitor = Calls {
                    context,
                    types: &types,
                    calls,
                };
                hir::walk_package(&mut visitor, &package);
                calls = visitor.calls;
                calls.sort_by(|(a, _), (b, _)| a.cmp(b));
            }
            let dcx = context.dcx();
            let mut diagnostics: Vec<_> = dcx
                .take_recorded_diagnostics()
                .into_iter()
                .map(|record| {
                    (
                        record.span.map(|span| Location::new(context, span)),
                        record.message,
                    )
                })
                .collect();
            diagnostics.sort();
            let counts = &dcx.analysis_work;
            (
                Snapshot {
                    succeeded,
                    calls,
                    diagnostics,
                },
                Work {
                    parsed_files: counts.parsed_files.get(),
                    callable_headers: counts.collected_callable_headers.get(),
                    function_bodies: counts.checked_function_bodies.get(),
                },
            )
        },
    )
}

#[test]
fn full_check_oracle_tracks_overloads_through_edits() {
    let moved =
        format!("// Move both declarations without changing their signatures.\n{DECLARATIONS}");
    let changed = CALLS.replace("Cell[int64] = cell", "Cell[int32] = cell");
    for (declarations, calls, shift, second_parameter) in [
        (DECLARATIONS, CALLS, 0, "string"),
        (&moved, &changed, 1, "bool"),
        (DECLARATIONS, CALLS, 0, "string"),
    ] {
        let (snapshot, work) = full_check(declarations, calls);
        assert!(snapshot.succeeded, "{:?}", snapshot.diagnostics);
        assert!(
            snapshot.diagnostics.is_empty(),
            "{:?}",
            snapshot.diagnostics
        );
        assert_eq!(snapshot, full_check(declarations, calls).0);
        assert_eq!(
            work,
            Work {
                parsed_files: 2,
                callable_headers: 6,
                function_bodies: 5
            }
        );
        assert_eq!(snapshot.calls.len(), 2);

        for ((_, call), parameter) in snapshot.calls.iter().zip(["bool", second_parameter]) {
            assert_eq!(call.receiver, "Dispatch");
            assert_eq!(call.argument, parameter);
            assert_eq!(call.result, "int32");
            let destination = &call.declaration.location;
            assert_eq!(destination.file, "dispatch.tr");
            assert_eq!(
                destination.start.line,
                7 + shift + usize::from(parameter == "string")
            );
            assert_eq!(destination.end.line, destination.start.line);
            assert_eq!((destination.start.offset, destination.end.offset), (9, 14));
            assert!(call.declaration.signature.contains(parameter));
        }
        if second_parameter == "string" {
            // The calls share a return type. Substituting the other overload
            // must fail comparison even if the inferred result is unchanged.
            let mut wrong = full_check(declarations, calls).0;
            wrong.calls[1].1.declaration = wrong.calls[0].1.declaration.clone();
            assert_ne!(snapshot, wrong);
        }
    }
}

#[test]
fn full_check_oracle_normalizes_diagnostics_across_checkouts() {
    let broken = CALLS.replace("dispatch.label(value)", "dispatch.label(missing)");
    let (snapshot, _) = full_check(DECLARATIONS, &broken);
    assert!(!snapshot.succeeded);
    assert!(
        snapshot.diagnostics.iter().any(|(location, message)| {
            location
                .as_ref()
                .is_some_and(|span| span.file == "calls.tr")
                && message.contains("missing")
        }),
        "{:?}",
        snapshot.diagnostics
    );
    assert_eq!(snapshot, full_check(DECLARATIONS, &broken).0);
}
