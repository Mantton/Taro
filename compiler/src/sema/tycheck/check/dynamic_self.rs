//! Dynamic Self construction captures the class identity as a machine word.
//! It adds no instance reference to an otherwise valid closure.
use super::*;
use crate::sema::{
    models::{CaptureKind, CapturedVar},
    tycheck::results::DynamicSelfContext,
};

pub(super) fn run<'ctx>(
    package: &hir::Package,
    gcx: Gcx<'ctx>,
    results: &mut TypeCheckResults<'ctx>,
) {
    struct Collector<'a, 'ctx> {
        gcx: Gcx<'ctx>,
        results: &'a mut TypeCheckResults<'ctx>,
        current: Option<(DefinitionID, DynamicSelfContext<'ctx>)>,
        closures: Vec<DefinitionID>,
        captures: rustc_hash::FxHashSet<DefinitionID>,
    }
    impl<'ctx> HirVisitor for Collector<'_, 'ctx> {
        fn visit_function(
            &mut self,
            id: DefinitionID,
            function: &hir::Function,
            fc: hir::FunctionContext,
        ) {
            let previous = self.current.take();
            let previous_closures = std::mem::take(&mut self.closures);
            if !matches!(fc, hir::FunctionContext::Initializer(_)) {
                let signature = self.gcx.get_signature(id);
                if let Some((parameter, input)) = function
                    .signature
                    .prototype
                    .inputs
                    .first()
                    .zip(signature.inputs.first())
                    && self.gcx.symbol_eq(parameter.name.symbol, "self")
                {
                    let class = match input.ty.kind() {
                        crate::sema::models::TyKind::Reference(class) => class,
                        _ => input.ty,
                    };
                    if self.gcx.is_class_type(class) {
                        self.current = Some((
                            id,
                            DynamicSelfContext {
                                receiver: parameter.id,
                                receiver_ty: input.ty,
                                class,
                            },
                        ));
                    }
                }
            }
            hir::walk_function(self, id, function, fc);
            self.current = previous;
            self.closures = previous_closures;
        }
        fn visit_expression(&mut self, expression: &hir::Expression) {
            if let hir::ExpressionKind::Closure(closure) = &expression.kind {
                self.closures.push(closure.def_id);
                hir::walk_expression(self, expression);
                self.closures.pop();
                return;
            }
            if let hir::ExpressionKind::Call { callee, .. } = &expression.kind
                && let hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path)) = &callee.kind
                && matches!(path.resolution, hir::Resolution::SelfTypeAlias(_))
            {
                let class = self
                    .gcx
                    .constructor_value(self.results.node_type(expression.id));
                if self
                    .gcx
                    .class_info(class)
                    .is_some_and(|info| !info.is_final)
                {
                    let source = self.results.overload_source(callee.id).or_else(|| {
                        self.results
                            .value_resolution(callee.id)
                            .and_then(|resolution| resolution.definition_id())
                    });
                    let required = source
                        .and_then(|source| {
                            self.gcx
                                .class_initializer(self.gcx.get_signature(source).output, source)
                        })
                        .is_some_and(|entry| entry.is_required);
                    if !required {
                        self.gcx.dcx().emit_error("constructing dynamic Self in a non-final class requires a required initializer".into(), Some(expression.span));
                    } else if let Some((owner, context)) = self.current {
                        self.results.dynamic_self_calls.insert(expression.id);
                        self.results.dynamic_self_contexts.insert(owner, context);
                        self.captures.extend(self.closures.iter().copied());
                    } else {
                        self.gcx.dcx().emit_error(
                            "dynamic Self construction requires an initialized instance receiver"
                                .into(),
                            Some(expression.span),
                        );
                    }
                }
            }
            hir::walk_expression(self, expression);
        }
    }
    let mut collector = Collector {
        gcx,
        results,
        current: None,
        closures: vec![],
        captures: Default::default(),
    };
    hir::walk_package(&mut collector, package);
    for closure in collector.captures {
        let mut captures = gcx
            .get_closure_captures(closure)
            .expect("checked closure captures");
        captures.captures.push(CapturedVar {
            source_id: hir::NodeID::from_raw(
                crate::sema::tycheck::results::DYNAMIC_SELF_CONTEXT_LOCAL_RAW,
            ),
            root_ty: gcx.types.uint,
            projection: &[],
            name: gcx.intern_symbol("$dynamic_self_context"),
            ty: gcx.types.uint,
            capture_kind: CaptureKind::ByCopy,
            source_immutable: true,
            field_index: crate::thir::FieldIndex::from_usize(captures.captures.len()),
        });
        gcx.cache_closure_captures(closure, captures);
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn g37_required_initializers_cannot_hide_the_subclass_contract() {
        for source in [
            "public class Example {}\nextend Example { private required init() {}; }",
            "public class Example {}\nextend Example { required init() {}; }",
            "class Example {}\nextend Example { private required init() {}; }",
            "private class Example {}\nextend Example { private required init() {}; }",
            "public class Example {}\nextend Example { public init(_ flag: bool) {}; private required convenience init() { self.init(true) }; }",
            "internal class Base {}\nextend Base { required init() {}; }\npublic class Child: Base {}",
        ] {
            let diagnostics = crate::test_support::analyze_script_diagnostics(&format!(
                "{source}\nfunc main() {{}}"
            ));
            assert!(
                diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.message.contains(
                        "required initializer must be at least as visible as its non-final class"
                    )),
                "{source}\n{diagnostics:#?}"
            );
        }
    }

    #[test]
    fn g37_required_initializer_visibility_allows_visible_contracts_and_final_classes() {
        for source in [
            "public class Example {}\nextend Example { public required init() {}; }",
            "internal class Example {}\nextend Example { required init() {}; }",
            "private class Example {}\nextend Example { required init() {}; }",
            "public final class Example {}\nextend Example { private required init() {}; static func fresh() -> Self { Self() }; }",
            "public final class Example {}\nextend Example { private init(_ flag: bool) {}; private required convenience init() { self.init(true) }; }",
            "internal class Base {}\nextend Base { required init() {}; }\npublic class Child: Base {}\nextend Child { public required override init() { super.init() }; }",
        ] {
            crate::test_support::analyze_script(&format!("{source}\nfunc main() {{}}"), |_, _| {});
        }
    }

    #[test]
    fn dynamic_self_closures_capture_type_context_without_referencing_the_instance() {
        crate::test_support::analyze_script(
            r#"
class Base { value: int32 }
extend Base {
    public required init(_ value: int32) { self.value = value }
    func fresh() -> Self { Self(7) }
    func callbacks() {
        callback := () => Self(1)
        nested := () => { inner := () => Self(2); inner() }
        first := callback()
        second := nested()
    }
}
final class Child: Base { extra: int32 = 11 }
func main() {}
"#,
            |_, gcx| {
                let captures = gcx.with_session_type_database(|database| {
                    database
                        .closure_captures
                        .values()
                        .cloned()
                        .collect::<Vec<_>>()
                });
                assert_eq!(captures.len(), 3);
                for closure in captures {
                    assert_eq!(closure.captures.len(), 1);
                    let context = closure.captures[0];
                    assert_eq!(context.ty, gcx.types.uint);
                    assert_eq!(
                        context.capture_kind,
                        crate::sema::models::CaptureKind::ByCopy
                    );
                    assert!(context.projection.is_empty());
                }
            },
        );
    }

    #[test]
    fn inherited_generic_methods_supply_collection_literal_context() {
        let errors = crate::test_support::analyze_language_item_script(
            r#"
struct List[T] {}
class Base[T] {}
extend[T] Base[T] { func accept(_ payload: T) {}; }
class Middle[T]: Base[T] {}
final class Child[U]: Middle[U] {}
func use(_ value: &Child[List[int32]]) { value.accept([1, 2]) }
func main() {}
"#,
            false,
            &[(crate::hir::StdItem::List, "List")],
        );
        assert!(errors.is_empty(), "{errors:#?}");
    }

    #[test]
    fn inherited_self_results_follow_the_static_receiver_type() {
        crate::test_support::analyze_script(
            r#"
class Base[T] { value: T }
extend[T] Base[T] {
    public required init(_ value: T) { self.value = value }
    func fresh(_ value: T) -> Self { Self(value) }
    func delayed(_ value: T) async -> Self { Self(value) }
    func identity() -> Self { self }
}
class Child[T]: Base[T] { extra: int32 = 11 }
final class Grandchild[T]: Child[T] {}
func inherited(_ value: &Child[int32]) -> Child[int32] { value.fresh(7) }
func generic[T](_ value: &Grandchild[T], _ payload: T) -> Grandchild[T] { value.fresh(payload) }
func delayed(_ value: &Child[int32]) async -> Child[int32] { await value.delayed(7) }
func bound(_ value: &Child[int32]) -> Child[int32] { call := value.identity; call() }
func main() {}
"#,
            |_, _| {},
        );
    }

    #[test]
    fn required_constructor_obligations_preserve_both_constructor_categories() {
        crate::test_support::analyze_script(
            r#"
class Base { value: int32 }
extend Base {
    public required init(_ value: int32) { self.value = value }
    public required convenience init() { self.init(7) }
}
class Automatic: Base { extra: int32 = 1 }
class Explicit: Base { extra: int32 }
extend Explicit {
    public required override init(_ value: int32) { super.init(value); self.extra = 2 }
    public required convenience init() { self.init(9) }
}
func main() {}
"#,
            |package, gcx| {
                for name in ["Automatic", "Explicit"] {
                    let id = package
                        .root
                        .declarations
                        .iter()
                        .find(|declaration| gcx.symbol_text(declaration.identifier.symbol).as_str() == name)
                        .unwrap()
                        .id;
                    let entries = gcx.class_info(gcx.get_type(id)).unwrap().initializers;
                    assert_eq!(entries.iter().filter(|entry| entry.is_required).count(), 2);
                }
            },
        );
    }

    #[test]
    fn invalid_dynamic_self_and_missing_required_implementations_reject() {
        for (source, expected) in [
            (
                "class Base { value: int32 }\nextend Base { init(_ value: int32) { self.value = value }; func fresh() -> Self { Self(7) }; }\nfunc main() {}",
                "requires a required initializer",
            ),
            (
                "class Base { value: int32 }\nextend Base { public required init(_ value: int32) { self.value = value }; static func fresh() -> Self { Self(7) }; }\nfunc main() {}",
                "requires an initialized instance receiver",
            ),
            (
                "class Base { value: int32 }\nextend Base { public required init(_ value: int32) { self.value = value } }\nclass Child: Base { extra: int32 }\nextend Child { init() { super.init(1); self.extra = 2 } }\nfunc main() {}",
                "every required initializer",
            ),
            (
                "class Base { value: int32 }\nextend Base { public required init(_ value: int32) { self.value = value } }\nclass Child: Base {}\nextend Child { override init(_ value: int32) { super.init(value) } }\nfunc main() {}",
                "must repeat required",
            ),
            (
                "struct Value { value: int32 }\nextend Value { public required init(_ value: int32) { self.value = value } }\nfunc main() {}",
                "required init requires a class",
            ),
        ] {
            let diagnostics = crate::test_support::analyze_script_diagnostics(source);
            assert!(
                diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.message.contains(expected)),
                "{expected}: {diagnostics:#?}"
            );
        }
    }
}
