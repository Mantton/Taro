//! Contextual views of built-in collections. This never changes call arity:
//! an argument is converted only when its expected type is already a Span.

use super::{Adjustment, ConstraintSolver, Goal, Obligation, SolverResult};
use crate::{
    hir::{NodeID, StdItem},
    sema::{
        models::{GenericArgument, Ty, TyKind},
        tycheck::utils::unresolved::ty_contains_unresolved_inference,
    },
    span::Span,
};

impl<'ctx> ConstraintSolver<'ctx> {
    pub(super) fn solve_collection_span_coercion(
        &mut self,
        location: Span,
        node_id: NodeID,
        from: Ty<'ctx>,
        to: Ty<'ctx>,
    ) -> Option<SolverResult<'ctx>> {
        let TyKind::Adt(target, target_args) = to.kind() else {
            return None;
        };
        if Some(target.id) != self.gcx().std_item_def(StdItem::Span) || target_args.len() != 1 {
            return None;
        }
        let Some(GenericArgument::Type(expected)) = target_args.get(0) else {
            return None;
        };
        let TyKind::Reference(collection) = from.kind() else {
            return None;
        };
        let collection = self.structurally_resolve(collection);
        let element = match collection.kind() {
            TyKind::Array { element, .. } => element,
            TyKind::Adt(definition, arguments)
                if Some(definition.id) == self.gcx().std_item_def(StdItem::List)
                    && arguments.len() == 1 =>
            {
                let Some(GenericArgument::Type(element)) = arguments.get(0) else {
                    return None;
                };
                *element
            }
            // Revisit an inferred literal/projection once its source shape is
            // known. An abstract associated type is not evidence of a built-in
            // collection; deferring it forever would skip a required check.
            _ if ty_contains_unresolved_inference(collection) => {
                return Some(SolverResult::Deferred);
            }
            _ => return None,
        };
        // Equality, not element-wise coercion: a writable view must preserve
        // the original storage representation and element type.
        self.coercions += 1;
        self.append_adjustments(node_id, vec![Adjustment::CollectionToSpan { to }]);
        Some(SolverResult::Solved(vec![Obligation {
            location,
            goal: Goal::ConstraintEqual(*expected, element),
        }]))
    }
}

#[cfg(test)]
mod tests {
    use crate::{hir::StdItem, test_support::analyze_language_item_script};

    const TYPES: &str = "struct Span[T] {}\nstruct List[T] {}\n";
    const ITEMS: &[(StdItem, &str)] = &[(StdItem::Span, "Span"), (StdItem::List, "List")];

    fn errors(source: &str) -> Vec<crate::diagnostics::Diagnostic> {
        analyze_language_item_script(&format!("{TYPES}{source}"), false, ITEMS)
    }

    #[test]
    fn collection_span_coercion_accepts_references_in_expected_type_positions() {
        let diagnostics = errors(
            r#"
type View[T] = Span[T]
func arrayView[T, const N: usize](_ value: &[T; N]) -> View[T] { value }
func listView[T](_ value: &List[T]) -> View[T] { value }
func take[T](_ value: Span[T]) {}
func main() {
    var array: [int32; 2] = [1, 2]
    var list: List[int32] = List[int32] {}
    var view: Span[int32] = &array
    view = &list
    take(&array)
    take(&list)
    var a: Span[int32] = arrayView(&array)
    var b: Span[int32] = listView(&list)
}
"#,
        );
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }

    #[test]
    fn collection_span_coercion_preserves_exact_reference_overloads() {
        let diagnostics = errors(
            r#"
func choose(_ value: &[int32; 2]) -> int32 { 1 }
func choose(_ value: Span[int32]) -> bool { true }
func main() {
    var array: [int32; 2] = [1, 2]
    var selected: int32 = choose(&array)
}
"#,
        );
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }

    #[test]
    fn collection_span_coercion_rejects_copies_and_different_element_types() {
        for source in [
            "func f(_ value: List[int32]) -> Span[int32] { value }",
            "func f(_ value: [int32; 2]) -> Span[int32] { value }",
            "func f(_ value: &List[int32]) -> Span[int64] { value }",
            "func f(_ value: &[int32; 2]) -> Span[int64] { value }",
            "func f(_ value: &Span[int32]) -> Span[int32] { value }",
            "func f(_ value: &string) -> Span[uint8] { value }",
        ] {
            assert!(!errors(source).is_empty(), "accepted {source}");
        }
    }

    #[test]
    fn collection_span_coercion_reports_the_target_element_type_as_expected() {
        for source in [
            "func view(_ value: &[int32; 2]) -> Span[int64] { value }",
            "func view(_ value: &List[int32]) -> Span[int64] { value }",
        ] {
            let diagnostics = errors(source);
            assert!(
                diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.message == "expected int64, found int32"),
                "{diagnostics:#?}"
            );
        }
    }

    #[test]
    fn collection_span_coercion_rejects_abstract_associated_types() {
        let diagnostics = errors(
            "interface Source { type Value; }\nfunc view[S: Source](_ value: &S::Value) -> Span[int32] { value }",
        );
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message.contains("expected Span[int32]")),
            "{diagnostics:#?}"
        );
        assert!(
            !diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message.contains("internal error")),
            "{diagnostics:#?}"
        );
    }

    #[test]
    fn collection_span_coercion_requires_builtin_identities_not_method_names() {
        let source = format!(
            "{TYPES}\nextend[T] &List[T] {{ func asSpan() -> Span[T] {{ Span[T] {{}} }} }}\nfunc view(_ value: &List[int32]) -> Span[int32] {{ value }}"
        );
        let diagnostics = analyze_language_item_script(&source, false, &[(StdItem::Span, "Span")]);
        assert!(
            !diagnostics.is_empty(),
            "a user-defined List/asSpan must not enable implicit coercion"
        );
    }

    #[test]
    fn collection_span_coercion_does_not_infer_a_span_or_expand_variadics() {
        let diagnostics = errors(
            r#"
func identity[T](_ value: T) -> T { value }
func pack[T](_ values: T...) -> Span[T] { values }
func main() {
    var array: [int32; 2] = [1, 2]
    var reference: &[int32; 2] = identity(&array)
    var packed: Span[&[int32; 2]] = pack(&array)
}
"#,
        );
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
        assert!(!errors("func sum(_ values: int32...) {}\nfunc main() { var array: [int32; 2] = [1, 2]; sum(&array) }").is_empty());
    }
}
