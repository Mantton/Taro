//! Brackets specialize a method or index a value according to member lookup.
//! The parser and resolver preserve both readings; neither token spelling nor
//! the presence of a subsequent call determines the interpretation.
use super::*;

impl<'ctx> Checker<'ctx> {
    /// Classification checks this exact receiver once. Replaying a chosen
    /// branch must reuse its type/adjustments, not synthesize its subtree again
    /// and append another borrow/deref to the same HIR identities.
    pub(super) fn with_prechecked_bracket_receiver<R>(
        &self,
        node: NodeID,
        ty: Ty<'ctx>,
        check: impl FnOnce() -> R,
    ) -> R {
        let previous = self
            .prechecked_bracket_receivers
            .borrow_mut()
            .insert(node, ty);
        let result = check();
        let mut receivers = self.prechecked_bracket_receivers.borrow_mut();
        match previous {
            Some(previous) => {
                receivers.insert(node, previous);
            }
            None => {
                receivers.remove(&node);
            }
        }
        result
    }

    pub(super) fn synth_member_brackets(
        &self,
        expression: &hir::Expression,
        member: &hir::Expression,
        arguments: &hir::TypeArguments,
        indexed: Option<&hir::Expression>,
        diagnostics: &crate::diagnostics::BracketDiagnostics,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let hir::ExpressionKind::Member { target, name } = &member.kind else {
            self.gcx().dcx().emit_error(
                "method type arguments require an instance member".into(),
                Some(expression.span),
            );
            return Ty::error(self.gcx());
        };
        let (kind, receiver) = cs.without_fallbacks(|cs| {
            let receiver = self.synth(target, cs);
            let kind = cs.infer_cx.next_ty_var(expression.span);
            let probe = self.method_value_node();
            cs.add_goal(
                Goal::Member(MemberGoalData {
                    classify_only: true,
                    receiver_addressable: self.receiver_is_addressable(target, cs),
                    explicit_arguments: None,
                    node_id: probe,
                    receiver_node: self.method_value_node(),
                    receiver,
                    name: *name,
                    result: kind,
                    span: member.span,
                    signature_hint: None,
                }),
                member.span,
            );
            cs.solve_intermediate();
            (cs.structurally_resolve(kind), receiver)
        });
        if kind.is_error() {
            return kind;
        }
        if kind.is_infer() {
            self.gcx().dcx().emit_error(
                "cannot infer the receiver type for this bracketed member".into(),
                Some(member.span),
            );
            return Ty::error(self.gcx());
        }
        let is_value = kind == self.gcx().types.bool;
        let selected_diagnostics = if is_value {
            &diagnostics.index
        } else {
            &diagnostics.types
        };
        let invalid = selected_diagnostics
            .iter()
            .any(|diagnostic| diagnostic.level == crate::diagnostics::DiagnosticLevel::Error);
        for diagnostic in selected_diagnostics {
            self.gcx().dcx().emit(diagnostic.clone());
        }
        if invalid {
            return Ty::error(self.gcx());
        }
        self.with_prechecked_bracket_receiver(target.id, receiver, || {
            if is_value {
                let Some(indexed) = indexed else {
                    self.gcx().dcx().emit_error(
                        "a value subscript requires one expression".into(),
                        Some(arguments.span),
                    );
                    return Ty::error(self.gcx());
                };
                let mut indexed = indexed.clone();
                indexed.id = expression.id;
                self.results
                    .borrow_mut()
                    .selected_brackets
                    .insert(expression.id, indexed.clone());
                self.synth_with_expectation(&indexed, expectation, cs)
            } else {
                let selected = hir::Expression {
                    id: expression.id,
                    span: expression.span,
                    kind: hir::ExpressionKind::Member {
                        target: target.clone(),
                        name: *name,
                    },
                };
                self.results
                    .borrow_mut()
                    .selected_brackets
                    .insert(expression.id, selected.clone());
                self.synth_member_expression_with_arguments(
                    &selected,
                    target,
                    name,
                    expectation,
                    Some(arguments),
                    cs,
                )
            }
        })
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn instance_brackets_select_generic_calls_method_values_and_const_arguments() {
        let diagnostics = crate::test_support::analyze_script_mir_diagnostics(
            r#"
struct Counter { value: int32 }
extend Counter {
    func echo[T](_ value: T) -> T { value }
    func width[const N: usize](_ value: [int32; N]) -> usize { N }
}
func main() {
    var counter: Counter = Counter { value: 1 }
    var result: int32 = counter.echo[int32](7)
    callback := counter.echo[int64]
    var second: int64 = callback(8_i64)
    var values: [int32; 2] = [1, 2]
    var count: usize = counter.width[2](values)
}
"#,
        );
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }

    #[test]
    fn specialized_method_values_preserve_unused_type_and_const_arguments() {
        let diagnostics = crate::test_support::analyze_script_mir_diagnostics(
            r#"
struct Counter {}
extend Counter {
    func token[T]() -> int32 { 7 }
    func width[const N: usize]() -> usize { N }
}
func main() {
    var counter: Counter = Counter {}
    callback := counter.token[int64]
    var value: int32 = callback()
    var count: usize = counter.width[3]()
}
"#,
        );
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }

    #[test]
    fn field_indexing_keeps_its_value_namespace_and_mutable_place() {
        let diagnostics = crate::test_support::analyze_script_mir_diagnostics(
            r#"

struct Buffer { item: int32 }
extend &Buffer { subscript(key: usize) -> int32 { address { &self.item } } }
struct Holder { values: Buffer }
func main() {
    var owner: Holder = Holder { values: Buffer { item: 1 } }
    var int32: usize = 0
    owner.values[int32] += 1
    value := owner.values[int32]
}
"#,
        );
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }

    #[test]
    fn immediate_specialized_borrowed_results_depend_on_the_actual_receiver() {
        let diagnostics = crate::test_support::analyze_script_mir_diagnostics(
            r#"
struct Counter { value: int32 }
extend Counter {
    func read[T]() -> &int32 { &self.value }
    func edit[T]() -> &int32 { &self.value }
}
func main() {
    var counter: Counter = Counter { value: 1 }
    var read: &int32 = counter.read[bool]()
    var first: int32 = *read
    var edit: &int32 = counter.edit[bool]()
    *edit = first + 1
}
"#,
        );
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }

    #[test]
    fn immediate_specialization_does_not_duplicate_receiver_dereferences() {
        let diagnostics = crate::test_support::analyze_script_mir_diagnostics(
            r#"
struct Counter { value: int32 }
struct Owner { counter: Counter }
extend Counter { func read[T]() -> &int32 { &self.value }; }
func direct(_ counter: &Counter) -> &int32 { counter.read[bool]() }
func nested(_ owner: &Owner) -> &int32 { owner.counter.read[bool]() }
func main() {}
"#,
        );
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }

    #[test]
    fn indexing_a_generic_field_through_a_borrow_returns_the_element() {
        let diagnostics = crate::test_support::analyze_script_mir_diagnostics(
            r#"

struct Buffer { value: int32 }
extend &Buffer { subscript(key: usize) -> int32 { address { &self.value } } }
struct Box[T] { value: T }
func read(_ value: &Box[Buffer]) -> int32 { value.value[0] }
func main() {}
"#,
        );
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }

    #[test]
    fn only_the_selected_bracket_namespace_reports_name_errors() {
        let prefix = "struct Counter { values: [int32; 2] }\nextend Counter { func echo[T](_ value: T) -> T { value }; }\n";
        for expression in ["counter.echo[Missing](7)", "counter.values[Missing]"] {
            let source = format!(
                "{prefix}func main() {{ counter := Counter {{ values: [1, 2] }}; result := {expression}; }}"
            );
            let diagnostics = crate::test_support::analyze_script_diagnostics(&source);
            assert_eq!(diagnostics.len(), 1, "{expression}: {diagnostics:#?}");
            assert!(
                diagnostics[0].message.contains("Missing"),
                "{expression}: {diagnostics:#?}"
            );
        }
    }
}
