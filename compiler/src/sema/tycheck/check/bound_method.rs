//! Method values capture their actual receiver once; they do not expose self
//! as an extra callable argument or copy a borrowed receiver to make it escape.

use super::*;
use crate::sema::tycheck::{results::BoundMethod, utils::normalize_aliases};

impl<'ctx> Checker<'ctx> {
    /// Reserve synthetic node identities in the compiler-generated namespace.
    /// Using the same allocator as synthetic definitions prevents collisions
    /// between independently desugared method values in a package.
    pub(super) fn method_value_node(&self) -> NodeID {
        NodeID::from_raw(
            self.gcx()
                .allocate_synthetic_id(self.current_def.package())
                .index()
                .raw(),
        )
    }

    /// A method value carries its receiver. Construct that environment after
    /// the enclosing expression supplies the receiver's type, and before the
    /// final solve commits uses of the callable.
    pub(super) fn finish_member_values(&self, cs: &mut Cs<'ctx>) {
        while let Some(pending) = cs.pending_member_values.front().cloned() {
            let member = pending.member;
            let signature = cs.solve_producers(pending.selection);
            let actual = if let hir::ExpressionKind::Member { target, name } = &member.kind
                && let Some(source) = cs.bound_method_source(member.id)
                && matches!(signature.kind(), TyKind::FnPointer { .. })
            {
                self.synth_bound_method(&member, target, *name, source, signature, cs)
            } else {
                signature
            };
            cs.finish_member_value(actual);
        }
    }

    pub(super) fn synth_bound_method(
        &self,
        expression: &hir::Expression,
        target: &hir::Expression,
        name: crate::span::Identifier,
        source: DefinitionID,
        callback_signature: Ty<'ctx>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let gcx = self.gcx();
        let signature = instantiate_signature_with_args(
            gcx,
            gcx.get_signature(source),
            cs.instantiation(expression.id)
                .unwrap_or_else(GenericArguments::empty),
        );
        if signature.is_variadic {
            gcx.dcx().emit_error(
                "variadic methods cannot be captured as method values".into(),
                Some(expression.span),
            );
            return Ty::error(gcx);
        }
        let receiver_ty = cs.structurally_resolve(signature.inputs[0].ty);
        let (mut value_ty, borrowed) = match receiver_ty.kind() {
            TyKind::Reference(inner) => (inner, true),
            _ => (receiver_ty, false),
        };
        let mut actual = cs
            .expr_ty(target.id)
            .map(|ty| cs.structurally_resolve(ty))
            .unwrap_or(value_ty);
        while let TyKind::Reference(inner) = actual.kind() {
            actual = inner;
        }
        if !borrowed && gcx.is_class_subtype(actual, value_ty) {
            value_ty = actual;
        }
        // A class method binds the selected object, not the variable holding
        // its handle. Reference receivers of inline values retain their slot.
        let snapshot = !borrowed;
        if borrowed {
            let mut selected = cs
                .expr_ty(target.id)
                .map(|ty| cs.structurally_resolve(ty))
                .unwrap_or(receiver_ty);
            for adjustment in cs.receiver_adjustments(target.id).unwrap_or_default() {
                if matches!(adjustment, Adjustment::Dereference)
                    && let TyKind::Reference(inner) = normalize_aliases(gcx, selected).kind()
                {
                    selected = inner;
                }
            }
            if normalize_aliases(gcx, selected) == normalize_aliases(gcx, receiver_ty) {
                // An explicit reference value selects its pointee storage;
                // an automatic reference already starts with that storage.
                cs.append_adjustments(target.id, vec![Adjustment::Dereference]);
            }
        }
        let root = self.method_value_node();
        self.set_local(
            root,
            super::super::checker::LocalBinding {
                ty: value_ty,
                mutable: true,
            },
        );
        let span = expression.span;
        let local = |id, symbol| hir::Expression {
            id: self.method_value_node(),
            span,
            kind: hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(hir::Path {
                span,
                resolution: hir::Resolution::LocalVariable(id),
                segments: vec![hir::PathSegment {
                    id: self.method_value_node(),
                    identifier: crate::span::Identifier { symbol, span },
                    arguments: None,
                    span,
                    resolution: hir::Resolution::LocalVariable(id),
                }],
            })),
        };
        let mut params = Vec::new();
        let mut arguments = Vec::new();
        for (index, parameter) in signature.inputs.iter().skip(1).enumerate() {
            let id = self.method_value_node();
            let symbol = gcx.intern_symbol(&format!("$argument{index}"));
            params.push(hir::ClosureParam {
                id,
                pattern: hir::Pattern {
                    id,
                    span,
                    kind: hir::PatternKind::Binding {
                        name: crate::span::Identifier { symbol, span },
                    },
                },
                ty: None,
                span,
            });
            arguments.push(hir::ExpressionArgument {
                label: parameter.label.map(|symbol| hir::Label {
                    identifier: crate::span::Identifier { symbol, span },
                    span,
                }),
                expression: Box::new(local(id, symbol)),
                span,
            });
        }
        let call_id = self.method_value_node();
        // Explicit type arguments and reference copies must reuse selection.
        // Abstract and erased method values retain ordinary interface dispatch.
        let direct = self
            .results
            .borrow()
            .selected_brackets
            .contains_key(&expression.id)
            || (borrowed && gcx.definition_is_clone_method(source));
        let kind = if direct {
            let receiver = Box::new(local(root, gcx.intern_symbol("$receiver")));
            let receiver = if borrowed {
                Box::new(hir::Expression {
                    id: self.method_value_node(),
                    span,
                    kind: hir::ExpressionKind::Reference(receiver),
                })
            } else {
                receiver
            };
            arguments.insert(
                0,
                hir::ExpressionArgument {
                    label: None,
                    expression: receiver,
                    span,
                },
            );
            let callee = hir::Expression {
                id: self.method_value_node(),
                span,
                kind: hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(hir::Path {
                    span,
                    resolution: hir::Resolution::Definition(source, gcx.definition_kind(source)),
                    segments: vec![hir::PathSegment {
                        id: self.method_value_node(),
                        identifier: name,
                        arguments: None,
                        span,
                        resolution: hir::Resolution::Definition(
                            source,
                            gcx.definition_kind(source),
                        ),
                    }],
                })),
            };
            self.results.borrow_mut().selected_method_calls.insert(
                call_id,
                (source, cs.instantiation(expression.id).unwrap_or_default()),
            );
            hir::ExpressionKind::Call {
                callee: Box::new(callee),
                arguments,
            }
        } else {
            hir::ExpressionKind::MethodCall {
                interface: None,
                receiver: Box::new(local(root, gcx.intern_symbol("$receiver"))),
                name,
                arguments,
            }
        };
        let mut body = hir::Expression {
            id: call_id,
            span,
            kind,
        };
        let is_async = gcx.definition_is_async(source);
        if is_async {
            body = hir::Expression {
                id: self.method_value_node(),
                span,
                kind: hir::ExpressionKind::Await(Box::new(body)),
            };
        }
        let closure = hir::ClosureExpr {
            def_id: gcx.allocate_synthetic_id(self.current_def.package()),
            params,
            return_ty: None,
            is_async,
            implicit_await: false,
            body: Box::new(body),
            snapshot_captures: snapshot,
            span,
        };
        let closure_ty =
            self.synth_closure_expression(expression, &closure, Some(callback_signature), cs);
        self.locals.borrow_mut().remove(&root);
        if borrowed && !snapshot {
            cs.append_adjustments(target.id, vec![Adjustment::Reference]);
        }
        self.results.borrow_mut().record_bound_method(
            expression.id,
            BoundMethod {
                closure: closure.clone(),
                receiver: target.clone(),
            },
        );
        self.update_closure_signature(closure.def_id, closure_ty);
        closure_ty
    }
}

#[cfg(test)]
mod tests {
    use crate::test_support::analyze_language_item_script;

    fn analyze_script_mir_diagnostics(source: &str) -> Vec<crate::diagnostics::Diagnostic> {
        analyze_language_item_script(source, true, &[])
    }

    const COUNTER: &str = r#"
struct Counter { value: int32 }
extend Counter {
    func read() -> int32 { self.value }
    func increment(_ amount: int32) -> int32 { self.value += amount; self.value }
    func take() -> int32 { self.value }
}
"#;

    #[test]
    fn member_elaboration_does_not_resolve_an_incomplete_outer_overload() {
        let errors = analyze_script_mir_diagnostics(
            r#"
struct Factory { value: int32 }
extend Factory {
    static func make() -> Self { Factory { value: 0 } }
    static func make(value: int32) -> Self { Factory { value } }
}
func main() {
    source := Factory { value: 7 }
    result := Factory::make(value: source.value)
}
"#,
        );
        assert!(errors.is_empty(), "{errors:#?}");
    }

    #[test]
    fn member_elaboration_does_not_default_outer_numeric_variables() {
        let errors = analyze_script_mir_diagnostics(&format!(
            "{COUNTER}\nfunc main() {{ counter := Counter {{ value: 7 }}; var count: usize = 0; if counter.value == 0 {{ count += 1 }}; read := counter.read; count += 1; result := read() }}"
        ));
        assert!(errors.is_empty(), "{errors:#?}");
    }

    #[test]
    fn unresolved_receiver_reports_inference_instead_of_reaching_field_lowering() {
        let errors = analyze_script_mir_diagnostics(&format!(
            "{COUNTER}\nfunc main() {{ bind := (counter) => counter.read; read := bind(Counter {{ value: 7 }}); result := read() }}"
        ));
        assert!(
            !errors.is_empty(),
            "unknown receiver requires a parameter annotation"
        );
    }

    #[test]
    fn mutable_method_values_validate_the_complete_receiver_place() {
        for body in [
            "var holder = Holder { counter: Counter { value: 7 } }; increment := holder.counter.increment",
            "counter := Counter { value: 7 }; shared := &counter; increment := shared.increment",
        ] {
            let errors = analyze_script_mir_diagnostics(&format!(
                "{COUNTER}\nstruct Holder {{ readonly counter: Counter }}\nfunc main() {{ {body} }}"
            ));
            assert!(errors.is_empty(), "{body}\n{errors:#?}");
        }
    }

    #[test]
    fn shared_mutable_and_owned_method_values_use_receiver_capabilities() {
        for body in [
            "var counter = Counter { value: 7 }; read := counter.read; a := read(); b := read(); counter.value = 9",
            "var counter = Counter { value: 7 }; var increment = counter.increment; a := increment(2); b := increment(3); value := counter.value",
            "counter := Counter { value: 7 }; take := counter.take; value := take()",
        ] {
            let errors =
                analyze_script_mir_diagnostics(&format!("{COUNTER}\nfunc main() {{ {body} }}"));
            assert!(errors.is_empty(), "{body}\n{errors:#?}");
        }
    }

    /// GC method values copy their receiver reference or value: no access is
    /// held until the last call and owned extraction does not consume the source.
    #[test]
    fn method_values_are_reusable_and_do_not_hold_receiver_access() {
        for body in [
            "var counter = Counter { value: 7 }; read := counter.read; counter.value = 9; value := read()",
            "var counter = Counter { value: 7 }; var increment = counter.increment; observed := counter.value; value := increment(1)",
            "counter := Counter { value: 7 }; take := counter.take; previous := counter.value; result := take()",
            "counter := Counter { value: 7 }; take := counter.take; first := take(); second := take()",
        ] {
            let errors =
                analyze_script_mir_diagnostics(&format!("{COUNTER}\nfunc main() {{ {body} }}"));
            assert!(errors.is_empty(), "{body}\n{errors:#?}");
        }
    }

    #[test]
    fn bound_methods_preserve_nested_and_abstract_receiver_dependencies() {
        for body in [
            "func main() { counter := Counter { value: 7 }; makeRead := () => counter.read; read := makeRead(); result := read() }",
            "interface Read { func get() -> int32; }\nconform Counter to Read { func get() -> int32 { self.value }\n}\nfunc generic[T: Read](_ value: &T) -> int32 { read := value.get; read() }\nfunc main() { value := Counter { value: 7 }; result := generic(&value); var erased: any Read = Counter { value: 9 }; read := erased.get; result := read() }",
            "struct Wrapper[T] { value: T }\nextend[T] Wrapper[T] { func get() -> T { self.value }\n}\nfunc call[T](_ value: &Wrapper[T]) -> T { get := value.get; get() }\nfunc main() { value := Wrapper { value: 7_i32 }; result := call(&value) }",
        ] {
            let errors = analyze_script_mir_diagnostics(&format!("{COUNTER}\n{body}"));
            assert!(errors.is_empty(), "{body}\n{errors:#?}");
        }
    }

    #[test]
    fn temporary_receiver_is_evaluated_once_and_retained_for_a_local_method_value() {
        let errors = analyze_script_mir_diagnostics(&format!(
            "{COUNTER}\nfunc make(_ calls: &int32) -> Counter {{ *calls += 1; Counter {{ value: *calls }} }}\nfunc main() {{ var calls: int32 = 0; read := make(&calls).read; first := read(); second := read(); observed := calls }}"
        ));
        assert!(errors.is_empty(), "{errors:#?}");
    }
}
