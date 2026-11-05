//! Raw pointers carry no checked validity or loan authority. Both explicit
//! dereference and compiler-inserted dereference need an unsafe source context.

use super::*;

impl<'ctx> Checker<'ctx> {
    pub(super) fn validate_raw_deref_adjustments(
        &self,
        id: NodeID,
        adjustments: &[Adjustment<'ctx>],
        cs: &Cs<'ctx>,
    ) {
        if !adjustments
            .iter()
            .any(|adjustment| matches!(adjustment, Adjustment::Dereference))
        {
            return;
        }
        let Some((span, is_unsafe)) = self.expression_contexts.borrow().get(&id).copied() else {
            return;
        };
        if is_unsafe {
            return;
        }
        let Some(mut ty) = cs.expr_ty(id) else {
            return;
        };
        for adjustment in adjustments {
            match adjustment {
                Adjustment::DerefCall { result, .. } => {
                    ty = *result;
                    continue;
                }
                Adjustment::Reference => {
                    ty = Ty::new(TyKind::Reference(ty), self.gcx());
                    continue;
                }
                Adjustment::Dereference => {}
                _ => break,
            }
            ty = crate::sema::tycheck::utils::normalize_aliases(
                self.gcx(),
                cs.structurally_resolve(ty),
            );
            match ty.kind() {
                TyKind::Reference(inner) => ty = inner,
                TyKind::Pointer(_, _) => {
                    if self.reported_raw_dereferences.borrow_mut().insert(id) {
                        self.gcx().dcx().emit_error(
                            "dereferencing a raw pointer requires an unsafe { ... } block".into(),
                            Some(span),
                        );
                    }
                    return;
                }
                _ => return,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::test_support::analyze_script_mir_diagnostics;

    const TYPES: &str = r#"
struct Counter { value: int32 }
extend Counter {
    func inspect() -> int32 { self.value }
    func increment() { self.value += 1 }
}
"#;

    #[test]
    fn raw_dereference_requires_unsafe_for_explicit_and_implicit_access() {
        for function in [
            "func bad(_ pointer: *const int32) -> int32 { *pointer }",
            "func bad(_ pointer: *const Counter) -> int32 { pointer.value }",
            "func bad(_ pointer: *const Counter) -> int32 { pointer.inspect() }",
            "func bad(_ pointer: *mut Counter) { pointer.increment() }",
            "func bad(_ pointer: *const Counter) -> int32 { inspect := pointer.inspect; inspect() }",
            "func bad(_ pointer: *const int32) { reference := &*pointer; value := *reference }",
        ] {
            let errors =
                analyze_script_mir_diagnostics(&format!("{TYPES}\n{function}\nfunc main() {{}}"));
            assert!(
                errors.iter().any(|error| error.message.contains("unsafe")),
                "{function}\n{errors:#?}"
            );
        }
    }

    #[test]
    fn block_local_receiver_constraints_survive_method_value_elaboration() {
        let errors = analyze_script_mir_diagnostics(&format!(
            r#"{TYPES}
func main() {{
    var value = Counter {{ value: 7 }}
    unsafe {{
        var pointer: *mut Counter = &value as *mut Counter
        inspect := pointer.inspect
        observed := inspect()
    }}
}}
"#
        ));
        assert!(errors.is_empty(), "{errors:#?}");
    }

    #[test]
    fn interface_witnesses_preserve_method_safety() {
        for (requirement, implementation, valid) in [
            ("", "unsafe ", false),
            ("unsafe ", "", false),
            ("unsafe ", "unsafe ", true),
            ("", "", true),
        ] {
            let source = format!(
                r#"
interface Inspect {{ {requirement}func inspect() -> int32; }}
struct Counter {{ value: int32 }}
conform Counter to Inspect {{
    {implementation}func inspect() -> int32 {{ self.value }}
}}
func generic[T: Inspect](_ value: &T) -> int32 {{ unsafe {{ value.inspect() }} }}
func main() {{ value := Counter {{ value: 7 }}; result := generic(&value) }}
"#
            );
            let errors = analyze_script_mir_diagnostics(&source);
            if valid {
                assert!(errors.is_empty(), "{source}\n{errors:#?}");
            } else {
                assert!(
                    errors
                        .iter()
                        .any(|error| error.message.contains("does not satisfy requirements")),
                    "{source}\n{errors:#?}"
                );
            }
        }
    }

    #[test]
    fn unsafe_context_is_preserved_through_deferred_member_resolution() {
        let errors = analyze_script_mir_diagnostics(&format!(
            r#"{TYPES}
func explicit(_ pointer: *const int32) -> int32 {{ unsafe {{ *pointer }} }}
func field(_ pointer: *const Counter) -> int32 {{ unsafe {{ pointer.value }} }}
func method(_ pointer: *mut Counter) {{ unsafe {{ pointer.increment() }} }}
func bound(_ pointer: *const Counter) -> int32 {{
    inspect := unsafe {{ pointer.inspect }}
    inspect()
}}
func shared(_ pointer: &Counter) -> int32 {{ pointer.inspect() }}
func main() {{}}
"#
        ));
        assert!(errors.is_empty(), "{errors:#?}");
    }
}
