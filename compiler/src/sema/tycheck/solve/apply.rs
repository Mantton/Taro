use crate::{
    sema::{
        error::{ApplyValidationError, TypeError},
        models::{LabeledFunctionParameter, LabeledFunctionSignature, Ty, TyKind, TyList},
        tycheck::{
            solve::{
                ApplyArgument, ApplyGoalData, ConstraintSolver, Goal, Obligation, SolverResult,
            },
            utils::{
                arguments::{match_arguments_to_parameters, validate_arity},
                callable::select_existential_callable,
            },
        },
    },
    span::Spanned,
};

impl<'ctx> ConstraintSolver<'ctx> {
    pub fn solve_apply(&mut self, data: ApplyGoalData<'ctx>) -> SolverResult<'ctx> {
        let mut callee_ty = self.structurally_resolve(data.callee_ty);
        if callee_ty.is_error() {
            // Avoid cascading errors when the callee already failed to type-check.
            return SolverResult::Solved(vec![]);
        }
        let original_callee_ty = callee_ty;
        let mut dereferences = 0;
        if data.callee_node_id.is_some() {
            while let TyKind::Reference(inner) = callee_ty.kind() {
                callee_ty = self.structurally_resolve(inner);
                dereferences += 1;
            }
        }
        let callee_source = data
            .callee_source
            .or_else(|| self.icx.overload_binding_for_ty(data.callee_ty));

        if let Some(def_id) = callee_source {
            if self.gcx().definition_is_unsafe(def_id) && !data.is_unsafe_context {
                return SolverResult::Error(vec![Spanned::new(
                    TypeError::UnsafeCallNeedsUnsafeBlock {
                        name: self.gcx().definition_symbol_or_fallback(def_id),
                    },
                    data.call_span,
                )]);
            }
        }

        if let TyKind::FnPointer { effects, .. } = callee_ty.kind()
            && effects.is_unsafe
            && !data.is_unsafe_context
        {
            return SolverResult::Error(vec![Spanned::new(
                TypeError::UnsafeCallNeedsUnsafeBlock {
                    name: self.gcx().intern_symbol("function pointer"),
                },
                data.call_span,
            )]);
        }
        let (inputs, mut output) = match callee_ty.kind() {
            TyKind::FnPointer { inputs, output, .. } => (inputs, output),
            TyKind::Closure { inputs, output, .. } => (inputs, output),
            TyKind::Infer(_) => return SolverResult::Deferred,
            TyKind::Parameter(_) => {
                // Check if this type parameter has Fn/AsyncFn bounds.
                if let Some((inputs, output)) = self.extract_fn_bound_signature(callee_ty) {
                    (inputs, output)
                } else {
                    return SolverResult::Error(vec![Spanned::new(
                        TypeError::NotCallable {
                            found: original_callee_ty,
                        },
                        data.call_span,
                    )]);
                }
            }
            _ => match select_existential_callable(self.gcx(), callee_ty) {
                Ok(Some(callable)) => {
                    self.record_interface_call(
                        data.call_node_id,
                        super::InterfaceCallInfo {
                            root_interface: callable.root_interface,
                            method_interface: callable.interface.id,
                            method_id: callable
                                .method_id(self.gcx())
                                .expect("callable method missing"),
                            table_index: callable.table_index,
                        },
                    );
                    callable
                        .signature(self.gcx())
                        .expect("callable interface signature missing")
                }
                selection => {
                    let error = if selection.is_err() {
                        TypeError::AmbiguousCallable { found: callee_ty }
                    } else {
                        TypeError::NotCallable {
                            found: original_callee_ty,
                        }
                    };
                    return SolverResult::Error(vec![Spanned::new(error, data.call_span)]);
                }
            },
        };

        let signature = if let Some(id) = callee_source {
            self.gcx().get_signature(id)
        } else {
            &LabeledFunctionSignature {
                inputs: inputs
                    .iter()
                    .map(|&t| LabeledFunctionParameter {
                        label: None,
                        name: self.gcx().intern_symbol(""),
                        ty: t,
                        default_provider: None,
                    })
                    .collect(),
                output,
                is_variadic: false,
                abi: None,
            }
        };

        // 1 - Arity
        let result = validate_arity(signature, data.arguments.len());
        match result {
            Err(e) => {
                return SolverResult::Error(vec![Spanned::new(
                    TypeError::Apply(e),
                    data.call_span,
                )]);
            }
            _ => {}
        }

        // 2 - Matching
        let result = match_arguments_to_parameters(
            &signature.inputs,
            signature.is_variadic,
            data.arguments.iter().map(|arg| (arg.label, arg.span)),
            data.skip_labels,
        );
        let positions = match result {
            Ok(v) => v,
            Err(e) => {
                return SolverResult::Error(vec![Spanned::new(TypeError::Apply(e.value), e.span)]);
            }
        };

        let result =
            produce_application_subobligations(positions, signature, &inputs, &data.arguments);
        let mut obligations = match result {
            Ok(v) => v,
            Err(e) => {
                return SolverResult::Error(vec![Spanned::new(
                    TypeError::Apply(e),
                    data.call_span,
                )]);
            }
        };

        if let Some(method) = callee_source
            && let Some(receiver) = data.arguments.first()
            && let Some(refined) = self
                .gcx()
                .class_self_result(self.structurally_resolve(receiver.ty), method)
        {
            output = refined;
        }

        obligations.push(Obligation {
            location: data.call_span,
            // A call produces its declared output. Contextual conversions
            // belong at the consuming site, after this fresh type is known.
            goal: Goal::Equal(data.result_ty, output),
        });

        if let Some(def_id) = callee_source {
            self.record_overload_source(data.call_node_id, def_id);
        }

        if let Some(node) = data.callee_node_id {
            self.record_adjustments(node, vec![super::Adjustment::Dereference; dereferences]);
        }

        return SolverResult::Solved(obligations);
    }

    /// Extract (inputs, output) from callable bounds on a type parameter.
    /// Returns None if the type has no such bounds.
    fn extract_fn_bound_signature(&self, ty: Ty<'ctx>) -> Option<(TyList<'ctx>, Ty<'ctx>)> {
        let gcx = self.gcx();
        // Get bounds for this type from the parameter environment
        let bounds = self.param_env.bounds_for(ty);

        for bound in bounds {
            if crate::sema::models::callable_kind(gcx, bound.id).is_none() {
                continue;
            }

            // Raw interface refs still carry `Self` as the first argument.
            if bound.arguments.len() < 3 {
                continue;
            }

            let args_ty = bound.arguments[1].ty()?;
            let output_ty = bound.arguments[2].ty()?;

            let inputs = crate::sema::models::callable_inputs(gcx, args_ty);

            return Some((inputs, output_ty));
        }

        None
    }
}

fn produce_application_subobligations<'c>(
    positions: Vec<Vec<usize>>,
    signature: &LabeledFunctionSignature<'c>,
    inputs: &[Ty<'c>],
    arguments: &[ApplyArgument<'c>],
) -> Result<Vec<Obligation<'c>>, ApplyValidationError> {
    let mut obligations = vec![];
    for (param_idx, arg_indices) in positions.iter().enumerate() {
        let param_defaults = signature.inputs[param_idx].default_provider.is_some();
        let param_ty = inputs[param_idx];

        if !arg_indices.is_empty() {
            // Determine expected type for the arguments
            // If this is the variadic parameter, we need to extract T from List[T]
            let expected_ty = if signature.is_variadic && param_idx == signature.inputs.len() - 1 {
                if let TyKind::Adt(_, args) = param_ty.kind() {
                    if let Some(crate::sema::models::GenericArgument::Type(inner)) = args.get(0) {
                        *inner
                    } else {
                        // Should not happen if well-formed
                        param_ty
                    }
                } else {
                    param_ty
                }
            } else {
                param_ty
            };
            for &arg_idx in arg_indices {
                let argument = arguments[arg_idx];
                let arg_ty = argument.ty;
                let constraint = Goal::Coerce {
                    node_id: argument.id,
                    from: arg_ty,
                    to: expected_ty,
                };
                let obligatin = Obligation {
                    location: argument.span,
                    goal: constraint,
                };
                obligations.push(obligatin);
            }
        } else if !param_defaults {
            // If it is variadic main parameter, it is allowed to be empty (it will be an empty list)
            let is_variadic_param =
                signature.is_variadic && param_idx == signature.inputs.len() - 1;

            if !is_variadic_param {
                let err = ApplyValidationError::MissingRequiredParameter {
                    param_index: param_idx,
                    param_name: signature.inputs[param_idx].name,
                };
                return Err(err);
            }
        }
    }

    return Ok(obligations);
}

#[cfg(test)]
mod borrowed_callable_tests {
    use crate::{hir::StdItem, test_support::analyze_language_item_script};

    #[test]
    fn direct_reference_calls_preserve_mutable_receiver_authority() {
        let errors = crate::test_support::analyze_script_mir_diagnostics(
            "func main() { read := () => 7_i32; shared := &read; result := shared(); var value: int32 = 0; var change = () => { value += 1 }; exclusive := &change; exclusive(); exclusive(); observed := value }",
        );
        assert!(errors.is_empty(), "{errors:?}");
        let errors = crate::test_support::analyze_script_mir_diagnostics(
            "func main() { var value: int32 = 0; var change = () => { value += 1 }; shared := &change; shared() }",
        );
        assert!(errors.is_empty(), "{errors:?}");
    }

    fn diagnostics(body: &str) -> Vec<crate::diagnostics::DiagnosticRecord> {
        diagnostics_with_mir(body, false)
    }

    fn diagnostics_with_mir(
        body: &str,
        build_mir: bool,
    ) -> Vec<crate::diagnostics::DiagnosticRecord> {
        let source = format!(
            r#"
interface Tuple {{}}


interface Fn[Args: Tuple, Output]{{
    func call(args: Args) -> Output
}}


interface AsyncFn[Args: Tuple, Output]{{
    func call(args: Args) async -> Output
}}
{body}
func main() {{}}
"#
        );
        analyze_language_item_script(
            &source,
            build_mir,
            &[
                (StdItem::Tuple, "Tuple"),
                (StdItem::Fn, "Fn"),
                (StdItem::Fn, "Fn"),
                (StdItem::Fn, "Fn"),
                (StdItem::AsyncFn, "AsyncFn"),
                (StdItem::AsyncFn, "AsyncFn"),
                (StdItem::AsyncFn, "AsyncFn"),
            ],
        )
    }

    #[test]
    fn reference_receiver_infers_callable_bound_outputs() {
        let prefix = r#"
struct S { x: int32 }
extend &S {
    func syncRef[R, F: Fn[(&int32,), R]](_ f: F) -> R { f(&self.x) }
    func asyncRef[R, F: Fn[(&int32,), R]](_ f: F) async -> R { f(&self.x) }
    func asyncCallback[R, F: AsyncFn[(&int32,), R]](_ f: F) async -> R { await f(&self.x) }
}
func inc(_ value: &int32) -> int32 { *value + 1 }
func incAsync(_ value: &int32) async -> int32 { *value + 1 }
func identity[T](_ value: &T) -> T { *value }
"#;
        let mut failures = Vec::new();
        for (name, code) in [
            (
                "param",
                "func run(_ p: &S) -> int32 { p.syncRef((v: &int32) => *v + 1) }",
            ),
            (
                "auto",
                "func run() { var s = S { x: 1 }; a := s.syncRef((v: &int32) => *v + 1) }",
            ),
            (
                "alias closure",
                "func run() { var s = S { x: 1 }; p := &s; a := p.syncRef((v: &int32) => *v + 1) }",
            ),
            (
                "explicit ref",
                "func run() { var s = S { x: 1 }; a := (&s).syncRef((v: &int32) => *v + 1) }",
            ),
            (
                "explicit argument",
                "func run() { var s = S { x: 1 }; p := &s; a := p.syncRef[int32]((v: &int32) => *v + 1) }",
            ),
            (
                "async",
                "func run(_ p: &S) async { a := await p.asyncRef((v: &int32) => *v + 1) }",
            ),
            (
                "named alias",
                "func run() { var s = S { x: 1 }; p := &s; a := p.syncRef(inc) }",
            ),
            (
                "named auto",
                "func run() { var s = S { x: 1 }; a := s.syncRef(inc) }",
            ),
            (
                "named parameter",
                "func run(_ p: &S) { a := p.syncRef(inc) }",
            ),
            (
                "named async method",
                "func run(_ p: &S) async { a := await p.asyncRef(inc) }",
            ),
            (
                "named async callback",
                "func run(_ p: &S) async { a := await p.asyncCallback(incAsync) }",
            ),
            (
                "generic named callback",
                "func run(_ p: &S) { a := p.syncRef(identity) }",
            ),
            (
                "function pointer variable",
                "func run(_ p: &S) { f := inc; a := p.syncRef(f) }",
            ),
        ] {
            let errors = diagnostics_with_mir(&format!("{prefix}\n{code}"), true);
            if !errors.is_empty() {
                failures.push((name, errors));
            }
        }
        assert!(failures.is_empty(), "{failures:#?}");
    }

    #[test]
    fn calls_borrowed_generic_callbacks_and_returned_callback_borrows() {
        let errors = diagnostics(
            "func read[F: Fn[(), int32]](_ f: &F) -> int32 { f() }\nfunc change[F: Fn[(), int32]](_ f: &F) -> int32 { f() }\nfunc borrowed[F: Fn[(), int32]](_ f: &F) -> &F { f }\nfunc nested[F: Fn[(), int32]](_ f: &F) -> int32 { borrowed(f)() }\nfunc asyncBorrowed[F: AsyncFn[(), int32]](_ f: &F) -> &F { f }\nfunc asyncRead[F: AsyncFn[(), int32]](_ f: &F) async -> int32 { await f() }\nfunc asyncNested[F: AsyncFn[(), int32]](_ f: &F) async -> int32 { await asyncBorrowed(f)() }",
        );
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn method_value_arguments_do_not_select_an_incomplete_outer_overload() {
        let errors = diagnostics_with_mir(
            r#"
struct Counter { value: int32 }
extend Counter {
    func inspect() -> int32 { self.value }
}
func choose[F: Fn[(), int32]](_ f: F, _ flag: int32) -> int32 { f() }
func choose[F: Fn[(), int32]](_ f: F, _ flag: bool) -> int32 { f() }
func run() {
    counter := Counter { value: 7 }
    value := choose(counter.inspect, 1_i32)
}
"#,
            true,
        );
        assert!(errors.is_empty(), "{errors:#?}");
    }

    #[test]
    fn regular_block_tail_boxes_a_concrete_closure() {
        let errors = diagnostics_with_mir(
            "func make() -> any Fn[(), int32] { var value: int32 = 7; callback := () => value; callback }",
            true,
        );
        assert!(errors.is_empty(), "{errors:#?}");
    }

    #[test]
    fn generic_callable_captures_preserve_shared_and_mutable_capabilities() {
        let errors = diagnostics_with_mir(
            "func twice[F: Fn[(), int32]](_ f: F) -> int32 { f() + f() }\nfunc repeat[F: Fn[(), int32]](_ f: &F) -> int32 { f() + f() }\nfunc wrap[F: Fn[(), int32]](_ f: F) -> int32 { outer := () => f(); twice(outer) }\nfunc wrapMut[F: Fn[(), int32]](_ f: F) -> int32 { var f = f; var outer = () => f(); repeat(&outer) }",
            true,
        );
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn borrowed_async_calls_still_require_immediate_await_after_inference() {
        for body in [
            "func bad[F: AsyncFn[(), int32]](_ f: &F) { f() }",
            "func borrow[F: AsyncFn[(), int32]](_ f: &F) -> &F { f }\nfunc bad[F: AsyncFn[(), int32]](_ f: &F) { borrow(f)() }",
        ] {
            let errors = diagnostics(body);
            assert!(
                errors.iter().any(|d| d
                    .message
                    .contains("async calls require an enclosing `await` expression")),
                "{errors:?}"
            );
        }
    }
}

#[cfg(test)]
mod function_callable_tests {
    #[test]
    fn named_functions_satisfy_generic_and_erased_fn() {
        let source = r#"
interface Tuple {}
interface Fn[Args: Tuple, Output] {
    func call(args: Args) -> Output
}
func inc(_ value: &int32) -> int32 { *value + 1 }
func apply[R, F: Fn(&int32) -> R](_ f: F) -> R { var x: int32 = 1; f(&x) }
func erased(_ f: any Fn(&int32) -> int32) -> int32 { var x: int32 = 1; f(&x) }
func main() { var a: int32 = apply(inc); var b: int32 = erased(inc) }
"#;
        let diagnostics = crate::test_support::analyze_language_item_script(
            source,
            false,
            &[
                (crate::hir::StdItem::Tuple, "Tuple"),
                (crate::hir::StdItem::Fn, "Fn"),
            ],
        );
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
    }
}

#[cfg(test)]
mod function_pointer_safety_tests {
    #[test]
    fn inferred_function_pointer_preserves_unsafe_call_requirement() {
        let errors = crate::test_support::analyze_script_diagnostics(
            "unsafe func secret() -> int32 { 1 }\nfunc main() { f := secret; f() }",
        );
        assert!(
            errors.iter().any(|d| d.message.contains("unsafe")),
            "{errors:?}"
        );
    }
    #[test]
    fn async_pointer_cannot_coerce_to_sync_pointer() {
        let errors = crate::test_support::analyze_script_diagnostics(
            "func later(_ x: int32) async -> int32 { x }\nfunc main() { var f: (int32) -> int32 = later }",
        );
        assert!(!errors.is_empty());
    }
    #[test]
    fn unsafe_pointer_does_not_implement_safe_fn() {
        let source = r#"
interface Tuple {}
interface Fn[Args: Tuple, Output] {
    func call(args: Args) -> Output
}
unsafe func secret() -> int32 { 1 }
func apply[F: Fn() -> int32](_ f: F) -> int32 { f() }
func main() { var x = apply(secret) }
"#;
        let errors = crate::test_support::analyze_language_item_script(
            source,
            false,
            &[
                (crate::hir::StdItem::Tuple, "Tuple"),
                (crate::hir::StdItem::Fn, "Fn"),
            ],
        );
        assert!(
            errors
                .iter()
                .any(|d| d.message.contains("does not conform")
                    || d.message.contains("unsafe function")),
            "{errors:?}"
        );
    }
}
