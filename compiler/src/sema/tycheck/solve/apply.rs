use crate::{
    sema::{
        error::{ApplyValidationError, TypeError},
        models::{LabeledFunctionParameter, LabeledFunctionSignature, Ty, TyKind, TyList},
        tycheck::{
            solve::{
                ApplyArgument, ApplyGoalData, ConstraintSolver, Goal, Obligation, SolverResult,
            },
            utils::{
                arguments::validate_arity,
                callable::select_existential_callable,
            },
        },
    },
    span::{Span, Spanned},
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
                        is_lazy: false,
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
        let trailing_closure = data
            .arguments
            .last()
            .is_some_and(|arg| self.gcx().is_trailing_closure_argument(arg.id));
        let result = crate::sema::tycheck::utils::arguments::match_arguments_to_parameters_with_trailing(
            &signature.inputs,
            signature.is_variadic,
            data.arguments.iter().map(|arg| (arg.label, arg.span)),
            data.skip_labels,
            trailing_closure,
        );
        let positions = match result {
            Ok(v) => v,
            Err(e) => {
                return SolverResult::Error(vec![Spanned::new(TypeError::Apply(e.value), e.span)]);
            }
        };

        let mut lazy_targets = Vec::new();
        let result = produce_application_subobligations(
            self.gcx(),
            positions,
            signature,
            &inputs,
            &data.arguments,
            data.call_span,
            &self.deferred_return_scopes,
            &mut lazy_targets,
        );
        let mut obligations = match result {
            Ok(v) => v,
            Err(e) => {
                return SolverResult::Error(vec![Spanned::new(TypeError::Apply(e.value), e.span)]);
            }
        };
        for (node_id, param_ty) in lazy_targets {
            self.record_lazy_argument_target(node_id, param_ty);
        }

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

    pub(super) fn solve_validate_propagation(
        &mut self,
        location: Span,
        node_id: crate::hir::NodeID,
        err_ty: Option<Ty<'ctx>>,
        return_ty: Ty<'ctx>,
    ) -> SolverResult<'ctx> {
        let gcx = self.gcx();
        let return_ty = self.structurally_resolve(return_ty);
        if return_ty.is_infer() {
            return SolverResult::Deferred;
        }
        if return_ty.is_error() {
            return SolverResult::Solved(vec![]);
        }

        let Some(operand_err) = err_ty else {
            let opt_id = gcx.std_item_def(crate::hir::StdItem::Optional);
            let is_optional = matches!(
                return_ty.kind(),
                TyKind::Adt(def, _) if Some(def.id) == opt_id
            );
            return if is_optional {
                SolverResult::Solved(vec![])
            } else {
                SolverResult::Error(vec![Spanned::new(
                    TypeError::OptionalPropagationReturnType { found: return_ty },
                    location,
                )])
            };
        };

        let result_id = gcx.std_item_def(crate::hir::StdItem::Result);
        let return_err = match return_ty.kind() {
            TyKind::Adt(def, args) if Some(def.id) == result_id => args.get(1).and_then(|a| a.ty()),
            _ => None,
        };
        let Some(return_err) = return_err else {
            return SolverResult::Error(vec![Spanned::new(
                TypeError::ResultPropagationReturnType { found: return_ty },
                location,
            )]);
        };

        let resolved_return_err = self.structurally_resolve(return_err);
        let resolved_operand_err = self.structurally_resolve(operand_err);
        if resolved_return_err.is_error() || resolved_operand_err.is_error() {
            return SolverResult::Solved(vec![]);
        }
        if resolved_return_err.is_infer() || resolved_operand_err.is_infer() {
            return SolverResult::Solved(vec![Obligation {
                location,
                goal: Goal::Equal(resolved_return_err, resolved_operand_err),
            }]);
        }
        if resolved_return_err == resolved_operand_err {
            return SolverResult::Solved(vec![]);
        }

        if let TyKind::BoxedExistential { interfaces } = resolved_return_err.kind()
            && !matches!(
                resolved_operand_err.kind(),
                TyKind::BoxedExistential { .. }
            )
        {
            let obligations = interfaces
                .iter()
                .map(|interface| {
                    let interface = crate::sema::impl_engine::ref_ops::interface_ref_with_self(
                        gcx,
                        resolved_operand_err,
                        *interface,
                    );
                    Obligation {
                        location,
                        goal: Goal::Conforms {
                            ty: resolved_operand_err,
                            interface,
                        },
                    }
                })
                .collect();
            self.result_propagation_conversions.insert(
                node_id,
                crate::sema::tycheck::results::ResultPropagationConversion {
                    kind: crate::sema::tycheck::results::ResultPropagationConversionKind::BoxExistential {
                        interfaces,
                    },
                    target_ty: resolved_return_err,
                },
            );
            return SolverResult::Solved(obligations);
        }

        let Some(from_id) = gcx.std_item_def(crate::hir::StdItem::From) else {
            return SolverResult::Error(vec![Spanned::new(
                TypeError::ResultPropagationReturnType { found: return_ty },
                location,
            )]);
        };
        let Some(from_method_id) = gcx
            .get_interface_requirements(from_id)
            .and_then(|requirements| {
                requirements.methods.iter().find_map(|method| {
                    (gcx.symbol_text(method.name) == "from" && !method.has_self)
                        .then_some(method.id)
                })
            })
        else {
            return SolverResult::Error(vec![Spanned::new(
                TypeError::ResultPropagationReturnType { found: return_ty },
                location,
            )]);
        };

        let generic_args = gcx.store.interners.intern_generic_args(vec![
            crate::sema::models::GenericArgument::Type(resolved_return_err),
            crate::sema::models::GenericArgument::Type(resolved_operand_err),
        ]);
        let interface = crate::sema::models::InterfaceReference {
            id: from_id,
            arguments: generic_args,
            bindings: &[],
        };
        self.result_propagation_conversions.insert(
            node_id,
            crate::sema::tycheck::results::ResultPropagationConversion {
                kind: crate::sema::tycheck::results::ResultPropagationConversionKind::From {
                    method_id: from_method_id,
                    generic_args,
                },
                target_ty: resolved_return_err,
            },
        );
        SolverResult::Solved(vec![Obligation {
            location,
            goal: Goal::Conforms {
                ty: resolved_return_err,
                interface,
            },
        }])
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
    gcx: crate::compile::context::Gcx<'c>,
    positions: Vec<Vec<usize>>,
    signature: &LabeledFunctionSignature<'c>,
    inputs: &[Ty<'c>],
    arguments: &[ApplyArgument<'c>],
    call_span: Span,
    deferred_return_scopes: &[super::DeferredReturnScope<'c>],
    lazy_targets: &mut Vec<(crate::hir::NodeID, Ty<'c>)>,
) -> Result<Vec<Obligation<'c>>, Spanned<ApplyValidationError>> {
    let mut obligations = vec![];
    for (param_idx, arg_indices) in positions.iter().enumerate() {
        let param_defaults = signature.inputs[param_idx].default_provider.is_some();
        let is_lazy = signature.inputs[param_idx].is_lazy;
        let param_ty = inputs[param_idx];

        if !arg_indices.is_empty() {
            // Determine expected type for the arguments
            // If this is the variadic parameter, we need to extract T from Span[T]
            let base_expected_ty = if signature.is_variadic && param_idx == signature.inputs.len() - 1 {
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
                if argument.is_spread
                    && (!signature.is_variadic || param_idx + 1 != signature.inputs.len())
                {
                    return Err(Spanned::new(
                        ApplyValidationError::SpreadOutsideVariadic,
                        argument.span,
                    ));
                }
                let (expected_ty, scope_return_ty) = if is_lazy && !argument.is_lazy_wrapped {
                    if argument.contains_await {
                        return Err(Spanned::new(
                            ApplyValidationError::LazyArgumentContainsAwait,
                            argument.span,
                        ));
                    }
                    if let Some(result_ty) =
                        crate::sema::models::lazy_parameter_result_ty(gcx, param_ty)
                    {
                        lazy_targets.push((argument.id, param_ty));
                        (result_ty, Some(result_ty))
                    } else {
                        (base_expected_ty, None)
                    }
                } else {
                    let enclosing = (!is_lazy)
                        .then_some(argument.deferred_return_scope)
                        .flatten()
                        .and_then(|id| deferred_return_scopes.get(id as usize))
                        .and_then(|scope| scope.enclosing_return);
                    (base_expected_ty, enclosing)
                };
                if let Some(scope_id) = argument.deferred_return_scope
                    && let Some(scope) = deferred_return_scopes.get(scope_id as usize)
                    && let Some(target_return_ty) = scope_return_ty
                {
                    if let Some(return_var) = scope.return_var {
                        obligations.push(Obligation {
                            location: argument.span,
                            goal: Goal::Equal(return_var, target_return_ty),
                        });
                    }
                    for site in &scope.returns {
                        let goal = if is_lazy {
                            site.coerce_to(gcx, target_return_ty)
                        } else {
                            Goal::ValidateReturn {
                                site: *site,
                                target: target_return_ty,
                            }
                        };
                        obligations.push(Obligation {
                            location: site.span,
                            goal,
                        });
                    }
                    for site in &scope.propagations {
                        obligations.push(Obligation {
                            location: site.span,
                            goal: Goal::ValidatePropagation {
                                node_id: site.node_id,
                                err_ty: site.err_ty,
                                return_ty: target_return_ty,
                            },
                        });
                    }
                }
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
                return Err(Spanned::new(err, call_span));
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

    fn diagnostics(body: &str) -> Vec<crate::diagnostics::Diagnostic> {
        diagnostics_with_mir(body, false)
    }

    fn diagnostics_with_mir(body: &str, build_mir: bool) -> Vec<crate::diagnostics::Diagnostic> {
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

#[cfg(test)]
mod lazy_overload_tests {
    use crate::{hir::StdItem, test_support::analyze_language_item_script};

    fn diagnostics_with_mir(body: &str, build_mir: bool) -> Vec<crate::diagnostics::Diagnostic> {
        let source = format!(
            r#"
interface Tuple {{}}
interface Fn[Args: Tuple, Output] {{
    func call(args: Args) -> Output
}}
interface AsyncFn[Args: Tuple, Output] {{
    func call(args: Args) async -> Output
}}
{body}
"#
        );
        analyze_language_item_script(
            &source,
            build_mir,
            &[
                (StdItem::Tuple, "Tuple"),
                (StdItem::Fn, "Fn"),
                (StdItem::AsyncFn, "AsyncFn"),
            ],
        )
    }

    #[test]
    fn free_and_method_overloads_select_by_result_type_in_either_order() {
        let errors = diagnostics_with_mir(
            r#"
struct Counter { n: int32 }
extend &Counter {
    func step() -> int32 { self.n += 1; self.n }
}
struct Forward {}
extend Forward {
    func pick(_ value: @lazy int32) -> int32 { 1 }
    func pick(_ value: bool) -> int32 { if value { 2 } else { 0 } }
}
struct Backward {}
extend Backward {
    func pick(_ value: bool) -> int32 { if value { 2 } else { 0 } }
    func pick(_ value: @lazy int32) -> int32 { 1 }
}
interface EagerBool {
    func choose(_ value: bool) -> int32
}
struct Mixed {}
extend Mixed {
    func choose(_ value: @lazy int32) -> int32 { value() }
}
conform Mixed to EagerBool {
    func choose(_ value: bool) -> int32 { if value { 2 } else { 0 } }
}
func select(_ value: @lazy int32) -> int32 { value() + value() }
func select(_ value: bool) -> int32 { if value { 2 } else { 0 } }
func selectRev(_ value: bool) -> int32 { if value { 2 } else { 0 } }
func selectRev(_ value: @lazy int32) -> int32 { value() + value() }
func main() {
    var counter = Counter { n: 0 }
    var borrowed = &counter
    a := select(borrowed.step())
    b := select(borrowed.step() == 1)
    c := selectRev(counter.step())
    d := selectRev(false)
    fwd := Forward {}
    bwd := Backward {}
    e := fwd.pick(borrowed.step())
    f := fwd.pick(true)
    g := bwd.pick(borrowed.step())
    h := bwd.pick(false)
    mixed := Mixed {}
    i := mixed.choose(borrowed.step())
    j := mixed.choose(true)
    nested := select(selectRev(borrowed.step()))
    wrapped := () => select(borrowed.step())
    k := wrapped()
}
"#,
            true,
        );
        assert!(errors.is_empty(), "{errors:#?}");
    }

    #[test]
    fn lazy_and_eager_overloads_with_same_result_type_are_ambiguous() {
        for body in [
            r#"
func dup(_ value: @lazy int32) -> int32 { value() }
func dup(_ value: int32) -> int32 { value }
func main() { x := dup(1_i32) }
"#,
            r#"
struct S {}
extend S {
    func dup(_ value: @lazy int32) -> int32 { value() }
    func dup(_ value: int32) -> int32 { value }
}
func main() { s := S {}; x := s.dup(1_i32) }
"#,
        ] {
            let errors = diagnostics_with_mir(body, false);
            assert!(
                errors.iter().any(|d| d.message.contains("ambiguous overload")),
                "{body}\n{errors:#?}"
            );
        }
    }

    #[test]
    fn unresolved_lazy_overload_reports_no_match() {
        let errors = diagnostics_with_mir(
            r#"
func select(_ value: @lazy int32) -> int32 { value() }
func select(_ value: bool) -> int32 { if value { 1 } else { 0 } }
func main() { x := select("nope") }
"#,
            false,
        );
        assert!(
            errors
                .iter()
                .any(|d| d.message.contains("no overload matches this call")),
            "{errors:#?}"
        );
    }

    #[test]
    fn lazy_overload_rejects_await_and_unawaited_async_calls() {
        let with_await = diagnostics_with_mir(
            r#"
func fetch() async -> int32 { 7 }
func select(_ value: @lazy int32) -> int32 { value() }
func select(_ value: bool) -> int32 { 0 }
func run() async { x := select(await fetch()) }
func main() {}
"#,
            false,
        );
        assert!(!with_await.is_empty(), "expected error for await in lazy argument");

        let outer_await = diagnostics_with_mir(
            r#"
func fetch() async -> int32 { 7 }
func select(_ value: @lazy int32) -> int32 { value() }
func select(_ value: bool) -> int32 { 0 }
func run() async { x := await select(fetch()) }
func main() {}
"#,
            false,
        );
        assert!(
            outer_await.iter().any(|d| d
                .message
                .contains("async calls require an enclosing `await` expression")),
            "{outer_await:#?}"
        );
    }

    #[test]
    fn lazy_method_and_overload_preserve_closure_return_scope() {
        let errors = diagnostics_with_mir(
            r#"
struct Gate {}
extend Gate {
    func pick(_ value: @lazy int32) -> int32 { value() }
}
func choose(_ value: @lazy int32) -> int32 { value() }
func choose(_ value: bool) -> int32 { if value { 2 } else { 0 } }
func fromMethod(_ gate: Gate, _ flag: bool) -> bool {
    n := gate.pick(if flag { return 41_i32 } else { 7_i32 })
    n == 41
}
func fromOverloadLazy(_ flag: bool) -> bool {
    n := choose(if flag { return 41_i32 } else { 7_i32 })
    n == 41
}
func fromOverloadReturnOnly() -> bool {
    n := choose({ return 41_i32 })
    n == 41
}
func fromOverloadEager(_ flag: bool) -> bool {
    n := choose(if flag { return true } else { false })
    n == 0
}
func main() {
    a := fromMethod(Gate {}, true)
    b := fromOverloadLazy(true)
    c := fromOverloadReturnOnly()
    d := fromOverloadEager(true)
}
"#,
            true,
        );
        assert!(errors.is_empty(), "{errors:#?}");

        let mismatched = diagnostics_with_mir(
            r#"
func choose(_ value: @lazy int32) -> int32 { value() }
func choose(_ value: bool) -> int32 { 0 }
func bad(_ flag: bool) -> int64 {
    n := choose(if flag { return false } else { 7_i32 })
    0
}
func main() {}
"#,
            false,
        );
        assert!(!mismatched.is_empty(), "expected return type mismatch error");
    }

    #[test]
    fn lazy_subscript_materializes_closure_without_eager_evaluation() {
        let errors = diagnostics_with_mir(
            r#"
struct Counter { n: int32 }
extend &Counter {
    func step() -> int32 { self.n += 1; self.n }
}
struct Gate {}
extend &Gate {
    subscript(index: @lazy int32) -> int32 {
        get { 42 }
        set(value) { }
    }
    subscript(flag: bool) -> int32 {
        get { if flag { 1 } else { 0 } }
    }
}
func main() {
    var counter = Counter { n: 0 }
    var borrowed = &counter
    var gate = Gate {}
    a := gate[borrowed.step()]
    b := gate[borrowed.step() == 1]
    gate[borrowed.step()] = 9
}
"#,
            true,
        );
        assert!(errors.is_empty(), "{errors:#?}");
    }

    #[test]
    fn lazy_argument_preserves_propagation_and_optional_return_coercion() {
        let items = [
            (StdItem::Tuple, "Tuple"),
            (StdItem::Fn, "Fn"),
            (StdItem::AsyncFn, "AsyncFn"),
            (StdItem::Optional, "Optional"),
            (StdItem::Result, "Result"),
        ];
        let optional_return_source = r#"
interface Tuple {}
interface Fn[Args: Tuple, Output] {
    func call(args: Args) -> Output
}
interface AsyncFn[Args: Tuple, Output] {
    func call(args: Args) async -> Output
}
enum Optional[T] {
    case some(T)
    case none
}
enum Result[T, E] {
    case ok(T)
    case err(E)
}
struct Gate {}
extend Gate {
    func takeOpt(_ v: @lazy Optional[int32]) -> Optional[int32] { v() }
}
func pickOpt(_ v: @lazy Optional[int32]) -> Optional[int32] { v() }
func pickOpt(_ v: int64) -> Optional[int32] { .none }
func pickBool(_ v: @lazy int32) -> int32 { v() }
func pickBool(_ v: bool) -> int32 { if v { 1 } else { 0 } }

func methodOptionalReturn(_ flag: bool) -> bool {
    gate := Gate {}
    a := gate.takeOpt(if flag { return 41_i32 } else { Optional[int32]::some(7_i32) })
    b := gate.takeOpt(if flag { return .some(41_i32) } else { Optional[int32]::some(7_i32) })
    true
}
func overloadOptionalReturn(_ flag: bool) -> bool {
    a := pickOpt(if flag { return 41_i32 } else { Optional[int32]::some(7_i32) })
    b := pickOpt(if flag { return .some(41_i32) } else { Optional[int32]::some(7_i32) })
    c := pickBool({ inner := () => { return true }; 7_i32 })
    true
}
func main() {
    a := methodOptionalReturn(true)
    b := overloadOptionalReturn(true)
}
"#;
        let errors = analyze_language_item_script(optional_return_source, true, &items);
        assert!(errors.is_empty(), "{errors:#?}");

        let propagate_source = r#"
interface Tuple {}
interface Fn[Args: Tuple, Output] {
    func call(args: Args) -> Output
}
interface AsyncFn[Args: Tuple, Output] {
    func call(args: Args) async -> Output
}
enum Optional[T] {
    case some(T)
    case none
}
enum Result[T, E] {
    case ok(T)
    case err(E)
}
struct Gate {}
extend Gate {
    func takeRes(_ v: @lazy Result[int32, bool]) -> Result[int32, bool] { v() }
    func takeOpt(_ v: @lazy Optional[int32]) -> Optional[int32] { v() }
}
func pickRes(_ v: @lazy Result[int32, bool]) -> Result[int32, bool] { v() }
func pickRes(_ v: int64) -> Result[int32, bool] { .ok(0) }
func pickOpt(_ v: @lazy Optional[int32]) -> Optional[int32] { v() }
func pickOpt(_ v: int64) -> Optional[int32] { .none }
func pickBool(_ v: @lazy int32) -> int32 { v() }
func pickBool(_ v: bool) -> int32 { if v { 1 } else { 0 } }
func failRes() -> Result[int32, bool] { .err(true) }
func failBoolRes() -> Result[bool, bool] { .err(true) }
func failOpt() -> Optional[int32] { .none }

func methodPropagate() -> bool {
    gate := Gate {}
    r := gate.takeRes(Result[int32, bool]::ok(failRes()!))
    o := gate.takeOpt(Optional[int32]::some(failOpt()!))
    true
}
func overloadPropagate() -> bool {
    r := pickRes(Result[int32, bool]::ok(failRes()!))
    o := pickOpt(Optional[int32]::some(failOpt()!))
    true
}
func overloadEagerPropagate() -> Result[int32, bool] {
    .ok(pickBool(failBoolRes()!))
}
func main() {}
"#;
        let errors = analyze_language_item_script(propagate_source, false, &items);
        assert!(errors.is_empty(), "{errors:#?}");
    }
}
