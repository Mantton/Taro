use super::*;
use crate::sema::models::{CaptureKind, ClosureKind};

impl<'ctx> Checker<'ctx> {
    pub(super) fn synth_closure_expression(
        &self,
        expression: &hir::Expression,
        closure: &hir::ClosureExpr,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let gcx = self.gcx();
        let effective_async = closure.is_async
            || closure_body_has_await(&closure.body)
            || self.is_forced_async_closure_expr(expression.id)
            || expectation.is_some_and(|ty| {
                let resolved = cs.infer_cx.resolve_vars_if_possible(ty);
                matches!(
                    resolved.kind(),
                    TyKind::FnPointer {
                        effects: crate::sema::models::FunctionPointerEffects {
                            kind: ClosureKind::AsyncFn,
                            ..
                        },
                        ..
                    }
                ) || crate::sema::tycheck::utils::callable::existential_callable(gcx, resolved)
                    .is_some_and(|callable| callable.is_async())
            });

        // GC closures capture by reference even when they escape: escape
        // analysis heapifies the captured variables instead (G17).
        let owns_captures = closure.snapshot_captures;

        // Collect closure parameter IDs (these are NOT captures)
        let param_ids: rustc_hash::FxHashSet<NodeID> =
            closure.params.iter().map(|p| p.id).collect();

        // Extract expected input/output types from the expectation (for type inference)
        let expected_inputs =
            expectation.and_then(|ty| self.extract_closure_expected_inputs(ty, cs));
        let expected_output =
            expectation.and_then(|ty| self.extract_closure_expected_output(ty, cs));

        // Collect parameter types
        let mut param_tys = Vec::with_capacity(closure.params.len());

        for (index, param) in closure.params.iter().enumerate() {
            // Check if there's an explicit type annotation (not an inferred placeholder)
            let has_explicit_type = param
                .ty
                .as_ref()
                .map_or(false, |ty| !matches!(ty.kind, hir::TypeKind::Infer));

            // Use explicit type annotation, or infer from expectation, or create infer var
            let param_ty = if has_explicit_type {
                // Explicit type annotation - lower it
                let explicit_ty = self.lower_type(param.ty.as_ref().unwrap());
                if let Some(ref inputs) = expected_inputs {
                    if let Some(&expected_ty) = inputs.get(index) {
                        cs.equal(expected_ty, explicit_ty, param.span);
                    }
                }
                explicit_ty
            } else if let Some(ref inputs) = expected_inputs {
                // Infer from expected type (e.g., from Fn bound)
                if let Some(&expected_ty) = inputs.get(index) {
                    expected_ty
                } else {
                    // More params than expected - create infer var
                    cs.infer_cx.next_ty_var(param.span)
                }
            } else {
                // No expectation available - create inference variable
                cs.infer_cx.next_ty_var(param.span)
            };

            param_tys.push(param_ty);

            // Register the parameter as a local binding
            self.set_local(
                param.id,
                super::super::checker::LocalBinding {
                    mutable: false,
                    ty: param_ty,
                },
            );
        }

        let expected_return = if let Some(ret_ty) = &closure.return_ty {
            // Like explicit parameters, an explicit result also feeds the
            // contextual signature, binding generic outputs such as `U`.
            let explicit_ty = self.lower_type(ret_ty);
            if let Some(expected_return) = expected_output {
                cs.equal(expected_return, explicit_ty, ret_ty.span);
            }
            explicit_ty
        } else if let Some(expected_return) = expected_output {
            expected_return
        } else {
            cs.infer_cx.next_ty_var(closure.body.span)
        };

        // Type check the closure body under the closure's own return context so
        // explicit `return expr` participates in the same output inference as a
        // tail expression.
        let (return_ty, body_ty) = self.without_deferred_return_scope(|| {
            self.with_return_ty(Some(expected_return), || {
            let prev_async_depth = self.async_depth.get();
            let prev_closure_depth = self.closure_depth.get();
            self.closure_depth.set(prev_closure_depth + 1);
            let prev_await_scope = self.await_scope.replace(None);
            let prev_loop_depth = self.loop_depth.replace(0);
            let prev_loop_stack = std::mem::take(&mut *self.loop_stack.borrow_mut());
            let prev_generator_element_ty = self.generator_element_ty.replace(None);
            if effective_async {
                self.async_depth.set(prev_async_depth + 1);
            }

            let synth_body = |cs: &mut Cs<'ctx>| match &closure.body.kind {
                hir::ExpressionKind::Block(block) | hir::ExpressionKind::UnsafeBlock(block) => {
                    for statement in &block.statements {
                        self.check_statement(statement, Some(cs));
                    }

                    if let Some(tail) = block.tail.as_deref() {
                        if matches!(tail.kind, hir::ExpressionKind::Return { .. }) {
                            self.synth_with_expectation(tail, None, cs)
                        } else {
                            let actual_return =
                                self.synth_with_expectation(tail, Some(expected_return), cs);
                            let resolved_actual =
                                cs.infer_cx.resolve_vars_if_possible(actual_return);
                            let resolved_expected =
                                cs.infer_cx.resolve_vars_if_possible(expected_return);
                            if matches!(resolved_actual.kind(), TyKind::Never)
                                && resolved_expected.is_infer()
                            {
                                cs.equal(expected_return, actual_return, tail.span);
                            } else {
                                cs.add_goal(
                                    Goal::Coerce {
                                        node_id: tail.id,
                                        from: actual_return,
                                        to: expected_return,
                                    },
                                    tail.span,
                                );
                            }
                            actual_return
                        }
                    } else if !closure_body_has_explicit_return(&closure.body) {
                        cs.equal(expected_return, self.gcx().types.void, closure.body.span);
                        self.gcx().types.void
                    } else {
                        self.gcx().types.void
                    }
                }
                hir::ExpressionKind::Return { .. } => {
                    self.synth_with_expectation(&closure.body, None, cs)
                }
                _ => {
                    let actual_return =
                        self.synth_with_expectation(&closure.body, Some(expected_return), cs);
                    let resolved_actual = cs.infer_cx.resolve_vars_if_possible(actual_return);
                    let resolved_expected = cs.infer_cx.resolve_vars_if_possible(expected_return);
                    if matches!(resolved_actual.kind(), TyKind::Never)
                        && resolved_expected.is_infer()
                    {
                        cs.equal(expected_return, actual_return, closure.body.span);
                    } else {
                        cs.add_goal(
                            Goal::Coerce {
                                node_id: closure.body.id,
                                from: actual_return,
                                to: expected_return,
                            },
                            closure.body.span,
                        );
                    }
                    actual_return
                }
            };
            let body_ty = if closure.implicit_await {
                self.with_implicit_await_scope(closure.body.id, closure.body.span, || synth_body(cs))
            } else {
                synth_body(cs)
            };

            if effective_async {
                self.async_depth.set(prev_async_depth);
            }
            self.closure_depth.set(prev_closure_depth);

            self.await_scope.set(prev_await_scope);
            self.loop_depth.set(prev_loop_depth);
            *self.loop_stack.borrow_mut() = prev_loop_stack;
            self.generator_element_ty.set(prev_generator_element_ty);
            (expected_return, body_ty)
            })
        });
        cs.record_expr_ty(closure.body.id, body_ty);

        // Learn the signature and capture paths that are already known.
        // Captured literals can still take their width from the enclosing
        // expression. Its final solve also finalizes the closure metadata.
        cs.without_fallbacks(|cs| cs.solve_intermediate());
        let return_ty = cs.infer_cx.resolve_vars_if_possible(return_ty);
        let param_tys: Vec<_> = param_tys
            .into_iter()
            .map(|ty| cs.infer_cx.resolve_vars_if_possible(ty))
            .collect();

        self.build_closure_metadata(
            closure,
            &param_ids,
            &param_tys,
            return_ty,
            effective_async,
            owns_captures,
            cs,
        )
    }

    fn build_closure_metadata(
        &self,
        closure: &hir::ClosureExpr,
        param_ids: &rustc_hash::FxHashSet<NodeID>,
        param_tys: &[Ty<'ctx>],
        return_ty: Ty<'ctx>,
        effective_async: bool,
        owns_captures: bool,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let gcx = self.gcx();

        // Perform capture analysis - collect free variables from the closure body
        let mut collector = CaptureCollector {
            param_ids,
            local_decls: rustc_hash::FxHashSet::default(),
            order: Vec::new(),
            info: rustc_hash::FxHashMap::default(),
            checker: self,
            cs,
        };
        collector.collect_expr(&closure.body);

        // Build capture list with types and capture kinds
        let mut captures = Vec::new();
        for (field_index, place) in collector.order.iter().enumerate() {
            if param_ids.contains(&place.root) {
                continue;
            }
            let info = collector
                .info
                .get(place)
                .expect("capture info should exist");
            // Get the type of the captured variable from local bindings
            let binding = self.get_local(place.root);
            let root_ty = cs.structurally_resolve(binding.ty);
            let projection = gcx.store.arenas.global.alloc_slice_copy(&info.projection);
            let ty = projection.last().map_or(root_ty, |field| field.ty);
            let capture_kind = if owns_captures {
                CaptureKind::ByCopy
            } else {
                CaptureKind::ByRef
            };

            captures.push(crate::sema::models::CapturedVar {
                source_id: place.root,
                root_ty,
                projection,
                name: info.name,
                ty,
                capture_kind,
                source_immutable: !binding.mutable,
                field_index: crate::thir::FieldIndex::from_raw(field_index as u32),
            });
        }

        let closure_kind = if effective_async {
            ClosureKind::AsyncFn
        } else {
            ClosureKind::Fn
        };

        if !captures.is_empty() {
            cs.capturing_closures.push(closure.def_id);
        }
        gcx.cache_closure_captures(
            closure.def_id,
            crate::sema::models::ClosureCaptures {
                captures,
                kind: closure_kind,
            },
        );

        // Create the closure type (with user-visible parameter types only)
        let inputs = gcx.store.interners.intern_ty_list(param_tys.to_vec());
        let captured_generics = GenericsBuilder::identity_for_item(gcx, self.current_def);

        // A closure has no generic parameters of its own, but its body and any
        // synthesized callable adapters inherit every generic parameter from
        // the enclosing definition. Record that parent relationship so those
        // adapters can be monomorphized with the closure's captured arguments.
        let owner_generics = gcx.generics_of(self.current_def);
        if !owner_generics.is_empty() {
            gcx.cache_generics(
                closure.def_id,
                crate::sema::models::Generics {
                    parameters: vec![],
                    has_self: owner_generics.has_self,
                    parent: Some(self.current_def),
                    parent_count: owner_generics.parent_count + owner_generics.total_count(),
                },
            );
        }

        // The generated closure body has the enclosing generic parameters and
        // must also retain their declaration bounds (not pending call goals).
        // Otherwise a shared capture of T: Copy is incorrectly moved from &T.
        gcx.update_constraints(
            closure.def_id,
            crate::sema::tycheck::constraints::canonical_constraints_of(gcx, self.current_def),
        );

        // Create the closure type first (we need it for the body function signature)
        let closure_ty = Ty::new(
            TyKind::Closure {
                closure_def_id: closure.def_id,
                kind: closure_kind,
                captured_generics,
                inputs,
                output: return_ty,
            },
            gcx,
        );
        if effective_async {
            gcx.cache_async_body_output(closure.def_id, return_ty);
        }

        let self_ty = closure_self_ty(gcx, closure_ty, closure_kind);

        let mut sig_inputs = vec![crate::sema::models::LabeledFunctionParameter {
            label: None,
            name: gcx.intern_symbol("self"),
            ty: self_ty,
            is_lazy: false,
            default_provider: None,
        }];

        // Add the explicit closure parameters after self
        sig_inputs.extend(
            closure
                .params
                .iter()
                .zip(param_tys.iter())
                .map(|(param, &ty)| {
                    let name = match &param.pattern.kind {
                        hir::PatternKind::Binding { name, .. } => name.symbol,
                        _ => gcx.intern_symbol("_"),
                    };
                    crate::sema::models::LabeledFunctionParameter {
                        label: None,
                        name,
                        ty,
                        is_lazy: false,
                        default_provider: None,
                    }
                }),
        );

        gcx.cache_signature(
            closure.def_id,
            crate::sema::models::LabeledFunctionSignature {
                inputs: sig_inputs,
                output: return_ty,
                is_variadic: false,
                abi: None,
            },
        );

        closure_ty
    }

    /// Materialize zero-argument closures for call arguments whose `@lazy`
    /// parameter was chosen by overload resolution. Checking candidates never
    /// creates closures or evaluates arguments; only the committed selection
    /// records targets here, and only those selected HIR subtrees are cloned.
    pub(super) fn finalize_lazy_arguments(
        &self,
        cs: &mut Cs<'ctx>,
        root_expr: Option<&hir::Expression>,
    ) {
        let targets = cs.take_lazy_argument_targets();
        if targets.is_empty() {
            return;
        }
        let wanted: rustc_hash::FxHashSet<NodeID> = targets.iter().map(|(id, _)| *id).collect();
        let mut expressions = rustc_hash::FxHashMap::default();
        if let Some(root) = root_expr {
            self.collect_expressions_by_id(root, &wanted, &mut expressions);
        }
        let gcx = self.gcx();
        let empty_params = rustc_hash::FxHashSet::default();
        for (body_id, param_ty) in targets {
            if self.results.borrow().lazy_arguments.contains_key(&body_id) {
                continue;
            }
            let Some(body) = expressions.remove(&body_id) else {
                debug_assert!(
                    false,
                    "missing HIR expression for selected lazy argument {body_id:?}"
                );
                continue;
            };
            let param_ty = cs.infer_cx.resolve_vars_or_error(param_ty);
            if param_ty.is_error() {
                continue;
            }
            let Some(result_ty) = crate::sema::models::lazy_parameter_result_ty(gcx, param_ty)
            else {
                continue;
            };
            if result_ty.is_error() {
                continue;
            }
            let TyKind::BoxedExistential { interfaces } = param_ty.kind() else {
                continue;
            };
            if let Some(span) = self.find_async_call_in_lazy_body(&body, cs) {
                gcx.dcx().emit_error(
                    "async calls require an enclosing `await` expression".into(),
                    Some(span),
                );
                continue;
            }
            let wrapper = hir::Expression::lazy_argument(
                self.method_value_node(),
                gcx.allocate_synthetic_id(self.current_def.package()),
                Box::new(body),
            );
            let hir::ExpressionKind::Closure(closure) = &wrapper.kind else {
                unreachable!("lazy argument wrapper must be a closure");
            };
            let closure_ty = self.build_closure_metadata(
                closure,
                &empty_params,
                &[],
                result_ty,
                false,
                false,
                cs,
            );
            cs.record_expr_ty(wrapper.id, closure_ty);
            cs.record_adjustments(
                wrapper.id,
                vec![Adjustment::BoxExistential {
                    from: closure_ty,
                    interfaces,
                }],
            );
            self.results
                .borrow_mut()
                .lazy_arguments
                .insert(body_id, wrapper);
        }
    }

    fn collect_expressions_by_id(
        &self,
        root: &hir::Expression,
        wanted: &rustc_hash::FxHashSet<NodeID>,
        found: &mut rustc_hash::FxHashMap<NodeID, hir::Expression>,
    ) {
        struct ExprFinder<'a, 'ctx> {
            checker: &'a Checker<'ctx>,
            wanted: &'a rustc_hash::FxHashSet<NodeID>,
            found: &'a mut rustc_hash::FxHashMap<NodeID, hir::Expression>,
        }
        impl hir::HirVisitor for ExprFinder<'_, '_> {
            fn visit_declaration(&mut self, _: &hir::Declaration) {}

            fn visit_expression(&mut self, node: &hir::Expression) {
                if self.found.len() == self.wanted.len() {
                    return;
                }
                if self.wanted.contains(&node.id) {
                    self.found.entry(node.id).or_insert_with(|| node.clone());
                }
                if matches!(node.kind, hir::ExpressionKind::MemberBrackets { .. })
                    && let Some(selected) = self
                        .checker
                        .results
                        .borrow()
                        .selected_brackets
                        .get(&node.id)
                        .cloned()
                {
                    self.visit_expression(&selected);
                }
                if matches!(node.kind, hir::ExpressionKind::Call { .. })
                    && let Some(selected) = self
                        .checker
                        .results
                        .borrow()
                        .elaborated_calls
                        .get(&node.id)
                        .cloned()
                {
                    self.visit_expression(&selected);
                }
                hir::walk_expression(self, node);
            }
        }
        let mut finder = ExprFinder {
            checker: self,
            wanted,
            found,
        };
        finder.visit_expression(root);
    }

    fn find_async_call_in_lazy_body(
        &self,
        expr: &hir::Expression,
        cs: &Cs<'ctx>,
    ) -> Option<Span> {
        struct AsyncCallFinder<'a, 'ctx> {
            checker: &'a Checker<'ctx>,
            cs: &'a Cs<'ctx>,
            found: Option<Span>,
        }
        impl hir::HirVisitor for AsyncCallFinder<'_, '_> {
            fn visit_expression(&mut self, node: &hir::Expression) {
                if self.found.is_some() {
                    return;
                }
                match &node.kind {
                    hir::ExpressionKind::Closure(_) => {}
                    hir::ExpressionKind::Call { .. } | hir::ExpressionKind::MethodCall { .. } => {
                        if self.checker.resolved_async_call_status(node.id, Some(self.cs))
                            == Some(true)
                        {
                            self.found = Some(node.span);
                            return;
                        }
                        hir::walk_expression(self, node);
                    }
                    _ => hir::walk_expression(self, node),
                }
            }
        }
        let mut finder = AsyncCallFinder {
            checker: self,
            cs,
            found: None,
        };
        finder.visit_expression(expr);
        finder.found
    }
    pub(super) fn extract_closure_expected_inputs(
        &self,
        expectation: Ty<'ctx>,
        cs: &mut Cs<'ctx>,
    ) -> Option<Vec<Ty<'ctx>>> {
        let expectation = cs.infer_cx.resolve_vars_if_possible(expectation);

        match expectation.kind() {
            // Direct closure type - use its inputs (this includes synthetic closures from Fn bounds)
            TyKind::Closure { inputs, .. } => Some(inputs.to_vec()),

            // Function pointer - use its inputs
            TyKind::FnPointer { inputs, .. } => Some(inputs.to_vec()),
            _ => {
                crate::sema::tycheck::utils::callable::existential_callable(self.gcx(), expectation)
                    .and_then(|callable| {
                        callable.interface.arguments.get(1).and_then(|arg| arg.ty())
                    })
                    .and_then(|args_ty| match args_ty.kind() {
                        TyKind::Tuple(inputs) => Some(inputs.to_vec()),
                        _ => None,
                    })
            }
        }
    }

    /// Extract expected output type for closure return type inference.
    /// Returns None if no expectation is available or it can't be extracted.
    pub(super) fn extract_closure_expected_output(
        &self,
        expectation: Ty<'ctx>,
        cs: &mut Cs<'ctx>,
    ) -> Option<Ty<'ctx>> {
        let expectation = cs.infer_cx.resolve_vars_if_possible(expectation);

        match expectation.kind() {
            TyKind::Closure { output, .. } => Some(output),
            TyKind::FnPointer { output, .. } => Some(output),
            _ => {
                crate::sema::tycheck::utils::callable::existential_callable(self.gcx(), expectation)
                    .and_then(|callable| callable.signature(self.gcx()))
                    .map(|(_, output)| output)
            }
        }
    }

    /// A nested closure can capture a literal before the enclosing match
    /// determines its width. Resolve the entire captured place in the system
    /// that created it, before MIR reads the environment and its field path.
    pub(super) fn finalize_closure_captures(&self, cs: &Cs<'ctx>) {
        let gcx = self.gcx();
        for &closure in &cs.capturing_closures {
            let mut captures = gcx.get_closure_captures(closure).expect("checked closure");
            for capture in &mut captures.captures {
                capture.root_ty = cs.infer_cx.resolve_vars_or_error(capture.root_ty);
                capture.ty = cs.infer_cx.resolve_vars_or_error(capture.ty);
                if capture
                    .projection
                    .iter()
                    .any(|field| field.ty.has_inference_variables())
                {
                    let mut path = capture.projection.to_vec();
                    for field in &mut path {
                        field.ty = cs.infer_cx.resolve_vars_or_error(field.ty);
                    }
                    capture.projection = gcx.store.arenas.global.alloc_slice_copy(&path);
                }
            }
            gcx.cache_closure_captures(closure, captures);
        }
    }

    /// Updates the global function signature for a closure with fully resolved types.
    ///
    /// This is critical because the initial signature created during closure synthesis may contain
    /// inference variables (e.g., `{var(N)}`). Codegen uses the global signature cache, so if we don't
    /// update it after type inference resolves these variables, `normalize_post_monomorphization` will panic.
    pub(super) fn update_closure_signature(
        &self,
        closure_def_id: DefinitionID,
        closure_ty: Ty<'ctx>,
    ) {
        use crate::sema::models::{LabeledFunctionParameter, LabeledFunctionSignature};

        let TyKind::Closure {
            kind,
            inputs,
            output,
            ..
        } = closure_ty.kind()
        else {
            return;
        };

        let gcx = self.gcx();
        let old_sig = gcx.get_signature(closure_def_id);

        let self_ty = closure_self_ty(gcx, closure_ty, kind);

        let mut new_inputs = Vec::with_capacity(old_sig.inputs.len());

        // Handle self (first arg)
        if !old_sig.inputs.is_empty() {
            let old_self = &old_sig.inputs[0];
            new_inputs.push(LabeledFunctionParameter {
                ty: self_ty,
                ..*old_self
            });
        }

        // Handle explicit args
        // inputs (from closure_ty) corresponds to old_sig.inputs[1..]
        for (i, param_ty) in inputs.iter().enumerate() {
            // +1 for self
            if i + 1 < old_sig.inputs.len() {
                let old_param = &old_sig.inputs[i + 1];
                new_inputs.push(LabeledFunctionParameter {
                    ty: *param_ty,
                    ..*old_param
                });
            }
        }

        let new_sig = LabeledFunctionSignature {
            inputs: new_inputs,
            output: output, // resolved output from closure_ty
            ..old_sig.clone()
        };

        if let Some(method) = self.results.borrow().bound_method_closure(closure_def_id) {
            // Synthetic declarations must track finalized closure types too;
            // get_signature consults this declaration before the ordinary cache.
            let signature = gcx.store.arenas.function_signatures.alloc(new_sig.clone());
            gcx.register_synthetic_definition(
                closure_def_id,
                crate::sema::models::SyntheticDefinition {
                    kind: crate::sema::models::SyntheticDefinitionKind::Ordinary,
                    name: gcx.intern_symbol("$boundMethod"),
                    generics: gcx.generics_of(closure_def_id),
                    signature,
                    span: method.closure.span,
                },
            );
            gcx.cache_type(closure_def_id, Ty::from_labeled_signature(gcx, signature));
        }
        gcx.cache_signature(closure_def_id, new_sig);
        // An async body's own output is cached apart from its signature at
        // synthesis, possibly still holding inference variables. MIR builds
        // the body's return slot from that cache, so it must be final too.
        if gcx.definition_is_async(closure_def_id) {
            gcx.cache_async_body_output(closure_def_id, output);
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct CapturePlace {
    root: NodeID,
    fields: Vec<crate::thir::FieldIndex>,
}

struct CaptureInfo<'ctx> {
    name: Symbol,
    projection: Vec<crate::sema::models::CaptureProjection<'ctx>>,
}

/// Only awaits executed by this closure affect its callable capability. A
/// nested closure's suspension does not make its enclosing closure async.
pub(super) fn closure_body_has_await(expr: &hir::Expression) -> bool {
    struct AwaitFinder {
        found: bool,
    }
    impl hir::HirVisitor for AwaitFinder {
        fn visit_expression(&mut self, node: &hir::Expression) {
            match &node.kind {
                hir::ExpressionKind::Await(_) | hir::ExpressionKind::Select(_) => self.found = true,
                hir::ExpressionKind::Closure(_) => {}
                _ => hir::walk_expression(self, node),
            }
        }
    }
    let mut finder = AwaitFinder { found: false };
    finder.visit_expression(expr);
    finder.found
}

fn closure_body_has_explicit_return(expr: &hir::Expression) -> bool {
    struct ReturnFinder {
        found: bool,
    }

    impl hir::HirVisitor for ReturnFinder {
        fn visit_expression(&mut self, node: &hir::Expression) {
            match &node.kind {
                hir::ExpressionKind::Return { .. } => {
                    self.found = true;
                }
                hir::ExpressionKind::Closure(_) => {}
                _ => hir::walk_expression(self, node),
            }
        }
    }

    let mut finder = ReturnFinder { found: false };
    finder.visit_expression(expr);
    finder.found
}

/// Collects free variable references from a closure body.
/// A "capture" is a local variable referenced in the closure body
/// that is not a closure parameter or locally declared.
struct CaptureCollector<'a, 'ctx> {
    /// IDs of closure parameters (these are NOT captures)
    param_ids: &'a rustc_hash::FxHashSet<NodeID>,
    /// IDs of variables declared inside the closure body (NOT captures)
    local_decls: rustc_hash::FxHashSet<NodeID>,
    /// Capture order (first-seen)
    order: Vec<CapturePlace>,
    /// Capture info keyed by NodeID
    info: rustc_hash::FxHashMap<CapturePlace, CaptureInfo<'ctx>>,
    /// Reference to the checker for accessing local bindings
    checker: &'a Checker<'ctx>,
    /// Field types can still be inferred by the enclosing expression.
    cs: &'a Cs<'ctx>,
}

impl<'a, 'ctx> CaptureCollector<'a, 'ctx> {
    fn record_capture(&mut self, id: NodeID, name: Symbol) {
        self.record_projected_capture(id, name, vec![]);
    }

    fn record_projected_capture(
        &mut self,
        root: NodeID,
        name: Symbol,
        projection: Vec<crate::sema::models::CaptureProjection<'ctx>>,
    ) {
        let place = CapturePlace {
            root,
            fields: projection.iter().map(|field| field.field).collect(),
        };
        if self
            .order
            .iter()
            .any(|existing| existing.root == root && place.fields.starts_with(&existing.fields))
        {
            return;
        }
        let mut position = self.order.len();
        let descendants = self
            .order
            .iter()
            .enumerate()
            .filter_map(|(index, existing)| {
                (existing.root == root && existing.fields.starts_with(&place.fields))
                    .then_some((index, existing.clone()))
            })
            .collect::<Vec<_>>();
        for (index, descendant) in descendants {
            position = position.min(index);
            self.info.remove(&descendant);
        }
        self.order
            .retain(|existing| self.info.contains_key(existing));
        self.order.insert(position, place.clone());
        self.info.insert(place, CaptureInfo { name, projection });
    }

    /// Only inline named fields participate in precision. Dereferencing a
    /// reference/raw pointer retains the existing token-capture rules instead.
    fn stored_projection(
        &self,
        expr: &hir::Expression,
    ) -> Option<(
        NodeID,
        Symbol,
        Vec<crate::sema::models::CaptureProjection<'ctx>>,
    )> {
        match &expr.kind {
            hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path)) => {
                let hir::Resolution::LocalVariable(root) = path.resolution else {
                    return None;
                };
                let name = path.segments.last()?.identifier.symbol;
                Some((root, name, vec![]))
            }
            hir::ExpressionKind::Member { target, .. }
            | hir::ExpressionKind::TupleAccess(target, _) => {
                let gcx = self.checker.gcx();
                let target_ty = self.cs.structurally_resolve(self.cs.expr_ty(target.id)?);
                // Object fields are behind identity, not inline capture
                // storage. Capture the handle (or an enclosing struct field
                // containing it), and access current object state at invocation.
                if gcx.is_class_type(target_ty) {
                    return None;
                }
                if !matches!(
                    target_ty.kind(),
                    TyKind::Tuple(_)
                        | TyKind::Adt(
                            crate::sema::models::AdtDef {
                                kind: crate::sema::models::AdtKind::Struct,
                                ..
                            },
                            _
                        )
                ) || self
                    .cs
                    .node_adjustments(target.id)
                    .iter()
                    .any(|adjustment| matches!(adjustment, Adjustment::Dereference))
                {
                    return None;
                }
                let field =
                    crate::thir::FieldIndex::from_usize(self.cs.fields.get(&expr.id)?.index);
                let (root, name, mut projection) = self.stored_projection(target)?;
                if let Some(class) = gcx.class_for_payload(target_ty) {
                    // Lifecycle self is private inline storage. Keep capture
                    // identity aligned with its physical base-prefix tree,
                    // rather than treating a flattened source index as bytes.
                    let mut owner = target_ty;
                    for index in gcx.class_field_payload_path(class, field.index())? {
                        let TyKind::Adt(def, args) = owner.kind() else {
                            return None;
                        };
                        let stored = gcx.get_struct_definition(def.id).fields[index as usize];
                        owner = crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args(
                            gcx, stored.ty, args,
                        );
                        projection.push(crate::sema::models::CaptureProjection {
                            field: crate::thir::FieldIndex::from_raw(index),
                            ty: owner,
                        });
                    }
                    return Some((root, name, projection));
                }
                let capture_ty = self.cs.structurally_resolve(self.cs.expr_ty(expr.id)?);
                projection.push(crate::sema::models::CaptureProjection {
                    field,
                    ty: capture_ty,
                });
                Some((root, name, projection))
            }
            _ => None,
        }
    }

    fn maybe_capture_projection(&mut self, expr: &hir::Expression) -> bool {
        let Some((root, name, projection)) = self.stored_projection(expr) else {
            return false;
        };
        if projection.is_empty()
            || self.param_ids.contains(&root)
            || self.local_decls.contains(&root)
            || self.checker.try_get_local(root).is_none()
        {
            return false;
        }
        self.record_projected_capture(root, name, projection);
        true
    }

    /// Captures share the enclosing variable, so only a direct write to the
    /// captured place counts as mutation.

    fn maybe_capture(&mut self, path: &hir::ResolvedPath) {
        let hir::ResolvedPath::Resolved(path) = path else {
            return;
        };
        let hir::Resolution::LocalVariable(id) = path.resolution else {
            return;
        };
        // Skip closure parameters
        if self.param_ids.contains(&id) {
            return;
        }
        // Skip variables declared inside this closure body
        if self.local_decls.contains(&id) {
            return;
        }
        let Some(_) = self.checker.try_get_local(id) else {
            return;
        };

        let name = path
            .segments
            .last()
            .map(|s| s.identifier.symbol)
            .unwrap_or_else(|| self.checker.gcx().intern_symbol("_"));
        self.record_capture(id, name);
    }

    fn collect_block(&mut self, block: &hir::Block) {
        for stmt in &block.statements {
            self.collect_statement(stmt);
        }
        if let Some(tail) = block.tail.as_deref() {
            self.collect_expr(tail);
        }
    }

    fn collect_statement(&mut self, stmt: &hir::Statement) {
        match &stmt.kind {
            hir::StatementKind::Declaration(_) => {}
            hir::StatementKind::Expression(expr) => {
                self.collect_expr(expr);
            }
            hir::StatementKind::Variable(local) => {
                // First collect captures from the initializer (before registering the local)
                if let Some(init) = local.initializer.as_deref() {
                    self.collect_expr(init);
                }
                // Mark every binding introduced by this local pattern as scoped to the closure body.
                self.collect_pattern_bindings(&local.pattern);
            }
            hir::StatementKind::Loop { block, .. } => {
                self.collect_block(block);
            }
            hir::StatementKind::Defer(_, block) => {
                self.collect_block(block);
            }
            hir::StatementKind::Guard {
                condition,
                else_block,
            } => {
                self.collect_expr(condition);
                self.collect_block(else_block);
            }
            hir::StatementKind::ComptimeFor { .. } | hir::StatementKind::ComptimeIf { .. } => {
                let expansions = self
                    .checker
                    .results
                    .borrow()
                    .comptime_expansions
                    .get(&stmt.id)
                    .cloned();
                if let Some(blocks) = expansions {
                    for block in &blocks {
                        self.collect_block(block);
                    }
                }
            }
        }
    }

    fn collect_expr(&mut self, expr: &hir::Expression) {
        if matches!(expr.kind, hir::ExpressionKind::Call { .. }) {
            let selected = self
                .checker
                .results
                .borrow()
                .elaborated_calls
                .get(&expr.id)
                .cloned();
            if let Some(selected) = selected {
                self.collect_expr(&selected);
                return;
            }
        }
        if self.maybe_capture_projection(expr) {
            return;
        }
        match &expr.kind {
            hir::ExpressionKind::MemberBrackets { .. } => {
                let selected = self
                    .checker
                    .results
                    .borrow()
                    .selected_brackets
                    .get(&expr.id)
                    .cloned();
                if let Some(selected) = selected {
                    self.collect_expr(&selected);
                }
            }
            hir::ExpressionKind::Literal(_)
            | hir::ExpressionKind::TypeName(_)
            | hir::ExpressionKind::Discard
            | hir::ExpressionKind::Malformed => {}
            hir::ExpressionKind::Closure(closure) => {
                // For nested closures, propagate their captures to our capture list.
                // The nested closure has already been type-checked (during body synthesis),
                // so its captures are cached.
                if let Some(nested_captures) =
                    self.checker.gcx().get_closure_captures(closure.def_id)
                {
                    for cap in &nested_captures.captures {
                        // Skip if this is one of our parameters
                        if self.param_ids.contains(&cap.source_id) {
                            continue;
                        }
                        // Skip if this is a local declared in our closure body
                        // (the nested closure can access it directly)
                        if self.local_decls.contains(&cap.source_id) {
                            continue;
                        }
                        if self.checker.try_get_local(cap.source_id).is_none() {
                            continue;
                        }
                        // Propagate the capture - the nested closure needs this variable,
                        // so we must capture it too to make it available
                        self.record_projected_capture(
                            cap.source_id,
                            cap.name,
                            cap.projection.to_vec(),
                        );
                    }
                }
            }
            hir::ExpressionKind::Path(path) => {
                self.maybe_capture(path);
            }
            hir::ExpressionKind::Member { target, .. }
            | hir::ExpressionKind::MissingMember { target, .. } => {
                self.collect_expr(target);
            }
            hir::ExpressionKind::Index { target, index, .. } => {
                self.collect_expr(target);
                for argument in index {
                    self.collect_expr(&argument.expression);
                }
            }
            hir::ExpressionKind::InferredMember { .. } => {}
            hir::ExpressionKind::Array(items) | hir::ExpressionKind::Tuple(items, _) => {
                for item in items {
                    self.collect_expr(item);
                }
            }
            hir::ExpressionKind::Repeat { value, .. } => {
                self.collect_expr(value);
            }
            hir::ExpressionKind::If(expr) => {
                self.collect_expr(&expr.condition);
                self.collect_expr(&expr.then_block);
                if let Some(else_block) = expr.else_block.as_deref() {
                    self.collect_expr(else_block);
                }
            }
            hir::ExpressionKind::Match(expr) => {
                self.collect_expr(&expr.value);
                for arm in &expr.arms {
                    let mut arm_bindings = Vec::new();
                    arm.pattern.for_each_binding(&mut |id, _| arm_bindings.push(id));
                    for binding_id in &arm_bindings {
                        self.local_decls.insert(*binding_id);
                    }
                    if let Some(guard) = arm.guard.as_deref() {
                        self.collect_expr(guard);
                    }
                    self.collect_expr(&arm.body);
                    for binding_id in arm_bindings {
                        self.local_decls.remove(&binding_id);
                    }
                }
            }
            hir::ExpressionKind::Select(expr) => {
                for arm in &expr.arms {
                    self.collect_expr(&arm.operation);
                    let mut arm_bindings = Vec::new();
                    arm.pattern
                        .for_each_binding(&mut |id, _| arm_bindings.push(id));
                    for binding_id in &arm_bindings {
                        self.local_decls.insert(*binding_id);
                    }
                    self.collect_expr(&arm.body);
                    for binding_id in arm_bindings {
                        self.local_decls.remove(&binding_id);
                    }
                }
            }
            hir::ExpressionKind::Loop { block, .. } => {
                self.collect_block(block);
            }
            hir::ExpressionKind::Return { value } => {
                if let Some(value) = value.as_deref() {
                    self.collect_expr(value);
                }
            }
            hir::ExpressionKind::Break { value, .. } => {
                if let Some(value) = value.as_deref() {
                    self.collect_expr(value);
                }
            }
            hir::ExpressionKind::Continue { .. } => {}
            hir::ExpressionKind::Call { callee, arguments } => {
                self.collect_expr(callee);
                for arg in arguments {
                    self.collect_expr(&arg.expression);
                }
            }
            hir::ExpressionKind::MethodCall {
                receiver,
                arguments,
                ..
            } => {
                self.collect_expr(receiver);
                for arg in arguments {
                    self.collect_expr(&arg.expression);
                }
            }
            hir::ExpressionKind::Reference(value) => {
                self.collect_expr(value);
            }
            hir::ExpressionKind::Dereference(value) | hir::ExpressionKind::Spread(value) => {
                self.collect_expr(value)
            }
            hir::ExpressionKind::Binary(_, lhs, rhs) => {
                self.collect_expr(lhs);
                self.collect_expr(rhs);
            }
            hir::ExpressionKind::AssignOp(_, lhs, rhs)
            | hir::ExpressionKind::AssignOptional(lhs, rhs) => {
                self.collect_expr(lhs);
                self.collect_expr(rhs);
            }
            hir::ExpressionKind::Unary(_, value)
            | hir::ExpressionKind::Propagate(value)
            | hir::ExpressionKind::CastAs(value, _)
            | hir::ExpressionKind::CastAsTry(value, _)
            | hir::ExpressionKind::TypeIs(value, _) => {
                self.collect_expr(value);
            }
            hir::ExpressionKind::TupleAccess(value, _) => {
                self.collect_expr(value);
            }
            hir::ExpressionKind::Assign(lhs, rhs) => {
                self.collect_expr(lhs);
                self.collect_expr(rhs);
            }
            hir::ExpressionKind::PatternBinding(binding) => {
                self.collect_expr(&binding.expression);
                // The condition introduces these locals inside this closure.
                // Only a nested closure may capture their values.
                self.collect_pattern_bindings(&binding.pattern);
            }
            hir::ExpressionKind::Block(block) | hir::ExpressionKind::UnsafeBlock(block) => {
                self.collect_block(block);
            }
            hir::ExpressionKind::StructLiteral(literal) => {
                for field in &literal.fields {
                    self.collect_expr(&field.expression);
                }
                if let Some(base) = &literal.base {
                    self.collect_expr(base);
                }
            }
            hir::ExpressionKind::Await(value) | hir::ExpressionKind::Yield(value) => {
                self.collect_expr(value);
            }
        }
    }

    fn collect_pattern_bindings(&mut self, pattern: &hir::Pattern) {
        pattern.for_each_binding(&mut |id, _| { self.local_decls.insert(id); });
    }
}

fn closure_self_ty<'ctx>(_gcx: Gcx<'ctx>, closure_ty: Ty<'ctx>, _kind: ClosureKind) -> Ty<'ctx> {
    // Copying the environment preserves its shared capture cells. Repeated and
    // suspended calls therefore observe the same captured variables.
    closure_ty
}

#[cfg(test)]
mod context_tests {
    use crate::test_support::{analyze_script_diagnostics, analyze_script_mir_diagnostics};

    /// Checking a closure solves the enclosing statement's constraints so far.
    /// That solve defaults only the closure's own literals: the `1` beside it
    /// takes `usize` from `same` once `apply`'s result is known, and the
    /// closure's own `2` still takes its default.
    #[test]
    fn checking_a_closure_defaults_only_its_own_literals() {
        for source in [
            "func same[T](_ a: T, _ b: T) -> T { b }\nfunc apply[T, U](_ v: T, _ f: (T) -> U) -> U { f(v) }\nfunc main() { var n: usize = 2; x := same(1, apply(n, (v) => v)); var y: usize = x }",
            "func apply[T, U](_ v: T, _ f: (T) -> U) -> U { f(v) }\nfunc main() { var n: usize = 2; x := 1 + apply(n, (v) => v); var y: usize = x }",
            "func apply[T, U](_ v: T, _ f: (T) -> U) -> U { f(v) }\nfunc main() { var n: usize = 2; x := [1, apply(n, (v) => v)]; var y: [usize; 2] = x }",
            "func apply[T, U](_ v: T, _ f: (T) -> U) -> U { f(v) }\nfunc main() { var n: usize = 2; x := apply(n, (v) => 2); var y: int32 = x }",
        ] {
            let errors = analyze_script_diagnostics(source);
            assert!(errors.is_empty(), "{source}\n{errors:#?}");
        }
    }

    #[test]
    fn invoking_a_captured_callable_uses_its_receiver_mode() {
        for source in [
            "func main() { inner := () => 7_i32; outer := () => inner(); a := outer(); b := outer(); c := inner() }",
            "func main() { inner := () => 7_i32; outer := () => inner(); a := outer(); b := outer() }",
            "func main() { var count: int32 = 0; var inner = () => { count += 1; count }; var outer = () => inner(); a := outer(); b := outer(); c := inner(); result := count }",
            "func main() { var count: int32 = 0; var inner = () => { count += 1; count }; token := &inner; var outer = () => token(); a := outer(); b := outer(); result := count }",
        ] {
            let errors = analyze_script_mir_diagnostics(source);
            assert!(errors.is_empty(), "{source}\n{errors:#?}");
        }
    }

    #[test]
    fn invoking_a_value_capture_can_repeat() {
        let errors = analyze_script_mir_diagnostics(
            "struct Owned { value: int32 }\nfunc main() { value := Owned { value: 7 }; inner := () => value; outer := () => inner(); a := outer(); b := outer() }",
        );
        assert!(errors.is_empty(), "{errors:#?}");
    }

    /// Captures are by reference (G17): writes after capture are observed and
    /// do not conflict, and capturing closures flow through generic code.
    #[test]
    fn reference_captures_allow_later_writes_and_generic_escape() {
        for source in [
            "func main() { var count: int32 = 7; read := () => count; count = 9; result := read() }",
            "func own[T](_ value: T) -> T { value }\nfunc main() { var count: int32 = 7; read := own(() => count); count = 9; result := read() }",
            "func own[T](_ value: T) -> T { value }\nfunc main() { var count: int32 = 7; read := () => count; escaped := own(read) }",
        ] {
            let diagnostics = analyze_script_mir_diagnostics(source);
            assert!(diagnostics.is_empty(), "{source}\n{diagnostics:#?}");
        }
    }

    #[test]
    fn await_in_a_local_closure_infers_async_call_diagnostics() {
        let diagnostics = analyze_script_diagnostics(
            "func tick() async -> int32 { 7 }\nfunc main() { run := () => { await tick() }; value := run() }",
        );
        assert!(
            diagnostics.iter().any(|d| d
                .message
                .contains("async calls require an enclosing `await` expression")),
            "{diagnostics:#?}"
        );
        assert!(
            !diagnostics
                .iter()
                .any(|d| d.message.contains("await is only allowed")),
            "{diagnostics:#?}"
        );
    }

    #[test]
    fn nested_async_closure_does_not_make_its_parent_async() {
        let diagnostics = analyze_script_diagnostics(
            "func tick() async -> int32 { 7 }\nfunc main() { outer := () => { inner := () => { await tick() }; 9 }; value := outer() }",
        );
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }
}

#[cfg(test)]
mod precise_capture_tests {
    use crate::test_support::analyze_script_mir_diagnostics;

    const TYPES: &str = "struct Item { value: int32 }\nstruct Pair { left: Item; right: Item }\n";

    #[test]
    fn nested_inferred_capture_paths_are_fully_resolved_before_publication() {
        crate::test_support::check_script(
            "struct Wrapper[T] { value: T }\nfunc main() { build := () => { wrapper := Wrapper { value: 7 }; read := () => wrapper.value; read() }; var result: int32 = build() }",
            |_, gcx| {
                gcx.with_session_type_database(|database| {
                    let mut projected = 0;
                    for captures in database.closure_captures.values() {
                        for capture in &captures.captures {
                            if capture.projection.is_empty() {
                                continue;
                            }
                            projected += 1;
                            assert!(
                                !capture.root_ty.contains_inference(),
                                "{:?}",
                                capture.root_ty
                            );
                            assert!(!capture.ty.contains_inference(), "{:?}", capture.ty);
                            assert!(
                                capture
                                    .projection
                                    .iter()
                                    .all(|field| !field.ty.contains_inference())
                            );
                        }
                    }
                    assert_eq!(projected, 1);
                });
            },
        );
    }

    #[test]
    fn inferred_capture_paths_inside_match_arms_are_fully_resolved() {
        // The arm's result literal is held for the other arms; the closure
        // in it still publishes resolved capture types.
        crate::test_support::check_script(
            "struct Wrapper[T] { value: T }\nfunc main() {\n    k := 1\n    out := match k {\n        case 1 => {\n            wrapper := Wrapper { value: 7 }\n            read := () => wrapper.value\n            read()\n        }\n        case _ => 0\n    }\n    var result: int32 = out\n}",
            |_, gcx| {
                gcx.with_session_type_database(|database| {
                    let mut projected = 0;
                    for captures in database.closure_captures.values() {
                        for capture in &captures.captures {
                            if capture.projection.is_empty() {
                                continue;
                            }
                            projected += 1;
                            assert!(
                                !capture.root_ty.contains_inference(),
                                "{:?}",
                                capture.root_ty
                            );
                            assert!(!capture.ty.contains_inference(), "{:?}", capture.ty);
                            assert!(
                                capture
                                    .projection
                                    .iter()
                                    .all(|field| !field.ty.contains_inference())
                            );
                        }
                    }
                    assert_eq!(projected, 1);
                });
            },
        );
    }

    #[test]
    fn unused_borrowed_fields_do_not_make_an_owned_capture_dependent() {
        let errors = crate::test_support::analyze_script_mir_diagnostics(
            "struct View { value: int32; other: &int32 }\nfunc own[T](_ value: T) -> T { value }\nfunc main() { var outside: int32 = 9; view := View { value: 7, other: &outside }; read := own(() => view.value); observed := read() }",
        );
        assert!(errors.is_empty(), "{errors:#?}");
    }

    #[test]
    fn prefix_merging_keeps_earliest_use_order_and_round_trips_paths() {
        crate::test_support::analyze_script_built_mir(
            &format!(
                "{TYPES}func inspect(_ item: &Item) -> int32 {{ item.value }}\nfunc main() {{ pair := Pair {{ left: Item {{ value: 7 }}, right: Item {{ value: 9 }} }}; read := () => {{ first := pair.left.value; second := pair.right.value; first + second + inspect(&pair.left) }}; observed := read() }}"
            ),
            |bodies, gcx| {
                let captures = bodies
                    .iter()
                    .find_map(|body| gcx.get_closure_captures(body.owner))
                    .unwrap();
                let paths = captures
                    .captures
                    .iter()
                    .map(|capture| {
                        capture
                            .projection
                            .iter()
                            .map(|field| field.field.index())
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>();
                assert_eq!(paths, [vec![0], vec![1, 0]]);
                assert_eq!(
                    captures.captures[0].source_id,
                    captures.captures[1].source_id
                );
                use crate::metadata::wire::{self, SymbolTableBuilder, SymbolTableRef};
                let mut symbols = SymbolTableBuilder::new(gcx.interner());
                let wire = wire::closure_captures_to_wire(&captures, &mut symbols);
                let wire: wire::ClosureCapturesWire =
                    bincode::deserialize(&bincode::serialize(&wire).unwrap()).unwrap();
                let symbols = symbols.finish();
                let invalid = std::cell::Cell::new(None);
                let restored = wire::closure_captures_from_wire(
                    gcx,
                    &wire,
                    SymbolTableRef::new(gcx.interner(), &symbols, &invalid),
                );
                for (original, restored) in captures.captures.iter().zip(&restored.captures) {
                    assert_eq!(original.root_ty, restored.root_ty);
                    assert_eq!(original.ty, restored.ty);
                    assert_eq!(original.projection, restored.projection);
                    assert_eq!(original.field_index, restored.field_index);
                }
                assert!(invalid.get().is_none());
            },
        );
    }

    #[test]
    fn projected_captures_leave_disjoint_storage_usable() {
        for body in [
            "read := () => pair.left.value; pair.right.value = 11; observed := read()",
            "var edit = () => { pair.left.value += 1 }; pair.right.value = 11; edit(); observed := pair.left.value",
            "take := () => pair.left; other := pair.right; item := take()",
            "read := () => pair.left.value; pair.left.value = 11; observed := read(); item := pair.left",
            "read := () => { inner := () => pair.left.value; inner() }; pair.right.value = 11; observed := read()",
            "take := () => { inner := () => pair.left; inner() }; other := pair.right; item := take()",
        ] {
            let source = format!(
                "{TYPES}func main() {{ var pair = Pair {{ left: Item {{ value: 7 }}, right: Item {{ value: 9 }} }}; {body} }}"
            );
            let errors = analyze_script_mir_diagnostics(&source);
            assert!(errors.is_empty(), "{body}\n{errors:#?}");
        }
    }

    #[test]
    fn projected_captures_do_not_lock_the_captured_field() {
        for body in [
            "read := () => pair.left.value; pair.left.value = 11; observed := read()",
            "var edit = () => { pair.left.value += 1 }; observed := pair.left.value; edit()",
            "read := () => { first := pair.left.value; inspect(&pair) + first }; pair.right.value = 11; observed := read()",
        ] {
            let source = format!(
                "{TYPES}func inspect(_ pair: &Pair) -> int32 {{ pair.right.value }}\nfunc main() {{ var pair = Pair {{ left: Item {{ value: 7 }}, right: Item {{ value: 9 }} }}; {body} }}"
            );
            let errors = analyze_script_mir_diagnostics(&source);
            assert!(errors.is_empty(), "{body}\n{errors:#?}");
        }
    }
}
