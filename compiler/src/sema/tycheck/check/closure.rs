use super::*;

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
            || self.is_forced_async_closure_expr(expression.id)
            || expectation.is_some_and(|ty| {
                crate::sema::tycheck::utils::callable::existential_callable(
                    gcx,
                    cs.infer_cx.resolve_vars_if_possible(ty),
                )
                .is_some_and(|callable| callable.is_async())
            });

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
            self.lower_type(ret_ty)
        } else if let Some(expected_return) = expected_output {
            expected_return
        } else {
            cs.infer_cx.next_ty_var(closure.body.span)
        };

        // Type check the closure body under the closure's own return context so
        // explicit `return expr` participates in the same output inference as a
        // tail expression.
        let (return_ty, body_ty) = self.with_return_ty(Some(expected_return), || {
            let prev_async_depth = self.async_depth.get();
            if effective_async {
                self.async_depth.set(prev_async_depth + 1);
            }

            let body_ty = match &closure.body.kind {
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

            if effective_async {
                self.async_depth.set(prev_async_depth);
            }

            (expected_return, body_ty)
        });
        cs.record_expr_ty(closure.body.id, body_ty);

        // Resolve what we can so we don't cache infer vars in closure signatures.
        cs.solve_intermediate();
        let adjustments = cs.resolved_adjustments();
        let expr_tys = cs.resolved_expr_types();
        let interface_calls = cs.resolved_interface_calls();
        let return_ty = cs.infer_cx.resolve_vars_if_possible(return_ty);
        let param_tys: Vec<_> = param_tys
            .into_iter()
            .map(|ty| cs.infer_cx.resolve_vars_if_possible(ty))
            .collect();

        // Perform capture analysis - collect free variables from the closure body
        let mut collector = CaptureCollector {
            param_ids: &param_ids,
            local_decls: rustc_hash::FxHashSet::default(),
            order: Vec::new(),
            info: rustc_hash::FxHashMap::default(),
            checker: self,
            adjustments: &adjustments,
            expr_tys: &expr_tys,
            interface_calls: &interface_calls,
        };
        collector.collect_expr(&closure.body, UseContext::Value);

        // Build capture list with types and capture kinds
        let mut captures = Vec::new();
        for (field_index, node_id) in collector.order.iter().enumerate() {
            if param_ids.contains(node_id) {
                continue;
            }
            let info = collector
                .info
                .get(node_id)
                .expect("capture info should exist");
            // Get the type of the captured variable from local bindings
            let binding = self.get_local(*node_id);
            let ty = cs.infer_cx.resolve_vars_if_possible(binding.ty);
            let capture_kind = classify_capture_kind(
                gcx,
                self.current_def,
                ty,
                info.usage,
                closure.is_move,
                effective_async,
            );

            captures.push(crate::sema::models::CapturedVar {
                source_id: *node_id,
                name: info.name,
                ty,
                capture_kind,
                access_kind: info.usage.access_kind,
                field_index: crate::thir::FieldIndex::from_raw(field_index as u32),
            });
        }

        let closure_kind = infer_closure_kind(effective_async, &captures);

        gcx.cache_closure_captures(
            closure.def_id,
            crate::sema::models::ClosureCaptures {
                captures: captures.clone(),
                kind: closure_kind,
            },
        );

        // Create the closure type (with user-visible parameter types only)
        let inputs = gcx.store.interners.intern_ty_list(param_tys.clone());
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

        gcx.cache_signature(closure_def_id, new_sig);
    }
}

#[derive(Clone, Copy)]
struct CaptureUsage {
    access_kind: crate::sema::models::CaptureAccessKind,
    by_ref: Option<hir::Mutability>,
}

impl Default for CaptureUsage {
    fn default() -> Self {
        Self {
            access_kind: crate::sema::models::CaptureAccessKind::Read,
            by_ref: None,
        }
    }
}

struct CaptureInfo {
    name: Symbol,
    usage: CaptureUsage,
}

#[derive(Clone, Copy)]
enum UseContext {
    Value,
    /// Read a captured place without moving the complete base value.
    Read,
    Place,
    Borrow {
        mutable: bool,
    },
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
    order: Vec<NodeID>,
    /// Capture info keyed by NodeID
    info: rustc_hash::FxHashMap<NodeID, CaptureInfo>,
    /// Reference to the checker for accessing local bindings
    checker: &'a Checker<'ctx>,
    /// Adjustments recorded during type checking
    adjustments: &'a rustc_hash::FxHashMap<NodeID, Vec<Adjustment<'ctx>>>,
    /// Fully resolved expression types used to distinguish copying a projected
    /// field from moving it out of the captured aggregate.
    expr_tys: &'a rustc_hash::FxHashMap<NodeID, Ty<'ctx>>,
    interface_calls:
        &'a rustc_hash::FxHashMap<NodeID, crate::sema::tycheck::solve::InterfaceCallInfo>,
}

impl<'a, 'ctx> CaptureCollector<'a, 'ctx> {
    fn stronger_access(
        lhs: crate::sema::models::CaptureAccessKind,
        rhs: crate::sema::models::CaptureAccessKind,
    ) -> crate::sema::models::CaptureAccessKind {
        use crate::sema::models::CaptureAccessKind;

        match (lhs, rhs) {
            (CaptureAccessKind::Move, _) | (_, CaptureAccessKind::Move) => CaptureAccessKind::Move,
            (CaptureAccessKind::Mutate, _) | (_, CaptureAccessKind::Mutate) => {
                CaptureAccessKind::Mutate
            }
            (CaptureAccessKind::Read, CaptureAccessKind::Read) => CaptureAccessKind::Read,
        }
    }

    fn record_capture(&mut self, id: NodeID, name: Symbol, usage: CaptureUsage) {
        let entry = self.info.entry(id).or_insert_with(|| {
            self.order.push(id);
            CaptureInfo {
                name,
                usage: CaptureUsage::default(),
            }
        });
        entry.usage.access_kind = Self::stronger_access(entry.usage.access_kind, usage.access_kind);
        match (entry.usage.by_ref, usage.by_ref) {
            (_, Some(hir::Mutability::Mutable)) => {
                entry.usage.by_ref = Some(hir::Mutability::Mutable);
            }
            (None, Some(hir::Mutability::Immutable)) => {
                entry.usage.by_ref = Some(hir::Mutability::Immutable);
            }
            _ => {}
        }
    }

    fn capture_usage(
        &self,
        expr: &hir::Expression,
        ctx: UseContext,
        local_ty: Ty<'ctx>,
    ) -> CaptureUsage {
        match ctx {
            UseContext::Read => CaptureUsage::default(),
            UseContext::Borrow { mutable } => CaptureUsage {
                access_kind: if mutable {
                    crate::sema::models::CaptureAccessKind::Mutate
                } else {
                    crate::sema::models::CaptureAccessKind::Read
                },
                by_ref: Some(if mutable {
                    hir::Mutability::Mutable
                } else {
                    hir::Mutability::Immutable
                }),
            },
            UseContext::Place => CaptureUsage {
                access_kind: crate::sema::models::CaptureAccessKind::Mutate,
                by_ref: Some(hir::Mutability::Mutable),
            },
            UseContext::Value => {
                if let Some(adjustments) = self.adjustments.get(&expr.id) {
                    if adjustments
                        .iter()
                        .any(|adj| matches!(adj, Adjustment::BorrowMutable))
                    {
                        return CaptureUsage {
                            access_kind: crate::sema::models::CaptureAccessKind::Mutate,
                            by_ref: Some(hir::Mutability::Mutable),
                        };
                    }
                    if adjustments
                        .iter()
                        .any(|adj| matches!(adj, Adjustment::BorrowImmutable))
                    {
                        return CaptureUsage {
                            access_kind: crate::sema::models::CaptureAccessKind::Read,
                            by_ref: Some(hir::Mutability::Immutable),
                        };
                    }
                }

                CaptureUsage {
                    access_kind: if self
                        .checker
                        .gcx()
                        .is_type_copyable_in_def(local_ty, self.checker.current_def)
                    {
                        crate::sema::models::CaptureAccessKind::Read
                    } else {
                        crate::sema::models::CaptureAccessKind::Move
                    },
                    by_ref: None,
                }
            }
        }
    }

    fn maybe_capture(&mut self, expr: &hir::Expression, path: &hir::ResolvedPath, ctx: UseContext) {
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
        let Some(binding) = self.checker.try_get_local(id) else {
            return;
        };

        let name = path
            .segments
            .last()
            .map(|s| s.identifier.symbol)
            .unwrap_or_else(|| self.checker.gcx().intern_symbol("_"));
        let usage = self.capture_usage(expr, ctx, binding.ty);
        self.record_capture(id, name, usage);
    }

    fn collect_block(&mut self, block: &hir::Block) {
        for stmt in &block.statements {
            self.collect_statement(stmt);
        }
        if let Some(tail) = block.tail.as_deref() {
            self.collect_expr(tail, UseContext::Value);
        }
    }

    fn collect_statement(&mut self, stmt: &hir::Statement) {
        match &stmt.kind {
            hir::StatementKind::Declaration(_) => {}
            hir::StatementKind::Expression(expr) => {
                self.collect_expr(expr, UseContext::Value);
            }
            hir::StatementKind::Variable(local) => {
                // First collect captures from the initializer (before registering the local)
                if let Some(init) = local.initializer.as_deref() {
                    self.collect_expr(init, UseContext::Value);
                }
                // Mark every binding introduced by this local pattern as scoped to the closure body.
                self.collect_pattern_bindings(&local.pattern);
            }
            hir::StatementKind::Loop { block, .. } => {
                self.collect_block(block);
            }
            hir::StatementKind::Defer(block) => {
                self.collect_block(block);
            }
            hir::StatementKind::Guard {
                condition,
                else_block,
            } => {
                self.collect_expr(condition, UseContext::Value);
                self.collect_block(else_block);
            }
        }
    }

    fn collect_expr(&mut self, expr: &hir::Expression, ctx: UseContext) {
        match &expr.kind {
            hir::ExpressionKind::Literal(_) | hir::ExpressionKind::Malformed => {}
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
                        let Some(binding) = self.checker.try_get_local(cap.source_id) else {
                            continue;
                        };
                        // Propagate the capture - the nested closure needs this variable,
                        // so we must capture it too to make it available
                        let usage = match cap.capture_kind {
                            crate::sema::models::CaptureKind::ByCopy => CaptureUsage::default(),
                            crate::sema::models::CaptureKind::ByRef { mutable } => CaptureUsage {
                                access_kind: if mutable {
                                    crate::sema::models::CaptureAccessKind::Mutate
                                } else {
                                    crate::sema::models::CaptureAccessKind::Read
                                },
                                by_ref: Some(if mutable {
                                    hir::Mutability::Mutable
                                } else {
                                    hir::Mutability::Immutable
                                }),
                            },
                            crate::sema::models::CaptureKind::ByMove => {
                                let copyable = self
                                    .checker
                                    .gcx()
                                    .is_type_copyable_in_def(binding.ty, self.checker.current_def);
                                CaptureUsage {
                                    access_kind: if copyable {
                                        crate::sema::models::CaptureAccessKind::Read
                                    } else {
                                        crate::sema::models::CaptureAccessKind::Move
                                    },
                                    by_ref: None,
                                }
                            }
                        };
                        self.record_capture(cap.source_id, cap.name, usage);
                    }
                }
            }
            hir::ExpressionKind::Path(path) => {
                self.maybe_capture(expr, path, ctx);
            }
            hir::ExpressionKind::Member { target, .. } => {
                self.collect_expr(target, self.projection_base_context(expr, ctx));
            }
            hir::ExpressionKind::InferredMember { .. } => {}
            hir::ExpressionKind::Array(items) | hir::ExpressionKind::Tuple(items) => {
                for item in items {
                    self.collect_expr(item, UseContext::Value);
                }
            }
            hir::ExpressionKind::Repeat { value, .. } => {
                self.collect_expr(value, UseContext::Value);
            }
            hir::ExpressionKind::If(expr) => {
                self.collect_expr(&expr.condition, UseContext::Value);
                self.collect_expr(&expr.then_block, UseContext::Value);
                if let Some(else_block) = expr.else_block.as_deref() {
                    self.collect_expr(else_block, UseContext::Value);
                }
            }
            hir::ExpressionKind::Match(expr) => {
                self.collect_expr(&expr.value, UseContext::Value);
                for arm in &expr.arms {
                    let mut arm_bindings = Vec::new();
                    self.collect_pattern_binding_ids(&arm.pattern, &mut arm_bindings);
                    for binding_id in &arm_bindings {
                        self.local_decls.insert(*binding_id);
                    }
                    if let Some(guard) = arm.guard.as_deref() {
                        self.collect_expr(guard, UseContext::Value);
                    }
                    self.collect_expr(&arm.body, UseContext::Value);
                    for binding_id in arm_bindings {
                        self.local_decls.remove(&binding_id);
                    }
                }
            }
            hir::ExpressionKind::Return { value } => {
                if let Some(value) = value.as_deref() {
                    self.collect_expr(value, UseContext::Value);
                }
            }
            hir::ExpressionKind::Break { .. } | hir::ExpressionKind::Continue { .. } => {}
            hir::ExpressionKind::Call { callee, arguments } => {
                let callee_context = self
                    .expr_tys
                    .get(&callee.id)
                    .and_then(|ty| {
                        crate::sema::tycheck::utils::callable::existential_callable(
                            self.checker.gcx(),
                            *ty,
                        )
                    })
                    .and_then(|callable| callable.receiver_mutability())
                    .map(|mutability| UseContext::Borrow {
                        mutable: mutability == hir::Mutability::Mutable,
                    })
                    .unwrap_or(UseContext::Value);
                self.collect_expr(callee, callee_context);
                for arg in arguments {
                    self.collect_expr(&arg.expression, UseContext::Value);
                }
            }
            hir::ExpressionKind::MethodCall {
                receiver,
                arguments,
                ..
            } => {
                let receiver_context = self
                    .interface_calls
                    .get(&expr.id)
                    .and_then(|info| {
                        let kind = crate::sema::models::callable_kind(
                            self.checker.gcx(),
                            info.method_interface,
                        )?;
                        match kind {
                            crate::sema::models::ClosureKind::Fn
                            | crate::sema::models::ClosureKind::AsyncFn => {
                                Some(UseContext::Borrow { mutable: false })
                            }
                            crate::sema::models::ClosureKind::FnMut
                            | crate::sema::models::ClosureKind::AsyncFnMut => {
                                Some(UseContext::Borrow { mutable: true })
                            }
                            _ => None,
                        }
                    })
                    .unwrap_or(UseContext::Value);
                self.collect_expr(receiver, receiver_context);
                for arg in arguments {
                    self.collect_expr(&arg.expression, UseContext::Value);
                }
            }
            hir::ExpressionKind::Reference(value, mutability) => {
                let mutable = matches!(mutability, hir::Mutability::Mutable);
                self.collect_expr(value, UseContext::Borrow { mutable });
            }
            hir::ExpressionKind::Dereference(value) => {
                self.collect_expr(value, ctx);
            }
            hir::ExpressionKind::Binary(_, lhs, rhs) => {
                self.collect_expr(lhs, UseContext::Value);
                self.collect_expr(rhs, UseContext::Value);
            }
            hir::ExpressionKind::AssignOp(_, lhs, rhs) => {
                self.collect_expr(lhs, UseContext::Place);
                self.collect_expr(rhs, UseContext::Value);
            }
            hir::ExpressionKind::Unary(_, value)
            | hir::ExpressionKind::Propagate(value)
            | hir::ExpressionKind::CastAs(value, _)
            | hir::ExpressionKind::CastAsTry(value, _)
            | hir::ExpressionKind::TypeIs(value, _) => {
                self.collect_expr(value, UseContext::Value);
            }
            hir::ExpressionKind::TupleAccess(value, _) => {
                self.collect_expr(value, self.projection_base_context(expr, ctx));
            }
            hir::ExpressionKind::Assign(lhs, rhs) => {
                self.collect_expr(lhs, UseContext::Place);
                self.collect_expr(rhs, UseContext::Value);
            }
            hir::ExpressionKind::PatternBinding(binding) => {
                self.collect_expr(&binding.expression, UseContext::Value);
            }
            hir::ExpressionKind::Block(block) | hir::ExpressionKind::UnsafeBlock(block) => {
                self.collect_block(block);
            }
            hir::ExpressionKind::StructLiteral(literal) => {
                for field in &literal.fields {
                    self.collect_expr(&field.expression, UseContext::Value);
                }
            }
            hir::ExpressionKind::Await(value) => {
                self.collect_expr(value, UseContext::Value);
            }
        }
    }

    fn projection_base_context(&self, expr: &hir::Expression, ctx: UseContext) -> UseContext {
        match ctx {
            // Once an outer projection is known to copy its result, every base
            // projection is only read to reach that value.
            UseContext::Read => UseContext::Read,
            UseContext::Value
                if self.expr_tys.get(&expr.id).is_some_and(|ty| {
                    self.checker
                        .gcx()
                        .is_type_copyable_in_def(*ty, self.checker.current_def)
                }) =>
            {
                UseContext::Read
            }
            other => other,
        }
    }

    fn collect_pattern_bindings(&mut self, pattern: &hir::Pattern) {
        let mut binding_ids = Vec::new();
        self.collect_pattern_binding_ids(pattern, &mut binding_ids);
        for binding_id in binding_ids {
            self.local_decls.insert(binding_id);
        }
    }

    fn collect_pattern_binding_ids(&self, pattern: &hir::Pattern, binding_ids: &mut Vec<NodeID>) {
        match &pattern.kind {
            hir::PatternKind::Binding { .. } => binding_ids.push(pattern.id),
            hir::PatternKind::Tuple(patterns, _) | hir::PatternKind::Or(patterns, _) => {
                for pattern in patterns {
                    self.collect_pattern_binding_ids(pattern, binding_ids);
                }
            }
            hir::PatternKind::Reference { pattern, .. } => {
                self.collect_pattern_binding_ids(pattern, binding_ids);
            }
            hir::PatternKind::PathTuple { fields, .. } => {
                for pattern in fields {
                    self.collect_pattern_binding_ids(pattern, binding_ids);
                }
            }
            hir::PatternKind::Wildcard
            | hir::PatternKind::Rest
            | hir::PatternKind::Member(_)
            | hir::PatternKind::Literal { .. } => {}
        }
    }
}

fn classify_capture_kind<'ctx>(
    gcx: Gcx<'ctx>,
    owner: DefinitionID,
    ty: Ty<'ctx>,
    usage: CaptureUsage,
    is_move_closure: bool,
    is_async: bool,
) -> crate::sema::models::CaptureKind {
    if is_move_closure {
        if gcx.is_type_copyable_in_def(ty, owner) {
            return crate::sema::models::CaptureKind::ByCopy;
        }
        return crate::sema::models::CaptureKind::ByMove;
    }
    if matches!(
        usage.access_kind,
        crate::sema::models::CaptureAccessKind::Move
    ) {
        return crate::sema::models::CaptureKind::ByMove;
    }
    if let Some(mutability) = usage.by_ref {
        // An implicit immutable borrow (for example, an `&self` method call)
        // does not require an async closure to borrow a Copy local. Store the
        // value instead so an owned/escaping future cannot retain a pointer to
        // the caller's short-lived closure argument.
        if is_async
            && matches!(mutability, hir::Mutability::Immutable)
            && gcx.is_type_copyable_in_def(ty, owner)
        {
            return crate::sema::models::CaptureKind::ByCopy;
        }
        return crate::sema::models::CaptureKind::ByRef {
            mutable: matches!(mutability, hir::Mutability::Mutable),
        };
    }
    if gcx.is_type_copyable_in_def(ty, owner) {
        crate::sema::models::CaptureKind::ByCopy
    } else {
        crate::sema::models::CaptureKind::ByMove
    }
}

fn infer_closure_kind(
    is_async: bool,
    captures: &[crate::sema::models::CapturedVar<'_>],
) -> crate::sema::models::ClosureKind {
    if is_async {
        let mut kind = crate::sema::models::ClosureKind::AsyncFn;
        for capture in captures {
            if matches!(
                capture.capture_kind,
                crate::sema::models::CaptureKind::ByMove
            ) || matches!(
                capture.access_kind,
                crate::sema::models::CaptureAccessKind::Move
            ) {
                return crate::sema::models::ClosureKind::AsyncFnOnce;
            }
            if matches!(
                capture.access_kind,
                crate::sema::models::CaptureAccessKind::Mutate
            ) || matches!(
                capture.capture_kind,
                crate::sema::models::CaptureKind::ByRef { mutable: true }
            ) {
                kind = crate::sema::models::ClosureKind::AsyncFnMut;
            }
        }
        return kind;
    }

    let mut kind = crate::sema::models::ClosureKind::Fn;

    for capture in captures {
        match capture.access_kind {
            crate::sema::models::CaptureAccessKind::Move => {
                return if is_async {
                    crate::sema::models::ClosureKind::AsyncFnOnce
                } else {
                    crate::sema::models::ClosureKind::FnOnce
                };
            }
            crate::sema::models::CaptureAccessKind::Mutate => {
                kind = if is_async {
                    crate::sema::models::ClosureKind::AsyncFnMut
                } else {
                    crate::sema::models::ClosureKind::FnMut
                };
            }
            crate::sema::models::CaptureAccessKind::Read => {
                if matches!(
                    capture.capture_kind,
                    crate::sema::models::CaptureKind::ByRef { mutable: true }
                ) {
                    kind = if is_async {
                        crate::sema::models::ClosureKind::AsyncFnMut
                    } else {
                        crate::sema::models::ClosureKind::FnMut
                    };
                }
            }
        }
    }

    kind
}

fn closure_self_ty<'ctx>(
    gcx: Gcx<'ctx>,
    closure_ty: Ty<'ctx>,
    kind: crate::sema::models::ClosureKind,
) -> Ty<'ctx> {
    match kind {
        crate::sema::models::ClosureKind::Fn => {
            Ty::new(TyKind::Pointer(closure_ty, hir::Mutability::Immutable), gcx)
        }
        crate::sema::models::ClosureKind::AsyncFn => {
            let owns_copyable_environment = match closure_ty.kind() {
                TyKind::Closure { closure_def_id, .. } => gcx
                    .get_closure_captures(closure_def_id)
                    .is_some_and(|captures| {
                        captures.captures.iter().all(|capture| {
                            matches!(
                                capture.capture_kind,
                                crate::sema::models::CaptureKind::ByCopy
                            )
                        })
                    }),
                _ => false,
            };
            if owns_copyable_environment {
                closure_ty
            } else {
                Ty::new(TyKind::Pointer(closure_ty, hir::Mutability::Immutable), gcx)
            }
        }
        crate::sema::models::ClosureKind::FnMut | crate::sema::models::ClosureKind::AsyncFnMut => {
            Ty::new(TyKind::Pointer(closure_ty, hir::Mutability::Mutable), gcx)
        }
        crate::sema::models::ClosureKind::FnOnce
        | crate::sema::models::ClosureKind::AsyncFnOnce => closure_ty,
    }
}
