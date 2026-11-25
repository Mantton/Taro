use super::super::checker::{LoopBreakSite, LoopContext};
use super::*;

impl<'ctx> Checker<'ctx> {
    pub(super) fn check_statement(&self, node: &hir::Statement, mut cs: Option<&mut Cs<'ctx>>) {
        match &node.kind {
            hir::StatementKind::Declaration(decl) => {
                self.check_local_declaration(decl);
            }
            hir::StatementKind::Expression(node) => {
                if let Some(cs) = cs.as_mut() {
                    self.synth_with_expectation(node, None, cs);
                } else {
                    self.top_level_check(node, None);
                }
            }
            hir::StatementKind::Variable(node) => {
                if let Some(cs) = cs.as_mut() {
                    self.check_local_in_block(node, cs);
                } else {
                    self.check_local(node);
                }
            }
            hir::StatementKind::Loop { label, block } => {
                self.check_loop(label.map(|l| l.identifier.symbol), block, cs);
            }
            hir::StatementKind::Defer(_, block) => {
                self.check_defer(block, cs.as_deref_mut());
            }
            hir::StatementKind::Guard {
                condition,
                else_block,
            } => {
                self.check_guard(condition, else_block, cs.as_deref_mut());
            }
            hir::StatementKind::ComptimeFor {
                pattern,
                target_type,
                body,
            } => {
                self.check_comptime_for(node.id, pattern, target_type, body, cs.as_deref_mut());
            }
            hir::StatementKind::ComptimeIf {
                condition,
                then_block,
                else_block,
            } => {
                self.check_comptime_if(
                    node.id,
                    condition,
                    then_block,
                    else_block.as_ref(),
                    cs.as_deref_mut(),
                );
            }
        }
    }

    pub(super) fn check_local_declaration(&self, decl: &hir::Declaration) {
        match &decl.kind {
            hir::DeclarationKind::Function(node) => {
                let mut checker = Checker::new(self.context, decl.id, self.results.clone());
                checker.check_function(decl.id, node, hir::FunctionContext::Free);
            }
            hir::DeclarationKind::Constant(node) => {
                let mut checker = Checker::new(self.context, decl.id, self.results.clone());
                checker.check_constant(decl.id, node);
            }
            _ => {}
        }
    }

    pub(super) fn check_return(
        &self,
        expression: Option<&hir::Expression>,
        span: Span,
        mut cs: Option<&mut Cs<'ctx>>,
    ) {
        if self.defer_depth.get() > 0 {
            self.gcx().dcx().emit_error(
                "`return` is not allowed inside a defer block".into(),
                Some(span),
            );
        }

        if self.generator_element_ty.get().is_some() && expression.is_some() {
            self.gcx().dcx().emit_error(
                "generator functions cannot `return` a value; use `yield` to produce elements and bare `return` to finish"
                    .into(),
                Some(span),
            );
            if let Some(expr) = expression {
                if let Some(cs) = cs.as_deref_mut() {
                    let _ = self.synth_with_expectation(expr, None, cs);
                } else {
                    let _ = self.top_level_check(expr, None);
                }
            }
            return;
        }

        if let Some(cs) = cs.as_deref_mut()
            && self.has_active_deferred_return_scope()
        {
            let Some(expression) = expression else {
                let _ = self.deferred_return_hint(cs, span);
                self.record_deferred_return_site(None, self.gcx().types.void, span);
                return;
            };
            let return_var = self.deferred_return_hint(cs, expression.span);
            let provided = self.synth_with_expectation(expression, return_var, cs);
            self.record_deferred_return_site(Some(expression.id), provided, expression.span);
            return;
        }

        let Some(expectation) = self.return_ty.get() else {
            unreachable!("ICE: return check called outside function body")
        };

        if crate::sema::tycheck::opaque::is_owner_return(expectation, self.current_def) {
            let Some(expression) = expression else {
                self.gcx().dcx().emit_error(
                    "an opaque-returning function must return a value".into(),
                    Some(span),
                );
                self.opaque_return_candidates.borrow_mut().push(
                    crate::sema::tycheck::check::checker::OpaqueReturnCandidate {
                        ty: self.gcx().types.error,
                        infer_cx: None,
                        span,
                    },
                );
                return;
            };
            let (provided, infer_cx) = if let Some(cs) = cs.as_deref_mut() {
                (
                    self.synth_with_expectation(expression, None, cs),
                    Some(cs.infer_cx.clone()),
                )
            } else {
                (self.top_level_check(expression, None), None)
            };
            self.opaque_return_candidates.borrow_mut().push(
                crate::sema::tycheck::check::checker::OpaqueReturnCandidate {
                    ty: provided,
                    infer_cx,
                    span: expression.span,
                },
            );
            return;
        }

        let Some(expression) = expression else {
            return;
        };
        if let Some(cs) = cs.as_deref_mut() {
            let provided = self.synth_with_expectation(expression, Some(expectation), cs);
            cs.add_goal(
                Goal::Coerce {
                    node_id: expression.id,
                    from: provided,
                    to: expectation,
                },
                expression.span,
            );
        } else {
            self.top_level_check(expression, Some(expectation));
        }
    }

    pub(super) fn check_defer(&self, node: &hir::Block, mut cs: Option<&mut Cs<'ctx>>) {
        let depth = self.defer_depth.get();
        self.defer_depth.set(depth + 1);
        self.check_block(node, cs.as_deref_mut());
        self.defer_depth.set(depth);
    }

    pub(super) fn check_block(&self, node: &hir::Block, mut cs: Option<&mut Cs<'ctx>>) {
        for statement in &node.statements {
            self.check_statement(statement, cs.as_deref_mut());
        }
        if let Some(tail) = node.tail.as_deref() {
            if let Some(cs) = cs.as_deref_mut() {
                self.synth_with_expectation(tail, None, cs);
            } else {
                self.top_level_check(tail, None);
            }
        }
    }

    pub(super) fn check_guard(
        &self,
        condition: &hir::Expression,
        else_block: &hir::Block,
        mut cs: Option<&mut Cs<'ctx>>,
    ) {
        // Else block is not allowed to see bindings introduced by the guard condition.
        self.check_block(else_block, cs.as_deref_mut());

        if let Some(cs) = cs.as_deref_mut() {
            let cond_ty = self.synth(condition, cs);
            cs.equal(self.gcx().types.bool, cond_ty, condition.span);
        } else {
            self.top_level_check(condition, Some(self.gcx().types.bool));
        }
    }
    pub(super) fn check_opaque_type_usage(&self, ty: Ty<'ctx>, span: Span, behind_pointer: bool) {
        match ty.kind() {
            TyKind::Opaque(def_id) => {
                if !behind_pointer {
                    let ident = self.gcx().definition_ident(def_id);
                    self.gcx().dcx().emit_error(
                        format!(
                            "opaque type `{}` can only be used behind a pointer",
                            self.gcx().symbol_text(ident.symbol)
                        ),
                        Some(span),
                    );
                }
            }
            TyKind::Pointer(inner, _) | TyKind::Reference(inner) => {
                self.check_opaque_type_usage(inner, span, true);
            }
            TyKind::Tuple(items) => {
                for item in items.iter() {
                    self.check_opaque_type_usage(*item, span, false);
                }
            }
            TyKind::Array { element, .. } => {
                self.check_opaque_type_usage(element, span, false);
            }
            _ => {}
        }
    }

    fn check_async_local_initializer(
        &self,
        node: &hir::Local,
        local_ty: Ty<'ctx>,
        expression: &hir::Expression,
        cs: &mut Cs<'ctx>,
    ) {
        let gcx = self.gcx();
        if self.defer_depth.get() > 0 {
            gcx.dcx().emit_error(
                "`async var` is not allowed inside a defer block".into(),
                Some(node.pattern.span),
            );
        } else if self.async_depth.get() == 0 {
            gcx.dcx().emit_error(
                "`async var` can only be used inside an `async` function".into(),
                Some(node.pattern.span),
            );
        }
        let empty_inputs = gcx.store.interners.intern_ty_list(Vec::new());
        let closure_expectation = Ty::new(
            TyKind::FnPointer {
                inputs: empty_inputs,
                output: local_ty,
                effects: crate::sema::models::FunctionPointerEffects {
                    kind: crate::sema::models::ClosureKind::AsyncFn,
                    is_unsafe: false,
                    abi: None,
                },
            },
            gcx,
        );
        let closure_ty = self.synth_with_expectation(expression, Some(closure_expectation), cs);
        let resolved_closure = cs.infer_cx.resolve_vars_if_possible(closure_ty);
        if let TyKind::Closure { output, .. } = resolved_closure.kind() {
            cs.equal(output, local_ty, expression.span);
        }
        self.results
            .borrow_mut()
            .record_async_var_binding(node.pattern.id);
        self.async_var_closure_depths
            .borrow_mut()
            .insert(node.pattern.id, self.closure_depth.get());
    }

    pub(super) fn check_local(&self, node: &hir::Local) {
        let mut cs = self.new_cs();
        self.with_infer_ctx(cs.infer_cx.clone(), || {
            GatherLocalsVisitor::from_local(&cs, &self, node);
            let local_ty = self.get_local(node.id).ty;
            if let Some(annotation) = node.ty.as_deref() {
                self.check_opaque_type_usage(local_ty, annotation.span, false);
                self.add_type_constraints(local_ty, annotation.span, &mut cs);
            }

            if let Some(expression) = node.initializer.as_ref() {
                if node.is_async {
                    self.check_async_local_initializer(node, local_ty, expression, &mut cs);
                } else {
                    let init_ty = self.synth_with_expectation(expression, Some(local_ty), &mut cs);
                    if node.ty.is_none()
                        && matches!(node.pattern.kind, hir::PatternKind::Wildcard)
                        && matches!(
                            cs.infer_cx.resolve_vars_if_possible(init_ty).kind(),
                            TyKind::Never
                        )
                    {
                        cs.equal(local_ty, init_ty, expression.span);
                    } else {
                        cs.add_goal(
                            Goal::Coerce {
                                node_id: expression.id,
                                from: init_ty,
                                to: local_ty,
                            },
                            expression.span,
                        );
                    }
                }
            }

            let scrutinee_id = if node.is_async {
                node.id
            } else {
                node.initializer.as_ref().map(|e| e.id).unwrap_or(node.id)
            };
            self.check_local_pattern(&node.pattern, local_ty, scrutinee_id, &mut cs);
            self.finish_member_values(&mut cs);
            self.finish_enum_patterns(&mut cs);
            cs.solve_all();

            self.commit_constraint_results(&mut cs, node.initializer.as_deref());
        });
    }

    pub(super) fn check_local_in_block(&self, node: &hir::Local, cs: &mut Cs<'ctx>) {
        GatherLocalsVisitor::from_local(cs, self, node);
        let local_ty = self.get_local(node.id).ty;
        if let Some(annotation) = node.ty.as_deref() {
            self.check_opaque_type_usage(local_ty, annotation.span, false);
            self.add_type_constraints(local_ty, annotation.span, cs);
        }

        if let Some(expression) = node.initializer.as_ref() {
            if node.is_async {
                self.check_async_local_initializer(node, local_ty, expression, cs);
            } else {
                // A literal initializing an unannotated local is an array, as it is at
                // the top level of a body. Here the local's unknown type must not read as
                // a generic expectation, which would keep it open past the code that uses it.
                let expectation = (node.ty.is_some()
                    || !matches!(expression.kind, hir::ExpressionKind::Array(_)))
                .then_some(local_ty);
                let init_ty = self.synth_with_expectation(expression, expectation, cs);
                if node.ty.is_none()
                    && matches!(node.pattern.kind, hir::PatternKind::Wildcard)
                    && matches!(
                        cs.infer_cx.resolve_vars_if_possible(init_ty).kind(),
                        TyKind::Never
                    )
                {
                    cs.equal(local_ty, init_ty, expression.span);
                } else {
                    cs.add_goal(
                        Goal::Coerce {
                            node_id: expression.id,
                            from: init_ty,
                            to: local_ty,
                        },
                        expression.span,
                    );
                }
            }
        }

        let scrutinee_id = if node.is_async {
            node.id
        } else {
            node.initializer.as_ref().map(|e| e.id).unwrap_or(node.id)
        };
        self.check_local_pattern(&node.pattern, local_ty, scrutinee_id, cs);
    }

    pub(super) fn check_loop(
        &self,
        label: Option<crate::span::Symbol>,
        block: &hir::Block,
        mut cs: Option<&mut Cs<'ctx>>,
    ) {
        let depth = self.loop_depth.get();
        self.loop_depth.set(depth + 1);
        self.loop_stack.borrow_mut().push(LoopContext {
            label,
            allows_value_break: false,
            expected_ty: None,
            result_ty: None,
            breaks: Vec::new(),
        });
        self.check_block(block, cs.as_deref_mut());
        self.loop_stack.borrow_mut().pop();
        self.loop_depth.set(depth);
    }

    pub(super) fn synth_loop_expression(
        &self,
        expression: &hir::Expression,
        label: Option<hir::Label>,
        block: &hir::Block,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let loop_expectation = expectation.filter(|ty| !matches!(ty.kind(), TyKind::Never));

        let depth = self.loop_depth.get();
        self.loop_depth.set(depth + 1);
        self.loop_stack.borrow_mut().push(LoopContext {
            label: label.map(|l| l.identifier.symbol),
            allows_value_break: true,
            expected_ty: loop_expectation,
            result_ty: None,
            breaks: Vec::new(),
        });
        self.check_block(block, Some(cs));
        let ctx = self
            .loop_stack
            .borrow_mut()
            .pop()
            .expect("loop context balanced");
        self.loop_depth.set(depth);

        if ctx.breaks.is_empty() {
            return Ty::new(TyKind::Never, self.gcx());
        }

        let has_value_break = ctx.breaks.iter().any(|b| b.node_id.is_some());
        let has_valueless_break = ctx.breaks.iter().any(|b| b.node_id.is_none());

        if !has_value_break {
            return self.gcx().types.void;
        }

        if has_valueless_break {
            let mut mixed_error = false;
            for brk in &ctx.breaks {
                if brk.node_id.is_some()
                    && !brk.ty.is_error()
                    && cs.infer_cx.resolve_vars_if_possible(brk.ty) != self.gcx().types.void
                {
                    mixed_error = true;
                    break;
                }
            }
            if mixed_error {
                let bad_span = ctx
                    .breaks
                    .iter()
                    .find(|b| b.node_id.is_none())
                    .map(|b| b.span)
                    .unwrap_or(expression.span);
                self.gcx().dcx().emit_error(
                    "cannot mix valueless `break` and `break` with a value in the same `loop`"
                        .into(),
                    Some(bad_span),
                );
                return Ty::error(self.gcx());
            }
            return self.gcx().types.void;
        }

        if ctx.breaks.iter().any(|b| b.ty.is_error()) {
            return Ty::error(self.gcx());
        }

        if loop_expectation.is_none()
            && ctx.breaks.iter().all(|b| {
                matches!(
                    cs.infer_cx.resolve_vars_if_possible(b.ty).kind(),
                    TyKind::Never
                )
            })
        {
            return Ty::new(TyKind::Never, self.gcx());
        }

        let result_ty =
            loop_expectation.unwrap_or_else(|| cs.infer_cx.next_ty_var(expression.span));

        for brk in &ctx.breaks {
            if let Some(val_node_id) = brk.node_id {
                let resolved = cs.infer_cx.resolve_vars_if_possible(brk.ty);
                if loop_expectation.is_some() || matches!(resolved.kind(), TyKind::Never) {
                    cs.add_goal(
                        Goal::Coerce {
                            node_id: val_node_id,
                            from: brk.ty,
                            to: result_ty,
                        },
                        brk.span,
                    );
                } else {
                    cs.equal(result_ty, brk.ty, brk.span);
                }
            }
        }

        result_ty
    }

    pub(super) fn check_break(
        &self,
        label: Option<crate::span::Identifier>,
        value: Option<&hir::Expression>,
        span: Span,
        cs: &mut Cs<'ctx>,
    ) {
        if self.defer_depth.get() > 0 {
            self.gcx().dcx().emit_error(
                "`break` is not allowed inside a defer block".into(),
                Some(span),
            );
            return;
        }

        let target_info = {
            let stack = self.loop_stack.borrow();
            let target_idx = match label {
                Some(lbl) => stack.iter().rposition(|ctx| ctx.label == Some(lbl.symbol)),
                None => stack.len().checked_sub(1),
            };
            target_idx.map(|idx| {
                let ctx = &stack[idx];
                (idx, ctx.allows_value_break, ctx.expected_ty, ctx.result_ty)
            })
        };

        let Some((target_idx, allows_value_break, expected_ty, result_ty)) = target_info else {
            if let Some(lbl) = label {
                self.gcx().dcx().emit_error(
                    format!(
                        "unknown loop label `{}`",
                        self.gcx().symbol_text(lbl.symbol)
                    ),
                    Some(lbl.span),
                );
            } else {
                self.gcx()
                    .dcx()
                    .emit_error("`break` used outside of a loop".into(), Some(span));
            }
            if let Some(val_expr) = value {
                let _ = self.synth_with_expectation(val_expr, None, cs);
            }
            return;
        };

        if let Some(val_expr) = value {
            if !allows_value_break {
                self.gcx().dcx().emit_error(
                    "`break` with a value is only allowed in an unconditional `loop`".into(),
                    Some(span),
                );
                let _ = self.synth_with_expectation(val_expr, None, cs);
                return;
            }
            let break_expectation = expected_ty.or(result_ty);
            let val_ty = self.synth_with_expectation(val_expr, break_expectation, cs);
            let mut stack = self.loop_stack.borrow_mut();
            let ctx = &mut stack[target_idx];
            if ctx.result_ty.is_none()
                && !val_ty.is_error()
                && !matches!(
                    cs.infer_cx.resolve_vars_if_possible(val_ty).kind(),
                    TyKind::Never
                )
            {
                ctx.result_ty = Some(val_ty);
            }
            ctx.breaks.push(LoopBreakSite {
                node_id: Some(val_expr.id),
                ty: val_ty,
                span: val_expr.span,
            });
        } else {
            self.loop_stack.borrow_mut()[target_idx]
                .breaks
                .push(LoopBreakSite {
                    node_id: None,
                    ty: self.gcx().types.void,
                    span,
                });
        }
    }

    pub(super) fn check_continue(&self, label: Option<crate::span::Identifier>, span: Span) {
        if self.defer_depth.get() > 0 {
            self.gcx().dcx().emit_error(
                "`continue` is not allowed inside a defer block".into(),
                Some(span),
            );
            return;
        }

        let stack = self.loop_stack.borrow();
        let target_idx = match label {
            Some(lbl) => stack.iter().rposition(|ctx| ctx.label == Some(lbl.symbol)),
            None => stack.len().checked_sub(1),
        };
        if target_idx.is_none() {
            if let Some(lbl) = label {
                self.gcx().dcx().emit_error(
                    format!(
                        "unknown loop label `{}`",
                        self.gcx().symbol_text(lbl.symbol)
                    ),
                    Some(lbl.span),
                );
            } else {
                self.gcx()
                    .dcx()
                    .emit_error("`continue` used outside of a loop".into(), Some(span));
            }
        }
    }

    pub(super) fn check_comptime_for(
        &self,
        stmt_id: hir::NodeID,
        pattern: &hir::Pattern,
        target_type: &hir::Type,
        body: &hir::Block,
        mut cs: Option<&mut Cs<'ctx>>,
    ) {
        let gcx = self.gcx();
        let hir::PatternKind::Binding { .. } = pattern.kind else {
            gcx.dcx().emit_error(
                "`#for` requires a simple identifier pattern".into(),
                Some(pattern.span),
            );
            return;
        };
        let binding_id = pattern.id;

        let raw_ty = self.lower_type(target_type);
        if raw_ty.is_error() {
            return;
        }
        let target_ty = crate::sema::tycheck::utils::normalize_aliases(gcx, raw_ty);
        let TyKind::Adt(adt_def, _generic_args) = target_ty.kind() else {
            gcx.dcx().emit_error(
                format!(
                    "`#fields(...)` requires a struct or class type, found `{}`",
                    target_ty.format(gcx)
                ),
                Some(target_type.span),
            );
            return;
        };
        let Some(struct_def) = gcx.try_get_struct_definition(adt_def.id) else {
            gcx.dcx().emit_error(
                format!(
                    "`#fields(...)` requires a struct or class type, found `{}`",
                    target_ty.format(gcx)
                ),
                Some(target_type.span),
            );
            return;
        };

        let mut expanded_blocks = Vec::with_capacity(struct_def.fields.len());
        for (index, field) in struct_def.fields.iter().enumerate() {
            let subst = ComptimeFieldSubst {
                binding_id,
                name: field.name,
                key: field.coding_key.unwrap_or(field.name),
                skipped: field.coding_skip,
                index,
                is_public: matches!(
                    field.visibility,
                    crate::sema::resolve::models::Visibility::Public
                ),
                is_visible: gcx.is_visibility_allowed(field.visibility, self.current_def),
            };
            let mut cloner = ComptimeCloner::new(self, Some(subst), body);
            let expanded = cloner.clone_block(body);
            self.check_block(&expanded, cs.as_deref_mut());
            expanded_blocks.push(expanded);
        }

        self.results
            .borrow_mut()
            .comptime_expansions
            .insert(stmt_id, expanded_blocks);
    }

    pub(super) fn check_comptime_if(
        &self,
        stmt_id: hir::NodeID,
        condition: &hir::Expression,
        then_block: &hir::Block,
        else_block: Option<&hir::Block>,
        mut cs: Option<&mut Cs<'ctx>>,
    ) {
        let Some(cond_val) = self.eval_comptime_bool(condition) else {
            self.gcx().dcx().emit_error(
                "`#if` condition must evaluate to a compile-time boolean constant".into(),
                Some(condition.span),
            );
            return;
        };

        let mut expanded_blocks = Vec::new();
        if cond_val {
            self.check_block(then_block, cs.as_deref_mut());
            expanded_blocks.push(then_block.clone());
        } else if let Some(else_blk) = else_block {
            self.check_block(else_blk, cs.as_deref_mut());
            expanded_blocks.push(else_blk.clone());
        }

        self.results
            .borrow_mut()
            .comptime_expansions
            .insert(stmt_id, expanded_blocks);
    }

    fn eval_comptime_bool(&self, expr: &hir::Expression) -> Option<bool> {
        match self.eval_comptime_value(expr)? {
            ConstValue::Bool(b) => Some(b),
            _ => None,
        }
    }

    fn eval_comptime_value(&self, expr: &hir::Expression) -> Option<ConstValue> {
        match &expr.kind {
            hir::ExpressionKind::Literal(lit) => match lit {
                hir::Literal::Bool(b) => Some(ConstValue::Bool(*b)),
                hir::Literal::String(s) => Some(ConstValue::String(*s)),
                hir::Literal::Integer { value, .. } => Some(ConstValue::Integer(*value)),
                hir::Literal::Rune(r) => Some(ConstValue::Rune(*r)),
                _ => None,
            },
            hir::ExpressionKind::TypeName(ty_node) => {
                Some(ConstValue::String(self.resolve_type_name_symbol(ty_node)))
            }
            hir::ExpressionKind::Unary(op, inner) => match op {
                hir::UnaryOperator::BitwiseNot | hir::UnaryOperator::LogicalNot => {
                    match self.eval_comptime_value(inner)? {
                        ConstValue::Bool(b) => Some(ConstValue::Bool(!b)),
                        _ => None,
                    }
                }
                hir::UnaryOperator::Negate => match self.eval_comptime_value(inner)? {
                    ConstValue::Integer(v) => Some(ConstValue::Integer(-v)),
                    _ => None,
                },
            },
            hir::ExpressionKind::Binary(op, lhs, rhs) => match op {
                hir::BinaryOperator::BoolAnd => {
                    let l = self.eval_comptime_bool(lhs)?;
                    if !l {
                        return Some(ConstValue::Bool(false));
                    }
                    Some(ConstValue::Bool(self.eval_comptime_bool(rhs)?))
                }
                hir::BinaryOperator::BoolOr => {
                    let l = self.eval_comptime_bool(lhs)?;
                    if l {
                        return Some(ConstValue::Bool(true));
                    }
                    Some(ConstValue::Bool(self.eval_comptime_bool(rhs)?))
                }
                hir::BinaryOperator::Eql => {
                    let l = self.eval_comptime_value(lhs)?;
                    let r = self.eval_comptime_value(rhs)?;
                    Some(ConstValue::Bool(l == r))
                }
                hir::BinaryOperator::Neq => {
                    let l = self.eval_comptime_value(lhs)?;
                    let r = self.eval_comptime_value(rhs)?;
                    Some(ConstValue::Bool(l != r))
                }
                hir::BinaryOperator::Lt
                | hir::BinaryOperator::Leq
                | hir::BinaryOperator::Gt
                | hir::BinaryOperator::Geq => {
                    let ConstValue::Integer(l) = self.eval_comptime_value(lhs)? else {
                        return None;
                    };
                    let ConstValue::Integer(r) = self.eval_comptime_value(rhs)? else {
                        return None;
                    };
                    let res = match op {
                        hir::BinaryOperator::Lt => l < r,
                        hir::BinaryOperator::Leq => l <= r,
                        hir::BinaryOperator::Gt => l > r,
                        hir::BinaryOperator::Geq => l >= r,
                        _ => unreachable!(),
                    };
                    Some(ConstValue::Bool(res))
                }
                _ => None,
            },
            _ => {
                let ty = self.top_level_check(expr, None);
                if ty.is_error() {
                    return None;
                }
                let results = self.results.borrow();
                eval_const_expression_with_type_results(self.gcx(), expr, &results)
            }
        }
    }
}

#[derive(Clone, Copy)]
struct ComptimeFieldSubst {
    binding_id: hir::NodeID,
    name: Symbol,
    key: Symbol,
    skipped: bool,
    index: usize,
    is_public: bool,
    is_visible: bool,
}

struct CollectInnerBindings<'a, 'ctx> {
    checker: &'a Checker<'ctx>,
    skip_binding: Option<hir::NodeID>,
    local_remap: rustc_hash::FxHashMap<hir::NodeID, hir::NodeID>,
}

impl<'a, 'ctx> HirVisitor for CollectInnerBindings<'a, 'ctx> {
    fn visit_local(&mut self, node: &hir::Local) {
        self.local_remap
            .entry(node.id)
            .or_insert_with(|| self.checker.method_value_node());
        hir::walk_local(self, node);
    }

    fn visit_pattern(&mut self, node: &hir::Pattern) {
        if self.skip_binding != Some(node.id) {
            self.local_remap
                .entry(node.id)
                .or_insert_with(|| self.checker.method_value_node());
        }
        hir::walk_pattern(self, node);
    }
}

struct ComptimeCloner<'a, 'ctx> {
    checker: &'a Checker<'ctx>,
    subst: Option<ComptimeFieldSubst>,
    local_remap: rustc_hash::FxHashMap<hir::NodeID, hir::NodeID>,
    node_remap: rustc_hash::FxHashMap<hir::NodeID, hir::NodeID>,
}

impl<'a, 'ctx> ComptimeCloner<'a, 'ctx> {
    fn new(
        checker: &'a Checker<'ctx>,
        subst: Option<ComptimeFieldSubst>,
        root: &hir::Block,
    ) -> Self {
        let mut collector = CollectInnerBindings {
            checker,
            skip_binding: subst.map(|s| s.binding_id),
            local_remap: rustc_hash::FxHashMap::default(),
        };
        hir::walk_block(&mut collector, root);
        let node_remap = collector.local_remap.clone();
        Self {
            checker,
            subst,
            local_remap: collector.local_remap,
            node_remap,
        }
    }

    fn remap_id(&mut self, id: hir::NodeID) -> hir::NodeID {
        let checker = self.checker;
        *self
            .node_remap
            .entry(id)
            .or_insert_with(|| checker.method_value_node())
    }

    fn remap_resolution(&self, res: &hir::Resolution) -> hir::Resolution {
        match res {
            hir::Resolution::LocalVariable(id) => {
                if let Some(&new_id) = self.local_remap.get(id) {
                    hir::Resolution::LocalVariable(new_id)
                } else {
                    hir::Resolution::LocalVariable(*id)
                }
            }
            other => other.clone(),
        }
    }

    fn is_subst_binding(&self, expr: &hir::Expression) -> bool {
        let Some(subst) = self.subst else {
            return false;
        };
        matches!(
            &expr.kind,
            hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path))
                if path.resolution == hir::Resolution::LocalVariable(subst.binding_id)
        )
    }

    fn clone_block(&mut self, block: &hir::Block) -> hir::Block {
        hir::Block {
            id: self.remap_id(block.id),
            statements: block
                .statements
                .iter()
                .map(|s| self.clone_statement(s))
                .collect(),
            tail: block
                .tail
                .as_ref()
                .map(|e| Box::new(self.clone_expression(e))),
            span: block.span,
        }
    }

    fn clone_statement(&mut self, stmt: &hir::Statement) -> hir::Statement {
        let id = self.remap_id(stmt.id);
        let kind = match &stmt.kind {
            hir::StatementKind::Declaration(decl) => {
                hir::StatementKind::Declaration(decl.clone())
            }
            hir::StatementKind::Expression(expr) => {
                hir::StatementKind::Expression(Box::new(self.clone_expression(expr)))
            }
            hir::StatementKind::Variable(local) => {
                hir::StatementKind::Variable(self.clone_local(local))
            }
            hir::StatementKind::Loop { label, block } => hir::StatementKind::Loop {
                label: *label,
                block: self.clone_block(block),
            },
            hir::StatementKind::Defer(kind, block) => {
                hir::StatementKind::Defer(*kind, self.clone_block(block))
            }
            hir::StatementKind::Guard {
                condition,
                else_block,
            } => hir::StatementKind::Guard {
                condition: Box::new(self.clone_expression(condition)),
                else_block: self.clone_block(else_block),
            },
            hir::StatementKind::ComptimeFor {
                pattern,
                target_type,
                body,
            } => hir::StatementKind::ComptimeFor {
                pattern: self.clone_pattern(pattern),
                target_type: Box::new(self.clone_type(target_type)),
                body: self.clone_block(body),
            },
            hir::StatementKind::ComptimeIf {
                condition,
                then_block,
                else_block,
            } => hir::StatementKind::ComptimeIf {
                condition: Box::new(self.clone_expression(condition)),
                then_block: self.clone_block(then_block),
                else_block: else_block.as_ref().map(|b| self.clone_block(b)),
            },
        };
        hir::Statement {
            id,
            kind,
            span: stmt.span,
        }
    }

    fn clone_local(&mut self, local: &hir::Local) -> hir::Local {
        hir::Local {
            id: self.remap_id(local.id),
            pattern: self.clone_pattern(&local.pattern),
            mutability: local.mutability,
            is_async: local.is_async,
            ty: local.ty.as_ref().map(|t| Box::new(self.clone_type(t))),
            initializer: local
                .initializer
                .as_ref()
                .map(|e| Box::new(self.clone_expression(e))),
        }
    }

    fn clone_pattern(&mut self, pat: &hir::Pattern) -> hir::Pattern {
        let id = self.remap_id(pat.id);
        let kind = match &pat.kind {
            hir::PatternKind::Wildcard => hir::PatternKind::Wildcard,
            hir::PatternKind::Rest => hir::PatternKind::Rest,
            hir::PatternKind::Binding { name } => hir::PatternKind::Binding { name: *name },
            hir::PatternKind::Tuple(parts, span) => hir::PatternKind::Tuple(
                parts.iter().map(|p| self.clone_pattern(p)).collect(),
                *span,
            ),
            hir::PatternKind::Member(cp) => {
                hir::PatternKind::Member(self.clone_constructor_path(cp))
            }
            hir::PatternKind::PathTuple {
                path,
                fields,
                field_span,
            } => hir::PatternKind::PathTuple {
                path: self.clone_constructor_path(path),
                fields: fields.iter().map(|p| self.clone_pattern(p)).collect(),
                field_span: *field_span,
            },
            hir::PatternKind::PathNamed {
                path,
                fields,
                rest,
                field_span,
            } => hir::PatternKind::PathNamed {
                path: self.clone_constructor_path(path),
                fields: fields
                    .iter()
                    .map(|f| hir::NamedPatternField {
                        name: f.name,
                        pattern: self.clone_pattern(&f.pattern),
                    })
                    .collect(),
                rest: *rest,
                field_span: *field_span,
            },
            hir::PatternKind::At { binding, pattern } => hir::PatternKind::At {
                binding: Box::new(self.clone_pattern(binding)),
                pattern: Box::new(self.clone_pattern(pattern)),
            },
            hir::PatternKind::TypeTest { target, binding } => hir::PatternKind::TypeTest {
                target: Box::new(self.clone_type(target)),
                binding: binding.as_ref().map(|p| Box::new(self.clone_pattern(p))),
            },
            hir::PatternKind::Range {
                start,
                end,
                inclusive,
            } => hir::PatternKind::Range {
                start: Box::new(self.clone_expression(start)),
                end: Box::new(self.clone_expression(end)),
                inclusive: *inclusive,
            },
            hir::PatternKind::Or(parts, span) => hir::PatternKind::Or(
                parts.iter().map(|p| self.clone_pattern(p)).collect(),
                *span,
            ),
            hir::PatternKind::Literal { value } => hir::PatternKind::Literal {
                value: value.clone(),
            },
        };
        hir::Pattern {
            id,
            span: pat.span,
            kind,
        }
    }

    fn clone_constructor_path(&mut self, cp: &hir::ConstructorPath) -> hir::ConstructorPath {
        match cp {
            hir::ConstructorPath::Qualified { path } => hir::ConstructorPath::Qualified {
                path: self.clone_resolved_path(path),
            },
            hir::ConstructorPath::Inferred { name, span } => hir::ConstructorPath::Inferred {
                name: *name,
                span: *span,
            },
        }
    }

    fn clone_resolved_path(&mut self, rp: &hir::ResolvedPath) -> hir::ResolvedPath {
        match rp {
            hir::ResolvedPath::Resolved(p) => hir::ResolvedPath::Resolved(self.clone_path(p)),
            hir::ResolvedPath::Relative(ty, seg) => {
                hir::ResolvedPath::Relative(Box::new(self.clone_type(ty)), self.clone_segment(seg))
            }
        }
    }

    fn clone_path(&mut self, path: &hir::Path) -> hir::Path {
        hir::Path {
            span: path.span,
            resolution: self.remap_resolution(&path.resolution),
            segments: path.segments.iter().map(|s| self.clone_segment(s)).collect(),
        }
    }

    fn clone_segment(&mut self, seg: &hir::PathSegment) -> hir::PathSegment {
        hir::PathSegment {
            id: self.remap_id(seg.id),
            identifier: seg.identifier,
            arguments: seg
                .arguments
                .as_ref()
                .map(|args| self.clone_type_arguments(args)),
            span: seg.span,
            resolution: self.remap_resolution(&seg.resolution),
        }
    }

    fn clone_path_node(&mut self, pn: &hir::PathNode) -> hir::PathNode {
        hir::PathNode {
            id: self.remap_id(pn.id),
            path: self.clone_resolved_path(&pn.path),
            span: pn.span,
        }
    }

    fn clone_type_arguments(&mut self, args: &hir::TypeArguments) -> hir::TypeArguments {
        hir::TypeArguments {
            span: args.span,
            arguments: args
                .arguments
                .iter()
                .map(|arg| match arg {
                    hir::TypeArgument::Type(ty) => {
                        hir::TypeArgument::Type(Box::new(self.clone_type(ty)))
                    }
                    hir::TypeArgument::Const(c) => hir::TypeArgument::Const(hir::AnonConst {
                        value: Box::new(self.clone_expression(&c.value)),
                    }),
                    hir::TypeArgument::AssociatedType(ident, ty) => {
                        hir::TypeArgument::AssociatedType(*ident, Box::new(self.clone_type(ty)))
                    }
                })
                .collect(),
        }
    }

    fn clone_type(&mut self, ty: &hir::Type) -> hir::Type {
        let id = self.remap_id(ty.id);
        let kind = match &ty.kind {
            hir::TypeKind::Nominal(rp) => hir::TypeKind::Nominal(self.clone_resolved_path(rp)),
            hir::TypeKind::Pointer(inner, m) => {
                hir::TypeKind::Pointer(Box::new(self.clone_type(inner)), *m)
            }
            hir::TypeKind::Reference(inner) => {
                hir::TypeKind::Reference(Box::new(self.clone_type(inner)))
            }
            hir::TypeKind::Tuple(tys, labels) => hir::TypeKind::Tuple(
                tys.iter().map(|t| Box::new(self.clone_type(t))).collect(),
                labels.clone(),
            ),
            hir::TypeKind::Array { size, element } => hir::TypeKind::Array {
                size: hir::AnonConst {
                    value: Box::new(self.clone_expression(&size.value)),
                },
                element: Box::new(self.clone_type(element)),
            },
            hir::TypeKind::Function { inputs, output } => hir::TypeKind::Function {
                inputs: inputs
                    .iter()
                    .map(|t| Box::new(self.clone_type(t)))
                    .collect(),
                output: Box::new(self.clone_type(output)),
            },
            hir::TypeKind::BoxedExistential { interfaces } => hir::TypeKind::BoxedExistential {
                interfaces: interfaces
                    .iter()
                    .map(|pn| self.clone_path_node(pn))
                    .collect(),
            },
            hir::TypeKind::ImplTrait { interfaces } => hir::TypeKind::ImplTrait {
                interfaces: interfaces
                    .iter()
                    .map(|pn| self.clone_path_node(pn))
                    .collect(),
            },
            hir::TypeKind::QualifiedAccess {
                target,
                interface,
                member,
            } => hir::TypeKind::QualifiedAccess {
                target: Box::new(self.clone_type(target)),
                interface: Box::new(self.clone_type(interface)),
                member: *member,
            },
            hir::TypeKind::Infer => hir::TypeKind::Infer,
            hir::TypeKind::Never => hir::TypeKind::Never,
        };
        hir::Type {
            id,
            span: ty.span,
            kind,
        }
    }

    fn clone_expression_arg(&mut self, arg: &hir::ExpressionArgument) -> hir::ExpressionArgument {
        hir::ExpressionArgument {
            label: arg.label,
            expression: Box::new(self.clone_expression(&arg.expression)),
            span: arg.span,
        }
    }

    fn subst_field_method_call(
        &mut self,
        id: hir::NodeID,
        span: Span,
        name: crate::span::Identifier,
        arguments: &[hir::ExpressionArgument],
        subst: ComptimeFieldSubst,
    ) -> hir::Expression {
        let gcx = self.checker.gcx();
        if gcx.symbol_eq(name.symbol, "get") {
            if arguments.len() != 1 {
                gcx.dcx().emit_error(
                    "`field.get(...)` expects exactly 1 receiver argument".into(),
                    Some(span),
                );
                return hir::Expression {
                    id,
                    span,
                    kind: hir::ExpressionKind::Literal(hir::Literal::Nil),
                };
            }
            let target = self.clone_expression(&arguments[0].expression);
            return hir::Expression {
                id,
                span,
                kind: hir::ExpressionKind::Member {
                    target: Box::new(target),
                    name: crate::span::Identifier {
                        symbol: subst.name,
                        span: name.span,
                    },
                },
            };
        }
        gcx.dcx().emit_error(
            format!(
                "unknown compile-time field method `{}`; expected `get(receiver)`",
                gcx.symbol_text(name.symbol)
            ),
            Some(name.span),
        );
        hir::Expression {
            id,
            span,
            kind: hir::ExpressionKind::Literal(hir::Literal::Nil),
        }
    }

    fn subst_field_property(
        &self,
        id: hir::NodeID,
        span: Span,
        name: crate::span::Identifier,
        subst: ComptimeFieldSubst,
    ) -> hir::Expression {
        let gcx = self.checker.gcx();
        let lit = if gcx.symbol_eq(name.symbol, "name") {
            hir::Literal::String(subst.name)
        } else if gcx.symbol_eq(name.symbol, "key") {
            hir::Literal::String(subst.key)
        } else if gcx.symbol_eq(name.symbol, "skipped") {
            hir::Literal::Bool(subst.skipped)
        } else if gcx.symbol_eq(name.symbol, "index") {
            hir::Literal::Integer {
                value: subst.index as i128,
                suffix: None,
            }
        } else if gcx.symbol_eq(name.symbol, "isPublic") {
            hir::Literal::Bool(subst.is_public)
        } else if gcx.symbol_eq(name.symbol, "isVisible") {
            hir::Literal::Bool(subst.is_visible)
        } else {
            gcx.dcx().emit_error(
                format!(
                    "unknown compile-time field property `{}`; expected `name`, `key`, `skipped`, `index`, `isPublic`, `isVisible`, or `get(receiver)`",
                    gcx.symbol_text(name.symbol)
                ),
                Some(name.span),
            );
            hir::Literal::Bool(false)
        };
        hir::Expression {
            id,
            span,
            kind: hir::ExpressionKind::Literal(lit),
        }
    }

    fn clone_expression(&mut self, expr: &hir::Expression) -> hir::Expression {
        let id = self.remap_id(expr.id);
        if let Some(subst) = self.subst {
            match &expr.kind {
                hir::ExpressionKind::MethodCall {
                    receiver,
                    name,
                    arguments,
                    ..
                } if self.is_subst_binding(receiver) => {
                    return self.subst_field_method_call(id, expr.span, *name, arguments, subst);
                }
                hir::ExpressionKind::Call { callee, arguments } => {
                    if let hir::ExpressionKind::Member { target, name } = &callee.kind
                        && self.is_subst_binding(target)
                    {
                        return self.subst_field_method_call(
                            id, expr.span, *name, arguments, subst,
                        );
                    }
                }
                hir::ExpressionKind::Member { target, name } if self.is_subst_binding(target) => {
                    return self.subst_field_property(id, expr.span, *name, subst);
                }
                _ if self.is_subst_binding(expr) => {
                    self.checker.gcx().dcx().emit_error(
                        "`#for` field binding can only be used with `.name`, `.key`, `.skipped`, `.index`, `.isPublic`, `.isVisible`, or `.get(receiver)`".into(),
                        Some(expr.span),
                    );
                    return hir::Expression {
                        id,
                        span: expr.span,
                        kind: hir::ExpressionKind::Literal(hir::Literal::String(subst.name)),
                    };
                }
                _ => {}
            }
        }

        let kind = match &expr.kind {
            hir::ExpressionKind::Literal(lit) => hir::ExpressionKind::Literal(lit.clone()),
            hir::ExpressionKind::Path(rp) => {
                hir::ExpressionKind::Path(self.clone_resolved_path(rp))
            }
            hir::ExpressionKind::Member { target, name } => hir::ExpressionKind::Member {
                target: Box::new(self.clone_expression(target)),
                name: *name,
            },
            hir::ExpressionKind::MissingMember { target, insertion } => {
                hir::ExpressionKind::MissingMember {
                    target: Box::new(self.clone_expression(target)),
                    insertion: *insertion,
                }
            }
            hir::ExpressionKind::MemberBrackets {
                member,
                type_arguments,
                indexed,
                diagnostics,
            } => hir::ExpressionKind::MemberBrackets {
                member: Box::new(self.clone_expression(member)),
                type_arguments: self.clone_type_arguments(type_arguments),
                indexed: indexed
                    .as_ref()
                    .map(|e| Box::new(self.clone_expression(e))),
                diagnostics: diagnostics.clone(),
            },
            hir::ExpressionKind::Index {
                target,
                index,
                nodes,
            } => hir::ExpressionKind::Index {
                target: Box::new(self.clone_expression(target)),
                index: index
                    .iter()
                    .map(|a| self.clone_expression_arg(a))
                    .collect(),
                nodes: hir::IndexCallNodes {
                    call: self.remap_id(nodes.call),
                    receiver: self.remap_id(nodes.receiver),
                },
            },
            hir::ExpressionKind::InferredMember { name } => {
                hir::ExpressionKind::InferredMember { name: *name }
            }
            hir::ExpressionKind::Array(items) => hir::ExpressionKind::Array(
                items
                    .iter()
                    .map(|e| Box::new(self.clone_expression(e)))
                    .collect(),
            ),
            hir::ExpressionKind::Spread(inner) => {
                hir::ExpressionKind::Spread(Box::new(self.clone_expression(inner)))
            }
            hir::ExpressionKind::Repeat { value, count } => hir::ExpressionKind::Repeat {
                value: Box::new(self.clone_expression(value)),
                count: hir::AnonConst {
                    value: Box::new(self.clone_expression(&count.value)),
                },
            },
            hir::ExpressionKind::Tuple(items, labels) => hir::ExpressionKind::Tuple(
                items
                    .iter()
                    .map(|e| Box::new(self.clone_expression(e)))
                    .collect(),
                labels.clone(),
            ),
            hir::ExpressionKind::Discard => hir::ExpressionKind::Discard,
            hir::ExpressionKind::If(if_expr) => hir::ExpressionKind::If(hir::IfExpression {
                condition: Box::new(self.clone_expression(&if_expr.condition)),
                then_block: Box::new(self.clone_expression(&if_expr.then_block)),
                else_block: if_expr
                    .else_block
                    .as_ref()
                    .map(|e| Box::new(self.clone_expression(e))),
            }),
            hir::ExpressionKind::Match(m) => hir::ExpressionKind::Match(hir::MatchExpression {
                source: m.source,
                value: Box::new(self.clone_expression(&m.value)),
                arms: m
                    .arms
                    .iter()
                    .map(|arm| hir::MatchArm {
                        pattern: self.clone_pattern(&arm.pattern),
                        body: Box::new(self.clone_expression(&arm.body)),
                        guard: arm
                            .guard
                            .as_ref()
                            .map(|g| Box::new(self.clone_expression(g))),
                        span: arm.span,
                    })
                    .collect(),
                kw_span: m.kw_span,
            }),
            hir::ExpressionKind::Select(s) => hir::ExpressionKind::Select(hir::SelectExpression {
                arms: s
                    .arms
                    .iter()
                    .map(|arm| hir::SelectArm {
                        pattern: self.clone_pattern(&arm.pattern),
                        operation: Box::new(self.clone_expression(&arm.operation)),
                        body: Box::new(self.clone_expression(&arm.body)),
                        span: arm.span,
                    })
                    .collect(),
                kw_span: s.kw_span,
            }),
            hir::ExpressionKind::Loop { label, block } => hir::ExpressionKind::Loop {
                label: *label,
                block: self.clone_block(block),
            },
            hir::ExpressionKind::Return { value } => hir::ExpressionKind::Return {
                value: value.as_ref().map(|e| Box::new(self.clone_expression(e))),
            },
            hir::ExpressionKind::Break { label, value } => hir::ExpressionKind::Break {
                label: *label,
                value: value.as_ref().map(|e| Box::new(self.clone_expression(e))),
            },
            hir::ExpressionKind::Continue { label } => {
                hir::ExpressionKind::Continue { label: *label }
            }
            hir::ExpressionKind::Call { callee, arguments } => hir::ExpressionKind::Call {
                callee: Box::new(self.clone_expression(callee)),
                arguments: arguments
                    .iter()
                    .map(|a| self.clone_expression_arg(a))
                    .collect(),
            },
            hir::ExpressionKind::MethodCall {
                interface,
                receiver,
                name,
                arguments,
            } => hir::ExpressionKind::MethodCall {
                interface: *interface,
                receiver: Box::new(self.clone_expression(receiver)),
                name: *name,
                arguments: arguments
                    .iter()
                    .map(|a| self.clone_expression_arg(a))
                    .collect(),
            },
            hir::ExpressionKind::Reference(inner) => {
                hir::ExpressionKind::Reference(Box::new(self.clone_expression(inner)))
            }
            hir::ExpressionKind::Dereference(inner) => {
                hir::ExpressionKind::Dereference(Box::new(self.clone_expression(inner)))
            }
            hir::ExpressionKind::Binary(op, lhs, rhs) => hir::ExpressionKind::Binary(
                *op,
                Box::new(self.clone_expression(lhs)),
                Box::new(self.clone_expression(rhs)),
            ),
            hir::ExpressionKind::Unary(op, inner) => {
                hir::ExpressionKind::Unary(*op, Box::new(self.clone_expression(inner)))
            }
            hir::ExpressionKind::TupleAccess(inner, idx) => hir::ExpressionKind::TupleAccess(
                Box::new(self.clone_expression(inner)),
                hir::AnonConst {
                    value: Box::new(self.clone_expression(&idx.value)),
                },
            ),
            hir::ExpressionKind::AssignOp(op, lhs, rhs) => hir::ExpressionKind::AssignOp(
                *op,
                Box::new(self.clone_expression(lhs)),
                Box::new(self.clone_expression(rhs)),
            ),
            hir::ExpressionKind::Assign(lhs, rhs) => hir::ExpressionKind::Assign(
                Box::new(self.clone_expression(lhs)),
                Box::new(self.clone_expression(rhs)),
            ),
            hir::ExpressionKind::AssignOptional(lhs, rhs) => hir::ExpressionKind::AssignOptional(
                Box::new(self.clone_expression(lhs)),
                Box::new(self.clone_expression(rhs)),
            ),
            hir::ExpressionKind::CastAs(inner, ty) => hir::ExpressionKind::CastAs(
                Box::new(self.clone_expression(inner)),
                Box::new(self.clone_type(ty)),
            ),
            hir::ExpressionKind::CastAsTry(inner, ty) => hir::ExpressionKind::CastAsTry(
                Box::new(self.clone_expression(inner)),
                Box::new(self.clone_type(ty)),
            ),
            hir::ExpressionKind::TypeIs(inner, ty) => hir::ExpressionKind::TypeIs(
                Box::new(self.clone_expression(inner)),
                Box::new(self.clone_type(ty)),
            ),
            hir::ExpressionKind::PatternBinding(cond) => {
                hir::ExpressionKind::PatternBinding(hir::PatternBindingCondition {
                    source: cond.source,
                    pattern: self.clone_pattern(&cond.pattern),
                    expression: Box::new(self.clone_expression(&cond.expression)),
                    span: cond.span,
                })
            }
            hir::ExpressionKind::Block(b) => hir::ExpressionKind::Block(self.clone_block(b)),
            hir::ExpressionKind::UnsafeBlock(b) => {
                hir::ExpressionKind::UnsafeBlock(self.clone_block(b))
            }
            hir::ExpressionKind::Propagate(inner) => {
                hir::ExpressionKind::Propagate(Box::new(self.clone_expression(inner)))
            }
            hir::ExpressionKind::StructLiteral(lit) => {
                hir::ExpressionKind::StructLiteral(hir::StructLiteral {
                    path: self.clone_constructor_path(&lit.path),
                    fields: lit
                        .fields
                        .iter()
                        .map(|f| hir::ExpressionField {
                            label: f.label,
                            expression: Box::new(self.clone_expression(&f.expression)),
                            span: f.span,
                        })
                        .collect(),
                    base: lit
                        .base
                        .as_ref()
                        .map(|b| Box::new(self.clone_expression(b))),
                })
            }
            hir::ExpressionKind::Closure(c) => hir::ExpressionKind::Closure(hir::ClosureExpr {
                def_id: self
                    .checker
                    .gcx()
                    .allocate_synthetic_id(self.checker.current_def.package()),
                params: c
                    .params
                    .iter()
                    .map(|p| hir::ClosureParam {
                        id: self.remap_id(p.id),
                        pattern: self.clone_pattern(&p.pattern),
                        ty: p.ty.as_ref().map(|t| Box::new(self.clone_type(t))),
                        span: p.span,
                    })
                    .collect(),
                return_ty: c.return_ty.as_ref().map(|t| Box::new(self.clone_type(t))),
                is_async: c.is_async,
                implicit_await: c.implicit_await,
                body: Box::new(self.clone_expression(&c.body)),
                snapshot_captures: c.snapshot_captures,
                span: c.span,
            }),
            hir::ExpressionKind::Await(inner) => {
                hir::ExpressionKind::Await(Box::new(self.clone_expression(inner)))
            }
            hir::ExpressionKind::Yield(inner) => {
                hir::ExpressionKind::Yield(Box::new(self.clone_expression(inner)))
            }
            hir::ExpressionKind::TypeName(ty) => {
                hir::ExpressionKind::TypeName(Box::new(self.clone_type(ty)))
            }
            hir::ExpressionKind::Malformed => hir::ExpressionKind::Malformed,
        };

        hir::Expression {
            id,
            kind,
            span: expr.span,
        }
    }
}
