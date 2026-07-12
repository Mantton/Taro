use super::*;

impl<'ctx> Checker<'ctx> {
    pub(super) fn check_statement(&self, node: &hir::Statement, mut cs: Option<&mut Cs<'ctx>>) {
        match &node.kind {
            hir::StatementKind::Declaration(decl) => {
                self.check_local_declaration(decl);
            }
            hir::StatementKind::Expression(node) => {
                let ty = if let Some(cs) = cs.as_mut() {
                    let ty = self.synth_with_expectation(node, None, cs);
                    cs.infer_cx.resolve_vars_if_possible(ty)
                } else {
                    self.top_level_check(node, None)
                };
                self.warn_if_discarded_task(ty, node.span);
            }
            hir::StatementKind::Variable(node) => {
                if let Some(cs) = cs.as_mut() {
                    self.check_local_in_block(node, cs);
                } else {
                    self.check_local(node);
                }
            }
            hir::StatementKind::Loop { block, .. } => {
                self.check_loop(block, cs);
            }
            hir::StatementKind::Defer(block) => {
                self.check_defer(block, cs.as_deref_mut());
            }
            hir::StatementKind::Guard {
                condition,
                else_block,
            } => {
                self.check_guard(condition, else_block, cs.as_deref_mut());
            }
        }
    }

    fn warn_if_discarded_task(&self, ty: Ty<'ctx>, span: Span) {
        if self.task_inner_type(ty).is_some() {
            self.gcx().dcx().emit_warning(
                "unused Task is cancelled immediately; await `.result()`, call `.detach()`, or use `std.task.detached(...)` for explicit fire-and-forget work".into(),
                Some(span),
            );
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

        let Some(expectation) = self.return_ty.get() else {
            unreachable!("ICE: return check called outside function body")
        };

        if matches!(
            expectation.kind(),
            TyKind::Alias {
                kind: crate::sema::models::AliasKind::Opaque,
                def_id,
                ..
            } if def_id == self.current_def
        ) {
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
            TyKind::Pointer(inner, _) | TyKind::Reference(inner, _) => {
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
                let init_ty = self.synth_with_expectation(expression, Some(local_ty), &mut cs);
                if matches!(node.pattern.kind, hir::PatternKind::Wildcard) {
                    self.warn_if_discarded_task(
                        cs.infer_cx.resolve_vars_if_possible(init_ty),
                        expression.span,
                    );
                }
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

            let scrutinee_id = node.initializer.as_ref().map(|e| e.id).unwrap_or(node.id);
            self.check_pattern(&node.pattern, local_ty, scrutinee_id, &mut cs);
            cs.solve_all();

            self.commit_constraint_results(&cs);
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
            let init_ty = self.synth_with_expectation(expression, Some(local_ty), cs);
            if matches!(node.pattern.kind, hir::PatternKind::Wildcard) {
                self.warn_if_discarded_task(
                    cs.infer_cx.resolve_vars_if_possible(init_ty),
                    expression.span,
                );
            }
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

        let scrutinee_id = node.initializer.as_ref().map(|e| e.id).unwrap_or(node.id);
        self.check_pattern(&node.pattern, local_ty, scrutinee_id, cs);
    }

    pub(super) fn check_loop(&self, block: &hir::Block, mut cs: Option<&mut Cs<'ctx>>) {
        let depth = self.loop_depth.get();
        self.loop_depth.set(depth + 1);
        self.check_block(block, cs.as_deref_mut());
        self.loop_depth.set(depth);
    }

    pub(super) fn check_break(&self, span: Span) {
        if self.defer_depth.get() > 0 {
            self.gcx().dcx().emit_error(
                "`break` is not allowed inside a defer block".into(),
                Some(span),
            );
            return;
        }

        if self.loop_depth.get() == 0 {
            self.gcx()
                .dcx()
                .emit_error("`break` used outside of a loop".into(), Some(span));
        }
    }

    pub(super) fn check_continue(&self, span: Span) {
        if self.defer_depth.get() > 0 {
            self.gcx().dcx().emit_error(
                "`continue` is not allowed inside a defer block".into(),
                Some(span),
            );
            return;
        }

        if self.loop_depth.get() == 0 {
            self.gcx()
                .dcx()
                .emit_error("`continue` used outside of a loop".into(), Some(span));
        }
    }
}
