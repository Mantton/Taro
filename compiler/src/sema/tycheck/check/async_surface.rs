use super::*;

impl<'ctx> Checker<'ctx> {
    pub(super) fn synth_await_expression(
        &self,
        inner: &hir::Expression,
        span: Span,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let gcx = self.gcx();

        if matches!(inner.kind, hir::ExpressionKind::Propagate(_)) {
            gcx.dcx().emit_error(
                "use `(await expr)!` to propagate an awaited Optional or Result".into(),
                Some(span),
            );
            return Ty::error(gcx);
        }

        if self.defer_depth.get() > 0 {
            gcx.dcx().emit_error(
                "`await` is not allowed inside a defer block".into(),
                Some(span),
            );
            return Ty::error(gcx);
        }

        // await is only valid inside an async context
        if self.async_depth.get() == 0 {
            gcx.dcx().emit_error(
                "`await` can only be used inside an `async` function".into(),
                Some(span),
            );
            return Ty::error(gcx);
        }

        let future_ty = self.with_direct_await_operand(inner.id, || self.synth(inner, cs));
        if future_ty.is_error() {
            return Ty::error(gcx);
        }
        cs.solve_intermediate();
        let future_ty = cs.infer_cx.resolve_vars_if_possible(future_ty);

        if self.results.borrow().is_async_call(inner.id) {
            return future_ty;
        }

        if matches!(
            self.resolved_async_call_status(inner.id, Some(cs)),
            Some(true)
        ) {
            return future_ty;
        }

        if self.task_inner_type(future_ty).is_some() {
            gcx.dcx().emit_error(
                "use `await task.result()` to await a `Task[T]`".into(),
                Some(span),
            );
            return Ty::error(gcx);
        }

        gcx.dcx()
            .emit_error("`await` expects an async call".into(), Some(span));
        Ty::error(gcx)
    }

    pub(super) fn synth_propagate_expression(
        &self,
        expression: &hir::Expression,
        inner: &hir::Expression,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let gcx = self.gcx();

        if self.defer_depth.get() > 0 {
            gcx.dcx().emit_error(
                "`!` is not allowed inside a defer block".into(),
                Some(expression.span),
            );
            return Ty::error(gcx);
        }

        let operand_ty = self.synth(inner, cs);
        if operand_ty.is_error() {
            return Ty::error(gcx);
        }
        cs.solve_intermediate();

        // Propagation compares the concrete error contracts, not their
        // unresolved associated-type spelling. Use the same structural
        // normalization as coercion so conditional generic witnesses can turn
        // `Concrete[T].Error` into the implementation's declared error type.
        let operand_ty = cs.structurally_resolve(operand_ty);
        let Some(return_ty) = self.return_ty.get() else {
            gcx.dcx().emit_error(
                "postfix `!` requires an enclosing Optional or Result return type".into(),
                Some(expression.span),
            );
            return Ty::error(gcx);
        };
        let return_ty = cs.structurally_resolve(return_ty);

        if let Some((_, inner_ty)) = self.optional_inner_type(operand_ty) {
            if self.is_optional_type(return_ty) {
                return inner_ty;
            }

            gcx.dcx().emit_error(
                format!(
                    "Optional propagation requires an enclosing Optional return type, found '{}'",
                    return_ty.format(gcx)
                )
                .into(),
                Some(expression.span),
            );
            return Ty::error(gcx);
        }

        if let Some((_, ok_ty, err_ty)) = self.result_inner_types(operand_ty) {
            let Some((_, _, return_err_ty)) = self.result_inner_types(return_ty) else {
                gcx.dcx().emit_error(
                    format!(
                        "Result propagation requires an enclosing Result return type, found '{}'",
                        return_ty.format(gcx)
                    )
                    .into(),
                    Some(expression.span),
                );
                return Ty::error(gcx);
            };

            let resolved_return_err = cs.structurally_resolve(return_err_ty);
            let resolved_operand_err = cs.structurally_resolve(err_ty);
            if resolved_return_err.is_infer() || resolved_operand_err.is_infer() {
                cs.equal(return_err_ty, err_ty, expression.span);
                return ok_ty;
            }

            if resolved_return_err == resolved_operand_err {
                return ok_ty;
            }

            let Some(from_id) = gcx.std_item_def(hir::StdItem::From) else {
                gcx.dcx().emit_error(
                    "Result error conversion requires the standard library From interface".into(),
                    Some(expression.span),
                );
                return Ty::error(gcx);
            };
            let Some(from_method_id) =
                gcx.get_interface_requirements(from_id)
                    .and_then(|requirements| {
                        requirements.methods.iter().find_map(|method| {
                            (gcx.symbol_text(method.name) == "from" && !method.has_self)
                                .then_some(method.id)
                        })
                    })
            else {
                gcx.dcx().emit_error(
                    "standard library From interface is missing its static from method".into(),
                    Some(expression.span),
                );
                return Ty::error(gcx);
            };

            let generic_args = gcx.store.interners.intern_generic_args(vec![
                GenericArgument::Type(resolved_return_err),
                GenericArgument::Type(resolved_operand_err),
            ]);
            let interface = InterfaceReference {
                id: from_id,
                arguments: generic_args,
                bindings: &[],
            };
            cs.add_goal(
                Goal::Conforms {
                    ty: resolved_return_err,
                    interface,
                },
                expression.span,
            );
            self.results
                .borrow_mut()
                .record_result_propagation_conversion(
                    expression.id,
                    crate::sema::tycheck::results::ResultPropagationConversion {
                        method_id: from_method_id,
                        generic_args,
                        target_ty: resolved_return_err,
                    },
                );
            return ok_ty;
        }

        gcx.dcx().emit_error(
            format!(
                "postfix `!` requires an Optional or Result value, found '{}'",
                operand_ty.format(gcx)
            )
            .into(),
            Some(inner.span),
        );
        Ty::error(gcx)
    }

    pub(super) fn is_optional_type(&self, ty: Ty<'ctx>) -> bool {
        let TyKind::Adt(def, _) = ty.kind() else {
            return false;
        };
        let Some(opt_id) = self.gcx().std_item_def(hir::StdItem::Optional) else {
            return false;
        };
        def.id == opt_id
    }

    pub(super) fn is_result_type(&self, ty: Ty<'ctx>) -> bool {
        let TyKind::Adt(def, _) = ty.kind() else {
            return false;
        };
        let Some(result_id) = self.gcx().std_item_def(hir::StdItem::Result) else {
            return false;
        };
        def.id == result_id
    }

    pub(super) fn task_inner_type(&self, ty: Ty<'ctx>) -> Option<Ty<'ctx>> {
        let TyKind::Adt(def, args) = ty.kind() else {
            return None;
        };
        let Some(task_id) = self.gcx().std_item_def(hir::StdItem::Task) else {
            return None;
        };
        if def.id != task_id {
            return None;
        }
        (*args.first()?).ty()
    }

    pub(super) fn with_return_ty<R>(
        &self,
        return_ty: Option<Ty<'ctx>>,
        f: impl FnOnce() -> R,
    ) -> R {
        let prev = self.return_ty.replace(return_ty);
        let result = f();
        self.return_ty.set(prev);
        result
    }

    pub(super) fn finish_async_call_surface_check(
        &self,
        node_id: NodeID,
        span: Span,
        result_ty: Ty<'ctx>,
    ) -> Ty<'ctx> {
        if self.results.borrow().is_async_call(node_id)
            && self.direct_await_operand.get() != Some(node_id)
        {
            self.gcx()
                .dcx()
                .emit_error("async calls must be immediately awaited".into(), Some(span));
            return Ty::error(self.gcx());
        }

        result_ty
    }

    pub(super) fn resolved_async_call_status(
        &self,
        node_id: NodeID,
        cs: Option<&Cs<'ctx>>,
    ) -> Option<bool> {
        if self.results.borrow().is_async_call(node_id) {
            return Some(true);
        }

        {
            let results = self.results.borrow();
            if let Some(def_id) = results.overload_source(node_id) {
                return Some(self.gcx().definition_is_async(def_id));
            }

            if let Some(call_info) = results.interface_call(node_id) {
                return Some(self.gcx().definition_is_async(call_info.method_id));
            }
        }

        let Some(cs) = cs else {
            return None;
        };

        if let Some(def_id) = cs.resolved_overload_sources().get(&node_id).copied() {
            return Some(self.gcx().definition_is_async(def_id));
        }

        if let Some(call_info) = cs.resolved_interface_calls().get(&node_id).copied() {
            return Some(self.gcx().definition_is_async(call_info.method_id));
        }

        None
    }

    pub(super) fn resolved_async_property_status(
        &self,
        node_id: NodeID,
        cs: Option<&Cs<'ctx>>,
    ) -> Option<bool> {
        if let Some(property) = self.results.borrow().property_read(node_id) {
            return Some(property.getter_is_async);
        }

        let Some(cs) = cs else {
            return None;
        };

        cs.resolved_property_reads()
            .get(&node_id)
            .map(|property| property.getter_is_async)
    }

    pub(super) fn finalize_deferred_async_call_surface_checks(&self, cs: &Cs<'ctx>) {
        let pending: Vec<_> = self
            .pending_async_surface_checks
            .borrow_mut()
            .drain(..)
            .collect();
        let mut unresolved = Vec::new();

        for pending in pending {
            match self.resolved_async_call_status(pending.node_id, Some(cs)) {
                Some(true) => {
                    self.results.borrow_mut().record_async_call(pending.node_id);
                    if !pending.directly_awaited {
                        self.gcx().dcx().emit_error(
                            "async calls must be immediately awaited".into(),
                            Some(pending.span),
                        );
                    }
                }
                Some(false) => {}
                None => unresolved.push(pending),
            }
        }

        if !unresolved.is_empty() {
            self.pending_async_surface_checks
                .borrow_mut()
                .extend(unresolved);
        }
    }

    pub(super) fn finalize_deferred_async_property_surface_checks(&self, cs: &Cs<'ctx>) {
        let pending: Vec<_> = self
            .pending_async_property_surface_checks
            .borrow_mut()
            .drain(..)
            .collect();

        for pending in pending {
            match self.resolved_async_property_status(pending.node_id, Some(cs)) {
                Some(true) => {
                    self.results.borrow_mut().record_async_call(pending.node_id);
                    if !pending.directly_awaited {
                        self.gcx().dcx().emit_error(
                            "async calls must be immediately awaited".into(),
                            Some(pending.span),
                        );
                    }
                }
                Some(false) => {}
                None => {}
            }
        }
    }

    pub(super) fn type_is_async_callable(&self, ty: Ty<'ctx>) -> bool {
        self.async_callable_input_count(ty).is_some()
    }

    pub(super) fn ty_is_known_async_callable(&self, ty: Ty<'ctx>) -> bool {
        matches!(
            ty.kind(),
            TyKind::Closure {
                kind: crate::sema::models::ClosureKind::AsyncFn
                    | crate::sema::models::ClosureKind::AsyncFnMut
                    | crate::sema::models::ClosureKind::AsyncFnOnce,
                ..
            }
        )
    }

    pub(super) fn async_callable_input_count(&self, ty: Ty<'ctx>) -> Option<usize> {
        match ty.kind() {
            TyKind::Closure { kind, inputs, .. } => matches!(
                kind,
                crate::sema::models::ClosureKind::AsyncFn
                    | crate::sema::models::ClosureKind::AsyncFnMut
                    | crate::sema::models::ClosureKind::AsyncFnOnce
            )
            .then_some(inputs.len()),
            TyKind::Parameter(param) => {
                let gcx = self.gcx();
                let Some(async_fn_def) = gcx.std_item_def(hir::StdItem::AsyncFn) else {
                    return None;
                };
                let async_fn_mut_def = gcx.std_item_def(hir::StdItem::AsyncFnMut);
                let async_fn_once_def = gcx.std_item_def(hir::StdItem::AsyncFnOnce);
                crate::sema::tycheck::constraints::canonical_constraints_of(gcx, self.current_def)
                    .into_iter()
                    .find_map(|constraint| {
                        let crate::sema::models::Constraint::Bound {
                            ty: bound_ty,
                            interface,
                        } = constraint.value
                        else {
                            return None;
                        };
                        let TyKind::Parameter(bound_param) = bound_ty.kind() else {
                            return None;
                        };
                        if bound_param.index != param.index
                            || bound_param.name != param.name
                            || (interface.id != async_fn_def
                                && Some(interface.id) != async_fn_mut_def
                                && Some(interface.id) != async_fn_once_def)
                        {
                            return None;
                        }

                        let args_ty = interface.arguments.get(1).and_then(|arg| arg.ty())?;
                        Some(match args_ty.kind() {
                            TyKind::Tuple(elem_tys) => elem_tys.len(),
                            _ => 1,
                        })
                    })
            }
            _ => None,
        }
    }

    pub(super) fn optional_inner_type(
        &self,
        ty: Ty<'ctx>,
    ) -> Option<(GenericArguments<'ctx>, Ty<'ctx>)> {
        let TyKind::Adt(def, args) = ty.kind() else {
            return None;
        };
        let Some(opt_id) = self.gcx().std_item_def(hir::StdItem::Optional) else {
            return None;
        };
        if def.id != opt_id {
            return None;
        }
        let inner = (*args.first()?).ty()?;
        Some((args, inner))
    }

    pub(super) fn result_inner_types(
        &self,
        ty: Ty<'ctx>,
    ) -> Option<(GenericArguments<'ctx>, Ty<'ctx>, Ty<'ctx>)> {
        if !self.is_result_type(ty) {
            return None;
        }
        let TyKind::Adt(_, args) = ty.kind() else {
            return None;
        };
        let ok_ty = args.get(0)?.ty()?;
        let err_ty = args.get(1)?.ty()?;
        Some((args, ok_ty, err_ty))
    }

    pub(super) fn mk_optional_type(&self, inner: Ty<'ctx>) -> (Ty<'ctx>, GenericArguments<'ctx>) {
        let gcx = self.gcx();
        let opt_id = gcx
            .std_item_def(hir::StdItem::Optional)
            .expect("Optional type must exist");
        let enum_def = gcx.get_enum_definition(opt_id);
        let args = gcx
            .store
            .interners
            .intern_generic_args(vec![GenericArgument::Type(inner)]);
        let opt_ty = gcx
            .store
            .interners
            .intern_ty(TyKind::Adt(enum_def.adt_def, args));
        (opt_ty, args)
    }
}
