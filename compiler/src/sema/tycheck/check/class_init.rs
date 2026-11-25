//! Resolve superclass construction as a constructor call, never as a method
//! on a partially initialized public handle. THIR installs its private result
//! in the base prefix and only then evaluates this level's field defaults.
use super::*;

impl<'ctx> Checker<'ctx> {
    pub(super) fn synth_base_initializer(
        &self,
        expression: &hir::Expression,
        receiver: &hir::Expression,
        name: &crate::span::Identifier,
        arguments: &[hir::ExpressionArgument],
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        if self.constructor_convenience.get() {
            self.gcx().dcx().emit_error(
                "convenience init must delegate with self.init, not super.init".into(),
                Some(expression.span),
            );
            return Ty::error(self.gcx());
        }
        let gcx = self.gcx();
        let base = self
            .constructor_payload
            .get()
            .and_then(|payload| gcx.class_for_payload(payload))
            .and_then(|class| gcx.class_base(class));
        let Some(base) = base else {
            gcx.dcx().emit_error(
                "super.init requires a derived class initializer".into(),
                Some(expression.span),
            );
            return Ty::error(gcx);
        };
        self.synth_initializer_delegation(expression, receiver, name, arguments, base, true, cs)
    }

    pub(super) fn synth_self_initializer(
        &self,
        expression: &hir::Expression,
        receiver: &hir::Expression,
        name: &crate::span::Identifier,
        arguments: &[hir::ExpressionArgument],
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let gcx = self.gcx();
        let class = gcx.initializer_target(self.current_def);
        if !self.constructor_convenience.get() || !gcx.is_class_type(class) {
            gcx.dcx().emit_error(
                "self.init delegation requires a class convenience initializer".into(),
                Some(expression.span),
            );
            return Ty::error(gcx);
        }
        self.synth_initializer_delegation(expression, receiver, name, arguments, class, false, cs)
    }

    fn synth_initializer_delegation(
        &self,
        expression: &hir::Expression,
        receiver: &hir::Expression,
        name: &crate::span::Identifier,
        arguments: &[hir::ExpressionArgument],
        base: Ty<'ctx>,
        super_call: bool,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let head = type_head_from_value_ty(base).expect("class type head");
        let resolution = self.resolve_static_member_resolution(head, base, name, name.span, true);
        let resolution = self.narrow_callable_shape(resolution, arguments);
        self.record_value_path_resolution(receiver.id, &resolution);
        let callee_ty = self.instantiate_value_path(
            receiver.id,
            receiver.span,
            &resolution,
            None,
            None,
            None,
            true,
            Some(false),
            cs,
        );
        cs.record_expr_ty(receiver.id, callee_ty);
        // Use ordinary call-site inference for literals, contextual fresh
        // borrows, default parameters and freshly owned callback captures.
        let mut callee = receiver.clone();
        if let hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path)) = &mut callee.kind {
            path.resolution = resolution.clone();
        }
        let expectations = self.argument_expectations_for_call(
            &callee,
            arguments,
            callee_ty,
            Some(base),
            resolution.definition_id(),
            cs,
        );
        let may_be_lazy = self.resolution_may_select_lazy(&resolution);
        let arguments = cs.with_deferred_callee(receiver.id, |cs| {
            arguments
                .iter()
                .enumerate()
                .map(|(index, argument)| {
                    let expected = expectations
                        .as_ref()
                        .and_then(|items| items.get(index))
                        .and_then(|item| *item);
                    let arg_may_be_lazy = may_be_lazy
                        && !(resolution.definition_id().is_some()
                            && expected.is_some_and(|e| !e.is_lazy));
                    self.synth_call_argument(argument, expected, arg_may_be_lazy, cs)
                })
                .collect()
        });
        let result = cs.infer_cx.next_ty_var(expression.span);
        let statement = cs.infer_cx.next_ty_var(expression.span);
        cs.add_goal(Goal::ConstructorResult(result, base), expression.span);
        cs.add_goal(
            Goal::InitializerStatement(result, statement),
            expression.span,
        );
        cs.add_goal(
            Goal::Apply(ApplyGoalData {
                call_node_id: expression.id,
                callee_node_id: Some(receiver.id),
                call_span: expression.span,
                callee_ty,
                callee_source: resolution.definition_id(),
                is_unsafe_context: self.unsafe_depth.get() > 0,
                result_ty: result,
                arguments,
                skip_labels: false,
                input_only_selection: false,
            }),
            expression.span,
        );
        if super_call {
            self.results
                .borrow_mut()
                .base_initializer_calls
                .insert(expression.id);
        } else {
            self.results
                .borrow_mut()
                .self_initializer_calls
                .insert(expression.id);
        }
        statement
    }
}
