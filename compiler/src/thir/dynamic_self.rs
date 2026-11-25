//! Lower dynamic construction using immutable class context. Store the address
//! as a compiler-private machine word so closure environments contain a plain
//! copied class identity, never an implicit reference to an instance receiver.
use super::*;

impl<'ctx> FunctionLower<'ctx> {
    pub(super) fn install_dynamic_self_context(&mut self, owner: DefinitionID) {
        let Some(context) = self.results.dynamic_self_contexts.get(&owner).copied() else {
            return;
        };
        let span = self.func.span;
        let receiver = self.push_expr(ExprKind::Local(context.receiver), context.receiver_ty, span);
        let value = if matches!(context.receiver_ty.kind(), TyKind::Reference(..)) {
            self.push_expr(ExprKind::Deref(receiver), context.class, span)
        } else {
            receiver
        };
        let helper = self
            .gcx
            .class_object_descriptor(context.class)
            .expect("actual class context helper");
        let TyKind::Adt(_, args) = context.class.kind() else {
            unreachable!()
        };
        let callee = self.push_expr(
            ExprKind::Zst {
                id: helper,
                generic_args: Some(args),
            },
            self.gcx.get_type(helper),
            span,
        );
        let address = self.push_expr(
            ExprKind::Call {
                callee,
                args: vec![value],
                is_async: false,
                argument_evaluation_order: None,
            },
            self.gcx.get_signature(helper).output,
            span,
        );
        let word = self.push_expr(ExprKind::Cast { value: address }, self.gcx.types.uint, span);
        let local =
            hir::NodeID::from_raw(crate::sema::tycheck::results::DYNAMIC_SELF_CONTEXT_LOCAL_RAW);
        let ty = self.gcx.types.uint;
        let statement = self.push_stmt(Stmt {
            kind: StmtKind::Let {
                id: local,
                pattern: thir::Pattern {
                    ty,
                    span,
                    kind: thir::PatternKind::Binding {
                        name: self.gcx.intern_symbol("$dynamic_self_context"),
                        local,
                        ty,
                    },
                },
                expr: Some(word),
                ty,
                mutable: false,
            },
            span,
        });
        let body = self.func.body.expect("instance method body");
        self.func.blocks[body].stmts.insert(0, statement);
    }

    pub(super) fn lower_dynamic_self_call(
        &mut self,
        expression: &hir::Expression,
        callee: &hir::Expression,
        arguments: &[hir::ExpressionArgument],
    ) -> Expr<'ctx> {
        let source = self
            .resolve_direct_callee_id(callee)
            .expect("required initializer");
        let helper = self
            .gcx
            .class_initializer_dispatch(source)
            .expect("required family dispatcher");
        let generics = self
            .results
            .instantiation(callee.id)
            .or_else(|| self.results.instantiation(expression.id));
        let local =
            hir::NodeID::from_raw(crate::sema::tycheck::results::DYNAMIC_SELF_CONTEXT_LOCAL_RAW);
        let context = self
            .captures_map
            .as_ref()
            .and_then(|captures| captures.iter().find(|capture| capture.source_id == local))
            .map(|capture| ExprKind::Upvar {
                field_index: capture.field_index,
                capture_kind: capture.capture_kind,
            })
            .unwrap_or(ExprKind::Local(local));
        let word = self.push_expr(context, self.gcx.types.uint, expression.span);
        let context = self.push_expr(
            ExprKind::Cast { value: word },
            self.gcx.get_signature(helper).inputs[0].ty,
            expression.span,
        );
        let mut prelude = Vec::new();
        let (mut args, order) = self
            .lower_call_args_with_defaults(
                self.gcx.get_signature(source),
                callee.id,
                arguments,
                &[],
                expression.span,
                &mut prelude,
            )
            .expect("required initializer arguments");
        args.insert(0, context);
        let order = order.map(|order| {
            std::iter::once(0)
                .chain(order.into_iter().map(|index| index + 1))
                .collect()
        });
        let callee = self.push_expr(
            ExprKind::Zst {
                id: helper,
                generic_args: generics,
            },
            self.gcx.get_type(helper),
            expression.span,
        );
        let ty = self.results.node_type(expression.id);
        let call = ExprKind::Call {
            callee,
            args,
            is_async: false,
            argument_evaluation_order: order,
        };
        Expr {
            kind: self.after_spread_arguments(prelude, call, ty, expression.span),
            ty,
            span: expression.span,
        }
    }
}
