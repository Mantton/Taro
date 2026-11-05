//! Native indexing lowers each declared capability directly. Numeric get/set
//! writeback captures RHS, receiver and indices once; it creates no element ref.
use super::*;
use crate::{
    sema::tycheck::results::{NativeAccessor, NativeIndex},
    span::Span,
};

impl<'ctx> FunctionLower<'ctx> {
    pub(super) fn native_index_info(&self, expr: &hir::Expression) -> Option<NativeIndex<'ctx>> {
        let hir::ExpressionKind::Index { .. } = &expr.kind else {
            return None;
        };
        self.results.native_indices.get(&expr.id).copied()
    }

    pub(super) fn native_index_call(
        &mut self,
        accessor: NativeAccessor<'ctx>,
        mut args: Vec<ExprId>,
        span: Span,
    ) -> ExprKind<'ctx> {
        let source = accessor.source;
        // An address-derived get/set is exactly a load/store through its
        // address capability. Expand explicitly inline static defaults here,
        // before forwarding receivers become separate GC root temporaries.
        // Custom accessors and dynamic class/interface dispatch stay calls.
        let static_inline =
            self.gcx.definition_parent(source).is_some_and(|parent| {
                self.gcx.definition_kind(parent) == hir::DefinitionKind::Impl
            }) && !self.gcx.is_virtual_class_method(source)
                && self.gcx.attributes_of(source).iter().any(|attribute| {
                    attribute.as_known(self.gcx) == Some(hir::KnownAttribute::Inline)
                })
                && !self.gcx.attributes_of(source).iter().any(|attribute| {
                    attribute.as_known(self.gcx) == Some(hir::KnownAttribute::NoInline)
                });
        if let Some((_, entry)) =
            self.gcx
                .native_subscript_for_accessor(source)
                .filter(|(_, entry)| {
                    static_inline
                        && (entry.getter == Some(source) && entry.getter_is_default
                            || entry.setter == Some(source) && entry.setter_is_default)
                })
        {
            let address = entry.address.expect("address-derived accessor");
            if !self.gcx.is_virtual_class_method(address) {
                let value = (entry.setter == Some(source)).then(|| args.pop().unwrap());
                let reference_ty =
                    crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args(
                        self.gcx,
                        self.gcx.get_signature(address).output,
                        accessor.arguments,
                    );
                let call = self.native_index_call(
                    NativeAccessor {
                        source: address,
                        arguments: accessor.arguments,
                    },
                    args,
                    span,
                );
                let address = self.push_expr(call, reference_ty, span);
                return if let Some(value) = value {
                    let crate::sema::models::TyKind::Reference(element_ty) = reference_ty.kind()
                    else {
                        unreachable!("address accessor returns a reference")
                    };
                    let target = self.push_expr(ExprKind::Deref(address), element_ty, span);
                    ExprKind::Assign { target, value }
                } else {
                    ExprKind::Deref(address)
                };
            }
        }
        let receiver_ty = crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args(
            self.gcx,
            self.gcx.get_signature(source).inputs[0].ty,
            accessor.arguments,
        );
        let actual = self.func.exprs[args[0]].ty;
        if self.gcx.is_class_type(actual)
            && self.gcx.is_class_type(receiver_ty)
            && actual != receiver_ty
        {
            args[0] = self.push_expr(ExprKind::ClassUpcast { value: args[0] }, receiver_ty, span);
        }
        let callee = self.push_expr(
            ExprKind::Zst {
                id: source,
                generic_args: Some(accessor.arguments),
            },
            self.gcx.get_type(source),
            span,
        );
        ExprKind::Call {
            callee,
            args,
            is_async: false,
            argument_evaluation_order: None,
        }
    }

    /// Keep the original static class until the actual capability is called;
    /// inherited getter and setter bodies can belong to different ancestors.
    pub(super) fn lower_native_index_receiver(
        &mut self,
        target: &hir::Expression,
        proxy: hir::NodeID,
    ) -> ExprId {
        let id = self.lower_expr(target);
        let mut expr = self.func.exprs[id].clone();
        for adjustment in self
            .results
            .node_adjustments(proxy)
            .unwrap_or_default()
            .to_vec()
        {
            if !matches!(adjustment, Adjustment::ClassUpcast { .. }) {
                expr = self.apply_adjustment(proxy, expr, adjustment, target.span);
            }
        }
        self.push_expr(expr.kind, expr.ty, expr.span)
    }

    pub(super) fn lower_native_index_set(
        &mut self,
        lhs: &hir::Expression,
        rhs: &hir::Expression,
        setter: NativeAccessor<'ctx>,
    ) -> ExprKind<'ctx> {
        let hir::ExpressionKind::Index {
            target,
            index,
            nodes,
        } = &lhs.kind
        else {
            unreachable!()
        };
        let receiver = self.lower_native_index_receiver(target, nodes.receiver);
        let mut args = vec![receiver];
        args.extend(
            index
                .iter()
                .map(|argument| self.lower_expr(&argument.expression)),
        );
        args.push(self.lower_expr(rhs));
        let last = args.len() - 1;
        let mut call = self.native_index_call(setter, args, lhs.span);
        if matches!(call, ExprKind::Assign { .. }) {
            // Ordinary assignment already evaluates its RHS before its place.
            return call;
        }
        let ExprKind::Call {
            argument_evaluation_order,
            ..
        } = &mut call
        else {
            unreachable!()
        };
        *argument_evaluation_order = Some(std::iter::once(last).chain(0..last).collect());
        call
    }

    fn capture_native_operand(
        &mut self,
        expression: ExprId,
        name: &str,
        span: Span,
        stmts: &mut Vec<StmtId>,
    ) -> ExprId {
        let ty = self.func.exprs[expression].ty;
        let local = self.fresh_synthetic_local();
        let pattern = thir::Pattern {
            ty,
            span,
            kind: thir::PatternKind::Binding {
                name: self.gcx.intern_symbol(name),
                local,
                ty,
            },
        };
        stmts.push(self.push_stmt(Stmt {
            span,
            kind: StmtKind::Let {
                id: local,
                pattern,
                expr: Some(expression),
                ty,
                mutable: true,
            },
        }));
        self.push_expr(ExprKind::Local(local), ty, span)
    }

    pub(super) fn lower_native_index_compound(
        &mut self,
        expression: &hir::Expression,
        op: hir::BinaryOperator,
        lhs: &hir::Expression,
        rhs: &hir::Expression,
        getter: NativeAccessor<'ctx>,
        setter: NativeAccessor<'ctx>,
    ) -> ExprKind<'ctx> {
        let hir::ExpressionKind::Index {
            target,
            index,
            nodes,
        } = &lhs.kind
        else {
            unreachable!()
        };
        let mut stmts = vec![];
        // General assignment order: snapshot RHS before resolving its destination.
        let rhs_value = self.lower_expr(rhs);
        let rhs_local = self.capture_native_operand(rhs_value, "__index_rhs", rhs.span, &mut stmts);
        let receiver = self.lower_native_index_receiver(target, nodes.receiver);
        let receiver =
            self.capture_native_operand(receiver, "__index_receiver", target.span, &mut stmts);
        let mut args = vec![receiver];
        for argument in index {
            let value = self.lower_expr(&argument.expression);
            args.push(self.capture_native_operand(
                value,
                "__index_argument",
                argument.span,
                &mut stmts,
            ));
        }
        let ty = self.results.node_type(lhs.id);
        let get = self.native_index_call(getter, args.clone(), lhs.span);
        let get = self.push_expr(get, ty, lhs.span);
        let value = self.capture_native_operand(get, "__index_value", lhs.span, &mut stmts);
        let assign = self.push_expr(
            ExprKind::AssignOp {
                op: bin_op(op),
                target: value,
                value: rhs_local,
            },
            self.gcx.types.void,
            expression.span,
        );
        stmts.push(self.push_stmt(Stmt {
            span: expression.span,
            kind: StmtKind::Expr(assign),
        }));
        args.push(value);
        let set = self.native_index_call(setter, args, expression.span);
        let set = self.push_expr(set, self.gcx.types.void, expression.span);
        let block = BlockId::from_raw(self.func.blocks.len() as u32);
        self.func.blocks.push(Block {
            id: block,
            stmts,
            expr: Some(set),
        });
        ExprKind::Block(block)
    }
}
