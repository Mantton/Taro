//! Build spread sequences with ordinary THIR calls, locals and loops. This
//! lets the existing MIR cleanup paths own each initialized element if source
//! evaluation suspends, panics, or returns from the enclosing function.
use super::*;
use crate::span::Span;

impl<'ctx> FunctionLower<'ctx> {
    fn spread_call(
        &mut self,
        name: &str,
        generics: Vec<GenericArgument<'ctx>>,
        args: Vec<ExprId>,
        span: Span,
    ) -> ExprId {
        let Ok(id) =
            mir::optimize::async_transform::find_std_function(self.gcx, "collections", name, span)
        else {
            let ty = self.gcx.types.error;
            return self.push_expr(
                ExprKind::Literal(Constant {
                    ty,
                    value: ConstantKind::Unit,
                }),
                ty,
                span,
            );
        };
        let arguments = self.gcx.store.interners.intern_generic_args(generics);
        let signature =
            instantiate_signature_with_args(self.gcx, self.gcx.get_signature(id), arguments);
        let callee = self.push_expr(
            ExprKind::Zst {
                id,
                generic_args: Some(arguments),
            },
            Ty::from_labeled_signature(self.gcx, &signature),
            span,
        );
        self.push_expr(
            ExprKind::Call {
                callee,
                args,
                argument_evaluation_order: None,
                is_async: false,
            },
            signature.output,
            span,
        )
    }

    fn spread_binding(
        &mut self,
        name: &str,
        ty: Ty<'ctx>,
        span: Span,
    ) -> (hir::NodeID, thir::Pattern<'ctx>) {
        let local = self.fresh_synthetic_local();
        (
            local,
            thir::Pattern {
                ty,
                span,
                kind: thir::PatternKind::Binding {
                    name: self.gcx.intern_symbol(name),
                    local,
                    ty,
                },
            },
        )
    }

    fn spread_local(
        &mut self,
        name: &str,
        init: ExprId,
        stmts: &mut Vec<StmtId>,
        span: Span,
    ) -> ExprId {
        let ty = self.func.exprs[init].ty;
        let (id, pattern) = self.spread_binding(name, ty, span);
        stmts.push(self.push_stmt(Stmt {
            kind: StmtKind::Let {
                id,
                pattern,
                expr: Some(init),
                ty,
                mutable: true,
            },
            span,
        }));
        self.push_expr(ExprKind::Local(id), ty, span)
    }

    fn spread_reference(&mut self, expr: ExprId, span: Span) -> ExprId {
        let ty = Ty::new(TyKind::Reference(self.func.exprs[expr].ty), self.gcx);
        self.push_expr(ExprKind::Reference { expr }, ty, span)
    }

    pub(super) fn lower_spread_literal(
        &mut self,
        items: &[Box<hir::Expression>],
        result: Ty<'ctx>,
        span: Span,
    ) -> Expr<'ctx> {
        let element = match result.kind() {
            TyKind::Array { element, .. } => element,
            TyKind::Adt(_, args) => args[0].ty().expect("List element type"),
            _ => unreachable!("checked spread literal has array or List type"),
        };
        let mut stmts = Vec::new();
        let (owner, receiver) = self.spread_storage(element, items.len(), &mut stmts, span);
        for item in items {
            self.append_contribution(item, receiver, element, &mut stmts);
        }
        let value = if let TyKind::Array { len, .. } = result.kind() {
            self.spread_call(
                "__spread_array",
                vec![GenericArgument::Type(element), GenericArgument::Const(len)],
                vec![receiver],
                span,
            )
        } else {
            owner
        };
        let block = self.func.blocks.push(Block {
            id: BlockId::from_usize(self.func.blocks.len()),
            stmts,
            expr: Some(value),
        });
        Expr {
            kind: ExprKind::Block(block),
            ty: result,
            span,
        }
    }

    fn spread_storage(
        &mut self,
        element: Ty<'ctx>,
        capacity: usize,
        stmts: &mut Vec<StmtId>,
        span: Span,
    ) -> (ExprId, ExprId) {
        let hint = self.push_expr(
            ExprKind::Literal(Constant {
                ty: self.gcx.types.uint,
                value: ConstantKind::Integer(capacity as u64),
            }),
            self.gcx.types.uint,
            span,
        );
        let init = self.spread_call(
            "__list_with_capacity",
            vec![GenericArgument::Type(element)],
            vec![hint],
            span,
        );
        let owner = self.spread_local("$spread_list", init, stmts, span);
        (owner, self.spread_reference(owner, span))
    }

    fn append_contribution(
        &mut self,
        item: &hir::Expression,
        receiver: ExprId,
        element: Ty<'ctx>,
        stmts: &mut Vec<StmtId>,
    ) {
        if let hir::ExpressionKind::Spread(source) = &item.kind {
            self.lower_spread_items(item, source, receiver, element, stmts);
        } else {
            let value = self.lower_expr(item);
            let append = self.spread_call(
                "__list_append",
                vec![GenericArgument::Type(element)],
                vec![receiver, value],
                item.span,
            );
            stmts.push(self.push_stmt(Stmt {
                kind: StmtKind::Expr(append),
                span: item.span,
            }));
        }
    }

    /// Materialize fixed arguments and drain each variadic contribution in
    /// source order, even when a labeled fixed argument occurs between spreads.
    pub(super) fn prepare_spread_call(
        &mut self,
        arguments: &[hir::ExpressionArgument],
        leading: &[ExprId],
        tail: &[usize],
        param: Ty<'ctx>,
        stmts: &mut Vec<StmtId>,
        span: Span,
    ) -> (Vec<ExprId>, Vec<ExprId>) {
        if let [index] = tail
            && let hir::ExpressionKind::Spread(source) = &arguments[*index].expression.kind
            && self.results.node_type(source.id) == param
        {
            // A sole exactly matching Span forwards its original backing owner.
            let supplied = arguments
                .iter()
                .enumerate()
                .map(|(i, arg)| {
                    if i == *index {
                        self.lower_expr(source)
                    } else {
                        self.lower_call_argument(arg)
                    }
                })
                .collect();
            return (leading.to_vec(), supplied);
        }
        let leading = leading
            .iter()
            .map(|id| self.spread_local("$spread_receiver", *id, stmts, span))
            .collect();
        let TyKind::Adt(_, args) = param.kind() else {
            unreachable!("variadic parameter is a Span")
        };
        let element = args[0].ty().expect("variadic element");
        let (_, receiver) = self.spread_storage(element, tail.len(), stmts, span);
        let view = self.spread_call(
            "__list_as_span",
            vec![GenericArgument::Type(element)],
            vec![receiver],
            span,
        );
        let tail: rustc_hash::FxHashSet<_> = tail.iter().copied().collect();
        let supplied = arguments
            .iter()
            .enumerate()
            .map(|(i, arg)| {
                if tail.contains(&i) {
                    self.append_contribution(&arg.expression, receiver, element, stmts);
                    view
                } else {
                    let value = self.lower_call_argument(arg);
                    self.spread_local("$spread_argument", value, stmts, arg.expression.span)
                }
            })
            .collect();
        (leading, supplied)
    }

    pub(super) fn after_spread_arguments(
        &mut self,
        stmts: Vec<StmtId>,
        call: ExprKind<'ctx>,
        ty: Ty<'ctx>,
        span: Span,
    ) -> ExprKind<'ctx> {
        if stmts.is_empty() {
            return call;
        }
        let value = self.push_expr(call, ty, span);
        let block = self.func.blocks.push(Block {
            id: BlockId::from_usize(self.func.blocks.len()),
            stmts,
            expr: Some(value),
        });
        ExprKind::Block(block)
    }

    fn lower_spread_items(
        &mut self,
        item: &hir::Expression,
        source: &hir::Expression,
        receiver: ExprId,
        element: Ty<'ctx>,
        stmts: &mut Vec<StmtId>,
    ) {
        let span = item.span;
        let source = self.lower_expr(source);
        let iter = self.spread_call(
            "__spread_iter",
            vec![GenericArgument::Type(self.func.exprs[source].ty)],
            vec![source],
            span,
        );
        let cursor = self.spread_local("$spread_cursor", iter, stmts, span);
        let cursor_ty = self.func.exprs[cursor].ty;
        let borrowed = self.spread_reference(cursor, span);
        let yielded = self.results.node_type(item.id);
        let next = self.spread_call(
            "__spread_next",
            vec![
                GenericArgument::Type(yielded),
                GenericArgument::Type(cursor_ty),
            ],
            vec![borrowed],
            span,
        );
        let optional = self.func.exprs[next].ty;
        let TyKind::Adt(def, _) = optional.kind() else {
            return;
        };
        let (id, pattern) = self.spread_binding("$spread_item", yielded, span);
        let mut value = Expr {
            kind: ExprKind::Local(id),
            ty: yielded,
            span,
        };
        let adjustments = self
            .results
            .node_adjustments(item.id)
            .unwrap_or_default()
            .to_vec();
        for adjustment in adjustments {
            value = self.apply_adjustment(item.id, value, adjustment, span);
        }
        let value = self.push_expr(value.kind, value.ty, span);
        let append = self.spread_call(
            "__list_append",
            vec![GenericArgument::Type(element)],
            vec![receiver, value],
            span,
        );
        let stop = self.push_expr(
            ExprKind::Break {
                label: None,
                value: None,
            },
            Ty::new(TyKind::Never, self.gcx),
            span,
        );
        let mut arms = Vec::new();
        let definition = self.gcx.get_enum_definition(def.id);
        for (variant, subpatterns, body) in [
            (
                hir::StdItem::OptionalSomeVariant,
                vec![thir::FieldPattern {
                    index: FieldIndex::from_usize(0),
                    pattern,
                }],
                append,
            ),
            (hir::StdItem::OptionalNoneVariant, vec![], stop),
        ] {
            let variant = self.gcx.std_item_def(variant).expect("Optional variant");
            let variant = *definition
                .variants
                .iter()
                .find(|v| v.def_id == variant)
                .expect("Optional variant definition");
            let pattern = thir::Pattern {
                ty: optional,
                span,
                kind: thir::PatternKind::Variant {
                    definition: def,
                    variant,
                    subpatterns,
                },
            };
            arms.push(self.func.arms.push(thir::Arm {
                pattern: Box::new(pattern),
                guard: None,
                body,
                span,
            }));
        }
        let step = self.push_expr(
            ExprKind::Match {
                scrutinee: next,
                arms,
                binding_condition: false,
            },
            self.gcx.types.void,
            span,
        );
        let step = self.push_stmt(Stmt {
            kind: StmtKind::Expr(step),
            span,
        });
        let block = self.func.blocks.push(Block {
            id: BlockId::from_usize(self.func.blocks.len()),
            stmts: vec![step],
            expr: None,
        });
        stmts.push(self.push_stmt(Stmt {
            kind: StmtKind::Loop { label: None, block },
            span,
        }));
    }
}
