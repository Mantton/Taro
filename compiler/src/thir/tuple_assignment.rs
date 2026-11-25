//! Snapshot the complete RHS, then perform ordinary assignments in depth-first
//! left-to-right order. Destination evaluation is intentionally not hoisted.

use super::*;

impl<'ctx> FunctionLower<'ctx> {
    pub(super) fn lower_assignment_with_value(
        &mut self,
        lhs: &hir::Expression,
        value: ExprId,
    ) -> ExprKind<'ctx> {
        let results = self.results.clone();
        let lhs = results.selected_brackets.get(&lhs.id).unwrap_or(lhs);
        if let Some(entry) = self.native_index_info(lhs) {
            self.lower_native_index_set(lhs, value, entry.setter.expect("validated set accessor"))
        } else {
            let target = self.lower_expr(lhs);
            ExprKind::Assign { target, value }
        }
    }

    pub(super) fn lower_tuple_assignment(
        &mut self,
        lhs: &hir::Expression,
        rhs: &hir::Expression,
    ) -> ExprKind<'ctx> {
        let value = self.lower_expr(rhs);
        let ty = self.func.exprs[value].ty;
        let local = self.fresh_synthetic_local();
        let declaration = self.push_stmt(Stmt {
            span: rhs.span,
            kind: StmtKind::Let {
                id: local,
                pattern: thir::Pattern {
                    ty,
                    span: rhs.span,
                    kind: thir::PatternKind::Binding {
                        name: self.gcx.intern_symbol("$tuple_assignment"),
                        local,
                        ty,
                    },
                },
                expr: Some(value),
                ty,
                mutable: false,
            },
        });
        let mut stmts = vec![declaration];
        // A diverging RHS cannot supply any projections.
        if !matches!(ty.kind(), TyKind::Never) {
            let saved = self.push_expr(ExprKind::Local(local), ty, rhs.span);
            self.lower_tuple_assignee(lhs, saved, &mut stmts);
        }
        let id = BlockId::from_usize(self.func.blocks.len());
        self.func.blocks.push(Block {
            id,
            stmts,
            expr: None,
        });
        ExprKind::Block(id)
    }

    fn lower_tuple_assignee(
        &mut self,
        lhs: &hir::Expression,
        value: ExprId,
        stmts: &mut Vec<StmtId>,
    ) {
        match &lhs.kind {
            hir::ExpressionKind::Tuple(items, _) => {
                let TyKind::Tuple(types) = self.func.exprs[value].ty.kind() else {
                    unreachable!("validated tuple assignee shape")
                };
                for (index, item) in items.iter().enumerate() {
                    let field = self.push_expr(
                        ExprKind::Field {
                            lhs: value,
                            index: FieldIndex::from_usize(index),
                        },
                        types[index],
                        item.span,
                    );
                    self.lower_tuple_assignee(item, field, stmts);
                }
            }
            hir::ExpressionKind::Discard => {}
            _ => {
                let site = self.results.tuple_assignment_values[&lhs.id];
                let mut expression = self.func.exprs[value].clone();
                if let Some(adjustments) = self.results.node_adjustments(site).map(<[_]>::to_vec) {
                    for adjustment in adjustments {
                        expression = self.apply_adjustment(site, expression, adjustment, lhs.span);
                    }
                }
                let value = self.push_expr(expression.kind, expression.ty, expression.span);
                let kind = self.lower_assignment_with_value(lhs, value);
                let assignment = self.push_expr(kind, self.gcx.types.void, lhs.span);
                stmts.push(self.push_stmt(Stmt {
                    kind: StmtKind::Expr(assignment),
                    span: lhs.span,
                }));
            }
        }
    }
}
