//! `target ??= value` reads the target once and assigns only when it is nil.
//! The value is evaluated only then, after every part of the target.

use super::*;

impl<'ctx> FunctionLower<'ctx> {
    pub(super) fn lower_assign_optional(
        &mut self,
        expression: &hir::Expression,
        lhs: &hir::Expression,
        rhs: &hir::Expression,
    ) -> ExprKind<'ctx> {
        let results = self.results.clone();
        let lhs = results.selected_brackets.get(&lhs.id).unwrap_or(lhs);
        let span = expression.span;
        let void = self.gcx.types.void;
        let target_ty = crate::sema::tycheck::utils::normalize_aliases(
            self.gcx,
            self.results.node_type(lhs.id),
        );
        let mut stmts = vec![];

        // A get/set subscript: capture the receiver and indices, read through
        // the getter, and call the setter only for nil.
        if let Some(entry) = self.native_index_info(lhs)
            && !entry.use_address
        {
            let hir::ExpressionKind::Index {
                target,
                index,
                nodes,
            } = &lhs.kind
            else {
                unreachable!()
            };
            let receiver = self.lower_native_index_receiver(target, nodes.receiver);
            let receiver =
                self.capture_native_operand(receiver, "__index_receiver", target.span, &mut stmts);
            let mut args = vec![receiver];
            for argument in index {
                let value = self.lower_call_argument(argument);
                args.push(self.capture_native_operand(
                    value,
                    "__index_argument",
                    argument.span,
                    &mut stmts,
                ));
            }
            let get = self.native_index_call(entry.getter, args.clone(), lhs.span);
            let current = self.push_expr(get, target_ty, lhs.span);
            args.push(self.lower_expr(rhs));
            let set = self.native_index_call(
                entry.setter.expect("validated set accessor"),
                args,
                span,
            );
            let assign = self.push_expr(set, void, span);
            return self.nil_check_block(stmts, current, target_ty, assign, span);
        }

        // A local, or fields and dereferences of one: reading the place twice
        // evaluates nothing twice.
        if self.is_stable_place(lhs) {
            let current = self.lower_expr(lhs);
            let value = self.lower_expr(rhs);
            let assign = self.lower_assignment_with_value(lhs, value);
            let assign = self.push_expr(assign, void, span);
            return self.nil_check_block(stmts, current, target_ty, assign, span);
        }

        // Anything else, such as a field of a call result or an addressable
        // subscript: hold a reference to the slot.
        let place = self.lower_expr(lhs);
        let reference = self.push_expr(
            ExprKind::Reference { expr: place },
            Ty::new(TyKind::Reference(target_ty), self.gcx),
            lhs.span,
        );
        let slot = self.capture_native_operand(reference, "__optional_slot", lhs.span, &mut stmts);
        let current = self.push_expr(ExprKind::Deref(slot), target_ty, lhs.span);
        let value = self.lower_expr(rhs);
        let target = self.push_expr(ExprKind::Deref(slot), target_ty, lhs.span);
        let assign = self.push_expr(ExprKind::Assign { target, value }, void, span);
        self.nil_check_block(stmts, current, target_ty, assign, span)
    }

    fn is_stable_place(&self, expr: &hir::Expression) -> bool {
        let derefs_by_call = |node: hir::NodeID| {
            self.results.node_adjustments(node).is_some_and(|adjustments| {
                adjustments
                    .iter()
                    .any(|adjustment| matches!(adjustment, Adjustment::DerefCall { .. }))
            })
        };
        match &expr.kind {
            hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path)) => {
                matches!(path.resolution, hir::Resolution::LocalVariable(_))
            }
            hir::ExpressionKind::Member { target, .. } => {
                self.results.field_index(expr.id).is_some()
                    && self.results.property_read(expr.id).is_none()
                    && !derefs_by_call(target.id)
                    && self.is_stable_place(target)
            }
            hir::ExpressionKind::TupleAccess(target, _) => {
                !derefs_by_call(target.id) && self.is_stable_place(target)
            }
            hir::ExpressionKind::Dereference(inner) => {
                self.results.overload_source(expr.id).is_none()
                    && !derefs_by_call(inner.id)
                    && self.is_stable_place(inner)
            }
            _ => false,
        }
    }

    /// `{ stmts; match current { .none => assign, _ => {} } }`
    fn nil_check_block(
        &mut self,
        mut stmts: Vec<StmtId>,
        current: ExprId,
        optional_ty: Ty<'ctx>,
        assign: ExprId,
        span: crate::span::Span,
    ) -> ExprKind<'ctx> {
        let void = self.gcx.types.void;
        let TyKind::Adt(optional, _) = optional_ty.kind() else {
            unreachable!("'??=' target must be Optional")
        };
        let enum_def = self.gcx.get_enum_definition(optional.id);
        let none_def = self
            .gcx
            .std_item_def(hir::StdItem::OptionalNoneVariant)
            .expect("Optional.none variant");
        let none_variant = enum_def
            .variants
            .iter()
            .find(|variant| variant.def_id == none_def)
            .copied()
            .expect("Optional.none variant in enum definition");
        let none_pattern = thir::Pattern {
            ty: optional_ty,
            span,
            kind: thir::PatternKind::Variant {
                definition: enum_def.adt_def,
                variant: none_variant,
                subpatterns: vec![],
            },
        };
        let other_pattern = thir::Pattern {
            ty: optional_ty,
            span,
            kind: thir::PatternKind::Wild,
        };
        let nothing = BlockId::from_usize(self.func.blocks.len());
        self.func.blocks.push(Block {
            id: nothing,
            stmts: vec![],
            expr: None,
        });
        let nothing = self.push_expr(ExprKind::Block(nothing), void, span);
        let mut arms = vec![];
        for (pattern, body) in [(none_pattern, assign), (other_pattern, nothing)] {
            let arm = thir::ArmId::from_raw(self.func.arms.len() as u32);
            self.func.arms.push(thir::Arm {
                pattern: Box::new(pattern),
                guard: None,
                body,
                span,
            });
            arms.push(arm);
        }
        let check = ExprKind::Match {
            scrutinee: current,
            arms,
            binding_condition: false,
        };
        if stmts.is_empty() {
            return check;
        }
        let check = self.push_expr(check, void, span);
        stmts.push(self.push_stmt(Stmt {
            span,
            kind: StmtKind::Expr(check),
        }));
        let block = BlockId::from_usize(self.func.blocks.len());
        self.func.blocks.push(Block {
            id: block,
            stmts,
            expr: None,
        });
        ExprKind::Block(block)
    }
}
