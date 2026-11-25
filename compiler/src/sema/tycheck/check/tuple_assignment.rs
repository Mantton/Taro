//! Tuple assignees preserve the RHS shape, with an ordinary coercion at each
//! leaf. Coercion identities are distinct from destination/place identities.

use super::*;

impl<'ctx> Checker<'ctx> {
    pub(super) fn synth_tuple_assignment(
        &self,
        lhs: &hir::Expression,
        rhs: &hir::Expression,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let mut discards = Vec::new();
        let mut conversions = Vec::new();
        let (source, expected) =
            self.tuple_assignment_shape(lhs, cs, &mut discards, &mut conversions);
        let actual = self.synth_with_expectation(rhs, Some(expected), cs);
        if matches!(
            cs.infer_cx.resolve_vars_if_possible(actual).kind(),
            TyKind::Never
        ) {
            // There will be no projections or writes at runtime, but synthetic
            // types still need to be fully resolved for subsequent lowering.
            cs.equal(source, expected, rhs.span);
            for discard in discards {
                cs.equal(discard, self.gcx().types.void, rhs.span);
            }
        } else {
            // Equality enforces the complete nested tuple shape and arity.
            // Leaf conversions were registered separately below.
            cs.equal(source, actual, rhs.span);
        }
        for (goal, span) in conversions {
            cs.add_goal(goal, span);
        }
        self.gcx().types.void
    }

    fn tuple_assignment_shape(
        &self,
        target: &hir::Expression,
        cs: &mut Cs<'ctx>,
        discards: &mut Vec<Ty<'ctx>>,
        conversions: &mut Vec<(Goal<'ctx>, Span)>,
    ) -> (Ty<'ctx>, Ty<'ctx>) {
        let (source, expected) = match &target.kind {
            hir::ExpressionKind::Tuple(items, _) => {
                let (sources, expected): (Vec<_>, Vec<_>) = items
                    .iter()
                    .map(|item| self.tuple_assignment_shape(item, cs, discards, conversions))
                    .unzip();
                (
                    Ty::new(
                        TyKind::Tuple(self.gcx().store.interners.intern_ty_list(sources)),
                        self.gcx(),
                    ),
                    Ty::new(
                        TyKind::Tuple(self.gcx().store.interners.intern_ty_list(expected)),
                        self.gcx(),
                    ),
                )
            }
            hir::ExpressionKind::Discard => {
                let ty = cs.infer_cx.next_ty_var(target.span);
                discards.push(ty);
                (ty, ty)
            }
            _ => {
                let expected = self.synth_assignment_target(target, cs);
                let source = cs.infer_cx.next_ty_var(target.span);
                let value = self
                    .results
                    .borrow()
                    .tuple_assignment_values
                    .get(&target.id)
                    .copied()
                    .unwrap_or_else(|| self.method_value_node());
                self.results
                    .borrow_mut()
                    .tuple_assignment_values
                    .insert(target.id, value);
                cs.record_expr_ty(value, source);
                conversions.push((
                    Goal::Coerce {
                        node_id: value,
                        from: source,
                        to: expected,
                    },
                    target.span,
                ));
                return (source, expected);
            }
        };
        cs.record_expr_ty(target.id, expected);
        (source, expected)
    }
}
