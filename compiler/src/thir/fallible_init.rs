//! Success is assembled from initialized construction fields. Failure returns
//! only an error and never reads or publishes the partial self storage.
use super::*;
use crate::span::Span;

impl<'ctx> FunctionLower<'ctx> {
    pub(super) fn initializer_ok(&mut self, span: Span) -> ExprId {
        let output = self.gcx.get_signature(self.func.id).output;
        let value_ty = self.gcx.constructor_value(output);
        let binding = self
            .func
            .constructor_self
            .or_else(|| self.convenience.map(|(binding, _)| binding))
            .expect("initializer self");
        let value = if self.gcx.is_class_type(value_ty) {
            // Convenience delegation already produced a complete class handle.
            self.push_expr(ExprKind::Local(binding), value_ty, span)
        } else {
            let TyKind::Adt(definition, generic_args) = value_ty.kind() else {
                unreachable!("constructor storage")
            };
            let mut fields = vec![];
            for (index, field) in self
                .gcx
                .get_struct_definition(definition.id)
                .fields
                .iter()
                .enumerate()
            {
                let owner = self.push_expr(ExprKind::Local(binding), value_ty, span);
                let ty = instantiate_ty_with_args(self.gcx, field.ty, generic_args);
                let expression = self.push_expr(
                    ExprKind::Field {
                        lhs: owner,
                        index: FieldIndex::from_usize(index),
                    },
                    ty,
                    span,
                );
                fields.push(thir::FieldExpression {
                    index: FieldIndex::from_usize(index),
                    expression,
                });
            }
            self.push_expr(
                ExprKind::Adt(thir::AdtExpression {
                    base: None,
                    definition,
                    generic_args,
                    variant_index: None,
                    fields,
                }),
                value_ty,
                span,
            )
        };
        self.initializer_variant(output, hir::StdItem::ResultOkVariant, value, span)
    }

    pub(super) fn initializer_variant(
        &mut self,
        ty: Ty<'ctx>,
        variant: hir::StdItem,
        value: ExprId,
        span: Span,
    ) -> ExprId {
        let TyKind::Adt(definition, generic_args) =
            crate::sema::tycheck::utils::normalize_aliases(self.gcx, ty).kind()
        else {
            unreachable!("constructor Result")
        };
        let variant = self.gcx.std_item_def(variant).expect("Result variant");
        let index = self
            .gcx
            .get_enum_definition(definition.id)
            .variants
            .iter()
            .position(|item| item.def_id == variant)
            .expect("Result variant index");
        self.push_expr(
            ExprKind::Adt(thir::AdtExpression {
                base: None,
                definition,
                generic_args,
                variant_index: Some(VariantIndex::from_usize(index)),
                fields: vec![thir::FieldExpression {
                    index: FieldIndex::from_usize(0),
                    expression: value,
                }],
            }),
            ty,
            span,
        )
    }

    pub(super) fn finish_fallible_initializer(&mut self) {
        if self.func.constructor_self.is_none()
            || self
                .gcx
                .result_parts(self.gcx.get_signature(self.func.id).output)
                .is_none()
        {
            return;
        }
        let body = self.func.body.expect("initializer body");
        if self.func.blocks[body]
            .expr
            .is_some_and(|tail| matches!(self.func.exprs[tail].ty.kind(), TyKind::Never))
        {
            return;
        }
        if let Some(tail) = self.func.blocks[body].expr.take() {
            let statement = self.push_stmt(Stmt {
                kind: StmtKind::Expr(tail),
                span: self.func.span,
            });
            self.func.blocks[body].stmts.push(statement);
        }
        let value = self.initializer_ok(self.func.span);
        self.func.blocks[body].expr = Some(value);
    }
}

impl<'ctx> FunctionLower<'ctx> {
    /// Match a construction result once. Only its success arm may install
    /// storage or publish an object; its error arm never reads partial self.
    fn match_initializer_result(
        &mut self,
        value: ExprId,
        output: Ty<'ctx>,
        span: Span,
        success: impl FnOnce(&mut Self, ExprId) -> ExprId,
        failure: impl FnOnce(&mut Self, ExprId) -> ExprId,
    ) -> ExprId {
        let input =
            crate::sema::tycheck::utils::normalize_aliases(self.gcx, self.func.exprs[value].ty);
        // Generated calls bypass the checker's expression normalization. Match
        // their transparent Result aliases as the underlying enum as well.
        self.func.exprs[value].ty = input;
        let (ok_ty, error_ty) = self.gcx.result_parts(input).expect("initializer Result");
        let TyKind::Adt(definition, _) =
            crate::sema::tycheck::utils::normalize_aliases(self.gcx, input).kind()
        else {
            unreachable!()
        };
        let mut patterns = vec![];
        let mut values = vec![];
        for (item, ty) in [
            (hir::StdItem::ResultOkVariant, ok_ty),
            (hir::StdItem::ResultErrVariant, error_ty),
        ] {
            let variant_id = self.gcx.std_item_def(item).expect("Result variant");
            let variant = *self
                .gcx
                .get_enum_definition(definition.id)
                .variants
                .iter()
                .find(|variant| variant.def_id == variant_id)
                .expect("Result variant");
            let local = self.fresh_synthetic_local();
            patterns.push(thir::Pattern {
                ty: input,
                span,
                kind: thir::PatternKind::Variant {
                    definition,
                    variant,
                    subpatterns: vec![thir::FieldPattern {
                        index: FieldIndex::from_raw(0),
                        pattern: thir::Pattern {
                            ty,
                            span,
                            kind: thir::PatternKind::Binding {
                                name: self.gcx.intern_symbol("$initializer_result"),
                                local,
                                ty,
                            },
                        },
                    }],
                },
            });
            values.push(self.push_expr(ExprKind::Local(local), ty, span));
        }
        let bodies = [success(self, values[0]), failure(self, values[1])];
        let arms = patterns
            .into_iter()
            .zip(bodies)
            .map(|(pattern, body)| {
                self.func.arms.push(thir::Arm {
                    pattern: Box::new(pattern),
                    guard: None,
                    body,
                    span,
                })
            })
            .collect();
        self.push_expr(
            ExprKind::Match {
                scrutinee: value,
                arms,
                binding_condition: false,
            },
            output,
            span,
        )
    }

    pub(super) fn map_initializer_success(
        &mut self,
        value: ExprId,
        output: Ty<'ctx>,
        span: Span,
        success: impl FnOnce(&mut Self, ExprId) -> ExprId,
    ) -> ExprId {
        if self.gcx.result_parts(self.func.exprs[value].ty).is_none() {
            return success(self, value);
        }
        self.match_initializer_result(
            value,
            output,
            span,
            |this, value| {
                let value = success(this, value);
                this.initializer_variant(output, hir::StdItem::ResultOkVariant, value, span)
            },
            |this, error| {
                this.initializer_variant(output, hir::StdItem::ResultErrVariant, error, span)
            },
        )
    }

    pub(super) fn propagate_initializer(&mut self, value: ExprId, span: Span) -> ExprId {
        let Some((ok_ty, _)) = self.gcx.result_parts(self.func.exprs[value].ty) else {
            return value;
        };
        let output = self.gcx.get_signature(self.func.id).output;
        self.match_initializer_result(
            value,
            ok_ty,
            span,
            |_, value| value,
            |this, error| {
                let error =
                    this.initializer_variant(output, hir::StdItem::ResultErrVariant, error, span);
                this.push_expr(
                    ExprKind::Return { value: Some(error) },
                    Ty::new(TyKind::Never, this.gcx),
                    span,
                )
            },
        )
    }
}
