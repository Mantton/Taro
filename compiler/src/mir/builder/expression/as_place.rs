use crate::{
    mir::{
        BasicBlockId, BlockAnd, BlockAndExtension, LocalId, Place, PlaceElem, builder::MirBuilder,
    },
    sema::models::TyKind,
    thir::{ExprId, ExprKind},
    unpack,
};

impl<'ctx, 'thir> MirBuilder<'ctx, 'thir> {
    pub fn as_place(&mut self, mut block: BasicBlockId, expr_id: ExprId) -> BlockAnd<Place<'ctx>> {
        if let Some(place) = self.prepared_call_arguments.get(&expr_id) {
            return block.and(place.clone());
        }
        if let Some(storage) = self.static_place(expr_id) {
            let id = self.gcx.static_reference_function(storage);
            let ty = self.gcx.get_signature(id).output;
            let temp = self.new_temp_with_ty(ty, self.thir.exprs[expr_id].span);

            block = self
                .static_reference_into(Place::from_local(temp), block, expr_id)
                .into_block();
            return block.and(Place {
                local: temp,
                projection: vec![PlaceElem::Deref],
            });
        }
        if self.class_field_path(expr_id).is_some() {
            let ty = crate::sema::models::Ty::new(
                TyKind::Reference(self.thir.exprs[expr_id].ty),
                self.gcx,
            );
            let temp = self.new_temp_with_ty(ty, self.thir.exprs[expr_id].span);

            block = self
                .class_field_into(Place::from_local(temp), block, expr_id)
                .into_block();
            return block.and(Place {
                local: temp,
                projection: vec![PlaceElem::Deref],
            });
        }
        let expr = &self.thir.exprs[expr_id];

        match &expr.kind {
            ExprKind::Local(id) => {
                let local = *self.locals.get(id).expect("lhs local");
                block.and(Place::from_local(local))
            }
            ExprKind::Upvar {
                field_index,
                capture_kind,
            } => {
                // Upvar access uses the closure's self parameter (_1).
                let self_local = LocalId::from_raw(1);
                let self_ty = self.body.locals[self_local].ty;
                let needs_self_deref =
                    matches!(self_ty.kind(), TyKind::Pointer(..) | TyKind::Reference(..));

                let mut projection = Vec::new();
                if needs_self_deref {
                    projection.push(PlaceElem::Deref);
                }

                let field_ty = match capture_kind {
                    crate::sema::models::CaptureKind::ByRef => {
                        crate::sema::models::Ty::new(TyKind::Reference(expr.ty), self.gcx)
                    }
                    _ => expr.ty,
                };

                projection.push(PlaceElem::Field(*field_index, field_ty));

                if matches!(capture_kind, crate::sema::models::CaptureKind::ByRef) {
                    projection.push(PlaceElem::Deref);
                }

                block.and(Place {
                    local: self_local,
                    projection,
                })
            }
            ExprKind::Deref(expr_id) => {
                let mut base = unpack!(block = self.as_place(block, *expr_id));
                base.projection.push(PlaceElem::Deref);
                block.and(base)
            }
            ExprKind::Field { lhs, index } => {
                let mut builder = unpack!(block = self.as_place(block, *lhs));
                builder.projection.push(PlaceElem::Field(*index, expr.ty));
                block.and(builder)
            }
            // Materialize a reborrow's token once before taking its address.
            ExprKind::Reference { .. }
            | ExprKind::If { .. }
            | ExprKind::Match { .. }
            | ExprKind::Return { .. }
            | ExprKind::Loop { .. }
            | ExprKind::Break { .. }
            | ExprKind::Continue { .. }
            | ExprKind::Assign { .. }
            | ExprKind::AssignOp { .. }
            | ExprKind::Literal(..)
            | ExprKind::Unary { .. }
            | ExprKind::Binary { .. }
            | ExprKind::ClassIdentity { .. }
            | ExprKind::Cast { .. }
            | ExprKind::ClassUpcast { .. }
            | ExprKind::ClassSelfResult { .. }
            | ExprKind::ExistentialTryCast { .. }
            | ExprKind::ExistentialTypeIs { .. }
            | ExprKind::ClosureToFnPointer { .. }
            | ExprKind::Logical { .. }
            | ExprKind::Call { .. }
            | ExprKind::BoxExistential { .. }
            | ExprKind::ExistentialUpcast { .. }
            | ExprKind::Block { .. }
            | ExprKind::Tuple { .. }
            | ExprKind::Array { .. }
            | ExprKind::ListLiteral { .. }
            | ExprKind::Repeat { .. }
            | ExprKind::Adt { .. }
            | ExprKind::Zst { .. }
            | ExprKind::Closure { .. }
            | ExprKind::Await { .. }
            | ExprKind::Yield { .. }
            | ExprKind::AwaitAsyncVar { .. }
            | ExprKind::Select { .. } => {
                let temp = unpack!(block = self.as_addressable_temp(block, expr_id));
                block.and(Place::from_local(temp))
            }
        }
    }
    pub(super) fn static_place(&self, expression: ExprId) -> Option<crate::hir::DefinitionID> {
        let ExprKind::Deref(pointer) = self.thir.exprs[expression].kind else {
            return None;
        };
        let ExprKind::Zst { id, .. } = self.thir.exprs[pointer].kind else {
            return None;
        };
        (self.gcx.definition_kind(id) == crate::hir::DefinitionKind::ModuleVariable).then_some(id)
    }

    pub(super) fn static_reference_into(
        &mut self,
        destination: Place<'ctx>,
        block: BasicBlockId,
        expression: ExprId,
    ) -> BlockAnd<()> {
        use crate::mir::{Constant, ConstantKind, Operand, TerminatorKind};
        let storage = self.static_place(expression).expect("static place");
        let id = self.gcx.static_reference_function(storage);
        let ty = self.gcx.get_type(id);
        let target = self.new_block();
        let span = self.thir.exprs[expression].span;
        let unwind = self.call_unwind_action(span);
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty,
                    value: ConstantKind::Function(
                        id,
                        crate::sema::models::GenericArguments::empty(),
                        ty,
                    ),
                }),
                args: vec![],
                destination,
                target,
                unwind,
            },
        );
        target.unit()
    }

    /// Combine inline projections into one object access. Stop at every class
    /// handle boundary so its slot remains protected by the next acquisition.
    fn class_field_path(
        &self,
        expression: ExprId,
    ) -> Option<(ExprId, Vec<crate::thir::FieldIndex>)> {
        let ExprKind::Field { lhs, index } = self.thir.exprs[expression].kind else {
            return None;
        };
        if self.gcx.is_class_type(self.thir.exprs[lhs].ty) {
            return Some((lhs, vec![index]));
        }
        let (root, mut path) = self.class_field_path(lhs)?;
        path.push(index);
        Some((root, path))
    }

    pub(super) fn class_field_into(
        &mut self,
        destination: Place<'ctx>,
        block: BasicBlockId,
        expression: ExprId,
    ) -> BlockAnd<()> {
        self.class_field_call(
            destination,
            block,
            expression,
            "__intrinsic_class_field_reference",
            vec![],
        )
    }

    /// Copy a trivially copyable class field out with one instantaneous
    /// access instead of publishing a borrow control.
    pub(super) fn class_field_read_into(
        &mut self,
        destination: Place<'ctx>,
        block: BasicBlockId,
        expression: ExprId,
    ) -> BlockAnd<()> {
        self.class_field_call(
            destination,
            block,
            expression,
            "__intrinsic_class_field_read",
            vec![],
        )
    }

    /// Store an already evaluated trivially copyable value into a class field
    /// with one instantaneous access. The RHS is evaluated before the handle
    /// slot is resolved, matching ordinary assignment order.
    pub(super) fn class_field_write(
        &mut self,
        block: BasicBlockId,
        expression: ExprId,
        value: crate::mir::Operand<'ctx>,
    ) -> BlockAnd<()> {
        let span = self.thir.exprs[expression].span;
        let unit = self.new_temp_with_ty(self.gcx.types.void, span);
        self.class_field_call(
            Place::from_local(unit),
            block,
            expression,
            "__intrinsic_class_field_write",
            vec![value],
        )
    }

    /// Apply a primitive compound assignment inside one exclusive
    /// instantaneous access. `checked` selects overflow-checked arithmetic,
    /// whose panic is raised only after the access ends.
    pub(super) fn class_field_modify(
        &mut self,
        block: BasicBlockId,
        expression: ExprId,
        op: crate::mir::BinaryOperator,
        checked: bool,
        rhs: crate::mir::Operand<'ctx>,
    ) -> BlockAnd<()> {
        use crate::mir::{Constant, ConstantKind, Operand};
        let span = self.thir.exprs[expression].span;
        let name = op.compound_name().expect("compound field operator");
        let op = if checked {
            format!("checked.{name}")
        } else {
            name.to_owned()
        };
        let op = Operand::Constant(Constant {
            ty: self.gcx.types.string,
            value: ConstantKind::String(self.gcx.intern_symbol(&op)),
        });
        let unit = self.new_temp_with_ty(self.gcx.types.void, span);
        self.class_field_call(
            Place::from_local(unit),
            block,
            expression,
            "__intrinsic_class_field_modify",
            vec![op, rhs],
        )
    }

    /// Every class field access is a single shared load or store: values
    /// copy shallowly and run no user code.
    pub(super) fn is_instant_class_field(&self, expression: ExprId) -> bool {
        self.is_class_field(expression)
    }

    fn class_field_call(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        expression: ExprId,
        name: &str,
        extra: Vec<crate::mir::Operand<'ctx>>,
    ) -> BlockAnd<()> {
        use crate::mir::{Constant, ConstantKind, Operand, Rvalue, TerminatorKind};
        use crate::sema::models::{GenericArgument, Ty};
        let (root, path) = self.class_field_path(expression).expect("class field path");
        let expr = &self.thir.exprs[expression];
        let root_ty = self.thir.exprs[root].ty;
        let slot = unpack!(block = self.as_place(block, root));
        let slot_ty = Ty::new(TyKind::Reference(root_ty), self.gcx);
        let slot_ref = self.new_temp_with_ty(slot_ty, expr.span);

        self.push_assign(
            block,
            Place::from_local(slot_ref),
            Rvalue::Ref { place: slot },
            expr.span,
        );
        let id = crate::mir::optimize::async_transform::find_std_function(
            self.gcx,
            "intrinsic",
            name,
            expr.span,
        )
        .unwrap_or_else(|_| panic!("class field intrinsic missing"));
        let fn_ty = self.gcx.get_type(id);
        let arguments = self.gcx.store.interners.intern_generic_args(vec![
            GenericArgument::Type(root_ty),
            GenericArgument::Type(expr.ty),
        ]);
        let path = path
            .iter()
            .map(|field| field.index().to_string())
            .collect::<Vec<_>>()
            .join(".");
        let path = self.gcx.intern_symbol(&path);
        let target = self.new_block();
        let unwind = self.call_unwind_action(expr.span);
        let mut args = vec![
            Operand::Copy(Place::from_local(slot_ref)),
            Operand::Constant(Constant {
                ty: self.gcx.types.string,
                value: ConstantKind::String(path),
            }),
        ];
        args.extend(extra);
        self.terminate(
            block,
            expr.span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: fn_ty,
                    value: ConstantKind::Function(id, arguments, fn_ty),
                }),
                args,
                destination,
                target,
                unwind,
            },
        );
        target.unit()
    }

    pub(super) fn is_class_field(&self, expression: ExprId) -> bool {
        self.class_field_path(expression).is_some()
    }
}
