use crate::{
    mir::{
        AggregateKind, BasicBlockId, BinaryOperator, BlockAnd, BlockAndExtension, CastKind,
        Category, Constant, ConstantKind, Operand, Place, Rvalue, RvalueFunc, TerminatorKind,
        UnaryOperator, builder::MirBuilder, optimize::async_transform::find_std_function,
    },
    sema::models::{GenericArgument, Ty, TyKind},
    span::Span,
    thir::{ExprId, ExprKind, FieldIndex},
    unpack,
};

impl<'ctx, 'thir> MirBuilder<'ctx, 'thir> {
    pub fn as_rvalue(
        &mut self,
        mut block: BasicBlockId,
        expr_id: ExprId,
    ) -> BlockAnd<Rvalue<'ctx>> {
        let expr = &self.thir.exprs[expr_id];
        if let Some(operand) = self.prepared_argument_operand(block, expr_id) {
            return block.and(Rvalue::Use(operand));
        }

        match &expr.kind {
            ExprKind::Assign { .. } | ExprKind::AssignOp { .. } => {
                block = self.lower_statement_expression(block, expr_id).into_block();
                block.and(Rvalue::Use(Operand::Constant(Constant {
                    ty: self.gcx.types.void,
                    value: ConstantKind::Unit,
                })))
            }
            ExprKind::Unary { op, operand } => {
                let operand_ty = crate::sema::tycheck::utils::normalize_aliases(
                    self.gcx,
                    self.thir.exprs[*operand].ty,
                );
                let operand = unpack!(block = self.as_operand(block, *operand));
                // Signed negation overflows for the minimum value; route it
                // through the checked intrinsic like binary arithmetic.
                if matches!(op, UnaryOperator::Negate)
                    && self.gcx.config.overflow_checks
                    && matches!(operand_ty.kind(), TyKind::Int(_))
                    && self.gcx.std_package_index().is_some()
                {
                    return self.build_checked_intrinsic(
                        block,
                        "__intrinsic_checked_neg",
                        operand_ty,
                        expr.span,
                        vec![operand],
                    );
                }
                block.and(Rvalue::UnaryOp { op: *op, operand })
            }
            ExprKind::ClassSelfResult { value } => {
                let operand = unpack!(block = self.as_operand(block, *value));
                block.and(Rvalue::Cast {
                    operand,
                    ty: expr.ty,
                    kind: CastKind::ClassSelfResult,
                })
            }
            ExprKind::ClassUpcast { value } => {
                let operand = unpack!(block = self.as_operand(block, *value));
                block.and(Rvalue::Cast {
                    operand,
                    ty: expr.ty,
                    kind: CastKind::ClassUpcast,
                })
            }
            ExprKind::Cast { value } => {
                // An immediate, type-preserving reference/raw/reference round
                // trip still has its original controller. Lower it as a
                // checked reborrow instead of discarding and inventing
                // provenance. Unrelated raw casts remain unsafe/unknown.
                if let TyKind::Reference(result) =
                    crate::sema::tycheck::utils::normalize_aliases(self.gcx, expr.ty).kind()
                    && let ExprKind::Cast { value: original } = self.thir.exprs[*value].kind
                    && let TyKind::Pointer(raw, _) = crate::sema::tycheck::utils::normalize_aliases(
                        self.gcx,
                        self.thir.exprs[*value].ty,
                    )
                    .kind()
                    && let TyKind::Reference(source) =
                        crate::sema::tycheck::utils::normalize_aliases(
                            self.gcx,
                            self.thir.exprs[original].ty,
                        )
                        .kind()
                    && source == result
                    && raw == result
                {
                    let mut place = unpack!(block = self.as_place(block, original));
                    place.projection.push(crate::mir::PlaceElem::Deref);
                    return block.and(Rvalue::Ref { place });
                }
                let reference_to_raw =
                    matches!(self.thir.exprs[*value].ty.kind(), TyKind::Reference(..))
                        && matches!(expr.ty.kind(), TyKind::Pointer(..));
                // Reading a reference's address does not transfer its exclusive
                // token. The raw result has no checked dependency and using it
                // remains subject to the language's unsafe pointer contract.
                let operand = if reference_to_raw {
                    Operand::Copy(unpack!(block = self.as_place(block, *value)))
                } else {
                    unpack!(block = self.as_operand(block, *value))
                };
                if self.thir.exprs[*value].ty == expr.ty {
                    return block.and(Rvalue::Use(operand));
                }
                block.and(Rvalue::Cast {
                    operand,
                    ty: expr.ty,
                    kind: if self.gcx.is_class_subtype(self.thir.exprs[*value].ty, expr.ty)
                        || matches!((self.thir.exprs[*value].ty.kind(),expr.ty.kind()),
                            (TyKind::Reference(from),TyKind::Reference(to)) if self.gcx.is_class_subtype(from,to)) {
                        CastKind::ClassUpcast
                    } else if reference_to_raw {
                        CastKind::Pointer
                    } else {
                        CastKind::Numeric
                    },
                })
            }
            ExprKind::ExistentialTryCast { value, target } => {
                self.checked_cast_rvalue(block, *value, *target, expr.ty, expr.span)
            }
            ExprKind::ExistentialTypeIs { value, target } => {
                // Type assertions are non-consuming reads; always copy the source place.
                let place = unpack!(block = self.as_place(block, *value));
                let operand = Operand::Copy(place);
                block.and(Rvalue::Cast {
                    operand,
                    ty: expr.ty,
                    kind: CastKind::ExistentialTypeIs { target: *target },
                })
            }
            ExprKind::ClosureToFnPointer { closure, .. } => {
                // Convert non-capturing closure to function pointer
                // The closure operand is evaluated (though for non-capturing closures
                // this is essentially a no-op), then cast to a fn pointer type.
                let operand = unpack!(block = self.as_operand(block, *closure));
                block.and(Rvalue::Cast {
                    operand,
                    ty: expr.ty,
                    kind: CastKind::ClosureToFnPointer,
                })
            }
            ExprKind::ClassIdentity { lhs, rhs, equal } => {
                // Snapshot left before evaluating right: callbacks on the
                // RHS may replace the original handle slot and release it.
                let left = unpack!(block = self.as_temp(block, *lhs));
                let right = unpack!(block = self.as_temp(block, *rhs));
                let pointer_ty = crate::sema::models::Ty::new(
                    TyKind::Pointer(self.gcx.types.uint8, crate::hir::Mutability::Immutable),
                    self.gcx,
                );
                let left_pointer = self.new_temp_with_ty(pointer_ty, expr.span);
                let right_pointer = self.new_temp_with_ty(pointer_ty, expr.span);
                for (destination, source) in [(left_pointer, left), (right_pointer, right)] {
                    self.push_assign(
                        block,
                        crate::mir::Place::from_local(destination),
                        Rvalue::Cast {
                            operand: Operand::Copy(crate::mir::Place::from_local(source)),
                            ty: pointer_ty,
                            kind: CastKind::ClassObjectOwner,
                        },
                        expr.span,
                    );
                }
                return block.and(Rvalue::BinaryOp {
                    op: if *equal {
                        BinaryOperator::Eql
                    } else {
                        BinaryOperator::Neq
                    },
                    lhs: Operand::Copy(crate::mir::Place::from_local(left_pointer)),
                    rhs: Operand::Copy(crate::mir::Place::from_local(right_pointer)),
                });
            }
            ExprKind::Binary { op, lhs, rhs } => {
                let operand_ty = crate::sema::tycheck::utils::normalize_aliases(
                    self.gcx,
                    self.thir.exprs[*lhs].ty,
                );
                if matches!(op, BinaryOperator::Eql | BinaryOperator::Neq)
                    && matches!(
                        operand_ty.kind(),
                        TyKind::Adt(def, _)
                            if self.gcx.std_item_def(crate::hir::StdItem::Optional) == Some(def.id)
                    )
                {
                    let left_local = unpack!(block = self.as_temp(block, *lhs));
                    let right_local = unpack!(block = self.as_temp(block, *rhs));
                    let left_discr = self.new_temp_with_ty(self.gcx.types.uint, expr.span);
                    let right_discr = self.new_temp_with_ty(self.gcx.types.uint, expr.span);
                    self.push_assign(
                        block,
                        Place::from_local(left_discr),
                        Rvalue::Discriminant {
                            place: Place::from_local(left_local),
                        },
                        expr.span,
                    );
                    self.push_assign(
                        block,
                        Place::from_local(right_discr),
                        Rvalue::Discriminant {
                            place: Place::from_local(right_local),
                        },
                        expr.span,
                    );
                    return block.and(Rvalue::BinaryOp {
                        op: *op,
                        lhs: Operand::Copy(Place::from_local(left_discr)),
                        rhs: Operand::Copy(Place::from_local(right_discr)),
                    });
                }
                let lhs = unpack!(block = self.as_operand(block, *lhs));
                let rhs = unpack!(block = self.as_operand(block, *rhs));
                self.build_binary_op(block, *op, operand_ty, expr.span, lhs, rhs)
            }
            ExprKind::Tuple { fields } => {
                let mut ops = Vec::with_capacity(fields.len());
                for field in fields.iter() {
                    let op = unpack!(block = self.as_operand(block, *field));
                    ops.push(op);
                }
                let fields: index_vec::IndexVec<FieldIndex, Operand<'ctx>> =
                    index_vec::IndexVec::from_vec(ops);
                block.and(Rvalue::Aggregate {
                    kind: AggregateKind::Tuple,
                    fields,
                })
            }
            ExprKind::Array { elements } => {
                let mut ops = Vec::with_capacity(elements.len());
                for elem in elements.iter() {
                    let op = unpack!(block = self.as_operand(block, *elem));
                    ops.push(op);
                }
                let fields: index_vec::IndexVec<FieldIndex, Operand<'ctx>> =
                    index_vec::IndexVec::from_vec(ops);
                let element_ty = match expr.ty.kind() {
                    crate::sema::models::TyKind::Array { element, .. } => element,
                    _ => expr.ty,
                };
                block.and(Rvalue::Aggregate {
                    kind: AggregateKind::Array {
                        len: elements.len(),
                        element: element_ty,
                    },
                    fields,
                })
            }
            ExprKind::Repeat { element, count } => {
                let element_ty = match expr.ty.kind() {
                    crate::sema::models::TyKind::Array { element, .. } => element,
                    _ => {
                        debug_assert!(
                            false,
                            "repeat expressions should only be used with array types"
                        );
                        expr.ty
                    }
                };
                if *count == 0 {
                    // Evaluate once, but keep ownership in its registered
                    // temporary: there is no array element to receive it.
                    // Normal statement cleanup must still destroy the value.
                    let _ = unpack!(block = self.as_temp(block, *element));
                    return block.and(Rvalue::Aggregate {
                        kind: AggregateKind::Array {
                            len: 0,
                            element: element_ty,
                        },
                        fields: index_vec::IndexVec::new(),
                    });
                }
                let op = unpack!(block = self.as_operand(block, *element));
                if *count == 1 {
                    // A singleton initializes by ordinary copy/move. In
                    // particular, it must not duplicate a NoCopy owner.
                    return block.and(Rvalue::Aggregate {
                        kind: AggregateKind::Array {
                            len: 1,
                            element: element_ty,
                        },
                        fields: index_vec::IndexVec::from_vec(vec![op]),
                    });
                }
                block.and(Rvalue::Repeat {
                    operand: op,
                    count: *count,
                    element: element_ty,
                })
            }
            ExprKind::If { .. }
            | ExprKind::Match { .. }
            | ExprKind::Return { .. }
            | ExprKind::Loop { .. }
            | ExprKind::Break { .. }
            | ExprKind::Continue { .. }
            | ExprKind::Deref(..)
            | ExprKind::Reference { .. }
            | ExprKind::Local(..)
            | ExprKind::Upvar { .. }
            | ExprKind::Logical { .. }
            | ExprKind::Call { .. }
            | ExprKind::ListLiteral { .. }
            | ExprKind::BoxExistential { .. }
            | ExprKind::ExistentialUpcast { .. }
            | ExprKind::Block(..)
            | ExprKind::Adt(..)
            | ExprKind::Field { .. }
            | ExprKind::Closure { .. }
            | ExprKind::Await { .. }
            | ExprKind::Yield { .. }
            | ExprKind::AwaitAsyncVar { .. }
            | ExprKind::Select { .. } => {
                debug_assert!(!matches!(
                    Category::of(&expr.kind),
                    Category::Rvalue(RvalueFunc::AsRvalue) | Category::Constant
                ));
                let operand = unpack!(block = self.as_operand(block, expr_id));
                block.and(Rvalue::Use(operand))
            }

            ExprKind::Literal(..) | ExprKind::Zst { .. } => {
                let constant = self.as_constant(expr_id);
                block.and(Rvalue::Use(Operand::Constant(constant)))
            }
        }
    }
}

impl<'ctx, 'thir> MirBuilder<'ctx, 'thir> {
    pub fn build_binary_op(
        &mut self,
        block: BasicBlockId,
        op: BinaryOperator,
        operand_ty: Ty<'ctx>,
        span: Span,
        lhs: Operand<'ctx>,
        rhs: Operand<'ctx>,
    ) -> BlockAnd<Rvalue<'ctx>> {
        let operand_ty = crate::sema::tycheck::utils::normalize_aliases(self.gcx, operand_ty);
        if self.should_check_overflow(op, operand_ty) {
            return self.build_overflow_checked_op(block, op, operand_ty, span, lhs, rhs);
        }
        block.and(Rvalue::BinaryOp { op, lhs, rhs })
    }

    /// Whether `op` on `operand_ty` must be lowered through a checked
    /// arithmetic intrinsic instead of a plain `BinaryOp`.
    pub(super) fn should_check_overflow(&self, op: BinaryOperator, operand_ty: Ty<'ctx>) -> bool {
        self.gcx.config.overflow_checks
            && matches!(
                op,
                BinaryOperator::Add
                    | BinaryOperator::Sub
                    | BinaryOperator::Mul
                    | BinaryOperator::Div
                    | BinaryOperator::Rem
                    | BinaryOperator::BitShl
                    | BinaryOperator::BitShr
            )
            && matches!(operand_ty.kind(), TyKind::Int(_) | TyKind::UInt(_))
            && self.gcx.std_package_index().is_some()
    }

    fn build_overflow_checked_op(
        &mut self,
        block: BasicBlockId,
        op: BinaryOperator,
        operand_ty: Ty<'ctx>,
        span: Span,
        lhs: Operand<'ctx>,
        rhs: Operand<'ctx>,
    ) -> BlockAnd<Rvalue<'ctx>> {
        let name = match op {
            BinaryOperator::Add => "__intrinsic_checked_add",
            BinaryOperator::Sub => "__intrinsic_checked_sub",
            BinaryOperator::Mul => "__intrinsic_checked_mul",
            BinaryOperator::Div => "__intrinsic_checked_div",
            BinaryOperator::Rem => "__intrinsic_checked_rem",
            BinaryOperator::BitShl => "__intrinsic_checked_shl",
            BinaryOperator::BitShr => "__intrinsic_checked_shr",
            _ => unreachable!("not an overflow-checked operator"),
        };
        self.build_checked_intrinsic(block, name, operand_ty, span, vec![lhs, rhs])
    }

    /// Lower a checked integer operation as a call to the matching
    /// `__intrinsic_checked_*` std intrinsic. Routing the panic through a
    /// real `Call` terminator gives it the enclosing cleanup chain
    /// (defers, logical stack pop) via `call_unwind_action`, which a plain
    /// `BinaryOp`/`UnaryOp` statement cannot carry.
    fn build_checked_intrinsic(
        &mut self,
        block: BasicBlockId,
        name: &str,
        operand_ty: Ty<'ctx>,
        span: Span,
        args: Vec<Operand<'ctx>>,
    ) -> BlockAnd<Rvalue<'ctx>> {
        let Ok(intrinsic_id) = find_std_function(self.gcx, "intrinsic", name, span) else {
            // Diagnostic already emitted; produce a placeholder of the right
            // type so building continues and further errors surface.
            let placeholder = args.into_iter().next().expect("checked op has operands");
            return block.and(Rvalue::Use(placeholder));
        };
        let intrinsic_ty = self.gcx.get_type(intrinsic_id);
        let generic_args = self
            .gcx
            .store
            .interners
            .intern_generic_args(vec![GenericArgument::Type(operand_ty)]);
        let dest = self.new_temp_with_ty(operand_ty, span);
        let target = self.new_block();
        let unwind = self.call_unwind_action(span);
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: intrinsic_ty,
                    value: ConstantKind::Function(intrinsic_id, generic_args, intrinsic_ty),
                }),
                args,
                destination: Place::from_local(dest),
                target,
                unwind,
            },
        );
        target.and(Rvalue::Use(Operand::Copy(Place::from_local(dest))))
    }
}
