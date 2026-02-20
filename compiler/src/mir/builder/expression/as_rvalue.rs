use crate::{
    mir::{
        AggregateKind, BasicBlockId, BinaryOperator, BlockAnd, BlockAndExtension, CastKind,
        Category, Constant, ConstantKind, Operand, Place, Rvalue, RvalueFunc, builder::MirBuilder,
    },
    thir::{ExprId, ExprKind, FieldIndex},
    unpack,
};

impl<'ctx, 'thir> MirBuilder<'ctx, 'thir> {
    pub fn as_local_rvalue(&mut self, block: BasicBlockId, expr: ExprId) -> BlockAnd<Rvalue<'ctx>> {
        self.as_rvalue(block, expr)
    }

    pub fn as_rvalue(
        &mut self,
        mut block: BasicBlockId,
        expr_id: ExprId,
    ) -> BlockAnd<Rvalue<'ctx>> {
        let expr = &self.thir.exprs[expr_id];

        match &expr.kind {
            ExprKind::Assign { .. } | ExprKind::AssignOp { .. } => {
                block = self.lower_statement_expression(block, expr_id).into_block();
                block.and(Rvalue::Use(Operand::Constant(Constant {
                    ty: self.gcx.types.void,
                    value: ConstantKind::Unit,
                })))
            }
            ExprKind::Unary { op, operand } => {
                let operand = unpack!(block = self.as_operand(block, *operand));
                block.and(Rvalue::UnaryOp { op: *op, operand })
            }
            ExprKind::Cast { value } => {
                let operand = unpack!(block = self.as_operand(block, *value));
                block.and(Rvalue::Cast {
                    operand,
                    ty: expr.ty,
                    kind: CastKind::Numeric,
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
            ExprKind::Make { .. } => unreachable!("make should be handled in into_dest"),
            ExprKind::Binary { op, lhs, rhs } => {
                let lhs = unpack!(block = self.as_operand(block, *lhs));
                let rhs = unpack!(block = self.as_operand(block, *rhs));
                self.build_binary_op(block, *op, lhs, rhs)
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
                let op = unpack!(block = self.as_operand(block, *element));

                // Store once then copy for each slot to avoid multiple moves.
                let tmp = self.new_temp_with_ty(element_ty, expr.span);
                self.push_assign(block, Place::from_local(tmp), Rvalue::Use(op), expr.span);
                let tmp_op = Operand::Copy(Place::from_local(tmp));
                block.and(Rvalue::Repeat {
                    operand: tmp_op,
                    count: *count,
                    element: element_ty,
                })
            }
            ExprKind::If { .. }
            | ExprKind::Match { .. }
            | ExprKind::Return { .. }
            | ExprKind::Break
            | ExprKind::Continue
            | ExprKind::Deref(..)
            | ExprKind::Reference { .. }
            | ExprKind::Local(..)
            | ExprKind::Upvar { .. }
            | ExprKind::Logical { .. }
            | ExprKind::Call { .. }
            | ExprKind::BoxExistential { .. }
            | ExprKind::ExistentialUpcast { .. }
            | ExprKind::Block(..)
            | ExprKind::Adt(..)
            | ExprKind::Field { .. }
            | ExprKind::Closure { .. } => {
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
        lhs: Operand<'ctx>,
        rhs: Operand<'ctx>,
    ) -> BlockAnd<Rvalue<'ctx>> {
        let rv = match op {
            _ => Rvalue::BinaryOp { op, lhs, rhs },
        };

        block.and(rv)
    }
}
