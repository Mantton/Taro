use crate::{
    hir::Mutability,
    mir::{
        BasicBlockId, BlockAnd, BlockAndExtension, LocalId, Place, PlaceElem, builder::MirBuilder,
    },
    sema::models::{CaptureKind, TyKind},
    thir::{ExprId, ExprKind},
    unpack,
};

impl<'ctx, 'thir> MirBuilder<'ctx, 'thir> {
    pub fn as_place(&mut self, mut block: BasicBlockId, expr_id: ExprId) -> BlockAnd<Place<'ctx>> {
        let builder = unpack!(block = self.as_place_builder(block, expr_id));
        block.and(builder.to_place(self))
    }

    pub(crate) fn as_place_builder(
        &mut self,
        block: BasicBlockId,
        expr_id: ExprId,
    ) -> BlockAnd<PlaceBuilder<'ctx>> {
        self.expr_as_place(block, expr_id, Mutability::Mutable)
    }

    fn expr_as_place(
        &mut self,
        mut block: BasicBlockId,
        expr_id: ExprId,
        mutability: Mutability,
    ) -> BlockAnd<PlaceBuilder<'ctx>> {
        let expr = &self.thir.exprs[expr_id];

        match &expr.kind {
            ExprKind::Local(id) => {
                if let Some(place) = self.place_bindings.get(id) {
                    block.and(PlaceBuilder {
                        base: place.local,
                        projection: place.projection.clone(),
                    })
                } else {
                    let local = *self.locals.get(id).expect("lhs local");
                    block.and(PlaceBuilder::from_local(local))
                }
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
                    CaptureKind::ByRef { mutable } => {
                        let mutability = if *mutable {
                            Mutability::Mutable
                        } else {
                            Mutability::Immutable
                        };
                        crate::sema::models::Ty::new(
                            TyKind::Reference(expr.ty, mutability),
                            self.gcx,
                        )
                    }
                    CaptureKind::ByCopy | CaptureKind::ByMove => expr.ty,
                };

                projection.push(PlaceElem::Field(*field_index, field_ty));

                if matches!(capture_kind, CaptureKind::ByRef { .. }) {
                    projection.push(PlaceElem::Deref);
                }

                block.and(PlaceBuilder {
                    base: self_local,
                    projection,
                })
            }
            ExprKind::Deref(expr_id) => {
                let mut base = unpack!(block = self.expr_as_place(block, *expr_id, mutability));
                base.projection.push(PlaceElem::Deref);
                block.and(base)
            }
            ExprKind::Field { lhs, index } => {
                let mut builder = unpack!(block = self.expr_as_place(block, *lhs, mutability));
                builder.projection.push(PlaceElem::Field(*index, expr.ty));
                block.and(builder)
            }
            ExprKind::Make { .. } => {
                unreachable!("make expression cannot be used as place")
            }
            ExprKind::Reference { .. }
            | ExprKind::If { .. }
            | ExprKind::Match { .. }
            | ExprKind::Return { .. }
            | ExprKind::Break
            | ExprKind::Continue
            | ExprKind::Assign { .. }
            | ExprKind::AssignOp { .. }
            | ExprKind::Literal(..)
            | ExprKind::Unary { .. }
            | ExprKind::Binary { .. }
            | ExprKind::Cast { .. }
            | ExprKind::ClosureToFnPointer { .. }
            | ExprKind::Logical { .. }
            | ExprKind::Call { .. }
            | ExprKind::BoxExistential { .. }
            | ExprKind::ExistentialUpcast { .. }
            | ExprKind::Block { .. }
            | ExprKind::Tuple { .. }
            | ExprKind::Array { .. }
            | ExprKind::Repeat { .. }
            | ExprKind::Adt { .. }
            | ExprKind::Zst { .. }
            | ExprKind::Closure { .. } => {
                let temp = unpack!(block = self.as_temp(block, expr_id));
                block.and(PlaceBuilder::from_local(temp))
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct PlaceBuilder<'tcx> {
    base: LocalId,
    projection: Vec<PlaceElem<'tcx>>,
}

impl<'a> PlaceBuilder<'a> {
    pub fn from_local(local: LocalId) -> PlaceBuilder<'a> {
        PlaceBuilder {
            base: local,
            projection: vec![],
        }
    }

    pub fn to_place(&self, builder: &MirBuilder<'a, '_>) -> Place<'a> {
        self.try_to_place(builder).unwrap()
    }

    pub fn try_to_place(&self, _: &MirBuilder<'a, '_>) -> Option<Place<'a>> {
        Some(Place {
            local: self.base,
            projection: self.projection.clone(),
        })
    }
}
