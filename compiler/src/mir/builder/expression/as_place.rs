use crate::{
    hir::Mutability,
    mir::{
        BasicBlockId, BlockAnd, BlockAndExtension, LocalId, Place, PlaceElem, builder::MirBuilder,
    },
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
                let local = *self.locals.get(id).expect("lhs local");
                block.and(PlaceBuilder::from_local(local))
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
            ExprKind::Reference { .. } => todo!(),
            ExprKind::Make { .. } => {
                unreachable!("make expression cannot be used as place")
            }
            ExprKind::If { .. }
            | ExprKind::Assign { .. }
            | ExprKind::Literal(..)
            | ExprKind::Unary { .. }
            | ExprKind::Binary { .. }
            | ExprKind::Logical { .. }
            | ExprKind::Call { .. }
            | ExprKind::Block { .. }
            | ExprKind::Tuple { .. }
            | ExprKind::Adt { .. }
            | ExprKind::Zst { .. } => {
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
