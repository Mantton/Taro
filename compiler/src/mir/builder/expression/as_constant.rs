use crate::{
    mir::{
        self, BasicBlockId, BlockAnd, BlockAndExtension, Constant, ConstantKind,
        builder::MirBuilder,
    },
    thir::{self, ExprId, ExprKind},
    unpack,
};

impl<'ctx, 'thir> MirBuilder<'ctx, 'thir> {
    pub fn as_constant(&mut self, expr: ExprId) -> Constant<'ctx> {
        let expr = &self.thir.exprs[expr];

        match &expr.kind {
            ExprKind::Literal(constant) => self.lower_constant(constant),
            ExprKind::Zst { id } => Constant {
                ty: expr.ty,
                value: mir::ConstantKind::Function(*id, expr.ty),
            },
            _ => unreachable!(),
        }
    }

    fn lower_constant(&self, lit: &thir::Constant<'ctx>) -> Constant<'ctx> {
        let value = match &lit.value {
            thir::ConstantKind::Bool(b) => ConstantKind::Bool(*b),
            thir::ConstantKind::Rune(r) => ConstantKind::Rune(*r),
            thir::ConstantKind::String(s) => ConstantKind::String(*s),
            thir::ConstantKind::Integer(i) => ConstantKind::Integer(*i),
            thir::ConstantKind::Float(f) => ConstantKind::Float(*f),
            thir::ConstantKind::Unit => ConstantKind::Unit,
        };
        Constant { ty: lit.ty, value }
    }
}
