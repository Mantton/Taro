use crate::{
    mir::{self, Constant, ConstantKind, builder::MirBuilder},
    sema::models::GenericArguments,
    thir::{self, ExprId, ExprKind},
};

impl<'ctx, 'thir> MirBuilder<'ctx, 'thir> {
    pub fn as_constant(&mut self, expr: ExprId) -> Constant<'ctx> {
        let expr = &self.thir.exprs[expr];

        match &expr.kind {
            ExprKind::Literal(constant) => self.lower_constant(constant),
            ExprKind::Zst { id, generic_args } => {
                let kind = self.gcx.definition_kind(*id);
                let value = match kind {
                    crate::hir::DefinitionKind::Function
                    | crate::hir::DefinitionKind::AssociatedFunction
                    | crate::hir::DefinitionKind::AssociatedOperator
                    | crate::hir::DefinitionKind::VariantConstructor(
                        crate::sema::resolve::models::VariantCtorKind::Function,
                    ) => mir::ConstantKind::Function(
                        *id,
                        (*generic_args).unwrap_or(GenericArguments::empty()),
                        expr.ty,
                    ),
                    crate::hir::DefinitionKind::ModuleVariable => {
                        mir::ConstantKind::GlobalVariableAddress(*id)
                    }
                    _ => unreachable!("unexpected ZST definition kind in MIR constant lowering"),
                };

                Constant { ty: expr.ty, value }
            }
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
            thir::ConstantKind::ConstParam(param) => ConstantKind::ConstParam(*param),
        };
        Constant { ty: lit.ty, value }
    }
}
