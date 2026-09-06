use crate::{
    compile::context::Gcx,
    sema::{
        models::{Const, Ty, TyKind},
        tycheck::{
            fold::{TypeFoldable, TypeFolder, TypeSuperFoldable},
            infer::InferCtx,
        },
    },
};

pub(super) struct InferVarResolver<'a, 'ctx> {
    icx: &'a InferCtx<'ctx>,
    replace_unresolved: bool,
}

impl<'a, 'ctx> InferVarResolver<'a, 'ctx> {
    pub fn new(icx: &'a InferCtx<'ctx>, replace_unresolved: bool) -> Self {
        Self {
            icx,
            replace_unresolved,
        }
    }
}

impl<'ctx> TypeFolder<'ctx> for InferVarResolver<'_, 'ctx> {
    fn gcx(&self) -> Gcx<'ctx> {
        self.icx.gcx
    }

    fn fold_ty(&mut self, ty: Ty<'ctx>) -> Ty<'ctx> {
        let shallow = self.icx.shallow_resolve(ty);
        if self.replace_unresolved && matches!(shallow.kind(), TyKind::Infer(_)) {
            return Ty::error(self.icx.gcx);
        }
        shallow.super_fold_with(self)
    }

    fn fold_const(&mut self, value: Const<'ctx>) -> Const<'ctx> {
        // Unknown consts remain inference values: there is no error ConstKind.
        // Release the inference-table borrow before traversing the const type.
        let value = self.icx.shallow_resolve_const(value);
        Const {
            ty: value.ty.fold_with(self),
            ..value
        }
    }
}
