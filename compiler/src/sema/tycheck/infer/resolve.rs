use crate::{
    compile::context::Gcx,
    sema::{
        models::Ty,
        tycheck::{fold::TypeFolder, fold::TypeSuperFoldable, infer::InferCtx},
    },
};

pub struct InferVarResolver<'a, 'gcx> {
    icx: &'a InferCtx<'gcx>,
}

impl<'a, 'tcx> InferVarResolver<'a, 'tcx> {
    #[inline]
    pub fn new(icx: &'a InferCtx<'tcx>) -> Self {
        InferVarResolver { icx }
    }
}

impl<'a, 'gcx> TypeFolder<'gcx> for InferVarResolver<'a, 'gcx> {
    fn gcx(&self) -> Gcx<'gcx> {
        self.icx.gcx
    }

    #[inline]
    fn fold_ty(&mut self, ty: Ty<'gcx>) -> Ty<'gcx> {
        if !ty.is_infer() {
            return ty;
        }

        let shallow = self.icx.shallow_resolve(ty);
        let res = shallow.super_fold_with(self);
        res
    }
}
