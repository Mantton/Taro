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
        // Always shallow-resolve at this node, then structurally recurse. This ensures we resolve
        // inference variables nested inside non-infer shells like `&T`, `*T`, tuples, and
        // function pointers.
        let shallow = self.icx.shallow_resolve(ty);
        shallow.super_fold_with(self)
    }
}
