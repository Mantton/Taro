use crate::{
    compile::context::Gcx,
    sema::{
        models::{Const, ConstKind, Ty, TyKind},
        tycheck::{fold::TypeFoldable, fold::TypeFolder, fold::TypeSuperFoldable, infer::InferCtx},
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

        // DEBUG
        // if let TyKind::Infer(_) = ty.kind() {
        //      let gcx = self.icx.gcx;
        //      eprintln!("DEBUG InferVarResolver: resolving {} -> {}", ty.format(gcx), shallow.format(gcx));
        // }

        shallow.super_fold_with(self)
    }

    fn fold_const(&mut self, c: Const<'gcx>) -> Const<'gcx> {
        let ConstKind::Infer(id) = c.kind else {
            return Const {
                ty: c.ty.fold_with(self),
                kind: c.kind,
            };
        };

        let value = {
            let mut inner = self.icx.inner.borrow_mut();
            let mut table = inner.const_variables();
            match table.probe(id) {
                crate::sema::tycheck::infer::keys::ConstVarValue::Known(value) => Some(value),
                crate::sema::tycheck::infer::keys::ConstVarValue::Param(param) => {
                    return Const {
                        ty: c.ty.fold_with(self),
                        kind: ConstKind::Param(param),
                    };
                }
                crate::sema::tycheck::infer::keys::ConstVarValue::Unknown => None,
            }
        };

        let ty = c.ty.fold_with(self);
        match value {
            Some(value) => Const {
                ty,
                kind: ConstKind::Value(value),
            },
            None => Const {
                ty,
                kind: ConstKind::Infer(id),
            },
        }
    }
}

/// Like InferVarResolver, but replaces unresolved inference variables with error type.
/// Use this when the infer_ctx is about to be dropped to prevent dangling type var references.
pub struct InferVarOrErrorResolver<'a, 'gcx> {
    icx: &'a InferCtx<'gcx>,
}

impl<'a, 'tcx> InferVarOrErrorResolver<'a, 'tcx> {
    #[inline]
    pub fn new(icx: &'a InferCtx<'tcx>) -> Self {
        InferVarOrErrorResolver { icx }
    }
}

impl<'a, 'gcx> TypeFolder<'gcx> for InferVarOrErrorResolver<'a, 'gcx> {
    fn gcx(&self) -> Gcx<'gcx> {
        self.icx.gcx
    }

    #[inline]
    fn fold_ty(&mut self, ty: Ty<'gcx>) -> Ty<'gcx> {
        let shallow = self.icx.shallow_resolve(ty);
        
        // If still an inference variable after resolution, replace with error type
        if matches!(shallow.kind(), TyKind::Infer(_)) {
            return Ty::error(self.icx.gcx);
        }

        shallow.super_fold_with(self)
    }

    fn fold_const(&mut self, c: Const<'gcx>) -> Const<'gcx> {
        let ConstKind::Infer(id) = c.kind else {
            return Const {
                ty: c.ty.fold_with(self),
                kind: c.kind,
            };
        };

        let value = {
            let mut inner = self.icx.inner.borrow_mut();
            let mut table = inner.const_variables();
            match table.probe(id) {
                crate::sema::tycheck::infer::keys::ConstVarValue::Known(value) => Some(value),
                crate::sema::tycheck::infer::keys::ConstVarValue::Param(param) => {
                    return Const {
                        ty: c.ty.fold_with(self),
                        kind: ConstKind::Param(param),
                    };
                }
                crate::sema::tycheck::infer::keys::ConstVarValue::Unknown => None,
            }
        };

        let ty = c.ty.fold_with(self);
        match value {
            Some(value) => Const {
                ty,
                kind: ConstKind::Value(value),
            },
            // Replace unresolved const vars with the original (could be error const, but keeping as-is for now)
            None => Const {
                ty,
                kind: ConstKind::Infer(id),
            },
        }
    }
}
