use super::root::TyCheckRootCtx;
use crate::ty::Ty;
use std::ops::Deref;
use taroc_hir::DefinitionID;

pub struct FnCtx<'rcx, 'ctx> {
    pub id: DefinitionID,
    pub rcx: &'rcx TyCheckRootCtx<'ctx>,
    pub ret_ty: Option<Ty<'ctx>>,
}

impl<'rcx, 'ctx> FnCtx<'rcx, 'ctx> {
    pub fn new(rcx: &'rcx TyCheckRootCtx<'ctx>, id: DefinitionID) -> FnCtx<'rcx, 'ctx> {
        FnCtx {
            rcx,
            id,
            ret_ty: None,
        }
    }
}

impl<'rcx, 'gcx> Deref for FnCtx<'rcx, 'gcx> {
    type Target = TyCheckRootCtx<'gcx>;
    fn deref(&self) -> &Self::Target {
        self.rcx
    }
}
