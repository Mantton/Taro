use super::root::TyCheckRootCtx;
use crate::ty::{ParamEnv, Ty};
use std::ops::Deref;
use taroc_hir::DefinitionID;

pub struct FnCtx<'rcx, 'ctx> {
    pub id: DefinitionID,
    pub rcx: &'rcx TyCheckRootCtx<'ctx>,
    pub ret_ty: Option<Ty<'ctx>>,
    pub param_env: ParamEnv<'ctx>,
}

impl<'rcx, 'ctx> FnCtx<'rcx, 'ctx> {
    pub fn new(rcx: &'rcx TyCheckRootCtx<'ctx>, id: DefinitionID) -> FnCtx<'rcx, 'ctx> {
        FnCtx {
            rcx,
            id,
            ret_ty: None,
            param_env: rcx.gcx.param_env(id),
        }
    }

    pub fn param_env(&self) -> ParamEnv<'ctx> {
        self.param_env
    }
}

impl<'rcx, 'gcx> Deref for FnCtx<'rcx, 'gcx> {
    type Target = TyCheckRootCtx<'gcx>;
    fn deref(&self) -> &Self::Target {
        self.rcx
    }
}
