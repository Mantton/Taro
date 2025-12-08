use crate::{
    compile::context::Gcx,
    hir::{self, DefinitionID, NodeID},
    sema::{models::Ty, tycheck::lower::TypeLowerer},
};
use rustc_hash::FxHashMap;
use std::{cell::RefCell, ops::Deref};

pub struct TyCheckRootCtx<'arena> {
    pub fn_id: DefinitionID,
    pub locals: RefCell<FxHashMap<NodeID, Ty<'arena>>>,
    pub gcx: Gcx<'arena>,
}

impl<'arena> TyCheckRootCtx<'arena> {
    pub fn new(fn_id: DefinitionID, gcx: Gcx<'arena>) -> TyCheckRootCtx<'arena> {
        TyCheckRootCtx {
            fn_id,
            locals: Default::default(),
            gcx,
        }
    }
}

impl<'arena> TyCheckRootCtx<'arena> {
    pub fn local_ty(&self, id: NodeID) -> Ty<'arena> {
        *self
            .locals
            .borrow()
            .get(&id)
            .expect("ICE: local variable must have type mapped")
    }
}

pub struct FnCtx<'rcx, 'arena> {
    pub id: DefinitionID,
    pub rcx: &'rcx TyCheckRootCtx<'arena>,
    pub return_ty: Option<Ty<'arena>>,
}

impl<'rcx, 'arena> FnCtx<'rcx, 'arena> {
    pub fn new(id: DefinitionID, rcx: &'rcx TyCheckRootCtx<'arena>) -> FnCtx<'rcx, 'arena> {
        FnCtx {
            rcx,
            id,
            return_ty: None,
        }
    }
}

impl<'rcx, 'arena> Deref for FnCtx<'rcx, 'arena> {
    type Target = TyCheckRootCtx<'arena>;
    fn deref(&self) -> &Self::Target {
        self.rcx
    }
}

impl<'arena> TypeLowerer<'arena> for FnCtx<'_, 'arena> {
    fn gcx(&self) -> Gcx<'arena> {
        self.gcx
    }
}

impl<'rcx, 'arena> FnCtx<'rcx, 'arena> {
    pub fn lower_type(&self, node: &hir::Type) -> Ty<'arena> {
        let ty = self.lowerer().lower_type(node);
        ty
    }
}
