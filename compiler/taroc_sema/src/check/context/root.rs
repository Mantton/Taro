use std::{cell::RefCell, ops::Deref};

use rustc_hash::FxHashMap;
use taroc_hir::{DefinitionID, NodeID};

use crate::{
    GlobalContext,
    check::infer::{InferCtx, InferMode},
    ty::Ty,
};

pub struct TyCheckRootCtx<'ctx> {
    pub fn_id: DefinitionID,
    pub icx: InferCtx<'ctx>,
    pub locals: RefCell<FxHashMap<NodeID, Ty<'ctx>>>,
}

impl<'ctx> TyCheckRootCtx<'ctx> {
    pub fn new(gcx: GlobalContext<'ctx>, def_id: DefinitionID) -> TyCheckRootCtx<'ctx> {
        let icx = InferCtx::new(gcx, InferMode::FnBody);
        TyCheckRootCtx {
            fn_id: def_id,
            icx,
            locals: Default::default(),
        }
    }
}

impl<'ctx> Deref for TyCheckRootCtx<'ctx> {
    type Target = InferCtx<'ctx>;
    fn deref(&self) -> &Self::Target {
        &self.icx
    }
}
