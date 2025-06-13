use crate::{
    GlobalContext,
    check::solver::ObligationCollector,
    infer::{InferCtx, InferMode},
    ty::Ty,
};
use rustc_hash::FxHashMap;
use std::{cell::RefCell, ops::Deref};
use taroc_hir::{DefinitionID, NodeID};

pub struct TyCheckRootCtx<'ctx> {
    pub fn_id: DefinitionID,
    pub icx: InferCtx<'ctx>,
    pub locals: RefCell<FxHashMap<NodeID, Ty<'ctx>>>,
    pub obligation_collector: RefCell<ObligationCollector<'ctx>>,
}

impl<'ctx> TyCheckRootCtx<'ctx> {
    pub fn new(gcx: GlobalContext<'ctx>, def_id: DefinitionID) -> TyCheckRootCtx<'ctx> {
        let icx = InferCtx::new(gcx, InferMode::FnBody);
        TyCheckRootCtx {
            fn_id: def_id,
            icx,
            locals: Default::default(),
            obligation_collector: RefCell::new(ObligationCollector::new()),
        }
    }
}

impl<'ctx> Deref for TyCheckRootCtx<'ctx> {
    type Target = InferCtx<'ctx>;
    fn deref(&self) -> &Self::Target {
        &self.icx
    }
}
