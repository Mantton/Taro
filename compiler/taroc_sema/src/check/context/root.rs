use crate::{
    GlobalContext,
    check::solver::{Obligation, ObligationSolver},
    infer::InferCtx,
    ty::Ty,
    typing::TypingResult,
};
use rustc_hash::FxHashMap;
use std::{cell::RefCell, ops::Deref};
use taroc_hir::{DefinitionID, NodeID};

pub struct TyCheckRootCtx<'ctx> {
    pub _fn_id: DefinitionID,
    pub icx: InferCtx<'ctx>,
    pub locals: RefCell<FxHashMap<NodeID, Ty<'ctx>>>,
    pub solver: RefCell<ObligationSolver<'ctx>>,
    pub results: RefCell<TypingResult<'ctx>>,
}

impl<'ctx> TyCheckRootCtx<'ctx> {
    pub fn new(gcx: GlobalContext<'ctx>, def_id: DefinitionID) -> TyCheckRootCtx<'ctx> {
        let icx = InferCtx::new(gcx);
        TyCheckRootCtx {
            _fn_id: def_id,
            icx,
            locals: Default::default(),
            solver: RefCell::new(ObligationSolver::new()),
            results: Default::default(),
        }
    }
}

impl<'ctx> Deref for TyCheckRootCtx<'ctx> {
    type Target = InferCtx<'ctx>;
    fn deref(&self) -> &Self::Target {
        &self.icx
    }
}

impl<'ctx> TyCheckRootCtx<'ctx> {
    pub fn add_obligation(&self, obligation: Obligation<'ctx>) {
        self.solver.borrow_mut().add_obligation(obligation);
    }
}

impl<'ctx> TyCheckRootCtx<'ctx> {
    pub fn local_ty(&self, id: NodeID) -> Ty<'ctx> {
        *self
            .locals
            .borrow()
            .get(&id)
            .expect("ICE: local ty should have type mapped")
    }
}
