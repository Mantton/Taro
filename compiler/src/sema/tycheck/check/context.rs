use crate::{
    compile::context::Gcx,
    hir::{self, DefinitionID, NodeID},
    sema::{
        models::{CalleeOrigin, Ty},
        tycheck::{
            infer::InferCtx,
            lower::TypeLowerer,
            solve::{Goal, Obligation, ObligationCtx},
        },
    },
    span::Span,
};
use rustc_hash::FxHashMap;
use std::{cell::RefCell, ops::Deref};

pub struct TyCheckRootCtx<'arena> {
    pub fn_id: DefinitionID,
    pub icx: InferCtx<'arena>,
    pub locals: RefCell<FxHashMap<NodeID, Ty<'arena>>>,
    pub solver: RefCell<ObligationCtx<'arena>>,
}

impl<'arena> TyCheckRootCtx<'arena> {
    pub fn new(fn_id: DefinitionID, gcx: Gcx<'arena>) -> TyCheckRootCtx<'arena> {
        let icx = InferCtx::new(gcx);

        TyCheckRootCtx {
            fn_id,
            locals: Default::default(),
            icx,
            solver: RefCell::new(ObligationCtx::new()),
        }
    }
}

impl<'ctx> Deref for TyCheckRootCtx<'ctx> {
    type Target = InferCtx<'ctx>;
    fn deref(&self) -> &Self::Target {
        &self.icx
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

    pub fn add_obligation(&self, obligation: Obligation<'arena>) {
        self.solver.borrow_mut().add_obligation(obligation);
    }
}

pub struct FnCtx<'rcx, 'arena> {
    pub id: DefinitionID,
    pub rcx: &'rcx TyCheckRootCtx<'arena>,
    pub return_ty: Option<Ty<'arena>>,
    pub callee_origins: RefCell<FxHashMap<NodeID, CalleeOrigin<'arena>>>,
}

impl<'rcx, 'arena> FnCtx<'rcx, 'arena> {
    pub fn new(id: DefinitionID, rcx: &'rcx TyCheckRootCtx<'arena>) -> FnCtx<'rcx, 'arena> {
        FnCtx {
            rcx,
            id,
            return_ty: None,
            callee_origins: Default::default(),
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

impl<'rcx, 'arena> FnCtx<'rcx, 'arena> {
    pub fn add_coercion_constraint(&self, from: Ty<'arena>, to: Ty<'arena>, location: Span) {
        // break early
        if from == to {
            return;
        }

        let obligation = Obligation {
            location,
            goal: Goal::Equal(to, from),
        };
        self.add_obligation(obligation);
    }
}
