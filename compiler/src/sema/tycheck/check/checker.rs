use crate::{
    compile::context::Gcx,
    hir::{self, NodeID},
    sema::{models::Ty, tycheck::lower::TypeLowerer},
};
use rustc_hash::FxHashMap;
use std::cell::RefCell;

pub struct Checker<'arena> {
    pub context: Gcx<'arena>,
    pub locals: RefCell<FxHashMap<NodeID, Ty<'arena>>>,
    pub return_ty: Option<Ty<'arena>>,
}

impl<'arena> Checker<'arena> {
    pub fn new(context: Gcx<'arena>) -> Checker<'arena> {
        Checker {
            context,
            return_ty: None,
            locals: Default::default(),
        }
    }
}

impl<'arena> TypeLowerer<'arena> for Checker<'arena> {
    fn gcx(&self) -> Gcx<'arena> {
        self.context
    }
}

impl<'arena> Checker<'arena> {
    pub fn get_local_ty(&self, id: NodeID) -> Ty<'arena> {
        *self
            .locals
            .borrow()
            .get(&id)
            .expect("ICE: local variable must have type mapped")
    }

    pub fn set_local_ty(&self, id: NodeID, ty: Ty<'arena>) {
        let mut locals = self.locals.borrow_mut();
        if locals.get(&id).is_some() {
            unreachable!("evaluated local more than once")
        };

        locals.insert(id, ty);
    }

    pub fn lower_type(&self, node: &hir::Type) -> Ty<'arena> {
        let ty = self.lowerer().lower_type(node);
        ty
    }
}
