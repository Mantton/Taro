use crate::{
    compile::context::Gcx,
    hir::{self, DefinitionID, NodeID},
    sema::{models::Ty, tycheck::lower::TypeLowerer},
};
use rustc_hash::FxHashMap;
use std::cell::{Cell, RefCell};

pub struct Checker<'arena> {
    pub context: Gcx<'arena>,
    pub locals: RefCell<FxHashMap<NodeID, LocalBinding<'arena>>>,
    pub return_ty: Option<Ty<'arena>>,
    pub(super) loop_depth: Cell<usize>,
    pub current_def: DefinitionID,
}

#[derive(Clone, Copy)]
pub struct LocalBinding<'arena> {
    pub ty: Ty<'arena>,
    pub mutable: bool,
}

impl<'arena> Checker<'arena> {
    pub fn new(context: Gcx<'arena>, current_def: DefinitionID) -> Checker<'arena> {
        Checker {
            context,
            return_ty: None,
            locals: Default::default(),
            loop_depth: Cell::new(0),
            current_def,
        }
    }
}

impl<'arena> TypeLowerer<'arena> for Checker<'arena> {
    fn gcx(&self) -> Gcx<'arena> {
        self.context
    }

    fn current_definition(&self) -> Option<DefinitionID> {
        Some(self.current_def)
    }
}

impl<'arena> Checker<'arena> {
    pub fn get_local(&self, id: NodeID) -> LocalBinding<'arena> {
        *self
            .locals
            .borrow()
            .get(&id)
            .expect("ICE: local variable must have type mapped")
    }

    pub fn set_local(&self, id: NodeID, binding: LocalBinding<'arena>) {
        let mut locals = self.locals.borrow_mut();
        if locals.get(&id).is_some() {
            unreachable!("evaluated local more than once")
        };

        locals.insert(id, binding);
    }

    pub fn lower_type(&self, node: &hir::Type) -> Ty<'arena> {
        let ty = self.lowerer().lower_type(node);
        ty
    }

    pub fn finalize_local(&self, id: NodeID, ty: Ty<'arena>) {
        let mut locals = self.locals.borrow_mut();

        let existing = locals.get(&id);
        let mutable = existing.map(|b| b.mutable).unwrap_or(false);

        locals.insert(id, LocalBinding { ty, mutable });
        self.context.cache_node_type(id, ty);
    }
}
