use crate::{
    compile::context::Gcx,
    hir::{self, DefinitionID, NodeID},
    sema::{
        models::Ty,
        tycheck::{infer::InferCtx, lower::TypeLowerer, results::TypeCheckResults},
    },
};
use rustc_hash::FxHashMap;
use std::cell::{Cell, RefCell};
use std::rc::Rc;

pub struct Checker<'arena> {
    pub context: Gcx<'arena>,
    pub locals: RefCell<FxHashMap<NodeID, LocalBinding<'arena>>>,
    pub return_ty: Option<Ty<'arena>>,
    pub(super) loop_depth: Cell<usize>,
    pub(super) unsafe_depth: Cell<usize>,
    pub current_def: DefinitionID,
    pub results: RefCell<TypeCheckResults<'arena>>,
    infer_cx: RefCell<Option<Rc<InferCtx<'arena>>>>,
}

#[derive(Clone, Copy)]
pub struct LocalBinding<'arena> {
    pub ty: Ty<'arena>,
    pub mutable: bool,
}

impl<'arena> Checker<'arena> {
    pub fn new(
        context: Gcx<'arena>,
        current_def: DefinitionID,
        results: RefCell<TypeCheckResults<'arena>>,
    ) -> Checker<'arena> {
        Checker {
            context,
            return_ty: None,
            locals: Default::default(),
            loop_depth: Cell::new(0),
            unsafe_depth: Cell::new(0),
            current_def,
            results,
            infer_cx: RefCell::new(None),
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

    fn ty_infer(
        &self,
        _: Option<&crate::sema::models::GenericParameterDefinition>,
        span: crate::span::Span,
    ) -> crate::sema::models::Ty<'arena> {
        let infer_cx = self.infer_cx.borrow().clone();
        let Some(infer_cx) = infer_cx else {
            let gcx = self.gcx();
            gcx.dcx()
                .emit_error("missing generic argument".into(), Some(span));
            return gcx.types.error;
        };

        infer_cx.next_ty_var(span)
    }
}

impl<'arena> Checker<'arena> {
    pub(super) fn with_infer_ctx<T>(
        &self,
        infer_cx: Rc<InferCtx<'arena>>,
        f: impl FnOnce() -> T,
    ) -> T {
        let prev = {
            let mut slot = self.infer_cx.borrow_mut();
            std::mem::replace(&mut *slot, Some(infer_cx))
        };
        let result = f();
        *self.infer_cx.borrow_mut() = prev;
        result
    }

    pub(super) fn infer_ctx(&self) -> Option<Rc<InferCtx<'arena>>> {
        self.infer_cx.borrow().clone()
    }

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
        self.results.borrow_mut().record_node_type(id, ty);
    }
}
