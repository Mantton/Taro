use crate::{
    compile::context::Gcx,
    hir::{self, DefinitionID, NodeID},
    sema::{
        models::Ty,
        tycheck::{
            infer::InferCtx, lower::TypeLowerer, results::TypeCheckResults,
            solve::DefaultFallbackGoalData,
        },
    },
    span::Span,
};
use rustc_hash::{FxHashMap, FxHashSet};
use std::cell::{Cell, RefCell};
use std::rc::Rc;

#[derive(Clone, Copy)]
pub(super) struct PendingAsyncCallSurfaceCheck {
    pub node_id: NodeID,
    pub callee_node_id: Option<NodeID>,
    pub span: Span,
    pub covered_by_await: bool,
}

/// Calls belong to the nearest lexical await expression, excluding closures.
/// Diagnose redundant markers only after overload resolution has completed.
pub(super) struct AwaitScope {
    pub span: Span,
    pub calls: Vec<NodeID>,
    pub complete: bool,
}

pub struct Checker<'arena> {
    pub context: Gcx<'arena>,
    pub locals: RefCell<FxHashMap<NodeID, LocalBinding<'arena>>>,
    /// Delayed receiver adjustments must retain the lexical unsafe permission
    /// of the source expression, not the context active when goals commit.
    pub(super) expression_contexts: RefCell<FxHashMap<NodeID, (Span, bool)>>,
    pub(super) reported_raw_dereferences: RefCell<FxHashSet<NodeID>>,
    /// Only intrinsic assignment writes back a value to the caller's slot;
    /// overload selection must finish before validating that destination.
    pub(super) pending_compound_assignments: RefCell<Vec<(NodeID, hir::Expression)>>,
    pub(super) pending_indices: RefCell<FxHashMap<NodeID, (hir::IndexCallNodes, Span)>>,
    pub(super) index_setter_uses: RefCell<FxHashSet<NodeID>>,
    pub(super) index_compound_uses: RefCell<FxHashSet<NodeID>>,
    pub(super) index_place_requests: RefCell<FxHashSet<NodeID>>,
    /// Receiver projections can cross into an independently shared object.
    /// Keep only index roots and projection type IDs, not cloned syntax trees.
    pub(super) receiver_index_roots: RefCell<FxHashMap<NodeID, Vec<(NodeID, Vec<NodeID>)>>>,
    pub return_ty: Cell<Option<Ty<'arena>>>,
    pub(super) constructor_self: Cell<Option<NodeID>>,
    pub(super) constructor_payload: Cell<Option<Ty<'arena>>>,
    pub(super) constructor_convenience: Cell<bool>,
    pub(super) opaque_return_candidates: RefCell<Vec<OpaqueReturnCandidate<'arena>>>,
    pub(super) loop_depth: Cell<usize>,
    pub(super) unsafe_depth: Cell<usize>,
    pub(super) defer_depth: Cell<usize>,
    pub(super) async_depth: Cell<usize>,
    pub(super) await_scope: Cell<Option<NodeID>>,
    pub(super) resolved_call_effects: RefCell<FxHashMap<NodeID, bool>>,
    pub(super) await_scopes: RefCell<FxHashMap<NodeID, AwaitScope>>,
    pub(super) direct_method_selection: Cell<Option<NodeID>>,
    pub(super) prechecked_bracket_receivers: RefCell<FxHashMap<NodeID, Ty<'arena>>>,
    pub(super) forced_async_closure_expr: Cell<Option<NodeID>>,
    pub(super) pending_async_surface_checks: RefCell<Vec<PendingAsyncCallSurfaceCheck>>,
    pub current_def: DefinitionID,
    pub results: Rc<RefCell<TypeCheckResults<'arena>>>,
    infer_cx: RefCell<Option<Rc<InferCtx<'arena>>>>,
    pub visible_traits: Rc<FxHashSet<DefinitionID>>,
}

pub(super) struct OpaqueReturnCandidate<'arena> {
    pub ty: Ty<'arena>,
    pub infer_cx: Option<Rc<InferCtx<'arena>>>,
    pub span: Span,
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
        results: Rc<RefCell<TypeCheckResults<'arena>>>,
    ) -> Checker<'arena> {
        let visible_traits = context.visible_traits(current_def);
        Checker {
            context,
            return_ty: Cell::new(None),
            constructor_self: Cell::new(None),
            constructor_payload: Cell::new(None),
            constructor_convenience: Cell::new(false),
            opaque_return_candidates: RefCell::new(Vec::new()),
            locals: Default::default(),
            expression_contexts: Default::default(),
            reported_raw_dereferences: Default::default(),
            pending_compound_assignments: Default::default(),
            pending_indices: Default::default(),
            index_setter_uses: Default::default(),
            index_compound_uses: Default::default(),
            index_place_requests: Default::default(),
            receiver_index_roots: Default::default(),
            loop_depth: Cell::new(0),
            unsafe_depth: Cell::new(0),
            defer_depth: Cell::new(0),
            async_depth: Cell::new(0),
            await_scope: Cell::new(None),
            await_scopes: Default::default(),
            resolved_call_effects: Default::default(),
            direct_method_selection: Cell::new(None),
            prechecked_bracket_receivers: Default::default(),
            forced_async_closure_expr: Cell::new(None),
            pending_async_surface_checks: RefCell::new(Vec::new()),
            current_def,
            results,
            infer_cx: RefCell::new(None),
            visible_traits,
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

    fn const_infer(
        &self,
        ty: crate::sema::models::Ty<'arena>,
        param: Option<&crate::sema::models::GenericParameterDefinition>,
        span: crate::span::Span,
    ) -> crate::sema::models::Const<'arena> {
        let infer_cx = self.infer_cx.borrow().clone();
        let Some(infer_cx) = infer_cx else {
            let gcx = self.gcx();
            gcx.dcx()
                .emit_error("missing generic argument".into(), Some(span));
            return crate::sema::models::Const {
                ty,
                kind: crate::sema::models::ConstKind::Value(crate::sema::models::ConstValue::Unit),
            };
        };

        let origin = crate::sema::tycheck::infer::keys::ConstVariableOrigin {
            location: span,
            param_name: param.map(|p| p.name),
        };
        infer_cx.new_const_var(ty, origin)
    }

    fn can_infer(&self) -> bool {
        self.infer_cx.borrow().is_some()
    }

    fn register_default_fallback(&self, data: DefaultFallbackGoalData<'arena>) {
        if let Some(icx) = self.infer_cx.borrow().as_ref() {
            icx.register_pending_fallback(data);
        }
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

    pub(super) fn with_await_scope<T>(
        &self,
        node_id: NodeID,
        span: Span,
        f: impl FnOnce() -> T,
    ) -> T {
        self.await_scopes.borrow_mut().insert(
            node_id,
            AwaitScope {
                span,
                calls: Vec::new(),
                complete: false,
            },
        );
        let prev = self.await_scope.replace(Some(node_id));
        let result = f();
        self.await_scope.set(prev);
        self.await_scopes
            .borrow_mut()
            .get_mut(&node_id)
            .unwrap()
            .complete = true;
        result
    }

    pub(super) fn call_is_awaited(&self) -> bool {
        self.await_scope.get().is_some() && self.defer_depth.get() == 0
    }

    pub(super) fn record_await_scope_call(&self, node_id: NodeID) {
        if let Some(scope) = self.await_scope.get() {
            self.await_scopes
                .borrow_mut()
                .get_mut(&scope)
                .unwrap()
                .calls
                .push(node_id);
        }
    }

    /// Context selects async-ness only while creating this fresh literal.
    pub(super) fn with_closure_argument_context<T>(
        &self,
        node_id: NodeID,
        force_async: bool,
        f: impl FnOnce() -> T,
    ) -> T {
        let previous_async = self.forced_async_closure_expr.get();
        if force_async {
            self.forced_async_closure_expr.set(Some(node_id));
        }
        let result = f();
        self.forced_async_closure_expr.set(previous_async);
        result
    }

    pub(super) fn is_forced_async_closure_expr(&self, node_id: NodeID) -> bool {
        self.forced_async_closure_expr.get() == Some(node_id)
    }

    pub(super) fn defer_async_call_surface_check(&self, node_id: NodeID, span: Span) {
        self.pending_async_surface_checks
            .borrow_mut()
            .push(PendingAsyncCallSurfaceCheck {
                node_id,
                callee_node_id: None,
                span,
                covered_by_await: self.call_is_awaited(),
            });
    }

    pub(super) fn defer_callable_async_surface_check(
        &self,
        node_id: NodeID,
        callee: NodeID,
        span: Span,
    ) {
        self.pending_async_surface_checks
            .borrow_mut()
            .push(PendingAsyncCallSurfaceCheck {
                node_id,
                callee_node_id: Some(callee),
                span,
                covered_by_await: self.call_is_awaited(),
            });
    }

    pub fn get_local(&self, id: NodeID) -> LocalBinding<'arena> {
        *self
            .locals
            .borrow()
            .get(&id)
            .expect("ICE: local variable must have type mapped")
    }

    pub fn try_get_local(&self, id: NodeID) -> Option<LocalBinding<'arena>> {
        self.locals.borrow().get(&id).cloned()
    }

    pub fn set_local(&self, id: NodeID, binding: LocalBinding<'arena>) {
        let mut locals = self.locals.borrow_mut();
        if locals.get(&id).is_some() {
            unreachable!("evaluated local more than once")
        };

        locals.insert(id, binding);
    }

    pub fn lower_type(&self, node: &hir::Type) -> Ty<'arena> {
        self.lowerer().lower_type(node)
    }

    pub fn finalize_local(&self, id: NodeID, ty: Ty<'arena>) {
        let mut locals = self.locals.borrow_mut();

        let existing = locals.get(&id);
        let mutable = existing.map(|b| b.mutable).unwrap_or(false);

        locals.insert(id, LocalBinding { ty, mutable });
        self.results.borrow_mut().record_node_type(id, ty);
    }
}
