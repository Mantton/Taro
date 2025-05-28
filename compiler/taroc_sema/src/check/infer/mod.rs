use crate::{
    GlobalContext,
    ty::{InferTy, Ty, TyKind},
};
use ena::unify::UnificationTableStorage;
use keys::{
    FloatVarID, FloatVarValue, IntVarID, IntVarValue, TypeVariableOrigin, TypeVariableStorage,
    TypeVariableTable,
};
use snapshot::IcxEventLogs;
use std::cell::RefCell;
use taroc_span::Span;

pub mod keys;
mod snapshot;
pub mod ty_var;

pub struct InferCtx<'ctx> {
    pub gcx: GlobalContext<'ctx>,
    pub inner: RefCell<InferCtxInner<'ctx>>,
    mode: InferMode,
}
pub enum InferMode {
    FnBody,
}

impl<'ctx> InferCtx<'ctx> {
    pub fn new(gcx: GlobalContext<'ctx>, mode: InferMode) -> InferCtx<'ctx> {
        InferCtx {
            gcx,
            mode,
            inner: RefCell::new(InferCtxInner::new()),
        }
    }
}

impl<'ctx> InferCtx<'ctx> {
    pub fn next_int_var(&self) -> Ty<'ctx> {
        let id = self
            .inner
            .borrow_mut()
            .int_unification_table()
            .new_key(IntVarValue::Unknown);

        let ty = self.gcx.mk_ty(TyKind::Infer(InferTy::IntVar(id)));
        ty
    }

    pub fn next_float_var(&self) -> Ty<'ctx> {
        let id = self
            .inner
            .borrow_mut()
            .float_unification_table()
            .new_key(FloatVarValue::Unknown);

        let ty = self.gcx.mk_ty(TyKind::Infer(InferTy::FloatVar(id)));
        ty
    }

    pub fn next_nil_var(&self) -> Ty<'ctx> {
        self.gcx.store.common_types.error
    }

    pub fn next_ty_var(&self, location: Span) -> Ty<'ctx> {
        let id = self
            .inner
            .borrow_mut()
            .type_variables()
            .new_var(TypeVariableOrigin { location });
        self.gcx.mk_ty(TyKind::Infer(InferTy::TyVar(id)))
    }
}

pub(crate) type UnificationTable<'a, 'tcx, T> = ena::unify::UnificationTable<
    ena::unify::InPlace<T, &'a mut ena::unify::UnificationStorage<T>, &'a mut IcxEventLogs<'tcx>>,
>;

#[derive(Default, Clone)]
pub struct InferCtxInner<'ctx> {
    event_logs: IcxEventLogs<'ctx>,
    int_storage: UnificationTableStorage<IntVarID>,
    float_storage: UnificationTableStorage<FloatVarID>,
    // nil_storage: UnificationTableStorage<NilVarID>,
    type_storage: TypeVariableStorage<'ctx>,
}

impl<'ctx> InferCtxInner<'ctx> {
    pub fn new() -> InferCtxInner<'ctx> {
        InferCtxInner {
            event_logs: Default::default(),
            int_storage: Default::default(),
            float_storage: Default::default(),
            type_storage: Default::default(),
        }
    }
}

impl<'ctx> InferCtxInner<'ctx> {
    #[inline]
    fn int_unification_table(&mut self) -> UnificationTable<'_, 'ctx, IntVarID> {
        self.int_storage.with_log(&mut self.event_logs)
    }

    #[inline]
    fn float_unification_table(&mut self) -> UnificationTable<'_, 'ctx, FloatVarID> {
        self.float_storage.with_log(&mut self.event_logs)
    }

    #[inline]
    fn type_variables(&mut self) -> TypeVariableTable<'_, 'ctx> {
        self.type_storage.with_log(&mut self.event_logs)
    }
}
