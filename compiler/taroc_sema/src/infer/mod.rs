use crate::{
    GlobalContext,
    fold::TypeFoldable,
    infer::{
        fn_var::{
            FnVarData, FunctionVariableOrigin, FunctionVariableStorage, FunctionVariableTable,
        },
        resolve::InferVarResolver,
    },
    ty::{
        FloatTy, GenericArgument, GenericArguments, GenericParameterDefinition, InferTy, IntTy, Ty,
        TyKind,
    },
    utils::GenericsBuilder,
};
use ena::{undo_log::Rollback, unify::UnificationTableStorage};
use keys::{
    FloatVarID, FloatVarValue, IntVarID, IntVarValue, TypeVariableOrigin, TypeVariableStorage,
    TypeVariableTable,
};
use snapshot::IcxEventLogs;
use std::{cell::RefCell, rc::Rc};
use taroc_hir::{BinaryOperator, DefinitionID, UnaryOperator};
use taroc_span::Span;

pub mod fn_var;
pub mod keys;
mod resolve;
mod snapshot;
pub mod ty_var;

pub struct InferCtx<'ctx> {
    pub gcx: GlobalContext<'ctx>,
    pub inner: RefCell<InferCtxInner<'ctx>>,
}

impl<'ctx> InferCtx<'ctx> {
    pub fn new(gcx: GlobalContext<'ctx>) -> InferCtx<'ctx> {
        InferCtx {
            gcx,
            inner: RefCell::new(InferCtxInner::new()),
        }
    }
}

impl<'ctx> InferCtx<'ctx> {
    /// Default any unconstrained integer/float inference variables to concrete types
    /// so subsequent solver passes can make progress.
    ///
    /// - `IntVar(Unknown)` -> `Int(I32)`
    /// - `FloatVar(Unknown)` -> `Float(F64)`
    pub fn default_numeric_vars(&self) {
        let mut inner = self.inner.borrow_mut();

        // Default integer vars
        let int_len = inner.int_storage.len();
        {
            let mut table = inner.int_unification_table();
            for i in 0..int_len {
                let id = IntVarID::new(i as u32);
                let root = table.find(id);
                match table.probe_value(root) {
                    IntVarValue::Unknown => {
                        table.union_value(root, IntVarValue::Signed(IntTy::I32));
                    }
                    _ => {}
                }
            }
        }

        // Default float vars
        let float_len = inner.float_storage.len();
        {
            let mut table = inner.float_unification_table();
            for i in 0..float_len {
                let id = FloatVarID::new(i as u32);
                let root = table.find(id);
                match table.probe_value(root) {
                    FloatVarValue::Unknown => {
                        table.union_value(root, FloatVarValue::Known(FloatTy::F64));
                    }
                    _ => {}
                }
            }
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

    pub fn next_ty_var(&self, location: Span) -> Ty<'ctx> {
        let id = self
            .inner
            .borrow_mut()
            .type_variables()
            .new_var(TypeVariableOrigin { location });
        self.gcx.mk_ty(TyKind::Infer(InferTy::TyVar(id)))
    }

    pub fn next_fn_var(&self, location: Span, mut data: FnVarData) -> Ty<'ctx> {
        data.update(self.gcx);
        let id = self
            .inner
            .borrow_mut()
            .fn_variables()
            .new_var(FunctionVariableOrigin {
                location,
                data: Rc::new(RefCell::new(data)),
            });
        self.gcx.mk_ty(TyKind::Infer(InferTy::FnVar(id)))
    }
}

impl<'ctx> InferCtx<'ctx> {
    pub fn fresh_args_for_def(&self, def_id: DefinitionID, span: Span) -> GenericArguments<'ctx> {
        GenericsBuilder::for_item(self.gcx, def_id, |p, _| self.var_for_generic_param(p, span))
    }

    pub fn var_for_generic_param(
        &self,
        param: &GenericParameterDefinition,
        span: Span,
    ) -> GenericArgument<'ctx> {
        match param.kind {
            crate::ty::GenericParameterDefinitionKind::Type { .. } => {
                let ty_var_id = self
                    .inner
                    .borrow_mut()
                    .type_variables()
                    .new_var(TypeVariableOrigin { location: span });

                let ty = self.gcx.mk_ty(TyKind::Infer(InferTy::TyVar(ty_var_id)));
                GenericArgument::Type(ty)
            }
            crate::ty::GenericParameterDefinitionKind::Const { .. } => todo!(),
        }
    }
}

impl<'ctx> InferCtx<'ctx> {
    fn start_snapshot(&self) -> self::snapshot::Snapshot<'ctx> {
        let mut inner = self.inner.borrow_mut();
        let snap = inner.event_logs.start_snapshot();
        snap
    }

    fn rollback_to(&self, snapshot: self::snapshot::Snapshot<'ctx>) {
        let mut inner = self.inner.borrow_mut();
        inner.rollback_to(snapshot)
    }

    pub fn probe<R, F>(&self, f: F) -> R
    where
        F: FnOnce(&self::snapshot::Snapshot<'ctx>) -> R,
    {
        let snapshot = self.start_snapshot();
        let r = f(&snapshot);
        self.rollback_to(snapshot);
        r
    }
}

impl<'ctx> InferCtx<'ctx> {
    pub fn shallow_resolve(&self, ty: Ty<'ctx>) -> Ty<'ctx> {
        let TyKind::Infer(inner) = ty.kind() else {
            return ty;
        };

        match inner {
            InferTy::TyVar(vid) => {
                // can resolve to float or int var, so resolve those too
                let known = self.inner.borrow_mut().type_variables().probe(vid).known();
                known.map_or(ty, |t| self.shallow_resolve(t))
            }
            InferTy::FnVar(vid) => {
                // can resolve to another fn var, so resolve too
                let known = self.inner.borrow_mut().fn_variables().probe(vid).known();
                known.map_or(ty, |t| self.shallow_resolve(t))
            }
            InferTy::IntVar(vid) => {
                match self
                    .inner
                    .borrow_mut()
                    .int_unification_table()
                    .probe_value(vid)
                {
                    IntVarValue::Unknown => ty,
                    IntVarValue::Signed(k) => self.gcx.mk_ty(TyKind::Int(k)),
                    IntVarValue::Unsigned(k) => self.gcx.mk_ty(TyKind::UInt(k)),
                }
            }
            InferTy::FloatVar(vid) => {
                match self
                    .inner
                    .borrow_mut()
                    .float_unification_table()
                    .probe_value(vid)
                {
                    FloatVarValue::Unknown => ty,
                    FloatVarValue::Known(k) => self.gcx.mk_ty(TyKind::Float(k)),
                }
            }
            InferTy::FreshTy(_) => ty,
        }
    }

    pub fn resolve_vars_if_possible<T>(&self, value: T) -> T
    where
        T: TypeFoldable<'ctx>,
    {
        let mut resolver = InferVarResolver::new(self);
        value.fold_with(&mut resolver)
    }
}

impl<'ctx> InferCtx<'ctx> {
    pub fn equate_int_vars_raw(&self, a: IntVarID, b: IntVarID) {
        self.inner.borrow_mut().int_unification_table().union(a, b);
    }

    pub fn equate_float_vars_raw(&self, a: FloatVarID, b: FloatVarID) {
        self.inner
            .borrow_mut()
            .float_unification_table()
            .union(a, b);
    }
}

impl<'ctx> InferCtx<'ctx> {
    pub fn instantiate_int_var_raw(&self, id: IntVarID, value: IntVarValue) {
        self.inner
            .borrow_mut()
            .int_unification_table()
            .union_value(id, value);
    }

    pub fn instantiate_float_var_raw(&self, id: FloatVarID, value: FloatVarValue) {
        self.inner
            .borrow_mut()
            .float_unification_table()
            .union_value(id, value);
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
    type_storage: TypeVariableStorage<'ctx>,
    fn_storage: FunctionVariableStorage<'ctx>,
    pub overload_calls: Vec<OverloadCallRecord>,
    pub adjustments: Vec<AdjustmentRecord>,
}

impl<'ctx> InferCtxInner<'ctx> {
    pub fn new() -> InferCtxInner<'ctx> {
        InferCtxInner {
            event_logs: Default::default(),
            int_storage: Default::default(),
            float_storage: Default::default(),
            type_storage: Default::default(),
            fn_storage: Default::default(),
            overload_calls: Default::default(),
            adjustments: Default::default(),
        }
    }
}

impl<'ctx> InferCtxInner<'ctx> {
    #[inline]
    pub fn int_unification_table(&mut self) -> UnificationTable<'_, 'ctx, IntVarID> {
        self.int_storage.with_log(&mut self.event_logs)
    }

    #[inline]
    pub fn float_unification_table(&mut self) -> UnificationTable<'_, 'ctx, FloatVarID> {
        self.float_storage.with_log(&mut self.event_logs)
    }

    #[inline]
    pub fn type_variables(&mut self) -> TypeVariableTable<'_, 'ctx> {
        self.type_storage.with_log(&mut self.event_logs)
    }

    #[inline]
    pub fn fn_variables(&mut self) -> FunctionVariableTable<'_, 'ctx> {
        self.fn_storage.with_log(&mut self.event_logs)
    }
}

impl<'ctx> InferCtxInner<'ctx> {
    pub fn rollback_to(&mut self, snapshot: self::snapshot::Snapshot<'ctx>) {
        while self.event_logs.logs.len() > snapshot.length {
            let undo = self.event_logs.logs.pop().unwrap();
            self.reverse(undo);
        }

        self.type_storage.finalize_rollback();
        self.fn_storage.finalize_rollback();

        if self.event_logs.open_snapshots == 1 {
            // After the root snapshot the undo log should be empty.
            assert!(snapshot.length == 0);
            assert!(self.event_logs.logs.is_empty());
        }

        self.event_logs.open_snapshots -= 1;
    }
}

// MARK: Tracking structures and helpers
#[derive(Debug, Clone, Copy)]
pub enum OverloadResolution {
    Intrinsic,
    Member(DefinitionID),
}

#[derive(Debug, Clone, Copy)]
pub enum OverloadCallKind {
    Method,
    Unary(UnaryOperator),
    Binary(BinaryOperator),
    Index,
}

#[derive(Debug, Clone, Copy)]
pub struct OverloadCallRecord {
    pub span: Span,
    pub kind: OverloadCallKind,
    pub resolution: OverloadResolution,
}

#[derive(Debug, Clone)]
pub struct AdjustmentRecord {
    pub span: Span,
    pub adjustments: Vec<crate::ty::Adjustment>,
}

impl<'ctx> InferCtx<'ctx> {
    pub fn record_overload_call(
        &self,
        span: Span,
        kind: OverloadCallKind,
        resolution: OverloadResolution,
    ) {
        self.inner
            .borrow_mut()
            .overload_calls
            .push(OverloadCallRecord {
                span,
                kind,
                resolution,
            });
    }

    pub fn record_adjustments(&self, span: Span, adjustments: Vec<crate::ty::Adjustment>) {
        if adjustments.is_empty() {
            return;
        }
        self.inner
            .borrow_mut()
            .adjustments
            .push(AdjustmentRecord { span, adjustments });
    }
}
