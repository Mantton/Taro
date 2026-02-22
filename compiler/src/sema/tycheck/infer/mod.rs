use crate::{
    compile::context::Gcx,
    sema::{
        models::{
            Const, ConstKind, ConstVarID, FloatTy, GenericArgument, GenericArguments,
            GenericParameterDefinition, GenericParameterDefinitionKind, InferTy, IntTy, Ty, TyKind,
            TyVarID,
        },
        resolve::models::DefinitionID,
        tycheck::{
            fold::TypeFoldable,
            infer::{
                keys::{
                    ConstVarValue, ConstVariableOrigin, ConstVariableStorage, ConstVariableTable,
                    FloatVarID, FloatVarValue, IntVarID, IntVarValue, NilVarID, NilVarValue,
                    TypeVariableOrigin, TypeVariableStorage, TypeVariableTable,
                },
                resolve::InferVarResolver,
                snapshot::IcxEvent,
            },
            lower::{DefTyLoweringCtx, TypeLowerer},
            solve::DefaultFallbackGoalData,
            utils::generics::GenericsBuilder,
        },
    },
    span::Span,
};
use ena::{undo_log::Rollback, unify::UnificationTableStorage};

use rustc_hash::FxHashMap;
use snapshot::IcxEventLogs;
use std::cell::RefCell;

pub mod keys;
mod resolve;
mod snapshot;

pub struct InferCtx<'ctx> {
    pub gcx: Gcx<'ctx>,
    pub inner: RefCell<InferCtxInner<'ctx>>,
}

impl<'ctx> InferCtx<'ctx> {
    pub fn new(gcx: Gcx<'ctx>) -> InferCtx<'ctx> {
        InferCtx {
            gcx,
            inner: RefCell::new(InferCtxInner::new()),
        }
    }
}

impl<'ctx> InferCtx<'ctx> {
    pub fn next_ty_var(&self, location: Span) -> Ty<'ctx> {
        let id = self
            .inner
            .borrow_mut()
            .type_variables()
            .new_var(TypeVariableOrigin {
                location,
                param_name: None,
            });
        Ty::new(TyKind::Infer(InferTy::TyVar(id)), self.gcx)
    }

    pub fn next_int_var(&self) -> Ty<'ctx> {
        let id = self
            .inner
            .borrow_mut()
            .int_unification_table()
            .new_key(IntVarValue::Unknown);

        Ty::new(TyKind::Infer(InferTy::IntVar(id)), self.gcx)
    }

    pub fn next_float_var(&self) -> Ty<'ctx> {
        let id = self
            .inner
            .borrow_mut()
            .float_unification_table()
            .new_key(FloatVarValue::Unknown);

        Ty::new(TyKind::Infer(InferTy::FloatVar(id)), self.gcx)
    }

    pub fn next_nil_var(&self) -> Ty<'ctx> {
        let id = self
            .inner
            .borrow_mut()
            .nil_unification_table()
            .new_key(NilVarValue::Unknown);

        Ty::new(TyKind::Infer(InferTy::NilVar(id)), self.gcx)
    }

    pub fn fresh_args_for_def(&self, def_id: DefinitionID, span: Span) -> GenericArguments<'ctx> {
        GenericsBuilder::for_item(self.gcx, def_id, |param, _| {
            self.var_for_generic_param(param, span)
        })
    }

    pub fn var_for_generic_param(
        &self,
        param: &GenericParameterDefinition,
        span: Span,
    ) -> GenericArgument<'ctx> {
        match param.kind {
            GenericParameterDefinitionKind::Type { .. } => {
                let ty_var_id =
                    self.inner
                        .borrow_mut()
                        .type_variables()
                        .new_var(TypeVariableOrigin {
                            location: span,
                            param_name: Some(param.name),
                        });

                let ty = Ty::new(TyKind::Infer(InferTy::TyVar(ty_var_id)), self.gcx);
                GenericArgument::Type(ty)
            }
            GenericParameterDefinitionKind::Const { .. } => {
                let origin = ConstVariableOrigin {
                    location: span,
                    param_name: Some(param.name),
                };
                let owner = self.gcx.definition_parent(param.id).unwrap_or(param.id);
                let lower_ctx = DefTyLoweringCtx::new(owner, self.gcx);
                let expected_ty = match &param.kind {
                    GenericParameterDefinitionKind::Const { ty, .. } => {
                        lower_ctx.lowerer().lower_type(ty)
                    }
                    _ => self.gcx.types.error,
                };
                GenericArgument::Const(self.new_const_var(expected_ty, origin))
            }
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
            InferTy::IntVar(vid) => {
                match self
                    .inner
                    .borrow_mut()
                    .int_unification_table()
                    .probe_value(vid)
                {
                    IntVarValue::Unknown => ty,
                    IntVarValue::Signed(k) => Ty::new_int(self.gcx, k),
                    IntVarValue::Unsigned(k) => Ty::new_uint(self.gcx, k),
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
                    FloatVarValue::Known(k) => Ty::new_float(self.gcx, k),
                }
            }
            // NilVar stays as-is during shallow resolve - coercion handles resolution
            InferTy::NilVar(_) => ty,
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

    /// Resolve inference variables, replacing any unresolved ones with error type.
    /// Use this when the infer_ctx is about to be dropped (e.g., at statement boundary)
    /// to prevent downstream code from accessing invalid type variable IDs.
    pub fn resolve_vars_or_error<T>(&self, value: T) -> T
    where
        T: TypeFoldable<'ctx>,
    {
        let mut resolver = resolve::InferVarOrErrorResolver::new(self);
        value.fold_with(&mut resolver)
    }

    /// Resolve inference variables in generic arguments.
    pub fn resolve_args_if_possible(&self, args: GenericArguments<'ctx>) -> GenericArguments<'ctx> {
        if args.is_empty() {
            return args;
        }
        let resolved: Vec<_> = args
            .iter()
            .map(|arg| match arg {
                GenericArgument::Type(ty) => {
                    GenericArgument::Type(self.resolve_vars_if_possible(*ty))
                }
                GenericArgument::Const(c) => {
                    GenericArgument::Const(self.resolve_const_if_possible(*c))
                }
            })
            .collect();
        self.gcx.store.interners.intern_generic_args(resolved)
    }

    pub fn bind_overload(&self, ty: Ty<'ctx>, source: DefinitionID) {
        let TyKind::Infer(InferTy::TyVar(var_id)) = ty.kind() else {
            return;
        };
        let mut inner = self.inner.borrow_mut();
        let prev = inner.overload_bindings.insert(var_id, source);
        inner.log_overload_binding(var_id, prev);
    }

    pub fn overload_binding_for_ty(&self, ty: Ty<'ctx>) -> Option<DefinitionID> {
        match ty.kind() {
            TyKind::Infer(InferTy::TyVar(var_id)) => {
                let inner = self.inner.borrow();
                inner.overload_bindings.get(&var_id).cloned()
            }
            _ => None,
        }
    }
}

pub(crate) type UnificationTable<'a, 'tcx, T> = ena::unify::UnificationTable<
    ena::unify::InPlace<T, &'a mut ena::unify::UnificationStorage<T>, &'a mut IcxEventLogs<'tcx>>,
>;

#[derive(Default, Clone)]
pub struct InferCtxInner<'ctx> {
    event_logs: IcxEventLogs<'ctx>,
    type_storage: TypeVariableStorage<'ctx>,
    const_storage: ConstVariableStorage<'ctx>,
    int_storage: UnificationTableStorage<IntVarID>,
    float_storage: UnificationTableStorage<FloatVarID>,
    nil_storage: UnificationTableStorage<NilVarID>,
    overload_bindings: FxHashMap<TyVarID, DefinitionID>,
    pending_fallbacks: Vec<DefaultFallbackGoalData<'ctx>>,
}

impl<'ctx> InferCtxInner<'ctx> {
    pub fn new() -> InferCtxInner<'ctx> {
        InferCtxInner {
            event_logs: Default::default(),
            type_storage: Default::default(),
            const_storage: Default::default(),
            int_storage: Default::default(),
            float_storage: Default::default(),
            nil_storage: Default::default(),
            overload_bindings: Default::default(),
            pending_fallbacks: Default::default(),
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
    pub fn const_variables(&mut self) -> ConstVariableTable<'_, 'ctx> {
        self.const_storage.with_log(&mut self.event_logs)
    }

    #[inline]
    pub fn nil_unification_table(&mut self) -> UnificationTable<'_, 'ctx, NilVarID> {
        self.nil_storage.with_log(&mut self.event_logs)
    }
}

impl<'ctx> InferCtxInner<'ctx> {
    pub fn log_overload_binding(&mut self, var: TyVarID, prev: Option<DefinitionID>) {
        self.event_logs
            .push_event(IcxEvent::OverloadBinding { var, prev });
    }
}

impl<'ctx> InferCtxInner<'ctx> {
    pub fn rollback_to(&mut self, snapshot: self::snapshot::Snapshot<'ctx>) {
        while self.event_logs.logs.len() > snapshot.length {
            let undo = self.event_logs.logs.pop().unwrap();
            self.reverse(undo);
        }

        self.type_storage.finalize_rollback();
        self.const_storage.finalize_rollback();

        if self.event_logs.open_snapshots == 1 {
            // After the root snapshot the undo log should be empty.
            assert!(snapshot.length == 0);
            assert!(self.event_logs.logs.is_empty());
        }

        self.event_logs.open_snapshots -= 1;
    }
}

impl<'ctx> InferCtx<'ctx> {
    pub fn new_const_var(&self, ty: Ty<'ctx>, origin: ConstVariableOrigin) -> Const<'ctx> {
        let id = self.inner.borrow_mut().const_variables().new_var(origin);
        Const {
            ty,
            kind: ConstKind::Infer(id),
        }
    }

    pub fn resolve_const_if_possible(&self, c: Const<'ctx>) -> Const<'ctx> {
        let ConstKind::Infer(id) = c.kind else {
            return Const {
                ty: self.resolve_vars_if_possible(c.ty),
                kind: c.kind,
            };
        };
        let binding = {
            let mut inner = self.inner.borrow_mut();
            let mut table = inner.const_variables();
            table.probe(id)
        };

        let ty = self.resolve_vars_if_possible(c.ty);
        match binding {
            ConstVarValue::Known(value) => Const {
                ty,
                kind: ConstKind::Value(value),
            },
            ConstVarValue::Param(param) => Const {
                ty,
                kind: ConstKind::Param(param),
            },
            ConstVarValue::Unknown => Const {
                ty,
                kind: ConstKind::Infer(id),
            },
        }
    }

    pub fn const_var_binding(&self, id: ConstVarID) -> ConstVarValue {
        let mut inner = self.inner.borrow_mut();
        let mut table = inner.const_variables();
        table.probe(id)
    }

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

impl<'ctx> InferCtx<'ctx> {
    pub fn equate_const_vars_raw(&self, a: ConstVarID, b: ConstVarID) {
        self.inner.borrow_mut().const_variables().equate(a, b);
    }

    pub fn instantiate_const_var_raw(&self, id: ConstVarID, value: ConstVarValue) {
        self.inner
            .borrow_mut()
            .const_variables()
            .instantiate(id, value);
    }

    pub fn equate_nil_vars_raw(&self, a: NilVarID, b: NilVarID) {
        self.inner.borrow_mut().nil_unification_table().union(a, b);
    }

    pub fn mark_nil_var_bound(&self, id: NilVarID) {
        self.inner
            .borrow_mut()
            .nil_unification_table()
            .union_value(id, NilVarValue::Bound);
    }
}

impl<'ctx> InferCtx<'ctx> {
    /// Returns all type variable IDs with their origins.
    /// Useful for debugging to identify unresolved type variables.
    pub fn all_type_var_origins(&self) -> Vec<(TyVarID, TypeVariableOrigin)> {
        let inner = self.inner.borrow();
        inner
            .type_storage
            .iter_origins()
            .map(|(id, origin)| (id, *origin))
            .collect()
    }

    pub fn all_const_var_origins(&self) -> Vec<(ConstVarID, ConstVariableOrigin)> {
        let inner = self.inner.borrow();
        inner
            .const_storage
            .iter_origins()
            .map(|(id, origin)| (id, *origin))
            .collect()
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

    pub fn register_pending_fallback(&self, data: DefaultFallbackGoalData<'ctx>) {
        self.inner.borrow_mut().pending_fallbacks.push(data);
    }

    pub fn take_pending_fallbacks(&self) -> Vec<DefaultFallbackGoalData<'ctx>> {
        std::mem::take(&mut self.inner.borrow_mut().pending_fallbacks)
    }
}
