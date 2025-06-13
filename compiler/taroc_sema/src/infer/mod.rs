use crate::{
    GlobalContext,
    error::TypeError,
    fold::TypeFoldable,
    infer::{
        fn_var::{FunctionVariableOrigin, FunctionVariableStorage, FunctionVariableTable},
        resolve::InferVarResolver,
    },
    ty::{GenericArgument, GenericArguments, GenericParameterDefinition, InferTy, Ty, TyKind},
};
use ena::unify::UnificationTableStorage;
use keys::{
    FloatVarID, FloatVarValue, IntVarID, IntVarValue, TypeVariableOrigin, TypeVariableStorage,
    TypeVariableTable,
};
use snapshot::IcxEventLogs;
use std::cell::RefCell;
use taroc_hir::DefinitionID;
use taroc_span::Span;

pub mod fn_var;
pub mod keys;
mod resolve;
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

    pub fn next_ty_var(&self, location: Span) -> Ty<'ctx> {
        let id = self
            .inner
            .borrow_mut()
            .type_variables()
            .new_var(TypeVariableOrigin { location });
        self.gcx.mk_ty(TyKind::Infer(InferTy::TyVar(id)))
    }

    pub fn next_fn_var(&self, location: Span) -> Ty<'ctx> {
        let id = self
            .inner
            .borrow_mut()
            .fn_variables()
            .new_var(FunctionVariableOrigin { location });
        self.gcx.mk_ty(TyKind::Infer(InferTy::FnVar(id)))
    }
}

impl<'ctx> InferCtx<'ctx> {
    pub fn fresh_args_for_def(&self, def_id: DefinitionID, span: Span) -> GenericArguments<'ctx> {
        let generics = self.gcx.generics_of(def_id);
        let args: Vec<GenericArgument> = generics
            .parameters
            .iter()
            .map(|param| self.var_for_generic_param(param, span))
            .collect();

        let args = self.gcx.store.interners.intern_generic_args(&args);
        args
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
    pub fn resolve_vars_if_possible<T>(&self, value: T) -> T
    where
        T: TypeFoldable<'ctx>,
    {
        let mut resolver = InferVarResolver::new(self);
        value.fold_with(&mut resolver)
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
                let res = self
                    .inner
                    .borrow_mut()
                    .fn_variables()
                    .storage()
                    .probe_value(vid);

                match res {
                    fn_var::FnVarValue::Unknown => ty,
                    fn_var::FnVarValue::Known(ty) => ty,
                }
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
}

impl<'ctx> InferCtxInner<'ctx> {
    pub fn new() -> InferCtxInner<'ctx> {
        InferCtxInner {
            event_logs: Default::default(),
            int_storage: Default::default(),
            float_storage: Default::default(),
            type_storage: Default::default(),
            fn_storage: Default::default(),
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

pub struct InferenceOutput<'gcx, T> {
    pub value: T,
    pub _data: &'gcx (),
}

pub type InferenceResult<'gcx, T> = Result<InferenceOutput<'gcx, T>, TypeError<'gcx>>;
