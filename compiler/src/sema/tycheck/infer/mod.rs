use crate::{
    compile::context::Gcx,
    sema::{
        models::{InferTy, Ty, TyKind},
        tycheck::{
            fold::TypeFoldable,
            infer::{
                resolve::InferVarResolver,
                ty_var::{TypeVariableOrigin, TypeVariableStorage, TypeVariableTable},
            },
        },
    },
    span::Span,
};
use ena::undo_log::Rollback;

use snapshot::IcxEventLogs;
use std::cell::RefCell;

mod resolve;
mod snapshot;
pub mod ty_var;

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
            .new_var(TypeVariableOrigin { location });
        Ty::new(TyKind::Infer(InferTy::TyVar(id)), self.gcx)
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

pub(crate) type UnificationTable<'a, 'tcx, T> = ena::unify::UnificationTable<
    ena::unify::InPlace<T, &'a mut ena::unify::UnificationStorage<T>, &'a mut IcxEventLogs<'tcx>>,
>;

#[derive(Default, Clone)]
pub struct InferCtxInner<'ctx> {
    event_logs: IcxEventLogs<'ctx>,
    type_storage: TypeVariableStorage<'ctx>,
}

impl<'ctx> InferCtxInner<'ctx> {
    pub fn new() -> InferCtxInner<'ctx> {
        InferCtxInner {
            event_logs: Default::default(),
            type_storage: Default::default(),
        }
    }
}

impl<'ctx> InferCtxInner<'ctx> {
    #[inline]
    pub fn type_variables(&mut self) -> TypeVariableTable<'_, 'ctx> {
        self.type_storage.with_log(&mut self.event_logs)
    }
}

impl<'ctx> InferCtxInner<'ctx> {
    pub fn rollback_to(&mut self, snapshot: self::snapshot::Snapshot<'ctx>) {
        while self.event_logs.logs.len() > snapshot.length {
            let undo = self.event_logs.logs.pop().unwrap();
            self.reverse(undo);
        }

        self.type_storage.finalize_rollback();

        if self.event_logs.open_snapshots == 1 {
            // After the root snapshot the undo log should be empty.
            assert!(snapshot.length == 0);
            assert!(self.event_logs.logs.is_empty());
        }

        self.event_logs.open_snapshots -= 1;
    }
}
