use crate::sema::{
    resolve::models::DefinitionID,
    tycheck::infer::keys::{FloatVarID, IntVarID, TyVarEqID},
};

use super::InferCtxInner;
use std::marker::PhantomData;

// Inference Context Snapshot
pub struct Snapshot<'ctx> {
    pub length: usize,
    _data: PhantomData<&'ctx ()>,
}

// records a single event within the Icx, that can be undone
#[derive(Clone)]
pub enum IcxEvent<'ctx> {
    TypeVar(ena::snapshot_vec::UndoLog<ena::unify::Delegate<TyVarEqID<'ctx>>>),
    IntVar(ena::snapshot_vec::UndoLog<ena::unify::Delegate<IntVarID>>),
    FloatVar(ena::snapshot_vec::UndoLog<ena::unify::Delegate<FloatVarID>>),
    OverloadBinding {
        var: crate::sema::models::TyVarID,
        prev: Option<DefinitionID>,
    },
}

macro_rules! impl_from {
    ($($ctor:ident ($ty:ty),)*) => {
        $(
        impl<'gcx> From<$ty> for IcxEvent<'gcx> {
            fn from(x: $ty) -> Self {
                IcxEvent::$ctor(x.into())
            }
        }
        )*
    }
}

// Upcast from a single kind of "undoable action" to the general enum
impl_from! {
    TypeVar(ena::snapshot_vec::UndoLog<ena::unify::Delegate<TyVarEqID<'gcx>>>),
    IntVar(ena::snapshot_vec::UndoLog<ena::unify::Delegate<IntVarID>>),
    FloatVar(ena::snapshot_vec::UndoLog<ena::unify::Delegate<FloatVarID>>),
}

// Combined Event Log for all unifcation tables within the icx
#[derive(Default, Clone)]
pub struct IcxEventLogs<'ctx> {
    pub logs: Vec<IcxEvent<'ctx>>,
    pub open_snapshots: usize,
}

impl<'ctx> IcxEventLogs<'ctx> {
    pub fn in_snapshot(&self) -> bool {
        self.open_snapshots > 0
    }

    pub fn push_event(&mut self, event: IcxEvent<'ctx>) {
        if self.in_snapshot() {
            self.logs.push(event);
        }
    }
}

impl<'ctx> IcxEventLogs<'ctx> {
    pub fn start_snapshot(&mut self) -> Snapshot<'ctx> {
        self.open_snapshots += 1;
        Snapshot {
            length: self.logs.len(),
            _data: PhantomData,
        }
    }
}

impl<'tcx, T> ena::undo_log::UndoLogs<T> for IcxEventLogs<'tcx>
where
    IcxEvent<'tcx>: From<T>,
{
    #[inline]
    fn num_open_snapshots(&self) -> usize {
        self.open_snapshots
    }

    #[inline]
    fn push(&mut self, undo: T) {
        if self.in_snapshot() {
            self.logs.push(undo.into())
        }
    }

    fn clear(&mut self) {
        self.logs.clear();
        self.open_snapshots = 0;
    }

    fn extend<J>(&mut self, undos: J)
    where
        Self: Sized,
        J: IntoIterator<Item = T>,
    {
        if self.in_snapshot() {
            self.logs.extend(undos.into_iter().map(IcxEvent::from))
        }
    }
}

/// The Rollback trait defines how to rollback a particular action.
impl<'tcx> ena::undo_log::Rollback<IcxEvent<'tcx>> for InferCtxInner<'tcx> {
    fn reverse(&mut self, undo: IcxEvent<'tcx>) {
        match undo {
            IcxEvent::TypeVar(undo) => self.type_storage.reverse(undo),
            IcxEvent::IntVar(undo) => self.int_storage.reverse(undo),
            IcxEvent::FloatVar(undo) => self.float_storage.reverse(undo),
            IcxEvent::OverloadBinding { var, prev } => match prev {
                Some(def) => {
                    self.overload_bindings.insert(var, def);
                }
                None => {
                    self.overload_bindings.remove(&var);
                }
            },
        }
    }
}
