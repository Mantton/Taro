use super::{
    InferCtxInner,
    keys::{FloatVarID, IntVarID, TyVarEqID},
};
use std::marker::PhantomData;

// Inference Context Snapshot
pub struct Snapshot<'ctx> {
    pub length: usize,
    _data: PhantomData<&'ctx ()>,
}

// records a single event within the Icx, that can be undone
#[derive(Clone)]
pub enum IcxEvent<'ctx> {
    IntVar(ena::snapshot_vec::UndoLog<ena::unify::Delegate<IntVarID>>),
    FloatVar(ena::snapshot_vec::UndoLog<ena::unify::Delegate<FloatVarID>>),
    TypeVar(ena::snapshot_vec::UndoLog<ena::unify::Delegate<TyVarEqID<'ctx>>>),
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
    IntVar(ena::snapshot_vec::UndoLog<ena::unify::Delegate<IntVarID>>),
    FloatVar(ena::snapshot_vec::UndoLog<ena::unify::Delegate<FloatVarID>>),
    TypeVar(ena::snapshot_vec::UndoLog<ena::unify::Delegate<TyVarEqID<'gcx>>>),
}

// Combined Event Log for all unifcation tables within the icx
#[derive(Default, Clone)]
pub struct IcxEventLogs<'ctx> {
    logs: Vec<IcxEvent<'ctx>>,
    open_snapshots: usize,
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
            IcxEvent::IntVar(undo) => self.int_storage.reverse(undo),
            IcxEvent::FloatVar(undo) => self.float_storage.reverse(undo),
            _ => unreachable!("ICE: Placeholder Event"),
        }
    }
}
