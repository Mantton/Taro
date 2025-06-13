use crate::ty::{FnVarID, Ty};
use ena::unify::{UnificationTableStorage, UnifyKey, UnifyValue};
use index_vec::IndexVec;
use std::marker::PhantomData;
use taroc_span::Span;

use super::{UnificationTable, snapshot::IcxEventLogs};

// Ty
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FnVarEqID<'ctx> {
    _raw: FnVarID,
    _data: PhantomData<&'ctx ()>,
}

impl<'gcx> From<FnVarID> for FnVarEqID<'gcx> {
    #[inline]
    fn from(vid: FnVarID) -> Self {
        FnVarEqID {
            _raw: vid,
            _data: PhantomData,
        }
    }
}

impl<'ctx> FnVarEqID<'ctx> {
    pub fn new(value: FnVarID) -> FnVarEqID<'ctx> {
        return FnVarEqID {
            _raw: value,
            _data: PhantomData,
        };
    }
}

impl<'ctx> UnifyKey for FnVarEqID<'ctx> {
    type Value = FnVarValue<'ctx>;
    #[inline] // make this function eligible for inlining - it is quite hot.
    fn index(&self) -> u32 {
        self._raw.raw()
    }
    #[inline]
    fn from_index(i: u32) -> FnVarEqID<'ctx> {
        FnVarEqID::new(FnVarID::from_raw(i))
    }
    fn tag() -> &'static str {
        "FnVarID"
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum FnVarValue<'ctx> {
    Unknown,
    Known(Ty<'ctx>),
}

impl<'gcx> FnVarValue<'gcx> {
    pub(crate) fn known(&self) -> Option<Ty<'gcx>> {
        match *self {
            FnVarValue::Unknown { .. } => None,
            FnVarValue::Known(ty) => Some(ty),
        }
    }

    pub(crate) fn is_unknown(&self) -> bool {
        match *self {
            FnVarValue::Unknown { .. } => true,
            FnVarValue::Known { .. } => false,
        }
    }
}

impl<'ctx> UnifyValue for FnVarValue<'ctx> {
    type Error = ena::unify::NoError;

    fn unify_values(lhs: &Self, rhs: &Self) -> Result<Self, ena::unify::NoError> {
        match (lhs, rhs) {
            (&FnVarValue::Known(_), &FnVarValue::Known(_)) => {
                unreachable!("ICE: equating two fn vars that have known types");
            }
            (&FnVarValue::Known(_), &FnVarValue::Unknown) => Ok(*lhs),
            (&FnVarValue::Unknown, &FnVarValue::Known(_)) => Ok(*rhs),
            (&FnVarValue::Unknown, &FnVarValue::Unknown) => Ok(FnVarValue::Unknown),
        }
    }
}

#[derive(Copy, Clone)]
pub struct FunctionVariableOrigin {
    pub location: Span,
}

#[derive(Default, Clone)]
pub struct FunctionVariableStorage<'gcx> {
    table: UnificationTableStorage<FnVarEqID<'gcx>>,
    values: IndexVec<FnVarID, FunctionVariableOrigin>,
}

impl<'gcx> FunctionVariableStorage<'gcx> {
    #[inline]
    pub fn with_log<'a>(
        &'a mut self,
        undo_log: &'a mut IcxEventLogs<'gcx>,
    ) -> FunctionVariableTable<'a, 'gcx> {
        FunctionVariableTable {
            _storage: self,
            undo_log,
        }
    }

    #[inline]
    pub fn storage(&self) -> &UnificationTableStorage<FnVarEqID<'gcx>> {
        &self.table
    }

    pub fn finalize_rollback(&mut self) {}
}

pub struct FunctionVariableTable<'a, 'gcx> {
    _storage: &'a mut FunctionVariableStorage<'gcx>,
    undo_log: &'a mut IcxEventLogs<'gcx>,
}

impl<'gcx> FunctionVariableTable<'_, 'gcx> {
    pub fn new_var(&mut self, origin: FunctionVariableOrigin) -> FnVarID {
        let key = self.storage().new_key(FnVarValue::Unknown);
        let index = self._storage.values.push(origin);
        debug_assert_eq!(key._raw, index);
        index
    }

    #[inline]
    pub fn storage(&mut self) -> UnificationTable<'_, 'gcx, FnVarEqID<'gcx>> {
        self._storage.table.with_log(self.undo_log)
    }
}

impl<'gcx> FunctionVariableTable<'_, 'gcx> {
    pub fn probe(&mut self, id: FnVarID) -> FnVarValue<'gcx> {
        self.inlined_probe(id)
    }

    #[inline(always)]
    pub fn inlined_probe(&mut self, vid: FnVarID) -> FnVarValue<'gcx> {
        self.storage().inlined_probe_value(vid)
    }
}
