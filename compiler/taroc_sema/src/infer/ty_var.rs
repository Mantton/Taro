use crate::ty::{Ty, TyVarID};
use ena::unify::{UnificationTableStorage, UnifyKey, UnifyValue};
use index_vec::IndexVec;
use std::marker::PhantomData;
use taroc_span::Span;

use super::{UnificationTable, snapshot::IcxEventLogs};

// Ty
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TyVarEqID<'ctx> {
    _raw: TyVarID,
    _data: PhantomData<&'ctx ()>,
}

impl<'gcx> From<TyVarID> for TyVarEqID<'gcx> {
    #[inline]
    fn from(vid: TyVarID) -> Self {
        TyVarEqID {
            _raw: vid,
            _data: PhantomData,
        }
    }
}

impl<'ctx> TyVarEqID<'ctx> {
    pub fn new(value: TyVarID) -> TyVarEqID<'ctx> {
        return TyVarEqID {
            _raw: value,
            _data: PhantomData,
        };
    }
}

impl<'ctx> UnifyKey for TyVarEqID<'ctx> {
    type Value = TyVarValue<'ctx>;
    #[inline] // make this function eligible for inlining - it is quite hot.
    fn index(&self) -> u32 {
        self._raw.raw()
    }
    #[inline]
    fn from_index(i: u32) -> TyVarEqID<'ctx> {
        TyVarEqID::new(TyVarID::from_raw(i))
    }
    fn tag() -> &'static str {
        "TyVarID"
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TyVarValue<'ctx> {
    Unknown,
    Known(Ty<'ctx>),
}

impl<'gcx> TyVarValue<'gcx> {
    pub(crate) fn known(&self) -> Option<Ty<'gcx>> {
        match *self {
            TyVarValue::Unknown { .. } => None,
            TyVarValue::Known(ty) => Some(ty),
        }
    }

    pub(crate) fn is_unknown(&self) -> bool {
        match *self {
            TyVarValue::Unknown { .. } => true,
            TyVarValue::Known { .. } => false,
        }
    }
}

impl<'ctx> UnifyValue for TyVarValue<'ctx> {
    type Error = ena::unify::NoError;

    fn unify_values(lhs: &Self, rhs: &Self) -> Result<Self, ena::unify::NoError> {
        match (lhs, rhs) {
            // We never equate two type variables, both of which
            // have known types. Instead, we recursively equate
            // those types.
            (&TyVarValue::Known(_), &TyVarValue::Known(_)) => {
                unreachable!("ICE: equating two vars that have known types");
            }
            (&TyVarValue::Known(_), &TyVarValue::Unknown) => Ok(*lhs),
            (&TyVarValue::Unknown, &TyVarValue::Known(_)) => Ok(*rhs),
            (&TyVarValue::Unknown, &TyVarValue::Unknown) => Ok(TyVarValue::Unknown),
        }
    }
}

#[derive(Copy, Clone)]
pub struct TypeVariableOrigin {
    pub location: Span,
}

#[derive(Default, Clone)]
pub struct TypeVariableStorage<'gcx> {
    table: UnificationTableStorage<TyVarEqID<'gcx>>,
    values: IndexVec<TyVarID, TypeVariableOrigin>,
}

impl<'gcx> TypeVariableStorage<'gcx> {
    #[inline]
    pub fn with_log<'a>(
        &'a mut self,
        undo_log: &'a mut IcxEventLogs<'gcx>,
    ) -> TypeVariableTable<'a, 'gcx> {
        TypeVariableTable {
            _storage: self,
            undo_log,
        }
    }

    #[inline]
    pub fn storage(&self) -> &UnificationTableStorage<TyVarEqID<'gcx>> {
        &self.table
    }

    pub fn finalize_rollback(&mut self) {}
}

pub struct TypeVariableTable<'a, 'gcx> {
    _storage: &'a mut TypeVariableStorage<'gcx>,
    undo_log: &'a mut IcxEventLogs<'gcx>,
}

impl<'gcx> TypeVariableTable<'_, 'gcx> {
    pub fn new_var(&mut self, origin: TypeVariableOrigin) -> TyVarID {
        let key = self.storage().new_key(TyVarValue::Unknown);
        let index = self._storage.values.push(origin);
        debug_assert_eq!(key._raw, index);
        index
    }

    #[inline]
    pub fn storage(&mut self) -> UnificationTable<'_, 'gcx, TyVarEqID<'gcx>> {
        self._storage.table.with_log(self.undo_log)
    }
}

impl<'gcx> TypeVariableTable<'_, 'gcx> {
    pub fn probe(&mut self, id: TyVarID) -> TyVarValue<'gcx> {
        self.inlined_probe(id)
    }

    #[inline(always)]
    pub fn inlined_probe(&mut self, vid: TyVarID) -> TyVarValue<'gcx> {
        self.storage().inlined_probe_value(vid)
    }
}
