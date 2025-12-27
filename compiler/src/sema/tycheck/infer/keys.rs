use super::{UnificationTable, snapshot::IcxEventLogs};
use crate::{
    sema::models::{FloatTy, IntTy, Ty, TyVarID, UIntTy},
    span::{Span, Symbol},
};
use ena::unify::{UnificationTableStorage, UnifyKey, UnifyValue};
use index_vec::IndexVec;
use std::marker::PhantomData;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct IntVarID {
    _raw: u32,
}

impl IntVarID {
    pub fn new(value: u32) -> IntVarID {
        return IntVarID { _raw: value };
    }
}

impl UnifyKey for IntVarID {
    type Value = IntVarValue;
    #[inline] // make this function eligible for inlining - it is quite hot.
    fn index(&self) -> u32 {
        self._raw as u32
    }

    #[inline]
    fn from_index(i: u32) -> IntVarID {
        IntVarID::new(i)
    }

    fn tag() -> &'static str {
        "IntVarID"
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum IntVarValue {
    Unknown,
    Signed(IntTy),
    Unsigned(UIntTy),
}

impl UnifyValue for IntVarValue {
    type Error = ena::unify::NoError;

    fn unify_values(value1: &Self, value2: &Self) -> Result<Self, Self::Error> {
        match (*value1, *value2) {
            (IntVarValue::Unknown, IntVarValue::Unknown) => Ok(IntVarValue::Unknown),
            (IntVarValue::Unknown, known @ (IntVarValue::Unsigned(_) | IntVarValue::Signed(_)))
            | (known @ (IntVarValue::Unsigned(_) | IntVarValue::Signed(_)), IntVarValue::Unknown) => {
                Ok(known)
            }
            _ => panic!("differing ints should have been resolved first"),
        }
    }
}

// Float
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FloatVarID {
    _raw: u32,
}

impl FloatVarID {
    pub fn new(value: u32) -> FloatVarID {
        return FloatVarID { _raw: value };
    }
}

impl UnifyKey for FloatVarID {
    type Value = FloatVarValue;
    #[inline] // make this function eligible for inlining - it is quite hot.
    fn index(&self) -> u32 {
        self._raw as u32
    }
    #[inline]
    fn from_index(i: u32) -> FloatVarID {
        FloatVarID::new(i)
    }
    fn tag() -> &'static str {
        "FloatVarID"
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum FloatVarValue {
    Unknown,
    Known(FloatTy),
}

impl UnifyValue for FloatVarValue {
    type Error = ena::unify::NoError;

    fn unify_values(value1: &Self, value2: &Self) -> Result<Self, Self::Error> {
        match (*value1, *value2) {
            (FloatVarValue::Unknown, FloatVarValue::Unknown) => Ok(FloatVarValue::Unknown),
            (FloatVarValue::Unknown, FloatVarValue::Known(known))
            | (FloatVarValue::Known(known), FloatVarValue::Unknown) => {
                Ok(FloatVarValue::Known(known))
            }
            (FloatVarValue::Known(_), FloatVarValue::Known(_)) => {
                panic!("differing floats should have been resolved first")
            }
        }
    }
}
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
    /// When this type variable was created for a generic parameter, stores its name.
    pub param_name: Option<Symbol>,
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

    /// Returns an iterator over all type variable origins.
    pub fn iter_origins(&self) -> impl Iterator<Item = (TyVarID, &TypeVariableOrigin)> {
        self.values.iter_enumerated()
    }

    pub fn finalize_rollback(&mut self) {
        debug_assert!(self.values.len() >= self.storage().len());
        self.values.truncate(self.storage().len());
    }
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

    pub fn root_var(&mut self, vid: TyVarID) -> TyVarID {
        self.storage().find(vid)._raw
    }

    pub fn equate(&mut self, a: TyVarID, b: TyVarID) {
        debug_assert!(self.probe(a).is_unknown());
        debug_assert!(self.probe(b).is_unknown());
        self.storage().union(a, b);
    }

    pub fn instantiate(&mut self, vid: TyVarID, ty: Ty<'gcx>) {
        let vid = self.root_var(vid);
        debug_assert!(
            !ty.is_ty_var(),
            "instantiating ty var with var: {vid:?} {ty:?}"
        );
        debug_assert!(self.probe(vid).is_unknown());
        debug_assert!(
            self.storage().probe_value(vid).is_unknown(),
            "instantiating type variable `{vid:?}` twice: new-value = {ty:?}, old-value={:?}",
            self.storage().probe_value(vid)
        );

        self.storage().union_value(vid, TyVarValue::Known(ty));
    }
}

impl<'ctx>
    ena::undo_log::Rollback<ena::snapshot_vec::UndoLog<ena::unify::Delegate<TyVarEqID<'ctx>>>>
    for TypeVariableStorage<'ctx>
{
    fn reverse(&mut self, undo: ena::snapshot_vec::UndoLog<ena::unify::Delegate<TyVarEqID<'ctx>>>) {
        self.table.reverse(undo)
    }
}
