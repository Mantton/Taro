use ena::unify::{UnifyKey, UnifyValue};

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

use crate::sema::models::{FloatTy, IntTy, UIntTy};

pub use super::ty_var::*;
