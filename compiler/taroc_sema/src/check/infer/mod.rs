use std::cell::RefCell;

use ena::unify::{InPlace, Snapshot, UnificationTable};

use crate::{
    GlobalContext,
    ty::{Ty, TypeVariableID},
};

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
    pub fn unify(&self, a: Ty<'ctx>, b: Ty<'ctx>) -> Result<(), ()> {
        if a == b {
            return Ok(());
        }

        return Ok(());
    }
}

impl<'ctx> InferCtx<'ctx> {
    pub fn take_snapshot(&self) -> Snapshot<InPlace<TypeVariableKey<'ctx>>> {
        self.inner.borrow_mut().var_unification_table.snapshot()
    }

    pub fn restore_snapshot(&self, snapshot: Snapshot<InPlace<TypeVariableKey<'ctx>>>) {
        self.inner
            .borrow_mut()
            .var_unification_table
            .rollback_to(snapshot);
    }
}

pub struct InferCtxInner<'ctx> {
    pub var_unification_table: UnificationTable<InPlace<TypeVariableKey<'ctx>>>,
}

impl<'ctx> InferCtxInner<'ctx> {
    pub fn new() -> InferCtxInner<'ctx> {
        InferCtxInner {
            var_unification_table: UnificationTable::new(),
        }
    }

    pub fn fresh_type_var(&mut self) -> TypeVariableKey<'ctx> {
        self.var_unification_table
            .new_key(TypeVariableValue::Unknown)
    }
}

// This is what gets stored in the unification table
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeVariableValue<'ctx> {
    Unknown,         // Variable is not yet bound to anything
    Known(Ty<'ctx>), // Variable is bound to a concrete type
}

// Key type for the unification table
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct TypeVariableKey<'ctx> {
    pub id: TypeVariableID,
    pub phantom: std::marker::PhantomData<&'ctx ()>,
}

// Implement the traits that ena needs
impl<'ctx> ena::unify::UnifyKey for TypeVariableKey<'ctx> {
    type Value = TypeVariableValue<'ctx>;

    fn index(&self) -> u32 {
        self.id.raw()
    }

    fn from_index(u: u32) -> Self {
        TypeVariableKey {
            id: TypeVariableID::from_raw(u),
            phantom: std::marker::PhantomData,
        }
    }

    fn tag() -> &'static str {
        "TypeVariableKey"
    }
}

impl<'ctx> ena::unify::UnifyValue for TypeVariableValue<'ctx> {
    type Error = ena::unify::NoError;

    fn unify_values(value1: &Self, value2: &Self) -> Result<Self, Self::Error> {
        match (value1, value2) {
            (TypeVariableValue::Unknown, TypeVariableValue::Unknown) => {
                Ok(TypeVariableValue::Unknown)
            }
            (TypeVariableValue::Known(ty), TypeVariableValue::Unknown)
            | (TypeVariableValue::Unknown, TypeVariableValue::Known(ty)) => {
                Ok(TypeVariableValue::Known(*ty))
            }
            (TypeVariableValue::Known(ty1), TypeVariableValue::Known(ty2)) => {
                // Two concrete types - they must be equal
                if ty1 == ty2 {
                    Ok(TypeVariableValue::Known(*ty1))
                } else {
                    // This shouldn't happen in a well-typed program
                    // You might want to handle this as an error
                    Ok(TypeVariableValue::Known(*ty1))
                }
            }
        }
    }
}
