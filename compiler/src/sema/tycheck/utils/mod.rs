use crate::sema::{
    models::{Ty, TyKind},
    resolve::models::TypeHead,
};

pub mod autoderef;
pub mod const_eval;
pub mod generics;
pub mod instantiate;
pub mod normalize;
pub mod param_env;
pub mod unify;

pub use normalize::{normalize_aliases, normalize_ty};
pub use param_env::ParamEnv;

pub enum AutoReference {
    None,
    Mutable,
    Immutable,
}

pub fn type_head_from_value_ty(ty: Ty<'_>) -> Option<TypeHead> {
    match ty.kind() {
        TyKind::Bool => Some(TypeHead::Primary(
            crate::sema::resolve::models::PrimaryType::Bool,
        )),
        TyKind::Rune => Some(TypeHead::Primary(
            crate::sema::resolve::models::PrimaryType::Rune,
        )),
        TyKind::String => Some(TypeHead::Primary(
            crate::sema::resolve::models::PrimaryType::String,
        )),
        TyKind::Int(k) => Some(TypeHead::Primary(
            crate::sema::resolve::models::PrimaryType::Int(k),
        )),
        TyKind::UInt(k) => Some(TypeHead::Primary(
            crate::sema::resolve::models::PrimaryType::UInt(k),
        )),
        TyKind::Float(k) => Some(TypeHead::Primary(
            crate::sema::resolve::models::PrimaryType::Float(k),
        )),
        TyKind::Array { .. } => Some(TypeHead::Array),
        TyKind::Adt(def, _) => Some(TypeHead::Nominal(def.id)),
        TyKind::Reference(_, mutbl) => Some(TypeHead::Reference(mutbl)),
        TyKind::Pointer(_, mutbl) => Some(TypeHead::Pointer(mutbl)),
        TyKind::GcPtr => Some(TypeHead::GcPtr),
        TyKind::Tuple(items) => Some(TypeHead::Tuple(items.len() as u16)),
        TyKind::Parameter(_)
        | TyKind::Infer(_)
        | TyKind::FnPointer { .. }
        | TyKind::Alias { .. }
        | TyKind::BoxedExistential { .. }
        | TyKind::Error => None,
    }
}
