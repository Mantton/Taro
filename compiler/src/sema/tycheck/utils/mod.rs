use crate::sema::{
    models::{InferTy, Ty, TyKind},
    resolve::models::TypeHead,
};

pub mod autoderef;
pub mod const_eval;
pub mod generics;
pub mod instantiate;
pub mod normalize;
pub mod normalize_post_mono;
pub mod param_env;
pub mod unify;

pub use normalize::{normalize_aliases, normalize_ty};
pub use normalize_post_mono::normalize_post_monomorphization;
pub use param_env::ParamEnv;

#[derive(Debug)]
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
        TyKind::Tuple(items) => Some(TypeHead::Tuple(items.len() as u16)),
        TyKind::Parameter(_)
        | TyKind::Infer(_)
        | TyKind::FnPointer { .. }
        | TyKind::Alias { .. }
        | TyKind::BoxedExistential { .. }
        | TyKind::Error
        | TyKind::Never => None,
    }
}

pub fn is_type_layout_compatible(from: Ty<'_>, to: Ty<'_>) -> bool {
    // Checks if two types are layout-compatible for unsafe casting.
    // This is a permissive check used by solve_cast() to determine if a bitcast
    // is potentially valid. The actual safety is enforced by requiring `unsafe`.
    //
    // Layout-compatible pairs:
    // 1. Pointer <-> Pointer (any pointer types, including references and fn pointers)
    // 2. Pointer <-> Integer (includes unresolved IntVar from literals like `0`)
    // 3. Integer <-> Integer (truncation/extension is allowed)
    match (from.kind(), to.kind()) {
        // Ptr <-> Ptr
        (
            TyKind::Pointer(..) | TyKind::Reference(..) | TyKind::FnPointer { .. },
            TyKind::Pointer(..) | TyKind::Reference(..) | TyKind::FnPointer { .. },
        ) => true,
        // Ptr <-> Int (includes IntVar for literals like `0 as *mut T`)
        (
            TyKind::Pointer(..) | TyKind::Reference(..) | TyKind::FnPointer { .. },
            TyKind::Int(_) | TyKind::UInt(_) | TyKind::Infer(InferTy::IntVar(_)),
        ) => true,
        (
            TyKind::Int(_) | TyKind::UInt(_) | TyKind::Infer(InferTy::IntVar(_)),
            TyKind::Pointer(..) | TyKind::Reference(..) | TyKind::FnPointer { .. },
        ) => true,
        // Int <-> Int
        (
            TyKind::Int(_) | TyKind::UInt(_) | TyKind::Infer(InferTy::IntVar(_)),
            TyKind::Int(_) | TyKind::UInt(_) | TyKind::Infer(InferTy::IntVar(_)),
        ) => true,
        _ => false,
    }
}
