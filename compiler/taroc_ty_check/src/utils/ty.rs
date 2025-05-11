use std::{iter::zip, marker::PhantomData};
use taroc_context::GlobalContext;
use taroc_hir::DefinitionID;
use taroc_span::{Span, Spanned};
use taroc_ty::{Constraint, FloatTy, GenericArguments, IntTy, SimpleType, Ty, UIntTy};

pub fn convert_ast_int_ty(ity: taroc_hir::IntTy) -> IntTy {
    match ity {
        taroc_hir::IntTy::ISize => IntTy::ISize,
        taroc_hir::IntTy::I8 => IntTy::I8,
        taroc_hir::IntTy::I16 => IntTy::I16,
        taroc_hir::IntTy::I32 => IntTy::I32,
        taroc_hir::IntTy::I64 => IntTy::I64,
    }
}

pub fn convert_ast_uint_ty(uty: taroc_hir::UIntTy) -> UIntTy {
    match uty {
        taroc_hir::UIntTy::USize => UIntTy::USize,
        taroc_hir::UIntTy::U8 => UIntTy::U8,
        taroc_hir::UIntTy::U16 => UIntTy::U16,
        taroc_hir::UIntTy::U32 => UIntTy::U32,
        taroc_hir::UIntTy::U64 => UIntTy::U64,
    }
}

pub fn convert_ast_float_ty(fty: taroc_hir::FloatTy) -> FloatTy {
    match fty {
        taroc_hir::FloatTy::F32 => FloatTy::F32,
        taroc_hir::FloatTy::F64 => FloatTy::F64,
    }
}

pub fn def_id_of_ty<'ctx>(gcx: GlobalContext<'ctx>, ty: Ty<'ctx>) -> Option<DefinitionID> {
    match ty.kind() {
        taroc_ty::TyKind::Pointer(_, muta) => match muta {
            taroc_hir::Mutability::Mutable => gcx.store.common_types.mappings.mut_ref.take(),
            taroc_hir::Mutability::Immutable => gcx.store.common_types.mappings.const_ref.take(),
        },
        taroc_ty::TyKind::Reference(_, muta) => match muta {
            taroc_hir::Mutability::Mutable => gcx.store.common_types.mappings.ptr.take(),
            taroc_hir::Mutability::Immutable => gcx.store.common_types.mappings.const_ptr.take(),
        },
        taroc_ty::TyKind::Array(..) => gcx.store.common_types.mappings.array.take(),
        taroc_ty::TyKind::Adt(adt_def, ..) => Some(adt_def.id),
        taroc_ty::TyKind::FnDef(definition_id, ..) => Some(definition_id),
        taroc_ty::TyKind::AssociatedType(definition_id) => Some(definition_id),
        _ => None,
    }
}

pub fn ty_from_simple<'ctx>(gcx: GlobalContext<'ctx>, ty: SimpleType) -> Ty<'ctx> {
    let common = &gcx.store.common_types;
    let optional = |id: Option<DefinitionID>| {
        if let Some(id) = id {
            return gcx.type_of(id);
        } else {
            gcx.store.common_types.error
        }
    };
    match ty {
        SimpleType::Rune => common.rune,
        SimpleType::Bool => common.bool,
        SimpleType::String => common.string,
        SimpleType::Int(int_ty) => match int_ty {
            IntTy::ISize => common.int,
            IntTy::I8 => common.int8,
            IntTy::I16 => common.int16,
            IntTy::I32 => common.int32,
            IntTy::I64 => common.int64,
        },
        SimpleType::UInt(uint_ty) => match uint_ty {
            UIntTy::USize => common.uint,
            UIntTy::U8 => common.uint8,
            UIntTy::U16 => common.uint16,
            UIntTy::U32 => common.uint32,
            UIntTy::U64 => common.uint64,
        },
        SimpleType::Float(float_ty) => match float_ty {
            FloatTy::F32 => common.float32,
            FloatTy::F64 => common.float64,
        },
        SimpleType::Array => optional(common.mappings.array.take()),
        SimpleType::Adt(definition_id) => gcx.type_of(definition_id),
        SimpleType::Reference(mutability) => match mutability {
            taroc_hir::Mutability::Mutable => optional(common.mappings.mut_ref.take()),
            taroc_hir::Mutability::Immutable => optional(common.mappings.const_ref.take()),
        },
        SimpleType::Pointer(mutability) => match mutability {
            taroc_hir::Mutability::Mutable => optional(common.mappings.ptr.take()),
            taroc_hir::Mutability::Immutable => optional(common.mappings.const_ptr.take()),
        },
        SimpleType::Interface(_) => todo!(),
    }
}
pub struct TyBuilder<'ctx> {
    _data: PhantomData<GlobalContext<'ctx>>,
}
