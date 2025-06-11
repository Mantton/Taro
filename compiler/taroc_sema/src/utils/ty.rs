use crate::{
    GlobalContext,
    ty::{
        Constraint, FloatTy, GenericArgument, GenericArguments, IntTy, InterfaceReference,
        SimpleType, Ty, TyKind, UIntTy,
    },
};
use ena::unify::UnifyKey;
use taroc_hir::{DefinitionID, Mutability};

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
    return gcx.ty_to_def(ty);
    // match ty.kind() {
    //     taroc_ty::TyKind::Pointer(_, muta) => match muta {
    //         taroc_hir::Mutability::Mutable => gcx.store.common_types.mappings.mut_ref.take(),
    //         taroc_hir::Mutability::Immutable => gcx.store.common_types.mappings.const_ref.take(),
    //     },
    //     taroc_ty::TyKind::Reference(_, muta) => match muta {
    //         taroc_hir::Mutability::Mutable => gcx.store.common_types.mappings.ptr.take(),
    //         taroc_hir::Mutability::Immutable => gcx.store.common_types.mappings.const_ptr.take(),
    //     },
    //     taroc_ty::TyKind::Array(..) => gcx.store.common_types.mappings.array.take(),
    //     taroc_ty::TyKind::Adt(adt_def, ..) => Some(adt_def.id),
    //     taroc_ty::TyKind::FnDef(definition_id, ..) => Some(definition_id),
    //     _ => None,
    // }
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

/// Render an entire type tree into a human‑readable string that uses real
/// identifiers instead of raw `DefinitionID`s.
pub fn ty2str<'ctx>(ty: Ty<'ctx>, gcx: GlobalContext<'ctx>) -> String {
    match ty.kind() {
        TyKind::Bool => "bool".into(),
        TyKind::Rune => "rune".into(),
        TyKind::String => "string".into(),
        TyKind::Int(i) => format!("{i}"),
        TyKind::UInt(u) => format!("{u}"),
        TyKind::Float(fl) => format!("{fl}"),

        TyKind::Pointer(inner, m) => {
            format!(
                "*{}{}",
                if matches!(m, Mutability::Mutable) {
                    "mut "
                } else {
                    ""
                },
                ty2str(inner, gcx)
            )
        }
        TyKind::Reference(inner, m) => {
            format!(
                "&{}{}",
                if matches!(m, Mutability::Mutable) {
                    "mut "
                } else {
                    ""
                },
                ty2str(inner, gcx)
            )
        }

        TyKind::Array(elem, size) => {
            format!("[{}; {size}]", ty2str(elem, gcx))
        }
        TyKind::Tuple(elems) => {
            let mut out = "(".to_owned();
            for (i, t) in elems.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                out.push_str(&ty2str(*t, gcx));
            }
            if elems.len() == 1 {
                out.push(',');
            } // 1‑tuple trailing comma
            out.push(')');
            out
        }

        TyKind::Adt(def, args) => {
            let mut out = def.name.to_string(); // `AdtDef` already stores a name
            if !args.is_empty() {
                out.push_str(&generic_args2str(args, gcx));
            }
            out
        }

        TyKind::Existential(ifaces) | TyKind::Opaque(ifaces) => ifaces
            .into_iter()
            .map(|iface| interface_ref2str(*iface, gcx))
            .collect::<Vec<_>>()
            .join(" | "),

        TyKind::Parameter(p) => p.name.to_string(),

        TyKind::Function {
            inputs,
            output,
            is_async,
        } => {
            let mut out = String::new();
            if is_async {
                out.push_str("async ");
            }
            out.push('(');
            for (i, inp) in inputs.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                out.push_str(&ty2str(*inp, gcx));
            }
            out.push_str(") -> ");
            out.push_str(&ty2str(output, gcx));
            out
        }

        TyKind::AssociatedType { .. } => "assoc()".into(),
        TyKind::Error => "<error>".into(),

        TyKind::FnDef(id, args) => {
            let mut out = format!("fn {}", gcx.ident_for(id).symbol.as_str());
            if !args.is_empty() {
                out.push_str(&generic_args2str(args, gcx));
            }
            out
        }

        TyKind::Infer(kind) => match kind {
            crate::ty::InferTy::Ty(id) => format!("TyVar({})", id.raw()),
            crate::ty::InferTy::IntVar(id) => format!("IntVar({})", id.index()),
            crate::ty::InferTy::FloatVar(id) => format!("FloatVar({})", id.index()),
            crate::ty::InferTy::FreshTy(index) => format!("FreshTy({})", index),
        },
    }
}

/// Turn a single interface reference (including its generic parameters)
/// into a string, resolving the `DefinitionID` through the context.
pub fn interface_ref2str<'ctx>(
    iface: InterfaceReference<'ctx>,
    gcx: GlobalContext<'ctx>,
) -> String {
    let mut out = gcx.ident_for(iface.id).symbol.as_str().to_owned();
    if !iface.arguments.is_empty() {
        out.push_str(&generic_args2str(iface.arguments, gcx));
    }
    out
}

/// Render one generic argument (`Type` or `Const`) to string.
fn generic_arg2str<'ctx>(arg: GenericArgument<'ctx>, gcx: GlobalContext<'ctx>) -> String {
    match arg {
        GenericArgument::Type(t) => ty2str(t, gcx),
        GenericArgument::Const(v) => v.to_string(),
    }
}

/// Render an entire slice of generic arguments, adding the `<…>` wrapper.
pub fn generic_args2str<'ctx>(args: GenericArguments<'ctx>, gcx: GlobalContext<'ctx>) -> String {
    let inner = args
        .iter()
        .map(|a| generic_arg2str(*a, gcx))
        .collect::<Vec<_>>()
        .join(", ");
    format!("<{inner}>")
}

/// Convert a constraint (`T: P`, `T == U`) into a readable string.
pub fn constraint2str<'ctx>(constraint: Constraint<'ctx>, gcx: GlobalContext<'ctx>) -> String {
    match constraint {
        Constraint::Bound { ty, interface } => {
            format!("{}: {}", ty2str(ty, gcx), interface_ref2str(interface, gcx))
        }
        Constraint::TypeEquality(lhs, rhs) => {
            format!("{} == {}", ty2str(lhs, gcx), ty2str(rhs, gcx))
        }
        Constraint::Subtype { sub, sup } => format!("{} <: {}", sub.format(gcx), sup.format(gcx)),
    }
}
