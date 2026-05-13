use crate::sema::models::{
    ConstKind, GenericArgument, InterfaceGoal, InterfaceReference, Ty, TyKind,
};

pub fn goal_contains_unresolved_inference(goal: InterfaceGoal<'_>) -> bool {
    ty_contains_unresolved_inference(goal.self_ty)
        || goal
            .interface_args
            .iter()
            .any(generic_arg_contains_unresolved_inference)
        || goal
            .bindings
            .iter()
            .any(|binding| ty_contains_unresolved_inference(binding.ty))
}

pub fn interface_ref_contains_unresolved_inference(interface: InterfaceReference<'_>) -> bool {
    interface
        .arguments
        .iter()
        .any(generic_arg_contains_unresolved_inference)
        || interface
            .bindings
            .iter()
            .any(|binding| ty_contains_unresolved_inference(binding.ty))
}

pub fn generic_arg_contains_unresolved_inference(arg: &GenericArgument<'_>) -> bool {
    match arg {
        GenericArgument::Type(ty) => ty_contains_unresolved_inference(*ty),
        GenericArgument::Const(c) => {
            matches!(c.kind, ConstKind::Infer(_)) || ty_contains_unresolved_inference(c.ty)
        }
    }
}

pub fn ty_contains_unresolved_inference(ty: Ty<'_>) -> bool {
    match ty.kind() {
        TyKind::Infer(_) => true,
        TyKind::Adt(_, args) | TyKind::Alias { args, .. } => {
            args.iter().any(generic_arg_contains_unresolved_inference)
        }
        TyKind::Pointer(inner, _) | TyKind::Reference(inner, _) => {
            ty_contains_unresolved_inference(inner)
        }
        TyKind::Array { element, len } => {
            ty_contains_unresolved_inference(element)
                || matches!(len.kind, ConstKind::Infer(_))
                || ty_contains_unresolved_inference(len.ty)
        }
        TyKind::Tuple(items) => items
            .iter()
            .any(|item| ty_contains_unresolved_inference(*item)),
        TyKind::FnPointer { inputs, output } => {
            inputs
                .iter()
                .any(|input| ty_contains_unresolved_inference(*input))
                || ty_contains_unresolved_inference(output)
        }
        TyKind::BoxedExistential { interfaces } => interfaces
            .iter()
            .any(|iface| interface_ref_contains_unresolved_inference(*iface)),
        TyKind::Closure {
            captured_generics,
            inputs,
            output,
            ..
        } => {
            captured_generics
                .iter()
                .any(generic_arg_contains_unresolved_inference)
                || inputs
                    .iter()
                    .any(|input| ty_contains_unresolved_inference(*input))
                || ty_contains_unresolved_inference(output)
        }
        TyKind::Bool
        | TyKind::Rune
        | TyKind::String
        | TyKind::Int(_)
        | TyKind::UInt(_)
        | TyKind::Float(_)
        | TyKind::Parameter(_)
        | TyKind::Opaque(_)
        | TyKind::Error
        | TyKind::Never => false,
    }
}
