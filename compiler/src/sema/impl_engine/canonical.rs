use crate::{
    compile::context::Gcx,
    sema::{
        models::{
            AssociatedTypeBinding, CanonicalGoalKey, Constraint, GenericArgument, InterfaceGoal,
            InterfaceReference, SelectionMode, Ty,
        },
        tycheck::utils::normalize_aliases,
    },
};

pub(super) fn goal_key<'ctx>(
    gcx: Gcx<'ctx>,
    goal: InterfaceGoal<'ctx>,
    mode: SelectionMode,
) -> CanonicalGoalKey<'ctx> {
    let canonical_goal = canonicalize_goal(gcx, goal);
    CanonicalGoalKey::from_goal(gcx.package_index(), mode, canonical_goal)
}

fn canonicalize_goal<'ctx>(gcx: Gcx<'ctx>, goal: InterfaceGoal<'ctx>) -> InterfaceGoal<'ctx> {
    let self_ty = canonicalize_ty(gcx, goal.self_ty);

    let interface_args: Vec<_> = goal
        .interface_args
        .iter()
        .map(|arg| canonicalize_generic_arg(gcx, *arg))
        .collect();
    let interface_args = gcx.store.interners.intern_generic_args(interface_args);

    let mut bindings: Vec<_> = goal
        .bindings
        .iter()
        .map(|binding| AssociatedTypeBinding {
            name: binding.name,
            ty: canonicalize_ty(gcx, binding.ty),
        })
        .collect();
    bindings.sort_by_cached_key(|binding| {
        (
            gcx.symbol_text(binding.name).to_string(),
            binding.ty.format(gcx),
        )
    });
    let bindings = gcx.store.arenas.global.alloc_slice_clone(&bindings);

    let mut param_env: Vec<_> = goal
        .param_env
        .iter()
        .map(|constraint| canonicalize_constraint(gcx, *constraint))
        .collect();
    param_env.sort_by_cached_key(|constraint| constraint_sort_key(gcx, *constraint));
    let param_env = gcx.store.arenas.global.alloc_slice_clone(&param_env);

    InterfaceGoal {
        interface_id: goal.interface_id,
        self_ty,
        interface_args,
        bindings,
        param_env,
    }
}

fn canonicalize_ty<'ctx>(gcx: Gcx<'ctx>, ty: Ty<'ctx>) -> Ty<'ctx> {
    normalize_aliases(gcx, ty)
}

fn canonicalize_generic_arg<'ctx>(gcx: Gcx<'ctx>, arg: GenericArgument<'ctx>) -> GenericArgument<'ctx> {
    match arg {
        GenericArgument::Type(ty) => GenericArgument::Type(canonicalize_ty(gcx, ty)),
        GenericArgument::Const(c) => GenericArgument::Const(crate::sema::models::Const {
            ty: canonicalize_ty(gcx, c.ty),
            kind: c.kind,
        }),
    }
}

fn canonicalize_interface_ref<'ctx>(
    gcx: Gcx<'ctx>,
    interface: InterfaceReference<'ctx>,
) -> InterfaceReference<'ctx> {
    let arguments: Vec<_> = interface
        .arguments
        .iter()
        .map(|arg| canonicalize_generic_arg(gcx, *arg))
        .collect();
    let arguments = gcx.store.interners.intern_generic_args(arguments);

    let mut bindings: Vec<_> = interface
        .bindings
        .iter()
        .map(|binding| AssociatedTypeBinding {
            name: binding.name,
            ty: canonicalize_ty(gcx, binding.ty),
        })
        .collect();
    bindings.sort_by_cached_key(|binding| {
        (
            gcx.symbol_text(binding.name).to_string(),
            binding.ty.format(gcx),
        )
    });
    let bindings = gcx.store.arenas.global.alloc_slice_clone(&bindings);

    InterfaceReference {
        id: interface.id,
        arguments,
        bindings,
    }
}

fn canonicalize_constraint<'ctx>(gcx: Gcx<'ctx>, constraint: Constraint<'ctx>) -> Constraint<'ctx> {
    match constraint {
        Constraint::TypeEquality(lhs, rhs) => {
            let lhs = canonicalize_ty(gcx, lhs);
            let rhs = canonicalize_ty(gcx, rhs);
            if lhs.format(gcx) <= rhs.format(gcx) {
                Constraint::TypeEquality(lhs, rhs)
            } else {
                Constraint::TypeEquality(rhs, lhs)
            }
        }
        Constraint::Bound { ty, interface } => Constraint::Bound {
            ty: canonicalize_ty(gcx, ty),
            interface: canonicalize_interface_ref(gcx, interface),
        },
    }
}

fn constraint_sort_key<'ctx>(gcx: Gcx<'ctx>, constraint: Constraint<'ctx>) -> String {
    match constraint {
        Constraint::TypeEquality(lhs, rhs) => {
            format!("Eq:{}={}", lhs.format(gcx), rhs.format(gcx))
        }
        Constraint::Bound { ty, interface } => {
            format!("Bound:{}:{}", ty.format(gcx), interface.format(gcx))
        }
    }
}
