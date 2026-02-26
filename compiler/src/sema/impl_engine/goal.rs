use crate::{
    compile::context::Gcx,
    sema::models::{
        AssociatedTypeBinding, GenericArgument, GenericArguments, InterfaceGoal, InterfaceReference,
        Ty,
    },
};

pub(super) fn goal_from_interface_ref<'ctx>(
    gcx: Gcx<'ctx>,
    interface: InterfaceReference<'ctx>,
    param_env: &'ctx [crate::sema::models::Constraint<'ctx>],
) -> Option<InterfaceGoal<'ctx>> {
    let self_ty = match interface.arguments.get(0).copied() {
        Some(GenericArgument::Type(ty)) => ty,
        _ => return None,
    };
    let interface_args = if interface.arguments.len() > 1 {
        gcx.store
            .interners
            .intern_generic_args_slice(&interface.arguments[1..])
    } else {
        GenericArguments::empty()
    };
    Some(InterfaceGoal {
        interface_id: interface.id,
        self_ty,
        interface_args,
        bindings: interface.bindings,
        param_env,
    })
}

pub(super) fn interface_ref_matches_goal<'ctx>(
    gcx: Gcx<'ctx>,
    interface: InterfaceReference<'ctx>,
    goal: InterfaceGoal<'ctx>,
) -> bool {
    let mut expected = goal.to_interface_ref(gcx);
    let expected_count = gcx.generics_of(goal.interface_id).total_count();
    if expected.arguments.len() < expected_count {
        let mut args = expected.arguments.to_vec();
        while args.len() < expected_count {
            args.push(GenericArgument::Type(goal.self_ty));
        }
        expected.arguments = gcx.store.interners.intern_generic_args(args);
    }
    interface.id == expected.id
        && interface.arguments == expected.arguments
        && bindings_are_compatible(interface.bindings, goal.bindings)
}

pub(super) fn interface_ref_to_goal<'ctx>(
    gcx: Gcx<'ctx>,
    interface: InterfaceReference<'ctx>,
    param_env: &'ctx [crate::sema::models::Constraint<'ctx>],
    fallback_self: Ty<'ctx>,
) -> InterfaceGoal<'ctx> {
    match goal_from_interface_ref(gcx, interface, param_env) {
        Some(goal) => goal,
        None => InterfaceGoal {
            interface_id: interface.id,
            self_ty: fallback_self,
            interface_args: interface.arguments,
            bindings: interface.bindings,
            param_env,
        },
    }
}

fn bindings_are_compatible(
    actual: &[AssociatedTypeBinding<'_>],
    expected: &[AssociatedTypeBinding<'_>],
) -> bool {
    for rhs in expected {
        let Some(lhs) = actual.iter().find(|lhs| lhs.name == rhs.name) else {
            return false;
        };
        if lhs.ty != rhs.ty {
            return false;
        }
    }

    true
}
