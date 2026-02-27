use crate::{
    compile::context::GlobalContext,
    hir::{DefinitionID, StdItem},
    sema::{
        models::{ConstKind, GenericArgument, GenericArguments, InterfaceReference, Ty, TyKind},
        resolve::models::DefinitionKind,
        tycheck::{
            resolve_conformance_witness,
            utils::instantiate::{instantiate_const_with_args, instantiate_ty_with_args},
            utils::type_head_from_value_ty,
        },
    },
    specialize::Instance,
};

pub fn resolve_instance<'ctx>(
    gcx: GlobalContext<'ctx>,
    def_id: DefinitionID,
    args: GenericArguments<'ctx>,
) -> Instance<'ctx> {
    let Some(interface_id) = interface_method_parent(gcx, def_id) else {
        return Instance::item(def_id, args);
    };

    let Some(self_ty) = self_ty_from_args(gcx, def_id, args) else {
        return Instance::item(def_id, args);
    };

    let TyKind::BoxedExistential { interfaces } = self_ty.kind() else {
        if let Some(instance) =
            resolve_interface_method_for_concrete(gcx, def_id, interface_id, self_ty, args)
        {
            return instance;
        }

        return Instance::item(def_id, args);
    };

    let Some(slot) = interface_method_slot(gcx, interface_id, def_id) else {
        return Instance::item(def_id, args);
    };

    let Some(table_index) = interface_table_index(gcx, interfaces, interface_id) else {
        return Instance::item(def_id, args);
    };

    Instance::virtual_call(def_id, interface_id, slot, table_index, args)
}

fn resolve_interface_method_for_concrete<'ctx>(
    gcx: GlobalContext<'ctx>,
    method_id: DefinitionID,
    interface_id: DefinitionID,
    self_ty: Ty<'ctx>,
    call_args: GenericArguments<'ctx>,
) -> Option<Instance<'ctx>> {
    let type_head = type_head_from_value_ty(self_ty)?;
    let interface_args = interface_args_from_call(gcx, interface_id, call_args)?;
    let interface = InterfaceReference {
        id: interface_id,
        arguments: interface_args,
        bindings: &[],
    };
    let witness = resolve_conformance_witness(gcx, interface)?;

    //  Check if this is a method or operator
    let def_kind = gcx.definition_kind(method_id);
    match def_kind {
        DefinitionKind::AssociatedFunction => {
            let method = witness.method_witnesses.get(&method_id)?;

            // Default interface methods are represented by the requirement definition itself.
            // They should use the witness args template directly; attempting impl-arg deduction
            // (which is designed for concrete impl methods) can drop `Self` substitutions.
            if matches!(
                method.implementation,
                crate::sema::models::MethodImplementation::Default(_)
            ) {
                let default_args =
                    instantiate_generic_args_with_args(gcx, method.args_template, call_args);
                let final_args =
                    complete_instance_args_for_def(gcx, method_id, default_args, call_args);
                let final_args =
                    ensure_monomorphized_instance_args(gcx, method_id, final_args, call_args);
                return Some(Instance::item(method_id, final_args));
            }

            // Synthetic impls are generated as associated functions on the concrete type.
            // Their generic layout is `[self type generics..., method generics...]`, while
            // call_args are `[Self, ...interface/method generics...]`. Build the synthetic
            // instance args directly from the concrete Self type plus call-site generics.
            if matches!(
                method.implementation,
                crate::sema::models::MethodImplementation::Synthetic(..)
            ) {
                let impl_func_id = method.implementation.impl_id().or_else(|| {
                    gcx.get_synthetic_method(type_head, method_id)
                        .and_then(|info| info.syn_id)
                })?;
                let mut final_args = Vec::new();
                if let TyKind::Adt(_, adt_args) = self_ty.kind() {
                    final_args.extend(adt_args.iter().cloned());
                }
                if call_args.len() > 1 {
                    final_args.extend_from_slice(&call_args[1..]);
                }
                let final_args = gcx.store.interners.intern_generic_args(final_args);
                let final_args =
                    complete_instance_args_for_def(gcx, impl_func_id, final_args, call_args);
                let final_args =
                    ensure_monomorphized_instance_args(gcx, impl_func_id, final_args, call_args);
                return Some(Instance::item(impl_func_id, final_args));
            }

            let impl_func_id = method.implementation.impl_id()?;

            // Strategy 1: Deduction (Preferred for concrete types)
            // If this is a method from an impl block, we try to deduce the impl's generic arguments
            // by structurally matching the concrete Self type (from call) against the impl's Self type.
            // This handles cases where we need to extract inner types (e.g. List[int32] -> int32).
            if let Some(impl_id) = witness.extension_id {
                if let Some(deduced_args) =
                    crate::sema::impl_engine::deduce_impl_subst(gcx, impl_id, self_ty, &[])
                {
                    // call_args are [Self, ...method_generics]
                    // We want [deduced_impl_args..., ...method_generics]
                    let method_generics = if call_args.len() > 0 {
                        &call_args[1..]
                    } else {
                        &[]
                    };

                    let mut final_args = deduced_args.to_vec();
                    final_args.extend_from_slice(method_generics);
                    let final_args = gcx.store.interners.intern_generic_args(final_args);
                    let final_args =
                        complete_instance_args_for_def(gcx, impl_func_id, final_args, call_args);
                    let final_args = ensure_monomorphized_instance_args(
                        gcx,
                        impl_func_id,
                        final_args,
                        call_args,
                    );

                    return Some(Instance::item(impl_func_id, final_args));
                }
            }

            // Strategy 2: Template Instantiation (Fallback)
            // Use the static args_template computed during conformance checking.
            // This works when no deduction is needed or for simple substitutions.
            let impl_args =
                instantiate_generic_args_with_args(gcx, method.args_template, call_args);
            let impl_args = complete_instance_args_for_def(gcx, impl_func_id, impl_args, call_args);
            let impl_args =
                ensure_monomorphized_instance_args(gcx, impl_func_id, impl_args, call_args);
            Some(Instance::item(impl_func_id, impl_args))
        }
        _ => None,
    }
}

fn interface_method_parent(gcx: GlobalContext<'_>, def_id: DefinitionID) -> Option<DefinitionID> {
    let def_kind = gcx.definition_kind(def_id);
    if def_kind != DefinitionKind::AssociatedFunction {
        return None;
    }

    let parent = gcx.definition_parent(def_id)?;
    if gcx.definition_kind(parent) == DefinitionKind::Interface {
        Some(parent)
    } else {
        None
    }
}

fn self_ty_from_args<'ctx>(
    gcx: GlobalContext<'ctx>,
    def_id: DefinitionID,
    args: GenericArguments<'ctx>,
) -> Option<Ty<'ctx>> {
    let generics = gcx.generics_of(def_id);
    if !generics.has_self {
        return None;
    }

    match args.get(0) {
        Some(GenericArgument::Type(ty)) => Some(*ty),
        _ => None,
    }
}

fn interface_method_slot(
    gcx: GlobalContext<'_>,
    interface_id: DefinitionID,
    method_id: DefinitionID,
) -> Option<usize> {
    gcx.with_type_database(interface_id.package(), |db| {
        let requirements = db.interface_requirements.get(&interface_id)?;
        requirements
            .methods
            .iter()
            .position(|method| method.id == method_id)
    })
}

fn interface_table_index<'ctx>(
    gcx: GlobalContext<'ctx>,
    interfaces: &'ctx [InterfaceReference<'ctx>],
    method_interface: DefinitionID,
) -> Option<usize> {
    for (index, iface) in interfaces.iter().enumerate() {
        // TODO: Match interface arguments if duplicates with different args are allowed.
        if iface.id == method_interface {
            return Some(index);
        }

        if interface_has_superface(gcx, iface.id, method_interface) {
            return Some(index);
        }
    }

    None
}

fn interface_has_superface(
    gcx: GlobalContext<'_>,
    root_interface: DefinitionID,
    target_interface: DefinitionID,
) -> bool {
    gcx.with_type_database(root_interface.package(), |db| {
        db.interface_to_supers
            .get(&root_interface)
            .map_or(false, |supers| supers.contains(&target_interface))
    })
}

fn interface_args_from_call<'ctx>(
    gcx: GlobalContext<'ctx>,
    interface_id: DefinitionID,
    args: GenericArguments<'ctx>,
) -> Option<GenericArguments<'ctx>> {
    let count = gcx.generics_of(interface_id).total_count();
    if count == 0 {
        return Some(gcx.store.interners.intern_generic_args(Vec::new()));
    }
    if args.len() < count {
        // PartialEq has default `Rhs = Self`; calls often materialize only `Self`.
        if let Some(partial_eq_id) = gcx.std_item_def(StdItem::PartialEq) {
            if interface_id == partial_eq_id && args.len() == 1 {
                let self_arg = args.get(0).copied()?;
                if let GenericArgument::Type(self_ty) = self_arg {
                    return Some(gcx.store.interners.intern_generic_args(vec![
                        GenericArgument::Type(self_ty),
                        GenericArgument::Type(self_ty),
                    ]));
                }
            }
        }
        return None;
    }
    let slice: Vec<_> = args.iter().take(count).cloned().collect();
    Some(gcx.store.interners.intern_generic_args(slice))
}

fn complete_instance_args_for_def<'ctx>(
    gcx: GlobalContext<'ctx>,
    def_id: DefinitionID,
    candidate: GenericArguments<'ctx>,
    call_args: GenericArguments<'ctx>,
) -> GenericArguments<'ctx> {
    let generics = gcx.generics_of(def_id);
    let expected = generics.parent_count + generics.total_count();
    if candidate.len() >= expected {
        return candidate;
    }

    let mut out: Vec<_> = candidate.iter().copied().collect();

    if generics.has_self && out.len() < expected {
        if let Some(self_arg) = call_args.get(0) {
            if out.first().copied() != Some(*self_arg) {
                out.insert(0, *self_arg);
            }
        }
    }

    while out.len() < expected {
        let next_index = out.len();
        let Some(arg) = call_args.get(next_index) else {
            break;
        };
        out.push(*arg);
    }

    gcx.store.interners.intern_generic_args(out)
}

fn ensure_monomorphized_instance_args<'ctx>(
    gcx: GlobalContext<'ctx>,
    def_id: DefinitionID,
    candidate: GenericArguments<'ctx>,
    call_args: GenericArguments<'ctx>,
) -> GenericArguments<'ctx> {
    if !signature_has_unresolved_generics(gcx, def_id, candidate) {
        return candidate;
    }

    if call_args.len() > candidate.len() {
        let mut merged: Vec<_> = candidate.iter().copied().collect();
        for index in merged.len()..call_args.len() {
            if let Some(arg) = call_args.get(index) {
                merged.push(*arg);
            }
        }
        let merged = gcx.store.interners.intern_generic_args(merged);
        if !signature_has_unresolved_generics(gcx, def_id, merged) {
            return merged;
        }
    }

    if !signature_has_unresolved_generics(gcx, def_id, call_args) {
        return call_args;
    }

    candidate
}

fn signature_has_unresolved_generics<'ctx>(
    gcx: GlobalContext<'ctx>,
    def_id: DefinitionID,
    args: GenericArguments<'ctx>,
) -> bool {
    let sig = gcx.get_signature(def_id);
    sig.inputs.iter().any(|param| {
        let instantiated = instantiate_ty_with_args(gcx, param.ty, args);
        ty_has_unresolved_generics(instantiated)
    }) || ty_has_unresolved_generics(instantiate_ty_with_args(gcx, sig.output, args))
}

fn ty_has_unresolved_generics<'ctx>(ty: Ty<'ctx>) -> bool {
    match ty.kind() {
        TyKind::Parameter(_) | TyKind::Infer(_) | TyKind::Alias { .. } => true,
        TyKind::Adt(_, args) => args.iter().any(|arg| match arg {
            GenericArgument::Type(ty) => ty_has_unresolved_generics(*ty),
            GenericArgument::Const(c) => {
                matches!(c.kind, ConstKind::Param(_) | ConstKind::Infer(_))
                    || ty_has_unresolved_generics(c.ty)
            }
        }),
        TyKind::Pointer(inner, _) | TyKind::Reference(inner, _) => {
            ty_has_unresolved_generics(inner)
        }
        TyKind::Array { element, len } => {
            ty_has_unresolved_generics(element)
                || matches!(len.kind, ConstKind::Param(_) | ConstKind::Infer(_))
                || ty_has_unresolved_generics(len.ty)
        }
        TyKind::Tuple(items) => items.iter().any(|item| ty_has_unresolved_generics(*item)),
        TyKind::FnPointer { inputs, output } => {
            inputs
                .iter()
                .any(|input| ty_has_unresolved_generics(*input))
                || ty_has_unresolved_generics(output)
        }
        TyKind::BoxedExistential { interfaces } => interfaces.iter().any(|iface| {
            iface.arguments.iter().any(|arg| match arg {
                GenericArgument::Type(ty) => ty_has_unresolved_generics(*ty),
                GenericArgument::Const(c) => {
                    matches!(c.kind, ConstKind::Param(_) | ConstKind::Infer(_))
                        || ty_has_unresolved_generics(c.ty)
                }
            }) || iface
                .bindings
                .iter()
                .any(|binding| ty_has_unresolved_generics(binding.ty))
        }),
        _ => false,
    }
}

fn instantiate_generic_args_with_args<'ctx>(
    gcx: GlobalContext<'ctx>,
    template: GenericArguments<'ctx>,
    args: GenericArguments<'ctx>,
) -> GenericArguments<'ctx> {
    if template.is_empty() {
        return template;
    }

    let mut out = Vec::with_capacity(template.len());
    for arg in template.iter() {
        match arg {
            GenericArgument::Type(ty) => {
                let instantiated = instantiate_ty_with_args(gcx, *ty, args);
                let normalized =
                    crate::sema::tycheck::utils::normalize_post_monomorphization(gcx, instantiated);
                out.push(GenericArgument::Type(normalized));
            }
            GenericArgument::Const(c) => {
                let instantiated = instantiate_const_with_args(gcx, *c, args);
                out.push(GenericArgument::Const(instantiated));
            }
        }
    }

    gcx.store.interners.intern_generic_args(out)
}
