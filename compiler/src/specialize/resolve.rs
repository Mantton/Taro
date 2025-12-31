use crate::{
    compile::context::GlobalContext,
    hir::DefinitionID,
    sema::{
        models::{GenericArgument, GenericArguments, InterfaceReference, Ty, TyKind},
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
    };
    let witness = resolve_conformance_witness(gcx, type_head, interface)?;
    let method = witness.method_witnesses.get(&method_id)?;
    let impl_args = instantiate_generic_args_with_args(gcx, method.args_template, call_args);
    Some(Instance::item(method.impl_id, impl_args))
}

fn interface_method_parent(gcx: GlobalContext<'_>, def_id: DefinitionID) -> Option<DefinitionID> {
    if gcx.definition_kind(def_id) != DefinitionKind::AssociatedFunction {
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
        return None;
    }
    let slice: Vec<_> = args.iter().take(count).copied().collect();
    Some(gcx.store.interners.intern_generic_args(slice))
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
                let normalized = crate::sema::tycheck::utils::normalize_post_monomorphization(
                    gcx,
                    instantiated,
                );
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
