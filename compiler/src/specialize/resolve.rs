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

use crate::sema::tycheck::infer::InferCtx;
use crate::sema::tycheck::utils::unify::TypeUnifier;
use std::rc::Rc;

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
    let witness = resolve_conformance_witness(gcx, type_head, interface)?;

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
                return Some(Instance::item(method_id, default_args));
            }

            let impl_func_id = method.implementation.impl_id()?;

            // Strategy 1: Deduction (Preferred for concrete types)
            // If this is a method from an impl block, we try to deduce the impl's generic arguments
            // by structurally matching the concrete Self type (from call) against the impl's Self type.
            // This handles cases where we need to extract inner types (e.g. List[int32] -> int32).
            if let Some(impl_id) = witness.extension_id {
                if let Some(deduced_args) = deduce_impl_args(gcx, impl_id, self_ty) {
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

                    return Some(Instance::item(impl_func_id, final_args));
                }
            }

            // Strategy 2: Template Instantiation (Fallback)
            // Use the static args_template computed during conformance checking.
            // This works when no deduction is needed or for simple substitutions.
            let impl_args =
                instantiate_generic_args_with_args(gcx, method.args_template, call_args);
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

fn deduce_impl_args<'ctx>(
    gcx: GlobalContext<'ctx>,
    impl_id: DefinitionID,
    concrete_self_ty: Ty<'ctx>,
) -> Option<GenericArguments<'ctx>> {
    let impl_self_ty = gcx.get_impl_self_ty(impl_id)?;

    // Create inference context
    let icx = Rc::new(InferCtx::new(gcx));

    // Create fresh inference vars for the impl's generic parameters
    // We pass a dummy span since we don't have a real call site span readily available here,
    // but we could thread one through if needed for error reporting (though we swallow errors here).
    let span = crate::span::Span::empty(crate::span::FileID::from_usize(0));
    let fresh_args = icx.fresh_args_for_def(impl_id, span);

    // Instantiate the impl's Self type with these fresh variables
    // e.g. ListRefIterator[?0]
    let instantiated_impl_ty = instantiate_ty_with_args(gcx, impl_self_ty, fresh_args);

    // Unify the instantiated impl type with the concrete type
    // e.g. Unify ListRefIterator[?0] with ListRefIterator[int32] -> ?0 = int32
    let unifier = TypeUnifier::new(icx.clone());

    if unifier
        .unify(instantiated_impl_ty, concrete_self_ty)
        .is_err()
    {
        return None;
    }

    // Resolve the inference variables to their concrete values
    let resolved_args = icx.resolve_args_if_possible(fresh_args);

    Some(resolved_args)
}
