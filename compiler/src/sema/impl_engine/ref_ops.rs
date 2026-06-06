use crate::{
    compile::context::Gcx,
    hir::DefinitionID,
    sema::{
        models::{
            AssociatedTypeBinding, GenericArgument, GenericArguments,
            GenericParameterDefinitionKind, InterfaceReference, Ty,
        },
        resolve::models::DefinitionKind,
        tycheck::{
            fold::{TypeFoldable, TypeFolder, TypeSuperFoldable},
            utils::instantiate::{instantiate_const_with_args, instantiate_ty_with_args},
        },
    },
};
use rustc_hash::FxHashSet;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InterfaceRefMatch {
    /// Match interface id and non-Self generic arguments, ignoring associated
    /// type bindings. This is used to find candidate conformance records before
    /// witness construction validates bindings.
    Header,
    /// Match the logical interface identity used by existential tables and metadata.
    /// The implicit Self argument is ignored, but non-Self arguments and bindings
    /// must match exactly.
    Logical,
}

pub fn complete_interface_arguments<'ctx>(
    gcx: Gcx<'ctx>,
    interface_id: DefinitionID,
    provided: GenericArguments<'ctx>,
) -> Option<GenericArguments<'ctx>> {
    if gcx.definition_kind(interface_id) != DefinitionKind::Interface {
        return Some(provided);
    }

    let generics = gcx.generics_of(interface_id);
    let expected = generics.total_count();
    if provided.len() >= expected {
        return Some(
            gcx.store
                .interners
                .intern_generic_args_slice(&provided[..expected]),
        );
    }

    let mut out: Vec<_> = provided.iter().copied().collect();
    for param in generics.parameters.iter().skip(out.len()) {
        let current_args = gcx.store.interners.intern_generic_args_slice(&out);
        match &param.kind {
            GenericParameterDefinitionKind::Type { default: Some(_) } => {
                let mut default_ty = gcx.try_generic_type_default(param.id)?;
                if let Some(GenericArgument::Type(self_ty)) = out.first().copied() {
                    default_ty = substitute_interface_self_default(gcx, default_ty, self_ty);
                }
                default_ty = instantiate_ty_with_args(gcx, default_ty, current_args);
                out.push(GenericArgument::Type(default_ty));
            }
            GenericParameterDefinitionKind::Const {
                default: Some(_), ..
            } => {
                let default_const = gcx.try_generic_const_default(param.id)?;
                let default_const = instantiate_const_with_args(gcx, default_const, current_args);
                out.push(GenericArgument::Const(default_const));
            }
            GenericParameterDefinitionKind::Type { default: None }
            | GenericParameterDefinitionKind::Const { default: None, .. } => return None,
        }
    }

    Some(gcx.store.interners.intern_generic_args(out))
}

pub fn interface_ref_with_self<'ctx>(
    gcx: Gcx<'ctx>,
    self_ty: Ty<'ctx>,
    iface: InterfaceReference<'ctx>,
) -> InterfaceReference<'ctx> {
    if iface.arguments.is_empty() {
        return iface;
    }

    let mut args: Vec<_> = iface.arguments.iter().copied().collect();
    args[0] = GenericArgument::Type(self_ty);
    let arguments = gcx.store.interners.intern_generic_args(args);
    InterfaceReference {
        id: iface.id,
        arguments,
        bindings: iface.bindings,
    }
}

pub fn substitute_interface_ref<'ctx>(
    gcx: Gcx<'ctx>,
    template: InterfaceReference<'ctx>,
    args: GenericArguments<'ctx>,
) -> InterfaceReference<'ctx> {
    if args.is_empty() {
        return template;
    }

    let mut new_args = Vec::with_capacity(template.arguments.len());
    for arg in template.arguments.iter().copied() {
        match arg {
            GenericArgument::Type(ty) => {
                new_args.push(GenericArgument::Type(instantiate_ty_with_args(
                    gcx, ty, args,
                )));
            }
            GenericArgument::Const(c) => {
                new_args.push(GenericArgument::Const(instantiate_const_with_args(
                    gcx, c, args,
                )));
            }
        }
    }

    let mut new_bindings = Vec::with_capacity(template.bindings.len());
    for binding in template.bindings {
        new_bindings.push(AssociatedTypeBinding {
            name: binding.name,
            ty: instantiate_ty_with_args(gcx, binding.ty, args),
        });
    }

    InterfaceReference {
        id: template.id,
        arguments: gcx.store.interners.intern_generic_args(new_args),
        bindings: gcx.store.arenas.global.alloc_slice_clone(&new_bindings),
    }
}

pub fn collect_interface_with_superfaces<'ctx>(
    gcx: Gcx<'ctx>,
    root: InterfaceReference<'ctx>,
) -> Vec<InterfaceReference<'ctx>> {
    let mut out = Vec::new();
    let mut queue = std::collections::VecDeque::new();
    let mut seen: FxHashSet<InterfaceReference<'ctx>> = FxHashSet::default();

    seen.insert(root);
    out.push(root);
    queue.push_back(root);

    while let Some(current) = queue.pop_front() {
        let Some(def) = gcx.get_interface_definition(current.id) else {
            continue;
        };

        for superface in &def.superfaces {
            let iface = substitute_interface_ref(gcx, superface.value, current.arguments);
            if seen.insert(iface) {
                out.push(iface);
                queue.push_back(iface);
            }
        }
    }

    out
}

pub fn direct_superfaces<'ctx>(
    gcx: Gcx<'ctx>,
    iface: InterfaceReference<'ctx>,
) -> Vec<InterfaceReference<'ctx>> {
    let Some(def) = gcx.get_interface_definition(iface.id) else {
        return Vec::new();
    };

    def.superfaces
        .iter()
        .map(|superface| substitute_interface_ref(gcx, superface.value, iface.arguments))
        .collect()
}

pub fn superface_chain_to_interface_ref<'ctx>(
    gcx: Gcx<'ctx>,
    root: InterfaceReference<'ctx>,
    target: InterfaceReference<'ctx>,
) -> Option<Vec<(DefinitionID, usize)>> {
    let mut queue = std::collections::VecDeque::new();
    let mut seen = FxHashSet::default();
    queue.push_back((root, Vec::new()));
    seen.insert(root);

    while let Some((current, chain)) = queue.pop_front() {
        for (super_index, superface) in direct_superfaces(gcx, current).into_iter().enumerate() {
            if !seen.insert(superface) {
                continue;
            }

            let mut next_chain = chain.clone();
            next_chain.push((current.id, super_index));
            if interface_ref_matches(target, superface, InterfaceRefMatch::Logical) {
                return Some(next_chain);
            }
            queue.push_back((superface, next_chain));
        }
    }

    None
}

pub fn interface_ref_matches<'ctx>(
    expected: InterfaceReference<'ctx>,
    actual: InterfaceReference<'ctx>,
    mode: InterfaceRefMatch,
) -> bool {
    if expected.id != actual.id {
        return false;
    }

    let expected_args = match mode {
        InterfaceRefMatch::Header | InterfaceRefMatch::Logical => {
            interface_args_without_self(expected)
        }
    };
    let actual_args = match mode {
        InterfaceRefMatch::Header | InterfaceRefMatch::Logical => {
            interface_args_without_self(actual)
        }
    };

    if expected_args != actual_args {
        return false;
    }

    match mode {
        InterfaceRefMatch::Header => true,
        InterfaceRefMatch::Logical => bindings_are_compatible(expected.bindings, actual.bindings),
    }
}

pub fn interface_method_slot(
    gcx: Gcx<'_>,
    interface_id: DefinitionID,
    method_id: DefinitionID,
) -> Option<usize> {
    let requirements = gcx.get_interface_requirements(interface_id)?;
    requirements
        .methods
        .iter()
        .filter(|method| method.has_self)
        .position(|method| method.id == method_id)
}

pub fn descriptor_key_interface_ref<'ctx>(
    gcx: Gcx<'ctx>,
    iface: InterfaceReference<'ctx>,
) -> InterfaceReference<'ctx> {
    let arguments = gcx
        .store
        .interners
        .intern_generic_args_slice(interface_args_without_self(iface));
    InterfaceReference {
        id: iface.id,
        arguments,
        bindings: iface.bindings,
    }
}

fn interface_args_without_self<'ctx>(
    iface: InterfaceReference<'ctx>,
) -> &'ctx [GenericArgument<'ctx>] {
    let args = iface.arguments.as_slice();
    if args.is_empty() { args } else { &args[1..] }
}

fn bindings_are_compatible(
    expected: &[AssociatedTypeBinding<'_>],
    actual: &[AssociatedTypeBinding<'_>],
) -> bool {
    expected.iter().all(|expected_binding| {
        actual
            .iter()
            .any(|actual_binding| actual_binding == expected_binding)
    })
}

fn substitute_interface_self_default<'ctx>(
    gcx: Gcx<'ctx>,
    ty: Ty<'ctx>,
    concrete_self_ty: Ty<'ctx>,
) -> Ty<'ctx> {
    struct InterfaceSelfSubstitutor<'ctx> {
        gcx: Gcx<'ctx>,
        concrete_self_ty: Ty<'ctx>,
    }

    impl<'ctx> TypeFolder<'ctx> for InterfaceSelfSubstitutor<'ctx> {
        fn gcx(&self) -> Gcx<'ctx> {
            self.gcx
        }

        fn fold_ty(&mut self, ty: Ty<'ctx>) -> Ty<'ctx> {
            if ty == self.gcx.types.self_type_parameter {
                return self.concrete_self_ty;
            }
            ty.super_fold_with(self)
        }
    }

    let mut substitutor = InterfaceSelfSubstitutor {
        gcx,
        concrete_self_ty,
    };
    ty.fold_with(&mut substitutor)
}
