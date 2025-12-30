use crate::{
    sema::{
        models::{
            GenericArgument, GenericArguments, InterfaceDefinition, InterfaceReference,
            InterfaceRequirements,
        },
        resolve::models::DefinitionID,
        tycheck::utils::instantiate::{instantiate_const_with_args, instantiate_ty_with_args},
    },
};

use rustc_hash::FxHashSet;

use super::ConstraintSolver;

impl<'ctx> ConstraintSolver<'ctx> {
    pub fn resolve_interface_ref(
        &self,
        interface: InterfaceReference<'ctx>,
    ) -> (InterfaceReference<'ctx>, bool) {
        let mut has_infer = false;
        let mut new_args = Vec::with_capacity(interface.arguments.len());
        for arg in interface.arguments.iter() {
            match arg {
                GenericArgument::Type(ty) => {
                    let resolved = self.structurally_resolve(*ty);
                    if resolved.is_infer() {
                        has_infer = true;
                    }
                    new_args.push(GenericArgument::Type(resolved));
                }
                GenericArgument::Const(c) => new_args.push(GenericArgument::Const(*c)),
            }
        }

        let interned = self.gcx().store.interners.intern_generic_args(new_args);
        (
            InterfaceReference {
                id: interface.id,
                arguments: interned,
            },
            has_infer,
        )
    }

    pub fn interface_requirements(
        &self,
        interface_id: DefinitionID,
    ) -> Option<&'ctx InterfaceRequirements<'ctx>> {
        self.gcx().with_type_database(interface_id.package(), |db| {
            db.interface_requirements.get(&interface_id).copied()
        })
    }

    pub fn interface_definition(
        &self,
        interface_id: DefinitionID,
    ) -> Option<&'ctx InterfaceDefinition<'ctx>> {
        self.gcx().with_type_database(interface_id.package(), |db| {
            db.def_to_iface_def.get(&interface_id).copied()
        })
    }

    pub fn interface_method_slot(
        &self,
        interface_id: DefinitionID,
        method_id: DefinitionID,
    ) -> Option<usize> {
        let requirements = self.interface_requirements(interface_id)?;
        requirements
            .methods
            .iter()
            .position(|method| method.id == method_id)
    }

    pub fn collect_interface_with_supers(
        &self,
        root: InterfaceReference<'ctx>,
    ) -> Vec<InterfaceReference<'ctx>> {
        let mut out = Vec::new();
        let mut queue = std::collections::VecDeque::new();
        let mut seen: FxHashSet<DefinitionID> = FxHashSet::default();

        seen.insert(root.id);
        out.push(root);
        queue.push_back(root);

        while let Some(current) = queue.pop_front() {
            let Some(def) = self.interface_definition(current.id) else {
                continue;
            };

            for superface in &def.superfaces {
                let iface = self.substitute_interface_ref(superface.value, current.arguments);
                if seen.insert(iface.id) {
                    out.push(iface);
                    queue.push_back(iface);
                }
            }
        }

        out
    }

    fn substitute_interface_ref(
        &self,
        template: InterfaceReference<'ctx>,
        args: GenericArguments<'ctx>,
    ) -> InterfaceReference<'ctx> {
        if args.is_empty() {
            return template;
        }

        let gcx = self.gcx();
        let mut new_args = Vec::with_capacity(template.arguments.len());
        for arg in template.arguments.iter() {
            match arg {
                GenericArgument::Type(ty) => {
                    let substituted = instantiate_ty_with_args(gcx, *ty, args);
                    new_args.push(GenericArgument::Type(substituted));
                }
                GenericArgument::Const(c) => {
                    let substituted = instantiate_const_with_args(gcx, *c, args);
                    new_args.push(GenericArgument::Const(substituted));
                }
            }
        }

        let interned = gcx.store.interners.intern_generic_args(new_args);
        InterfaceReference {
            id: template.id,
            arguments: interned,
        }
    }
}
