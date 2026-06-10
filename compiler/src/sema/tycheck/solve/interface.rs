use crate::sema::{
    models::{GenericArgument, InterfaceReference, InterfaceRequirements},
    resolve::models::DefinitionID,
};

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
                GenericArgument::Const(c) => {
                    let resolved = self.icx.resolve_const_if_possible(*c);
                    if matches!(resolved.kind, crate::sema::models::ConstKind::Infer(_)) {
                        has_infer = true;
                    }
                    new_args.push(GenericArgument::Const(resolved));
                }
            }
        }

        let mut new_bindings = Vec::with_capacity(interface.bindings.len());
        for binding in interface.bindings {
            let resolved_ty = self.structurally_resolve(binding.ty);
            if resolved_ty.is_infer() {
                has_infer = true;
            }
            new_bindings.push(crate::sema::models::AssociatedTypeBinding {
                name: binding.name,
                ty: resolved_ty,
            });
        }

        let interned = self.gcx().store.interners.intern_generic_args(new_args);
        (
            InterfaceReference {
                id: interface.id,
                arguments: interned,
                bindings: self
                    .gcx()
                    .store
                    .arenas
                    .global
                    .alloc_slice_clone(&new_bindings),
            },
            has_infer,
        )
    }

    pub fn interface_requirements(
        &self,
        interface_id: DefinitionID,
    ) -> Option<&'ctx InterfaceRequirements<'ctx>> {
        self.gcx().with_type_database(interface_id.package(), |db| {
            db.interface_requirements.get(&interface_id).cloned()
        })
    }

    pub fn collect_interface_with_supers(
        &self,
        root: InterfaceReference<'ctx>,
    ) -> Vec<InterfaceReference<'ctx>> {
        crate::sema::impl_engine::ref_ops::collect_interface_with_superfaces(self.gcx(), root)
    }
}
