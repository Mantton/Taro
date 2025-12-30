use crate::{
    compile::context::GlobalContext,
    hir::DefinitionID,
    sema::{
        models::{AliasKind, GenericArgument, InterfaceReference, Ty, TyKind},
        tycheck::fold::{TypeFoldable, TypeFolder, TypeSuperFoldable},
    },
};
use crate::sema::tycheck::{
    resolve_conformance_witness,
    utils::{instantiate::instantiate_ty_with_args, type_head_from_value_ty},
};

pub fn normalize_ty<'ctx>(gcx: GlobalContext<'ctx>, ty: Ty<'ctx>) -> Ty<'ctx> {
    let mut folder = NormalizeFolder { gcx };
    ty.fold_with(&mut folder)
}

struct NormalizeFolder<'ctx> {
    gcx: GlobalContext<'ctx>,
}

impl<'ctx> TypeFolder<'ctx> for NormalizeFolder<'ctx> {
    fn gcx(&self) -> GlobalContext<'ctx> {
        self.gcx
    }

    fn fold_ty(&mut self, ty: Ty<'ctx>) -> Ty<'ctx> {
        match ty.kind() {
            TyKind::Alias {
                kind: AliasKind::Projection,
                def_id,
                args,
            } => {
                if let Some(resolved) = self.resolve_projection(def_id, args) {
                    return resolved.fold_with(self);
                }
                ty.super_fold_with(self)
            }
            TyKind::Alias { def_id, args, .. } => {
                let base = self.gcx.get_alias_type(def_id);
                let instantiated = instantiate_ty_with_args(self.gcx, base, args);
                instantiated.fold_with(self)
            }
            _ => ty.super_fold_with(self),
        }
    }
}

impl<'ctx> NormalizeFolder<'ctx> {
    fn resolve_projection(
        &self,
        assoc_id: DefinitionID,
        args: crate::sema::models::GenericArguments<'ctx>,
    ) -> Option<Ty<'ctx>> {
        let interface_id = self.gcx.definition_parent(assoc_id)?;
        let self_arg = args.get(0)?;
        let GenericArgument::Type(self_ty) = self_arg else {
            return None;
        };

        let self_ty = normalize_ty(self.gcx, *self_ty);
        let head = type_head_from_value_ty(self_ty)?;
        let interface = InterfaceReference {
            id: interface_id,
            arguments: args,
        };
        let witness = resolve_conformance_witness(self.gcx, head, interface)?;
        let witness_ty = witness.type_witnesses.get(&assoc_id)?;
        Some(instantiate_ty_with_args(self.gcx, *witness_ty, args))
    }
}
