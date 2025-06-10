use crate::GlobalContext;
use crate::fold::{TypeFoldable, TypeFolder, TypeSuperFoldable};
use crate::ty::{GenericArguments, Ty, TyKind};

pub fn instantiate_ty_with_args<'ctx>(
    gcx: GlobalContext<'ctx>,
    ty: Ty<'ctx>,
    args: GenericArguments<'ctx>,
) -> Ty<'ctx> {
    if !ty.needs_instantiation() {
        return ty;
    }

    let mut folder = InstantiateFolder { gcx, args };
    ty.fold_with(&mut folder)
}

pub struct InstantiateFolder<'ctx> {
    gcx: GlobalContext<'ctx>,
    args: GenericArguments<'ctx>,
}

impl<'ctx> TypeFolder<'ctx> for InstantiateFolder<'ctx> {
    fn gcx(&self) -> GlobalContext<'ctx> {
        self.gcx
    }

    fn fold_ty(&mut self, ty: Ty<'ctx>) -> Ty<'ctx> {
        match ty.kind() {
            TyKind::Parameter(p) => self.args.get(p.index).and_then(|ga| ga.ty()).unwrap_or(ty),

            // Delegate to `TypeFoldable` on the *kind* itself, then rebuild
            // a fresh `Ty` only if something actually changed.
            _ => ty.super_fold_with(self),
        }
    }
}
