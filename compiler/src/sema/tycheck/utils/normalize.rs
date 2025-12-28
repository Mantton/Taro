use crate::{
    compile::context::GlobalContext,
    sema::{
        models::{Ty, TyKind},
        tycheck::fold::{TypeFoldable, TypeFolder, TypeSuperFoldable},
    },
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
            TyKind::Alias { def_id, args, .. } => {
                // TODO: Handle projection aliases.
                let base = self.gcx.get_alias_type(def_id);
                let instantiated =
                    crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args(
                        self.gcx, base, args,
                    );
                instantiated.fold_with(self)
            }
            _ => ty.super_fold_with(self),
        }
    }
}
