use super::Emitter;
use crate::sema::{
    models::{Const, GenericArgument, GenericArguments, Ty},
    tycheck::utils::{
        instantiate::{instantiate_const_with_args, instantiate_ty_with_args},
        normalize_post_monomorphization,
    },
};

impl<'llvm, 'gcx> Emitter<'llvm, 'gcx> {
    #[inline]
    pub(super) fn substitute_ty_current(&self, ty: Ty<'gcx>) -> Ty<'gcx> {
        if self.current_subst.is_empty() {
            return ty;
        }
        instantiate_ty_with_args(self.gcx, ty, self.current_subst)
    }

    #[inline]
    pub(super) fn substitute_const_current(&self, konst: Const<'gcx>) -> Const<'gcx> {
        if self.current_subst.is_empty() {
            return konst;
        }
        instantiate_const_with_args(self.gcx, konst, self.current_subst)
    }

    #[inline]
    pub(super) fn normalize_post_mono_ty(&self, ty: Ty<'gcx>) -> Ty<'gcx> {
        normalize_post_monomorphization(self.gcx, ty)
    }

    #[inline]
    pub(super) fn mono_ty(&self, ty: Ty<'gcx>) -> Ty<'gcx> {
        self.normalize_post_mono_ty(self.substitute_ty_current(ty))
    }

    pub(super) fn resolve_generic_args(&self, args: GenericArguments<'gcx>) -> GenericArguments<'gcx> {
        if args.is_empty() {
            return args;
        }

        let resolved: Vec<_> = args
            .iter()
            .map(|arg| match arg {
                GenericArgument::Type(ty) => GenericArgument::Type(self.mono_ty(*ty)),
                GenericArgument::Const(c) => {
                    GenericArgument::Const(self.substitute_const_current(*c))
                }
            })
            .collect();
        self.gcx.store.interners.intern_generic_args(resolved)
    }
}
