use crate::GlobalContext;
use crate::fold::{TypeFoldable, TypeFolder, TypeSuperFoldable};
use crate::ty::{Constraint, GenericArgument, GenericArguments, InterfaceReference, Ty, TyKind};

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
            TyKind::Parameter(p) => {
                if let Some(ty) = self.args.get(p.index) {
                    ty.ty().expect("Argument is not a Type")
                } else {
                    unreachable!("index must be present");
                }
            }
            // Delegate to `TypeFoldable` on the *kind* itself, then rebuild
            // a fresh `Ty` only if something actually changed.
            _ => ty.super_fold_with(self),
        }
    }
}

impl<'ctx> InstantiateFolder<'ctx> {
    fn fold_interface_ref(&mut self, iface: InterfaceReference<'ctx>) -> InterfaceReference<'ctx> {
        if iface.arguments.is_empty() {
            return iface;
        }

        let args: Vec<GenericArgument<'ctx>> = iface
            .arguments
            .iter()
            .map(|ga| self.fold_generic_arg(*ga))
            .collect();
        let args = self.gcx.store.interners.intern_generic_args(&args);
        InterfaceReference {
            id: iface.id,
            arguments: args,
        }
    }

    fn fold_constraint(&mut self, c: Constraint<'ctx>) -> Constraint<'ctx> {
        match c {
            Constraint::Bound { ty, interface } => Constraint::Bound {
                ty: self.fold_ty(ty),
                interface: self.fold_interface_ref(interface),
            },
            Constraint::TypeEquality(a, b) => {
                Constraint::TypeEquality(self.fold_ty(a), self.fold_ty(b))
            }
        }
    }
}

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

pub fn instantiate_constraint_with_args<'ctx>(
    gcx: GlobalContext<'ctx>,
    constraint: Constraint<'ctx>,
    args: GenericArguments<'ctx>,
) -> Constraint<'ctx> {
    let mut folder = InstantiateFolder { gcx, args };
    folder.fold_constraint(constraint)
}
