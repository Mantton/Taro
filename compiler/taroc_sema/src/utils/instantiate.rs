use crate::GlobalContext;
use crate::ty::{GenericArguments, Ty};

pub fn instantiate_ty_with_args<'ctx>(
    gcx: GlobalContext<'ctx>,
    ty: Ty<'ctx>,
    args: GenericArguments<'ctx>,
) -> Ty<'ctx> {
    if !ty.needs_instantiation() {
        return ty;
    }

    todo!()
}
