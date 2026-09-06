use crate::{
    compile::context::GlobalContext,
    sema::{
        models::{
            Const, ConstKind, Constraint, EnumDefinition, GenericArgument, GenericArguments,
            InterfaceReference, LabeledFunctionParameter, LabeledFunctionSignature,
            StructDefinition, Ty, TyKind,
        },
        tycheck::fold::{TypeFoldable, TypeFolder, TypeSuperFoldable},
    },
};

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
                    (*ty).ty().expect("Argument is not a Type")
                } else {
                    ty
                }
            }
            // Delegate to `TypeFoldable` on the *kind* itself, then rebuild
            // a fresh `Ty` only if something actually changed.
            _ => ty.super_fold_with(self),
        }
    }

    fn fold_const(&mut self, c: Const<'ctx>) -> Const<'ctx> {
        if let ConstKind::Param(param) = c.kind {
            if let Some(GenericArgument::Const(value)) = self.args.get(param.index) {
                return *value;
            }
        }
        Const {
            ty: c.ty.fold_with(self),
            ..c
        }
    }
}

pub fn instantiate_ty_with_args<'ctx>(
    gcx: GlobalContext<'ctx>,
    ty: Ty<'ctx>,
    args: GenericArguments<'ctx>,
) -> Ty<'ctx> {
    if args.is_empty() {
        return ty;
    }

    let mut folder = InstantiateFolder { gcx, args };
    ty.fold_with(&mut folder)
}

pub fn instantiate_const_with_args<'ctx>(
    gcx: GlobalContext<'ctx>,
    c: Const<'ctx>,
    args: GenericArguments<'ctx>,
) -> Const<'ctx> {
    c.fold_with(&mut InstantiateFolder { gcx, args })
}

pub fn instantiate_constraint_with_args<'ctx>(
    gcx: GlobalContext<'ctx>,
    constraint: Constraint<'ctx>,
    args: GenericArguments<'ctx>,
) -> Constraint<'ctx> {
    let mut folder = InstantiateFolder { gcx, args };
    constraint.fold_with(&mut folder)
}

/// Substitute type and const arguments without normalizing associated projections.
pub fn instantiate_generic_args<'ctx>(
    gcx: GlobalContext<'ctx>,
    template: GenericArguments<'ctx>,
    args: GenericArguments<'ctx>,
) -> GenericArguments<'ctx> {
    if args.is_empty() {
        return template;
    }
    template.fold_with(&mut InstantiateFolder { gcx, args })
}

pub fn instantiate_interface_ref_with_args<'ctx>(
    gcx: GlobalContext<'ctx>,
    interface: InterfaceReference<'ctx>,
    args: GenericArguments<'ctx>,
) -> InterfaceReference<'ctx> {
    if args.is_empty() {
        return interface;
    }

    interface.fold_with(&mut InstantiateFolder { gcx, args })
}

pub fn instantiate_signature_with_args<'ctx>(
    gcx: GlobalContext<'ctx>,
    signature: &LabeledFunctionSignature<'ctx>,
    args: GenericArguments<'ctx>,
) -> LabeledFunctionSignature<'ctx> {
    if args.is_empty() {
        return signature.clone();
    }
    let mut folder = InstantiateFolder { gcx, args };

    let inputs = signature
        .inputs
        .iter()
        .map(|param| LabeledFunctionParameter {
            label: param.label,
            name: param.name,
            ty: param.ty.fold_with(&mut folder),
            default_provider: param.default_provider,
        })
        .collect();

    let output = signature.output.fold_with(&mut folder);

    LabeledFunctionSignature {
        inputs,
        output,
        is_variadic: signature.is_variadic,
        abi: signature.abi,
    }
}

pub fn instantiate_struct_definition_with_args<'ctx>(
    gcx: GlobalContext<'ctx>,
    def: &StructDefinition<'ctx>,
    args: GenericArguments<'ctx>,
) -> StructDefinition<'ctx> {
    let mut folder = InstantiateFolder { gcx, args };
    def.clone().fold_with(&mut folder)
}

pub fn instantiate_enum_definition_with_args<'ctx>(
    gcx: GlobalContext<'ctx>,
    def: &EnumDefinition<'ctx>,
    args: GenericArguments<'ctx>,
) -> EnumDefinition<'ctx> {
    let mut folder = InstantiateFolder { gcx, args };
    def.clone().fold_with(&mut folder)
}
