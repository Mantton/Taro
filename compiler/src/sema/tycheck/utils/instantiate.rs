use crate::{
    compile::context::GlobalContext,
    sema::{
        models::{
            Constraint, EnumDefinition, GenericArguments, LabeledFunctionParameter,
            LabeledFunctionSignature, StructDefinition, Ty, TyKind,
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
                    ty.ty().expect("Argument is not a Type")
                } else {
                    ty
                }
            }
            // Delegate to `TypeFoldable` on the *kind* itself, then rebuild
            // a fresh `Ty` only if something actually changed.
            _ => ty.super_fold_with(self),
        }
    }
}

impl<'ctx> InstantiateFolder<'ctx> {
    fn fold_constraint(&mut self, c: Constraint<'ctx>) -> Constraint<'ctx> {
        match c {
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

pub fn instantiate_signature_with_args<'ctx>(
    gcx: GlobalContext<'ctx>,
    signature: &LabeledFunctionSignature<'ctx>,
    args: GenericArguments<'ctx>,
) -> LabeledFunctionSignature<'ctx> {
    if !signature
        .inputs
        .iter()
        .any(|param| param.ty.needs_instantiation())
        && !signature.output.needs_instantiation()
    {
        return signature.clone();
    }

    let inputs = signature
        .inputs
        .iter()
        .map(|param| LabeledFunctionParameter {
            label: param.label,
            name: param.name,
            ty: instantiate_ty_with_args(gcx, param.ty, args),
            has_default: param.has_default,
        })
        .collect();

    let output = instantiate_ty_with_args(gcx, signature.output, args);

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
