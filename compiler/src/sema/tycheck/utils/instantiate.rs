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

    fn fold_const(&mut self, c: Const<'ctx>) -> Const<'ctx> {
        instantiate_const_with_args(self.gcx, c, self.args)
    }
}

impl<'ctx> InstantiateFolder<'ctx> {
    fn fold_constraint(&mut self, c: Constraint<'ctx>) -> Constraint<'ctx> {
        match c {
            Constraint::TypeEquality(a, b) => {
                Constraint::TypeEquality(self.fold_ty(a), self.fold_ty(b))
            }
            Constraint::Bound { ty, interface } => Constraint::Bound {
                ty: self.fold_ty(ty),
                interface: instantiate_interface_ref_with_args(self.gcx, interface, self.args),
            },
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

pub fn instantiate_const_with_args<'ctx>(
    gcx: GlobalContext<'ctx>,
    c: Const<'ctx>,
    args: GenericArguments<'ctx>,
) -> Const<'ctx> {
    let ty = instantiate_ty_with_args(gcx, c.ty, args);
    let kind = match c.kind {
        ConstKind::Param(p) => match args.get(p.index) {
            Some(GenericArgument::Const(arg)) => return *arg,
            _ => ConstKind::Param(p),
        },
        ConstKind::Infer(_) => c.kind,
        ConstKind::Value(_) => c.kind,
    };
    Const { ty, kind }
}

pub fn instantiate_constraint_with_args<'ctx>(
    gcx: GlobalContext<'ctx>,
    constraint: Constraint<'ctx>,
    args: GenericArguments<'ctx>,
) -> Constraint<'ctx> {
    let mut folder = InstantiateFolder { gcx, args };
    folder.fold_constraint(constraint)
}

pub fn instantiate_interface_ref_with_args<'ctx>(
    gcx: GlobalContext<'ctx>,
    interface: InterfaceReference<'ctx>,
    args: GenericArguments<'ctx>,
) -> InterfaceReference<'ctx> {
    if args.is_empty() {
        return interface;
    }

    let mut new_args = Vec::with_capacity(interface.arguments.len());
    for arg in interface.arguments.iter() {
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

    let mut new_bindings = Vec::with_capacity(interface.bindings.len());
    for binding in interface.bindings {
        let substituted = instantiate_ty_with_args(gcx, binding.ty, args);
        new_bindings.push(crate::sema::models::AssociatedTypeBinding {
            name: binding.name,
            ty: substituted,
        });
    }

    let interned = gcx.store.interners.intern_generic_args(new_args);
    InterfaceReference {
        id: interface.id,
        arguments: interned,
        bindings: gcx.store.arenas.global.alloc_slice_copy(&new_bindings),
    }
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
            default_provider: param.default_provider,
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
