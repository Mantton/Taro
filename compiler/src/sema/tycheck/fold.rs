use crate::{
    compile::context::GlobalContext,
    sema::models::{
        Const, EnumDefinition, EnumVariant, EnumVariantField, EnumVariantKind, GenericArgument,
        InterfaceReference, StructDefinition, StructField, Ty, TyKind,
    },
};

/// The transformer – you implement this once per pass.
pub trait TypeFolder<'ctx> {
    fn gcx(&self) -> GlobalContext<'ctx>;
    /// Called on every `Ty` that is *not* a leaf. You usually match on `ty.kind()`
    /// and reconstruct it with `self.fold_ty(...)` where needed.
    fn fold_ty(&mut self, ty: Ty<'ctx>) -> Ty<'ctx>;
    /// Called on const values encountered inside types.
    fn fold_const(&mut self, c: Const<'ctx>) -> Const<'ctx> {
        Const {
            ty: c.ty.fold_with(self),
            kind: c.kind,
        }
    }

    // Default rewrite for a generic argument.
    // fn fold_generic_arg(&mut self, arg: GenericArgument<'ctx>) -> GenericArgument<'ctx> {
    //     match arg {
    //         GenericArgument::Type(t) => GenericArgument::Type(self.fold_ty(t)),
    //         other @ GenericArgument::Const(_) => other,
    //     }
    // }
}

/// Blanket traversal: every container that can hold a `Ty` implements this.
pub trait TypeFoldable<'ctx>: Sized {
    fn fold_with<F: TypeFolder<'ctx> + ?Sized>(self, folder: &mut F) -> Self;
}

impl<'ctx> TypeFoldable<'ctx> for Ty<'ctx> {
    fn fold_with<F: TypeFolder<'ctx> + ?Sized>(self, folder: &mut F) -> Self {
        folder.fold_ty(self)
    }
}

impl<'ctx> TypeFoldable<'ctx> for Const<'ctx> {
    fn fold_with<F: TypeFolder<'ctx> + ?Sized>(self, folder: &mut F) -> Self {
        folder.fold_const(self)
    }
}

impl<'ctx> TypeFoldable<'ctx> for TyKind<'ctx> {
    fn fold_with<F: TypeFolder<'ctx> + ?Sized>(self, folder: &mut F) -> Self {
        self.super_fold_with(folder)
    }
}
/// Provides default structural folding behavior
pub trait TypeSuperFoldable<'ctx>: TypeFoldable<'ctx> {
    /// Default structural folding - recurses into substructures
    fn super_fold_with<F: TypeFolder<'ctx> + ?Sized>(self, folder: &mut F) -> Self;
}

impl<'ctx> TypeSuperFoldable<'ctx> for Ty<'ctx> {
    fn super_fold_with<F: TypeFolder<'ctx> + ?Sized>(self, folder: &mut F) -> Self {
        let folded_kind = self.kind().super_fold_with(folder);
        Ty::new(folded_kind, folder.gcx())
    }
}

impl<'ctx> TypeSuperFoldable<'ctx> for TyKind<'ctx> {
    fn super_fold_with<F: TypeFolder<'ctx> + ?Sized>(self, folder: &mut F) -> Self {
        use TyKind::*;
        match self {
            // Primitive/leaf types - no folding needed
            Bool | Rune | Int(_) | UInt(_) | Float(_) | Infer(_) | Error => self,

            // Types with single Ty parameter
            Array { element, len } => {
                let new_element = element.fold_with(folder);
                let new_len = fold_const(len, folder);

                Array {
                    element: new_element,
                    len: new_len,
                }
            }
            Pointer(t, m) => Pointer(t.fold_with(folder), m),
            Reference(t, m) => Reference(t.fold_with(folder), m),

            Adt(def, args) => {
                let args = fold_generic_args(folder.gcx(), args, folder);
                Adt(def, args)
            }

            // Tuple - fold each element
            Tuple(ts) => {
                let folded = ts.iter().map(|t| t.fold_with(folder)).collect::<Vec<_>>();
                let folded = folder.gcx().store.interners.intern_ty_list(folded);
                Tuple(folded)
            }

            // Function type - fold inputs and output
            FnPointer { inputs, output } => {
                let folded_inputs = inputs
                    .iter()
                    .map(|t| t.fold_with(folder))
                    .collect::<Vec<_>>();
                let folded_inputs = folder.gcx().store.interners.intern_ty_list(folded_inputs);
                let folded_output = output.fold_with(folder);

                FnPointer {
                    inputs: folded_inputs,
                    output: folded_output,
                }
            }

            BoxedExistential { interfaces } => {
                let folded_refs: Vec<_> = interfaces
                    .iter()
                    .map(|iface| InterfaceReference {
                        id: iface.id,
                        arguments: fold_generic_args(folder.gcx(), iface.arguments, folder),
                    })
                    .collect();
                let list = folder
                    .gcx()
                    .store
                    .arenas
                    .global
                    .alloc_slice_copy(&folded_refs);
                BoxedExistential { interfaces: list }
            }

            // Alias type - fold generic args
            Alias { kind, def_id, args } => {
                let args = fold_generic_args(folder.gcx(), args, folder);
                Alias { kind, def_id, args }
            }

            _ => self,
        }
    }
}

fn fold_const<'ctx, F: TypeFolder<'ctx> + ?Sized>(c: Const<'ctx>, folder: &mut F) -> Const<'ctx> {
    folder.fold_const(c)
}

fn fold_generic_args<'ctx, F: TypeFolder<'ctx> + ?Sized>(
    gcx: GlobalContext<'ctx>,
    args: &'ctx [GenericArgument<'ctx>],
    folder: &mut F,
) -> &'ctx [GenericArgument<'ctx>] {
    let folded_args: Vec<_> = args
        .iter()
        .map(|arg| match arg {
            GenericArgument::Type(ty) => GenericArgument::Type(ty.fold_with(folder)),
            GenericArgument::Const(c) => GenericArgument::Const(fold_const(*c, folder)),
        })
        .collect();

    gcx.store.interners.intern_generic_args(folded_args)
}

impl<'ctx> TypeFoldable<'ctx> for StructField<'ctx> {
    fn fold_with<F: TypeFolder<'ctx> + ?Sized>(self, folder: &mut F) -> Self {
        StructField {
            ty: self.ty.fold_with(folder),
            ..self
        }
    }
}

impl<'ctx> TypeFoldable<'ctx> for StructDefinition<'ctx> {
    fn fold_with<F: TypeFolder<'ctx> + ?Sized>(self, folder: &mut F) -> Self {
        let fields: Vec<_> = self
            .fields
            .iter()
            .map(|field| field.fold_with(folder))
            .collect();

        let fields = folder.gcx().store.arenas.global.alloc_slice_copy(&fields);
        StructDefinition {
            adt_def: self.adt_def,
            fields,
        }
    }
}

impl<'ctx> TypeFoldable<'ctx> for EnumVariantField<'ctx> {
    fn fold_with<F: TypeFolder<'ctx> + ?Sized>(self, folder: &mut F) -> Self {
        EnumVariantField {
            ty: self.ty.fold_with(folder),
            ..self
        }
    }
}

impl<'ctx> TypeFoldable<'ctx> for EnumVariantKind<'ctx> {
    fn fold_with<F: TypeFolder<'ctx> + ?Sized>(self, folder: &mut F) -> Self {
        match self {
            EnumVariantKind::Unit => self,
            EnumVariantKind::Tuple(fields) => {
                let folded_fields: Vec<_> =
                    fields.iter().map(|field| field.fold_with(folder)).collect();

                let folded_fields = folder
                    .gcx()
                    .store
                    .arenas
                    .global
                    .alloc_slice_copy(&folded_fields);
                EnumVariantKind::Tuple(folded_fields)
            }
        }
    }
}

impl<'ctx> TypeFoldable<'ctx> for EnumVariant<'ctx> {
    fn fold_with<F: TypeFolder<'ctx> + ?Sized>(self, folder: &mut F) -> Self {
        EnumVariant {
            kind: self.kind.fold_with(folder),
            ..self
        }
    }
}

impl<'ctx> TypeFoldable<'ctx> for EnumDefinition<'ctx> {
    fn fold_with<F: TypeFolder<'ctx> + ?Sized>(self, folder: &mut F) -> Self {
        let variants: Vec<_> = self
            .variants
            .iter()
            .map(|variant| variant.fold_with(folder))
            .collect();

        let variants = folder.gcx().store.arenas.global.alloc_slice_copy(&variants);
        EnumDefinition {
            adt_def: self.adt_def,
            variants,
        }
    }
}
