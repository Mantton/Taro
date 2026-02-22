use crate::{
    compile::context::GlobalContext,
    sema::models::{
        AssociatedTypeBinding, Const, EnumDefinition, EnumVariant, EnumVariantField,
        EnumVariantKind, GenericArgument, InterfaceReference, StructDefinition, StructField, Ty,
        TyKind,
    },
};
use std::ptr;

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
        if self.kind_ref() == &folded_kind {
            self
        } else {
            Ty::new(folded_kind, folder.gcx())
        }
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

                if new_element == element && new_len == len {
                    Array { element, len }
                } else {
                    Array {
                        element: new_element,
                        len: new_len,
                    }
                }
            }
            Pointer(t, m) => {
                let new_t = t.fold_with(folder);
                if new_t == t {
                    Pointer(t, m)
                } else {
                    Pointer(new_t, m)
                }
            }
            Reference(t, m) => {
                let new_t = t.fold_with(folder);
                if new_t == t {
                    Reference(t, m)
                } else {
                    Reference(new_t, m)
                }
            }

            Adt(def, args) => {
                let folded_args = fold_generic_args(folder.gcx(), args, folder);
                if ptr::eq(args, folded_args) {
                    Adt(def, args)
                } else {
                    Adt(def, folded_args)
                }
            }

            // Tuple - fold each element
            Tuple(ts) => {
                let folded = fold_ty_list(folder.gcx(), ts, folder);
                if ptr::eq(ts, folded) {
                    Tuple(ts)
                } else {
                    Tuple(folded)
                }
            }

            // Function type - fold inputs and output
            FnPointer { inputs, output } => {
                let folded_inputs = fold_ty_list(folder.gcx(), inputs, folder);
                let folded_output = output.fold_with(folder);

                if ptr::eq(inputs, folded_inputs) && folded_output == output {
                    FnPointer { inputs, output }
                } else {
                    FnPointer {
                        inputs: folded_inputs,
                        output: folded_output,
                    }
                }
            }

            BoxedExistential { interfaces } => {
                let gcx = folder.gcx();
                let mut changed = false;
                let mut folded_refs = Vec::with_capacity(interfaces.len());

                for iface in interfaces.iter() {
                    let folded_arguments = fold_generic_args(gcx, iface.arguments, folder);
                    let (folded_bindings, bindings_changed) =
                        fold_associated_type_bindings(gcx, iface.bindings, folder);
                    let iface_changed =
                        !ptr::eq(iface.arguments, folded_arguments) || bindings_changed;
                    changed |= iface_changed;

                    if iface_changed {
                        folded_refs.push(InterfaceReference {
                            id: iface.id,
                            arguments: folded_arguments,
                            bindings: folded_bindings,
                        });
                    } else {
                        folded_refs.push(*iface);
                    }
                }

                if changed {
                    let list = gcx.store.arenas.global.alloc_slice_clone(&folded_refs);
                    BoxedExistential { interfaces: list }
                } else {
                    BoxedExistential { interfaces }
                }
            }

            // Alias type - fold generic args
            Alias { kind, def_id, args } => {
                let folded_args = fold_generic_args(folder.gcx(), args, folder);
                if ptr::eq(args, folded_args) {
                    Alias { kind, def_id, args }
                } else {
                    Alias {
                        kind,
                        def_id,
                        args: folded_args,
                    }
                }
            }

            Closure {
                closure_def_id,
                captured_generics,
                inputs,
                output,
                kind,
            } => {
                // Determine implicit closure types must be deeply resolved to eliminate inference variables.
                let folded_generics = fold_generic_args(folder.gcx(), captured_generics, folder);
                let folded_inputs = fold_ty_list(folder.gcx(), inputs, folder);
                let folded_output = output.fold_with(folder);

                if ptr::eq(captured_generics, folded_generics)
                    && ptr::eq(inputs, folded_inputs)
                    && folded_output == output
                {
                    Closure {
                        closure_def_id,
                        captured_generics,
                        inputs,
                        output,
                        kind,
                    }
                } else {
                    Closure {
                        closure_def_id,
                        captured_generics: folded_generics,
                        inputs: folded_inputs,
                        output: folded_output,
                        kind,
                    }
                }
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
    if args.is_empty() {
        return args;
    }

    let mut changed = false;
    let mut folded_args = Vec::with_capacity(args.len());
    for arg in args.iter() {
        let folded = match arg {
            GenericArgument::Type(ty) => {
                let folded_ty = ty.fold_with(folder);
                if folded_ty != *ty {
                    changed = true;
                }
                GenericArgument::Type(folded_ty)
            }
            GenericArgument::Const(c) => {
                let folded_const = fold_const(*c, folder);
                if folded_const != *c {
                    changed = true;
                }
                GenericArgument::Const(folded_const)
            }
        };
        folded_args.push(folded);
    }

    if changed {
        gcx.store.interners.intern_generic_args(folded_args)
    } else {
        args
    }
}

fn fold_ty_list<'ctx, F: TypeFolder<'ctx> + ?Sized>(
    gcx: GlobalContext<'ctx>,
    items: &'ctx [Ty<'ctx>],
    folder: &mut F,
) -> &'ctx [Ty<'ctx>] {
    if items.is_empty() {
        return items;
    }

    let mut changed = false;
    let mut folded = Vec::with_capacity(items.len());
    for ty in items.iter() {
        let folded_ty = ty.fold_with(folder);
        if folded_ty != *ty {
            changed = true;
        }
        folded.push(folded_ty);
    }

    if changed {
        gcx.store.interners.intern_ty_list(folded)
    } else {
        items
    }
}

fn fold_associated_type_bindings<'ctx, F: TypeFolder<'ctx> + ?Sized>(
    gcx: GlobalContext<'ctx>,
    bindings: &'ctx [AssociatedTypeBinding<'ctx>],
    folder: &mut F,
) -> (&'ctx [AssociatedTypeBinding<'ctx>], bool) {
    if bindings.is_empty() {
        return (bindings, false);
    }

    let mut changed = false;
    let mut folded_bindings = Vec::with_capacity(bindings.len());
    for binding in bindings.iter() {
        let folded_ty = binding.ty.fold_with(folder);
        if folded_ty != binding.ty {
            changed = true;
        }
        folded_bindings.push(AssociatedTypeBinding {
            name: binding.name,
            ty: folded_ty,
        });
    }

    if changed {
        let folded_bindings = gcx.store.arenas.global.alloc_slice_clone(&folded_bindings);
        (folded_bindings, true)
    } else {
        (bindings, false)
    }
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
            .map(|field| (*field).fold_with(folder))
            .collect();

        let fields = folder.gcx().store.arenas.global.alloc_slice_clone(&fields);
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
                let folded_fields: Vec<_> = fields
                    .iter()
                    .map(|field| (*field).fold_with(folder))
                    .collect();

                let folded_fields = folder
                    .gcx()
                    .store
                    .arenas
                    .global
                    .alloc_slice_clone(&folded_fields);
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
            .map(|variant| (*variant).fold_with(folder))
            .collect();

        let variants = folder
            .gcx()
            .store
            .arenas
            .global
            .alloc_slice_clone(&variants);
        EnumDefinition {
            adt_def: self.adt_def,
            variants,
        }
    }
}
