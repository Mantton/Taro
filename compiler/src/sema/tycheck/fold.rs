use crate::{
    compile::context::GlobalContext,
    sema::models::{
        AssociatedTypeBinding, Const, EnumDefinition, EnumVariant, EnumVariantField,
        EnumVariantKind, GenericArgument, GenericArguments, InterfaceReference, StructDefinition,
        StructField, Ty, TyKind, TyList,
    },
};

/// The transformer – you implement this once per pass.
pub trait TypeFolder<'ctx> {
    fn gcx(&self) -> GlobalContext<'ctx>;
    /// Called on every `Ty`. You usually match on `ty.kind()`
    /// and reconstruct it with `self.fold_ty(...)` where needed.
    fn fold_ty(&mut self, ty: Ty<'ctx>) -> Ty<'ctx>;
    /// Called on const values encountered inside types.
    fn fold_const(&mut self, c: Const<'ctx>) -> Const<'ctx> {
        Const {
            ty: c.ty.fold_with(self),
            kind: c.kind,
        }
    }
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
        if let Some(folded_kind) = fold_ty_kind(folder.gcx(), self.kind(), folder) {
            Ty::new(folded_kind, folder.gcx())
        } else {
            self
        }
    }
}

impl<'ctx> TypeSuperFoldable<'ctx> for TyKind<'ctx> {
    fn super_fold_with<F: TypeFolder<'ctx> + ?Sized>(self, folder: &mut F) -> Self {
        fold_ty_kind(folder.gcx(), self, folder).unwrap_or(self)
    }
}

fn fold_ty_kind<'ctx, F: TypeFolder<'ctx> + ?Sized>(
    gcx: GlobalContext<'ctx>,
    kind: TyKind<'ctx>,
    folder: &mut F,
) -> Option<TyKind<'ctx>> {
    use TyKind::*;
    match kind {
        // Primitive/leaf types - no folding needed
        Bool | Rune | Int(_) | UInt(_) | Float(_) | Infer(_) | Error => None,

        // Types with single Ty parameter
        Array { element, len } => {
            let new_element = element.fold_with(folder);
            let new_len = len.fold_with(folder);

            if new_element == element && new_len == len {
                None
            } else {
                Some(Array {
                    element: new_element,
                    len: new_len,
                })
            }
        }
        Pointer(t, m) => {
            let new_t = t.fold_with(folder);
            if new_t == t {
                None
            } else {
                Some(Pointer(new_t, m))
            }
        }
        Reference(t, m) => {
            let new_t = t.fold_with(folder);
            if new_t == t {
                None
            } else {
                Some(Reference(new_t, m))
            }
        }

        Adt(def, args) => {
            let folded_args = fold_generic_args(gcx, args, folder);
            if args == folded_args {
                None
            } else {
                Some(Adt(def, folded_args))
            }
        }

        // Tuple - fold each element
        Tuple(ts) => {
            let folded = fold_ty_list(gcx, ts, folder);
            if ts == folded {
                None
            } else {
                Some(Tuple(folded))
            }
        }

        // Function type - fold inputs and output
        FnPointer { inputs, output } => {
            let folded_inputs = fold_ty_list(gcx, inputs, folder);
            let folded_output = output.fold_with(folder);

            if inputs == folded_inputs && folded_output == output {
                None
            } else {
                Some(FnPointer {
                    inputs: folded_inputs,
                    output: folded_output,
                })
            }
        }

        BoxedExistential { interfaces } => {
            let folded = map_changed(interfaces, |iface| InterfaceReference {
                id: iface.id,
                arguments: fold_generic_args(gcx, iface.arguments, folder),
                bindings: fold_associated_type_bindings(gcx, iface.bindings, folder),
            })?;
            Some(BoxedExistential {
                interfaces: gcx.store.arenas.global.alloc_slice_clone(&folded),
            })
        }

        // Alias type - fold generic args
        Alias { kind, def_id, args } => {
            let folded_args = fold_generic_args(gcx, args, folder);
            if args == folded_args {
                None
            } else {
                Some(Alias {
                    kind,
                    def_id,
                    args: folded_args,
                })
            }
        }

        Closure {
            closure_def_id,
            kind,
            captured_generics,
            inputs,
            output,
        } => {
            // Determine implicit closure types must be deeply resolved to eliminate inference variables.
            let folded_generics = fold_generic_args(gcx, captured_generics, folder);
            let folded_inputs = fold_ty_list(gcx, inputs, folder);
            let folded_output = output.fold_with(folder);

            if captured_generics == folded_generics
                && inputs == folded_inputs
                && folded_output == output
            {
                None
            } else {
                Some(Closure {
                    closure_def_id,
                    kind,
                    captured_generics: folded_generics,
                    inputs: folded_inputs,
                    output: folded_output,
                })
            }
        }

        _ => None,
    }
}

/// Reuse unchanged slices; allocate only after the first changed element.
fn map_changed<T: Copy + PartialEq>(items: &[T], mut fold: impl FnMut(T) -> T) -> Option<Vec<T>> {
    let mut rebuilt: Option<Vec<T>> = None;
    for (index, &item) in items.iter().enumerate() {
        let folded = fold(item);
        if let Some(buf) = rebuilt.as_mut() {
            buf.push(folded);
        } else if folded != item {
            let mut buf = Vec::with_capacity(items.len());
            buf.extend_from_slice(&items[..index]);
            buf.push(folded);
            rebuilt = Some(buf);
        }
    }
    rebuilt
}

fn fold_generic_args<'ctx, F: TypeFolder<'ctx> + ?Sized>(
    gcx: GlobalContext<'ctx>,
    args: GenericArguments<'ctx>,
    folder: &mut F,
) -> GenericArguments<'ctx> {
    match map_changed(&args, |arg| match arg {
        GenericArgument::Type(ty) => GenericArgument::Type(ty.fold_with(folder)),
        GenericArgument::Const(c) => GenericArgument::Const(c.fold_with(folder)),
    }) {
        Some(folded) => gcx.store.interners.intern_generic_args(folded),
        None => args,
    }
}

fn fold_ty_list<'ctx, F: TypeFolder<'ctx> + ?Sized>(
    gcx: GlobalContext<'ctx>,
    items: TyList<'ctx>,
    folder: &mut F,
) -> TyList<'ctx> {
    match map_changed(&items, |ty| ty.fold_with(folder)) {
        Some(folded) => gcx.store.interners.intern_ty_list(folded),
        None => items,
    }
}

fn fold_associated_type_bindings<'ctx, F: TypeFolder<'ctx> + ?Sized>(
    gcx: GlobalContext<'ctx>,
    bindings: &'ctx [AssociatedTypeBinding<'ctx>],
    folder: &mut F,
) -> &'ctx [AssociatedTypeBinding<'ctx>] {
    match map_changed(bindings, |binding| AssociatedTypeBinding {
        name: binding.name,
        ty: binding.ty.fold_with(folder),
    }) {
        Some(folded) => gcx.store.arenas.global.alloc_slice_clone(&folded),
        None => bindings,
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
            repr: self.repr,
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
