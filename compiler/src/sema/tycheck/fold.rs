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
            let new_len = fold_const(len, folder);

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
            let mut changed = false;
            let mut rebuilt: Option<Vec<InterfaceReference<'ctx>>> = None;

            for (idx, iface) in interfaces.iter().enumerate() {
                let folded_arguments = fold_generic_args(gcx, iface.arguments, folder);
                let (folded_bindings, bindings_changed) =
                    fold_associated_type_bindings(gcx, iface.bindings, folder);
                let iface_changed = iface.arguments != folded_arguments || bindings_changed;

                let Some(buf) = rebuilt.as_mut() else {
                    if !iface_changed {
                        continue;
                    }

                    let mut buf = Vec::with_capacity(interfaces.len());
                    buf.extend_from_slice(&interfaces[..idx]);
                    buf.push(InterfaceReference {
                        id: iface.id,
                        arguments: folded_arguments,
                        bindings: folded_bindings,
                    });
                    rebuilt = Some(buf);
                    changed = true;
                    continue;
                };

                if iface_changed {
                    changed = true;
                    buf.push(InterfaceReference {
                        id: iface.id,
                        arguments: folded_arguments,
                        bindings: folded_bindings,
                    });
                } else {
                    buf.push(*iface);
                }
            }

            if changed {
                let folded_refs = rebuilt.expect("rebuilt list exists when changed");
                let list = gcx.store.arenas.global.alloc_slice_clone(&folded_refs);
                Some(BoxedExistential { interfaces: list })
            } else {
                None
            }
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

fn fold_const<'ctx, F: TypeFolder<'ctx> + ?Sized>(c: Const<'ctx>, folder: &mut F) -> Const<'ctx> {
    folder.fold_const(c)
}

fn fold_generic_args<'ctx, F: TypeFolder<'ctx> + ?Sized>(
    gcx: GlobalContext<'ctx>,
    args: GenericArguments<'ctx>,
    folder: &mut F,
) -> GenericArguments<'ctx> {
    if args.is_empty() {
        return args;
    }

    let mut folded_args: Option<Vec<GenericArgument<'ctx>>> = None;
    for (idx, arg) in args.iter().enumerate() {
        let folded = match arg {
            GenericArgument::Type(ty) => {
                let folded_ty = ty.fold_with(folder);
                GenericArgument::Type(folded_ty)
            }
            GenericArgument::Const(c) => {
                let folded_const = fold_const(*c, folder);
                GenericArgument::Const(folded_const)
            }
        };

        if let Some(buf) = folded_args.as_mut() {
            buf.push(folded);
            continue;
        }

        if folded != *arg {
            let mut buf = Vec::with_capacity(args.len());
            buf.extend_from_slice(&args[..idx]);
            buf.push(folded);
            folded_args = Some(buf);
        }
    }

    match folded_args {
        Some(folded_args) => gcx.store.interners.intern_generic_args(folded_args),
        None => args,
    }
}

fn fold_ty_list<'ctx, F: TypeFolder<'ctx> + ?Sized>(
    gcx: GlobalContext<'ctx>,
    items: TyList<'ctx>,
    folder: &mut F,
) -> TyList<'ctx> {
    if items.is_empty() {
        return items;
    }

    let mut folded: Option<Vec<Ty<'ctx>>> = None;
    for (idx, ty) in items.iter().enumerate() {
        let folded_ty = ty.fold_with(folder);

        if let Some(buf) = folded.as_mut() {
            buf.push(folded_ty);
            continue;
        }

        if folded_ty != *ty {
            let mut buf = Vec::with_capacity(items.len());
            buf.extend_from_slice(&items[..idx]);
            buf.push(folded_ty);
            folded = Some(buf);
        }
    }

    match folded {
        Some(folded) => gcx.store.interners.intern_ty_list(folded),
        None => items,
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
    let mut rebuilt: Option<Vec<AssociatedTypeBinding<'ctx>>> = None;
    for (idx, binding) in bindings.iter().enumerate() {
        let folded_ty = binding.ty.fold_with(folder);
        let binding_changed = folded_ty != binding.ty;

        let Some(buf) = rebuilt.as_mut() else {
            if !binding_changed {
                continue;
            }

            let mut buf = Vec::with_capacity(bindings.len());
            buf.extend_from_slice(&bindings[..idx]);
            buf.push(AssociatedTypeBinding {
                name: binding.name,
                ty: folded_ty,
            });
            rebuilt = Some(buf);
            changed = true;
            continue;
        };

        if binding_changed {
            changed = true;
            buf.push(AssociatedTypeBinding {
                name: binding.name,
                ty: folded_ty,
            });
        } else {
            buf.push(*binding);
        }
    }

    if changed {
        let folded_bindings = rebuilt.expect("rebuilt list exists when changed");
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
