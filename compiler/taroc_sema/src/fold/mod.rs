use crate::{
    GlobalContext,
    ty::{GenericArgument, Ty, TyKind},
};

/// The transformer – you implement this once per pass.
pub trait TypeFolder<'ctx> {
    fn gcx(&self) -> GlobalContext<'ctx>;
    /// Called on every `Ty` that is *not* a leaf. You usually match on `ty.kind()`
    /// and reconstruct it with `self.fold_ty(...)` where needed.
    fn fold_ty(&mut self, ty: Ty<'ctx>) -> Ty<'ctx>;

    /// Default rewrite for a generic argument.
    fn fold_generic_arg(&mut self, arg: GenericArgument<'ctx>) -> GenericArgument<'ctx> {
        match arg {
            GenericArgument::Type(t) => GenericArgument::Type(self.fold_ty(t)),
            other @ GenericArgument::Const(_) => other,
        }
    }
}

/// Blanket traversal: every container that can hold a `Ty` implements this.
pub trait TypeFoldable<'ctx>: Sized {
    fn fold_with<F: TypeFolder<'ctx>>(self, folder: &mut F) -> Self;
}

impl<'ctx> TypeFoldable<'ctx> for Ty<'ctx> {
    fn fold_with<F: TypeFolder<'ctx>>(self, folder: &mut F) -> Self {
        if !self.needs_instantiation() {
            return self;
        }
        folder.fold_ty(self)
    }
}

impl<'ctx> TypeFoldable<'ctx> for TyKind<'ctx> {
    fn fold_with<F: TypeFolder<'ctx>>(self, folder: &mut F) -> Self {
        self.super_fold_with(folder)
    }
}
/// Provides default structural folding behavior
pub trait TypeSuperFoldable<'ctx>: TypeFoldable<'ctx> {
    /// Default structural folding - recurses into substructures
    fn super_fold_with<F: TypeFolder<'ctx>>(self, folder: &mut F) -> Self;
}

impl<'ctx> TypeSuperFoldable<'ctx> for Ty<'ctx> {
    fn super_fold_with<F: TypeFolder<'ctx>>(self, folder: &mut F) -> Self {
        let folded_kind = self.kind().super_fold_with(folder);
        folder.gcx().mk_ty(folded_kind)
    }
}

impl<'ctx> TypeSuperFoldable<'ctx> for TyKind<'ctx> {
    fn super_fold_with<F: TypeFolder<'ctx>>(self, folder: &mut F) -> Self {
        use TyKind::*;
        match self {
            // Primitive/leaf types - no folding needed
            Bool | Rune | String | Int(_) | UInt(_) | Float(_) | Parameter(_) | Infer(_)
            | Error => self,

            // Types with single Ty parameter
            Pointer(t, m) => Pointer(t.fold_with(folder), m),
            Reference(t, m) => Reference(t.fold_with(folder), m),
            Array(t, n) => Array(t.fold_with(folder), n),

            // Tuple - fold each element
            Tuple(ts) => {
                let folded = ts.iter().map(|t| t.fold_with(folder)).collect::<Vec<_>>();
                let folded = folder.gcx().store.interners.intern_ty_list(&folded);
                Tuple(folded)
            }

            // ADT with generic arguments
            Adt(def, args) => {
                let folded = args
                    .iter()
                    .map(|a| folder.fold_generic_arg(*a))
                    .collect::<Vec<_>>();
                let folded = folder.gcx().store.interners.intern_generic_args(&folded);
                Adt(def, folded)
            }

            // Function definition with generic arguments
            FnDef(def_id, args) => {
                let folded = args
                    .iter()
                    .map(|a| folder.fold_generic_arg(*a))
                    .collect::<Vec<_>>();
                let folded = folder.gcx().store.interners.intern_generic_args(&folded);
                FnDef(def_id, folded)
            }

            // Function type - fold inputs and output
            Function { inputs, output } => {
                let folded_inputs = inputs
                    .iter()
                    .map(|t| t.fold_with(folder))
                    .collect::<Vec<_>>();
                let folded_inputs = folder.gcx().store.interners.intern_ty_list(&folded_inputs);
                let folded_output = output.fold_with(folder);

                Function {
                    inputs: folded_inputs,
                    output: folded_output,
                }
            }

            _ => self,
        }
    }
}
