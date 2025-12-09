use crate::{
    compile::context::GlobalContext,
    sema::models::{Ty, TyKind},
};

/// The transformer – you implement this once per pass.
pub trait TypeFolder<'ctx> {
    fn gcx(&self) -> GlobalContext<'ctx>;
    /// Called on every `Ty` that is *not* a leaf. You usually match on `ty.kind()`
    /// and reconstruct it with `self.fold_ty(...)` where needed.
    fn fold_ty(&mut self, ty: Ty<'ctx>) -> Ty<'ctx>;

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
    fn fold_with<F: TypeFolder<'ctx>>(self, folder: &mut F) -> Self;
}

impl<'ctx> TypeFoldable<'ctx> for Ty<'ctx> {
    fn fold_with<F: TypeFolder<'ctx>>(self, folder: &mut F) -> Self {
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
        Ty::new(folded_kind, folder.gcx())
    }
}

impl<'ctx> TypeSuperFoldable<'ctx> for TyKind<'ctx> {
    fn super_fold_with<F: TypeFolder<'ctx>>(self, folder: &mut F) -> Self {
        use TyKind::*;
        match self {
            // Primitive/leaf types - no folding needed
            Bool | Rune | Int(_) | UInt(_) | Float(_) | Infer(_) | Error => self,

            // Types with single Ty parameter
            Pointer(t, m) => Pointer(t.fold_with(folder), m),
            Reference(t, m) => Reference(t.fold_with(folder), m),

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

            _ => self,
        }
    }
}

// impl<'ctx> TypeFoldable<'ctx> for GenericArgument<'ctx> {
//     fn fold_with<F: TypeFolder<'ctx>>(self, folder: &mut F) -> Self {
//         // Delegate to the folder’s helper (keeps the logic in one place)
//         folder.fold_generic_arg(self)
//     }
// }

// impl<'ctx> TypeFoldable<'ctx> for InterfaceReference<'ctx> {
//     fn fold_with<F: TypeFolder<'ctx>>(self, folder: &mut F) -> Self {
//         // Fold every generic argument, then re-intern the list.
//         let folded_args: Vec<_> = self
//             .arguments
//             .iter()
//             .map(|arg| folder.fold_generic_arg(*arg))
//             .collect();

//         let interned = folder
//             .gcx()
//             .store
//             .interners
//             .intern_generic_args(&folded_args);

//         InterfaceReference {
//             id: self.id,
//             arguments: interned,
//         }
//     }
// }

// impl<'ctx> TypeFoldable<'ctx> for Constraint<'ctx> {
//     fn fold_with<F: TypeFolder<'ctx>>(self, folder: &mut F) -> Self {
//         match self {
//             Constraint::Bound { ty, interface } => Constraint::Bound {
//                 ty: ty.fold_with(folder),
//                 interface: interface.fold_with(folder),
//             },
//             Constraint::TypeEquality(lhs, rhs) => {
//                 Constraint::TypeEquality(lhs.fold_with(folder), rhs.fold_with(folder))
//             }
//         }
//     }
// }
