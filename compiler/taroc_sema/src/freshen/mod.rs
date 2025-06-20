use crate::{
    GlobalContext,
    fold::{TypeFoldable, TypeFolder, TypeSuperFoldable},
    ty::{GenericParameter, InferTy, Ty, TyKind},
};
use std::collections::HashMap;

/// TypeFreshener that implements TypeFolder to automatically handle all type structures
pub struct TypeFreshener<'ctx> {
    next_var_id: u32,
    generic_substitutions: HashMap<GenericParameter, u32>, // or String if you use names
    gcx: GlobalContext<'ctx>,
}

impl<'ctx> TypeFreshener<'ctx> {
    pub fn new(gcx: GlobalContext<'ctx>) -> Self {
        TypeFreshener {
            next_var_id: 0,
            generic_substitutions: HashMap::new(),
            gcx,
        }
    }

    /// Generate a fresh type variable
    fn fresh_type_var(&mut self) -> u32 {
        let var = self.next_var_id;
        self.next_var_id += 1;
        var
    }

    /// Freshen any type - function signatures, tuples, etc. all handled automatically
    pub fn freshen(&mut self, ty: Ty<'ctx>) -> Ty<'ctx> {
        ty.fold_with(self)
    }
}

impl<'ctx> TypeFolder<'ctx> for TypeFreshener<'ctx> {
    fn gcx(&self) -> GlobalContext<'ctx> {
        self.gcx
    }

    fn fold_ty(&mut self, ty: Ty<'ctx>) -> Ty<'ctx> {
        match ty.kind() {
            TyKind::Parameter(param) => {
                // Check if we already have a mapping
                if let Some(&existing_var) = self.generic_substitutions.get(&param) {
                    return self
                        .gcx()
                        .mk_ty(TyKind::Infer(InferTy::FreshTy(existing_var)));
                }

                // Create fresh var and insert
                let fresh_var = self.fresh_type_var();
                self.generic_substitutions.insert(param, fresh_var);
                self.gcx().mk_ty(TyKind::Infer(InferTy::FreshTy(fresh_var)))
            }

            // Let the folder automatically handle structural types
            _ => ty.super_fold_with(self),
        }
    }
}
