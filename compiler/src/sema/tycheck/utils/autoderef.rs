use crate::sema::{models::Ty, tycheck::infer::InferCtx};

pub struct Autoderef<'gcx> {
    ty: Ty<'gcx>,
    at_start: bool,
}

impl<'gcx> Iterator for Autoderef<'gcx> {
    type Item = Ty<'gcx>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.at_start {
            self.at_start = false;
            return Some(self.ty);
        }
        if self.ty.is_ty_var() {
            return None;
        }

        self.ty = self.ty.dereference()?;

        Some(self.ty)
    }
}

impl<'gcx> Autoderef<'gcx> {
    pub fn new(icx: &InferCtx<'gcx>, base_ty: Ty<'gcx>) -> Self {
        Autoderef {
            ty: icx.resolve_vars_if_possible(base_ty),
            at_start: true,
        }
    }

    pub fn final_ty(&self) -> Ty<'gcx> {
        self.ty
    }
}
