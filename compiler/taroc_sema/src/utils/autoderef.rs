use crate::{infer::InferCtx, ty::Ty};
use taroc_span::Span;

pub struct Autoderef<'icx, 'gcx> {
    icx: &'icx InferCtx<'gcx>,
    span: Span,
    ty: Ty<'gcx>,
    at_start: bool,
}

impl<'icx, 'gcx> Iterator for Autoderef<'icx, 'gcx> {
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

impl<'icx, 'gcx> Autoderef<'icx, 'gcx> {
    pub fn new(icx: &'icx InferCtx<'gcx>, base_ty: Ty<'gcx>, span: Span) -> Self {
        Autoderef {
            icx,
            span,
            ty: icx.resolve_vars_if_possible(base_ty),
            at_start: true,
        }
    }

    pub fn final_ty(&self) -> Ty<'gcx> {
        self.ty
    }
}
