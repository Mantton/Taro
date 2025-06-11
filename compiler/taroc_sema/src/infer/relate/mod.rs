use crate::{
    error::TypeError,
    infer::InferCtx,
    ty::{InferTy, Ty, TyKind},
};

pub mod type_relating;

pub struct TypeRelating<'icx, 'gcx> {
    icx: &'icx InferCtx<'gcx>,
}

impl<'icx, 'gcx> TypeRelating<'icx, 'gcx> {
    pub fn new(icx: &'icx InferCtx<'gcx>) -> TypeRelating<'icx, 'gcx> {
        TypeRelating { icx }
    }

    pub fn relate(&mut self, a: Ty<'gcx>, b: Ty<'gcx>) -> Result<Ty<'gcx>, TypeError> {
        if a == b {
            return Ok(a);
        }

        let icx = self.icx;
        let a = icx.shallow_resolve(a);
        let b = icx.shallow_resolve(b);

        match (a.kind(), b.kind()) {
            (TyKind::Infer(InferTy::Ty(a_id)), TyKind::Infer(InferTy::Ty(b_id))) => {}
            (TyKind::Infer(InferTy::Ty(a_id)), _) => {}
            (_, TyKind::Infer(InferTy::Ty(b_id))) => {}
            _ => todo!(),
        }

        todo!()
    }
}
