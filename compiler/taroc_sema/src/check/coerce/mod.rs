use super::context::func::FnCtx;
use crate::ty::Ty;
use std::ops::Deref;

pub struct CoerceRequest<'ctx> {
    expected: Ty<'ctx>,
}
impl<'ctx> CoerceRequest<'ctx> {
    pub fn new(expected: Ty<'ctx>) -> CoerceRequest<'ctx> {
        CoerceRequest { expected }
    }

    pub fn expected_ty(&self) -> Ty<'ctx> {
        self.expected
    }
}

struct CoerceCtx<'fcx, 'gcx> {
    fcx: &'fcx FnCtx<'fcx, 'gcx>,
}

impl<'fcx, 'gcx> Deref for CoerceCtx<'fcx, 'gcx> {
    type Target = FnCtx<'fcx, 'gcx>;
    fn deref(&self) -> &Self::Target {
        self.fcx
    }
}

impl<'fcx, 'gcx> CoerceCtx<'fcx, 'gcx> {
    fn new(fcx: &'fcx FnCtx<'fcx, 'gcx>) -> Self {
        CoerceCtx { fcx }
    }

    fn coerce(&self, expected: Ty<'gcx>, provided: Ty<'gcx>) -> Result<(), ()> {
        // TODO: Coercion Checks
        // TODO: Try Unify when coercion fails
        return Ok(());
    }
}

impl<'rcx, 'gcx> FnCtx<'rcx, 'gcx> {
    pub fn coerce(
        &self,
        _: &taroc_hir::Expression,
        expression_ty: Ty<'gcx>,
        expectation: Ty<'gcx>,
    ) -> Result<(), ()> {
        let ctx = CoerceCtx::new(self);
        let result = ctx.coerce(expectation, expression_ty);
        result
    }
}
