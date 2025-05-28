use std::ops::Deref;

use crate::ty::Ty;

use super::context::func::FnCtx;

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

    fn coerce(&self, lhs: Ty<'gcx>, rhs: Ty<'gcx>) -> Result<(), ()> {
        // TODO: Resolve Type Vars where possible

        if lhs.is_ty_var() {
            self.coerce_from_inference_variable(lhs, rhs)?;
        }

        return self.unify(lhs, rhs);
    }

    fn coerce_from_inference_variable(&self, lhs: Ty<'gcx>, rhs: Ty<'gcx>) -> Result<(), ()> {
        assert!(lhs.is_ty_var());

        if rhs.is_ty_var() {
            // lhs & rhs are type variables
            todo!()
        } else {
            self.unify(lhs, rhs)
        }
    }
}

impl<'fcx, 'gcx> CoerceCtx<'fcx, 'gcx> {
    fn unify(&self, lhs: Ty<'gcx>, rhs: Ty<'gcx>) -> Result<(), ()> {
        println!("Unify {lhs:?} {rhs:?}");
        self.unify_raw(lhs, rhs)
    }

    fn unify_raw(&self, lhs: Ty<'gcx>, rhs: Ty<'gcx>) -> Result<(), ()> {
        todo!()
    }
}

impl<'rcx, 'gcx> FnCtx<'rcx, 'gcx> {
    pub fn coerce(
        &self,
        expression: &taroc_hir::Expression,
        expression_ty: Ty<'gcx>,
        expectation: Ty<'gcx>,
    ) -> Result<(), ()> {
        let ctx = CoerceCtx::new(self);

        let result = ctx.coerce(expression_ty, expectation);
        Ok(())
    }
}
