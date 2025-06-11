use crate::{
    check::FnCtx,
    infer::{InferenceOutput, InferenceResult, relate::TypeRelating},
    ty::Ty,
};
use std::ops::Deref;

type CoercionResult<'gcx> = InferenceResult<'gcx, (Vec<()>, Ty<'gcx>)>; // TODO: Adjustment
fn success<'tcx>(adj: Vec<()>, target: Ty<'tcx>) -> CoercionResult<'tcx> {
    Ok(InferenceOutput {
        value: (adj, target),
        _data: &(),
    })
}

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

    fn coerce(&self, expected: Ty<'gcx>, provided: Ty<'gcx>) -> CoercionResult<'gcx> {
        let expected = self.shallow_resolve(expected);
        let provided = self.shallow_resolve(provided);

        if provided.is_ty_var() {
            return self.coerce_from_inference_variable(provided, expected);
        }
        // TODO: Coercion Checks
        {}

        // unify if can't coerce
        return self.unify(provided, expected);
    }

    fn coerce_from_inference_variable(
        &self,
        provided: Ty<'gcx>,
        expected: Ty<'gcx>,
    ) -> CoercionResult<'gcx> {
        println!("{}", provided.format(self.gcx));
        assert!(provided.is_ty_var() && self.shallow_resolve(provided) == provided);
        assert!(self.shallow_resolve(expected) == expected);

        if expected.is_ty_var() {
            // two unresolved ty vars, create a future coercion constraint to solve
            // TODO: Generate Obligation
            println!("TODO: Store Future Coercion Obligation");
            return success(vec![], expected);
        } else {
            return self.unify(provided, expected); // apply subtyping
        }
    }
}

impl<'fcx, 'gcx> CoerceCtx<'fcx, 'gcx> {
    fn unify(&self, a: Ty<'gcx>, b: Ty<'gcx>) -> CoercionResult<'gcx> {
        self.unify_raw(a, b)
    }

    fn unify_raw(&self, a: Ty<'gcx>, b: Ty<'gcx>) -> CoercionResult<'gcx> {
        let inference_result = self.supertype(a, b).map(|_| InferenceOutput {
            value: (vec![], b),
            _data: &(),
        });

        return inference_result;
    }

    fn supertype(&self, subtype: Ty<'gcx>, supertype: Ty<'gcx>) -> InferenceResult<'gcx, ()> {
        let mut actor = TypeRelating::new(&self.icx);
        actor.relate(supertype, subtype)?;

        return Ok(InferenceOutput {
            value: (),
            _data: &(),
        });
    }
}

impl<'rcx, 'gcx> FnCtx<'rcx, 'gcx> {
    pub fn coerce(
        &self,
        expr: &taroc_hir::Expression,
        expression_ty: Ty<'gcx>,
        expectation: Ty<'gcx>,
    ) -> CoercionResult<'gcx> {
        let span = expr.span;
        self.gcx.diagnostics.warn(
            format!(
                "Coercing {} to {}",
                expression_ty.format(self.gcx),
                expectation.format(self.gcx)
            ),
            span,
        );
        let ctx = CoerceCtx::new(self);
        let result = ctx.coerce(expectation, expression_ty);
        result
    }
}
