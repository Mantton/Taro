use crate::sema::{
    error::{ExpectedFound, TypeError},
    models::{GenericArgument, GenericArguments, InferTy, Ty, TyKind},
    tycheck::infer::{InferCtx, keys::FloatVarValue, keys::IntVarValue},
};
use std::rc::Rc;

type UnificationResult<'ctx> = Result<(), TypeError<'ctx>>;

pub struct TypeUnifier<'ctx> {
    icx: Rc<InferCtx<'ctx>>,
}

impl<'ctx> TypeUnifier<'ctx> {
    pub fn new(icx: Rc<InferCtx<'ctx>>) -> TypeUnifier<'ctx> {
        TypeUnifier { icx }
    }

    pub fn unify(&self, a: Ty<'ctx>, b: Ty<'ctx>) -> UnificationResult<'ctx> {
        let a = self.structurally_resolve(a);
        let b = self.structurally_resolve(b);

        use InferTy::*;
        match (a.kind(), b.kind()) {
            // TyVars
            (TyKind::Infer(TyVar(a_id)), TyKind::Infer(TyVar(b_id))) => {
                self.icx
                    .inner
                    .borrow_mut()
                    .type_variables()
                    .equate(a_id, b_id);
            }
            (TyKind::Infer(TyVar(id)), _) => {
                self.icx
                    .inner
                    .borrow_mut()
                    .type_variables()
                    .instantiate(id, b);
            }
            (_, TyKind::Infer(TyVar(id))) => {
                self.icx
                    .inner
                    .borrow_mut()
                    .type_variables()
                    .instantiate(id, a);
            }

            _ => return self.unify_inference_vars(a, b),
        }
        Ok(())
    }

    /// Resolve inference variables only (no normalization).
    /// The caller (ConstraintSolver) is responsible for normalization.
    pub fn structurally_resolve(&self, ty: Ty<'ctx>) -> Ty<'ctx> {
        self.icx.resolve_vars_if_possible(ty)
    }

    fn unify_inference_vars(&self, a: Ty<'ctx>, b: Ty<'ctx>) -> UnificationResult<'ctx> {
        use InferTy::*;
        use TyKind::*;
        match (a.kind(), b.kind()) {
            // Error - silently succeed if either side is an error type
            // This prevents cascading errors when one node has already failed
            (Error, _) | (_, Error) => return Ok(()),

            // Integers
            (Infer(IntVar(a_id)), Infer(IntVar(b_id))) => {
                self.icx.equate_int_vars_raw(a_id, b_id);
            }
            (Infer(IntVar(id)), Int(k)) | (Int(k), Infer(IntVar(id))) => {
                self.icx.instantiate_int_var_raw(id, IntVarValue::Signed(k));
            }
            (Infer(IntVar(id)), UInt(k)) | (UInt(k), Infer(IntVar(id))) => {
                self.icx
                    .instantiate_int_var_raw(id, IntVarValue::Unsigned(k));
            }

            // Floats
            (Infer(FloatVar(a_id)), Infer(FloatVar(b_id))) => {
                self.icx.equate_float_vars_raw(a_id, b_id);
            }
            (Infer(FloatVar(id)), Float(k)) | (Float(k), Infer(FloatVar(id))) => {
                self.icx
                    .instantiate_float_var_raw(id, FloatVarValue::Known(k));
            }

            // NilVars - can only equate with other NilVars
            // Resolution to Optional/Pointer must go through coercion
            (Infer(NilVar(a_id)), Infer(NilVar(b_id))) => {
                self.icx.equate_nil_vars_raw(a_id, b_id);
            }

            (Infer(_), _) | (_, Infer(_)) => {
                return Err(TypeError::TyMismatch(ExpectedFound::new(a, b)));
            }
            _ => return self.unify_nominal_types(a, b),
        }

        Ok(())
    }

    fn unify_nominal_types(&self, a: Ty<'ctx>, b: Ty<'ctx>) -> UnificationResult<'ctx> {
        use TyKind::*;
        match (a.kind(), b.kind()) {
            (Infer(_), _) | (_, Infer(_)) => {
                unreachable!("ICE: inference variables encountered in `unify_nominal_tys`")
            }
            // Error - silently succeed if either side is an error type
            (Error, _) | (_, Error) => return Ok(()),
            (Rune | Bool | Int(_) | UInt(_) | Float(_) | String | GcPtr, _) if a == b => {
                return Ok(());
            }
            (Parameter(a_p), Parameter(b_p)) if a_p.index == b_p.index => return Ok(()),
            (Adt(a_def, a_args), Adt(b_def, b_args)) if a_def.id == b_def.id => {
                self.unify_generic_args(a_args, b_args)?;
                return Ok(());
            }
            (
                Array {
                    element: a_elem,
                    len: a_len,
                },
                Array {
                    element: b_elem,
                    len: b_len,
                },
            ) => {
                self.unify(a_elem, b_elem)?;
                if a_len != b_len {
                    return Err(TypeError::TyMismatch(ExpectedFound::new(a, b)));
                }
                return Ok(());
            }
            (Pointer(a_ty, a_mut), Pointer(b_ty, b_mut)) => {
                if a_mut != b_mut {
                    return Err(TypeError::Mutability(ExpectedFound::new(a_ty, b_ty)));
                }
                return self.unify(a_ty, b_ty);
            }
            (Reference(a_ty, a_mut), Reference(b_ty, b_mut)) => {
                if a_mut != b_mut {
                    return Err(TypeError::Mutability(ExpectedFound::new(a_ty, b_ty)));
                }
                return self.unify(a_ty, b_ty);
            }
            (Tuple(a_items), Tuple(b_items)) => {
                if a_items.len() == b_items.len() {
                    for (a_item, b_item) in a_items.iter().zip(b_items.iter()) {
                        self.unify(*a_item, *b_item)?;
                    }
                } else if !(a_items.is_empty() || b_items.is_empty()) {
                    return Err(TypeError::TupleArity(ExpectedFound::new(
                        a_items.len(),
                        b_items.len(),
                    )));
                } else {
                    return Err(TypeError::TyMismatch(ExpectedFound::new(a, b)));
                }
                return Ok(());
            }
            (
                BoxedExistential {
                    interfaces: a_ifaces,
                },
                BoxedExistential {
                    interfaces: b_ifaces,
                },
            ) => {
                if a_ifaces.len() != b_ifaces.len() {
                    return Err(TypeError::TyMismatch(ExpectedFound::new(a, b)));
                }

                for (a_iface, b_iface) in a_ifaces.iter().zip(b_ifaces.iter()) {
                    if a_iface.id != b_iface.id {
                        return Err(TypeError::TyMismatch(ExpectedFound::new(a, b)));
                    }
                    self.unify_generic_args(a_iface.arguments, b_iface.arguments)?;
                }

                return Ok(());
            }
            _ => {
                return Err(TypeError::TyMismatch(ExpectedFound::new(a, b)));
            }
        }
    }

    fn unify_generic_args(
        &self,
        a: GenericArguments<'ctx>,
        b: GenericArguments<'ctx>,
    ) -> UnificationResult<'ctx> {
        if a.len() != b.len() {
            return Err(TypeError::ArgCountMismatch(a.len(), b.len()));
        }

        for (a, b) in a.iter().zip(b.iter()) {
            self.unify_generic_arg(*a, *b)?;
        }

        Ok(())
    }

    fn unify_generic_arg(
        &self,
        a: GenericArgument<'ctx>,
        b: GenericArgument<'ctx>,
    ) -> UnificationResult<'ctx> {
        match (a, b) {
            (GenericArgument::Type(a_ty), GenericArgument::Type(b_ty)) => self.unify(a_ty, b_ty),
            (GenericArgument::Const(a_const), GenericArgument::Const(b_const)) => {
                if a_const.ty.is_error() || b_const.ty.is_error() {
                    return Ok(());
                }
                if a_const == b_const {
                    return Ok(());
                }
                Err(TypeError::ArgMismatch(ExpectedFound::new(a, b)))
            }
            _ => Err(TypeError::ArgMismatch(ExpectedFound::new(a, b))),
        }
    }
}
