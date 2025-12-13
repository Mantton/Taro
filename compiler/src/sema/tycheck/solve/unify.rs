use crate::sema::{
    error::{ExpectedFound, TypeError},
    models::{InferTy, Ty, TyKind},
    tycheck::{
        infer::keys::{FloatVarValue, IntVarValue},
        solve::ConstraintSolver,
    },
};

type UnificationResult<'ctx> = Result<(), TypeError<'ctx>>;

impl<'ctx> ConstraintSolver<'ctx> {
    pub fn unify(&self, a: Ty<'ctx>, b: Ty<'ctx>) -> UnificationResult<'ctx> {
        let a = self.structurally_resolve(a);
        let b = self.structurally_resolve(b);

        println!("unify: {} - {}", a.format(self.gcx()), b.format(self.gcx()));

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
        return Ok(());
    }

    fn unify_inference_vars(&self, a: Ty<'ctx>, b: Ty<'ctx>) -> UnificationResult<'ctx> {
        use InferTy::*;
        use TyKind::*;
        match (a.kind(), b.kind()) {
            // Error
            (Error, Error) => return Ok(()),

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
            (Infer(_), _) | (_, Infer(_)) => {
                return Err(TypeError::TyMismatch(ExpectedFound::new(a, b)));
            }
            _ => return self.unify_nominal_types(a, b),
        }

        return Ok(());
    }

    fn unify_nominal_types(&self, a: Ty<'ctx>, b: Ty<'ctx>) -> UnificationResult<'ctx> {
        use TyKind::*;
        match (a.kind(), b.kind()) {
            (Infer(_), _) | (_, Infer(_)) => {
                unreachable!("ICE: inference variables encountered in `unify_nominal_tys`")
            }
            (Error, Error) => return Ok(()),
            (Rune | Bool | Int(_) | UInt(_) | Float(_) | String, _) if a == b => return Ok(()),
            // (Parameter(a_p), Parameter(b_p)) if a_p.index == b_p.index => return Ok(()),
            // (Adt(a_def, a_args), Adt(b_def, b_args)) if a_def.id == b_def.id => {
            //     self.unify_generic_args(a_args, b_args)?;
            //     return Ok(());
            // }
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
            _ => {
                return Err(TypeError::TyMismatch(ExpectedFound::new(a, b)));
            }
        }
    }
}

// impl< 'ctx> SolverDelegate< 'ctx> {
//     fn unify_generic_args(
//         &self,
//         a: GenericArguments<'ctx>,
//         b: GenericArguments<'ctx>,
//     ) -> UnificationResult<'ctx> {
//         if a.len() != b.len() {
//             return Err(TypeError::ArgCount);
//         }

//         for (a, b) in a.iter().zip(b.iter()) {
//             self.unify_generic_arg(*a, *b)?;
//         }

//         return Ok(());
//     }

//     fn unify_generic_arg(
//         &self,
//         a: GenericArgument<'ctx>,
//         b: GenericArgument<'ctx>,
//     ) -> UnificationResult<'ctx> {
//         match (a, b) {
//             (GenericArgument::Type(a_ty), GenericArgument::Type(b_ty)) => {
//                 return self.unify(a_ty, b_ty);
//             }
//             (GenericArgument::Const(_), GenericArgument::Const(_)) => {
//                 todo!()
//             }
//             _ => return Err(TypeError::ArgMismatch(ExpectedFound::new(a, b))),
//         }
//     }
// }

impl<'ctx> ConstraintSolver<'ctx> {
    pub fn structurally_resolve(&self, mut ty: Ty<'ctx>) -> Ty<'ctx> {
        ty = self.icx.resolve_vars_if_possible(ty);
        ty
    }
}
