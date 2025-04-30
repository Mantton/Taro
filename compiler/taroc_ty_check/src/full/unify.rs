use taroc_ty::{GenericArgument, InferTy, Ty, TyKind};

use crate::models::UnificationError;

use super::FunctionChecker;

impl<'ctx> FunctionChecker<'ctx> {
    pub fn unify(&mut self, lhs: Ty<'ctx>, rhs: Ty<'ctx>) -> Result<(), UnificationError> {
        if lhs == rhs {
            return Ok(());
        };

        match (lhs.kind(), rhs.kind()) {
            (TyKind::Parameter(_), _) => self.unify_var(lhs, rhs),
            (_, TyKind::Parameter(_)) => self.unify_var(rhs, lhs),
            (TyKind::Infer(_), _) => self.unify_var(lhs, rhs),
            (_, TyKind::Infer(_)) => self.unify_var(rhs, lhs),

            // Structural types
            (TyKind::Tuple(lhs_e), TyKind::Tuple(rhs_e)) if lhs_e.len() == rhs_e.len() => {
                for (a, b) in lhs_e.iter().zip(rhs_e.iter()) {
                    self.unify(*a, *b)?;
                }
                Ok(())
            }

            (
                TyKind::Function {
                    inputs: lhs_i,
                    output: lhs_o,
                    is_async: lhs_is_async,
                },
                TyKind::Function {
                    inputs: rhs_i,
                    output: rhs_o,
                    is_async: rhs_is_async,
                },
            ) if lhs_i.len() == rhs_i.len() && lhs_is_async == rhs_is_async => {
                // inputs
                for (lhs_i, rhs_i) in lhs_i.iter().zip(rhs_i.iter()) {
                    self.unify(*lhs_i, *rhs_i)?;
                }

                // outputs
                self.unify(lhs_o, rhs_o)?;

                return Ok(());
            }

            (
                TyKind::Adt(lhs_id, lhs_args, lhs_parent),
                TyKind::Adt(rhs_id, rhs_args, rhs_parent),
            ) if lhs_id == rhs_id && lhs_args.len() == rhs_args.len() => {
                // Parent
                match (lhs_parent, rhs_parent) {
                    (Some(s1), Some(s2)) => self.unify(s1, s2)?,
                    (None, None) => {}
                    _ => unreachable!("ICE: ADT subtype presence mismatch"),
                };

                // Arguments
                for (a1, a2) in lhs_args.iter().zip(rhs_args.iter()) {
                    match (a1, a2) {
                        (GenericArgument::Type(t1), GenericArgument::Type(t2)) => {
                            self.unify(*t1, *t2)?;
                        }
                        (GenericArgument::Const(c1), GenericArgument::Const(c2)) => {
                            if c1 != c2 {
                                unreachable!("mismatch const generic argument");
                            }
                        }
                        _ => {
                            unreachable!(
                                "ICE: cannot have mismatched generic argument kind (type vs const)"
                            );
                        }
                    }
                }
                return Ok(());
            }
            _ => {
                return Err(UnificationError::TypeMismatch);
            }
        }
    }

    fn unify_var(&mut self, lhs: Ty<'ctx>, rhs: Ty<'ctx>) -> Result<(), UnificationError> {
        match lhs.kind() {
            TyKind::Infer(InferTy::TyVar(id)) => {
                let root = self.context.find_tyvar(id);

                // already bound  ⇒  delegate
                if let Some(bound) = self.context.tyvar_bindings[root].bound_ty {
                    return self.unify(bound, rhs);
                }

                // TyVar ↔ TyVar  ⇒  merge
                if let TyKind::Infer(InferTy::TyVar(rid)) = rhs.kind() {
                    let rhs_root = self.context.find_tyvar(rid);
                    if root == rhs_root {
                        return Ok(());
                    }

                    // pick the representative that already has a concrete type
                    let (rep, other) = if self.context.tyvar_bindings[root].bound_ty.is_some() {
                        (root, rhs_root)
                    } else {
                        (rhs_root, root)
                    };

                    // *move* the binding so the representative keeps it
                    if let Some(t) = self.context.tyvar_bindings[other].bound_ty {
                        self.context.tyvar_bindings[rep].bound_ty = Some(t);
                    }

                    self.context.tyvar_bindings[other].parent = Some(rep);
                    return Ok(());
                }

                // occurs-check to avoid α = List<α>
                if self.occurs_in_ty(root, rhs) {
                    return Err(UnificationError::OccursCheckFailed);
                }

                // bind var → rhs
                self.context.tyvar_bindings[root].bound_ty = Some(rhs);
                Ok(())
            }

            TyKind::Infer(InferTy::IntVar(id)) => {
                let root = self.context.find_intvar(id);

                if let TyKind::Infer(InferTy::IntVar(rhs_id)) = rhs.kind() {
                    let rhs_root = self.context.find_intvar(rhs_id);
                    if root == rhs_root {
                        return Ok(());
                    }

                    self.context.intvar_bindings[root].parent = Some(rhs_root);
                    return Ok(());
                }

                if let Some(bound) = self.context.intvar_bindings[root].bound_ty {
                    return self.unify(bound, rhs);
                }

                // If `rhs` is a concrete integer type, bind var → that type
                if matches!(rhs.kind(), TyKind::Int(..) | TyKind::UInt(..)) {
                    self.context.intvar_bindings[root].bound_ty = Some(rhs);
                    return Ok(());
                }

                return Err(UnificationError::TypeMismatch);
            }
            TyKind::Infer(InferTy::FloatVar(id)) => {
                let root = self.context.find_floatvar(id);
                if let TyKind::Infer(InferTy::FloatVar(rid)) = rhs.kind() {
                    let rhs_root = self.context.find_floatvar(rid);
                    if root != rhs_root {
                        self.context.floatvar_bindings[root].parent = Some(rhs_root);
                    }
                    return Ok(());
                }
                if let Some(bound) = self.context.floatvar_bindings[root].bound_ty {
                    return self.unify(bound, rhs);
                }
                if matches!(rhs.kind(), TyKind::Float(..)) {
                    self.context.floatvar_bindings[root].bound_ty = Some(rhs);
                    return Ok(());
                }
                return Err(UnificationError::TypeMismatch);
            }

            TyKind::Infer(InferTy::NilVar(id)) => {
                let root = self.context.find_nilvar(id);
                if let TyKind::Infer(InferTy::NilVar(rid)) = rhs.kind() {
                    let rhs_root = self.context.find_nilvar(rid);
                    if root != rhs_root {
                        self.context.nilvar_bindings[root].parent = Some(rhs_root);
                    }
                    return Ok(());
                }
                if let Some(bound) = self.context.nilvar_bindings[root].bound_ty {
                    return self.unify(bound, rhs);
                }
                if self.is_nil_compatible(rhs.kind()) {
                    self.context.nilvar_bindings[root].bound_ty = Some(rhs);
                    return Ok(());
                }
                return Err(UnificationError::TypeMismatch);
            }
            _ => unreachable!("ICE: `unify_var` called for non inferred type {lhs}"),
        }
    }

    fn is_nil_compatible(&self, kind: TyKind<'ctx>) -> bool {
        match kind {
            TyKind::Pointer(..) => true,
            TyKind::Adt(def, ..) => def.id == self.optional_def_id(), // TODO: isOption type
            _ => false,
        }
    }
}
