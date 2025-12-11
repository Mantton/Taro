use crate::{
    hir::{BinaryOperator, UnaryOperator},
    sema::{
        models::{InferTy, Ty, TyKind},
        tycheck::solve::{
            BinOpGoalData, ConstraintSolver, Goal, Obligation, SolverResult, UnOpGoalData,
        },
    },
};

impl<'ctx> ConstraintSolver<'ctx> {
    pub fn solve_unary(&mut self, data: UnOpGoalData<'ctx>) -> SolverResult<'ctx> {
        let ty = self.structurally_resolve(data.lhs);

        if let Some(obligations) = self.solve_unary_intrinsic(&data, ty) {
            return SolverResult::Solved(obligations);
        }

        todo!("operator methods")
    }

    fn solve_unary_intrinsic(
        &self,
        data: &UnOpGoalData<'ctx>,
        lhs: Ty<'ctx>,
    ) -> Option<Vec<Obligation<'ctx>>> {
        use TyKind::*;
        use UnaryOperator::*;

        let gcx = self.gcx();
        let mut obligations = vec![];

        match data.operator {
            // Numeric negation on ints, uints, and floats yields same type
            Negate => match lhs.kind() {
                Int(_) | UInt(_) | Float(_) | Infer(InferTy::IntVar(_) | InferTy::FloatVar(_)) => {
                    obligations.push(Obligation {
                        location: data.span,
                        goal: Goal::Equal(data.rho, lhs),
                    });
                    return Some(obligations);
                }
                _ => {}
            },
            // Bitwise not on integers yields same type
            BitwiseNot => match lhs.kind() {
                Int(_) | UInt(_) | Infer(InferTy::IntVar(_)) => {
                    obligations.push(Obligation {
                        location: data.span,
                        goal: Goal::Equal(data.rho, lhs),
                    });
                    return Some(obligations);
                }
                _ => {}
            },
            // Logical not only on bool; result is bool
            LogicalNot => {
                if matches!(lhs.kind(), Bool) {
                    obligations.push(Obligation {
                        location: data.span,
                        goal: Goal::Equal(data.rho, gcx.types.bool),
                    });
                    return Some(obligations);
                }
            }
        }

        None
    }
}

impl<'ctx> ConstraintSolver<'ctx> {
    pub fn solve_binary(&mut self, data: BinOpGoalData<'ctx>) -> SolverResult<'ctx> {
        let lhs = self.structurally_resolve(data.lhs);
        let rhs = self.structurally_resolve(data.rhs);

        // Try intrinsic resolution first (e.g., u8 + u8, bool && bool)
        if let Some(obligations) = self.solve_binary_intrinsic(&data, lhs, rhs) {
            return SolverResult::Solved(obligations);
        }

        todo!("operator methods")
    }
}

impl<'ctx> ConstraintSolver<'ctx> {
    /// Try to resolve “intrinsic” binary operations on primitives without invoking overloads.
    /// Returns Some(obligations) if handled intrinsically; None to fall back to overload search.
    fn solve_binary_intrinsic(
        &self,
        data: &BinOpGoalData<'ctx>,
        lhs: Ty<'ctx>,
        rhs: Ty<'ctx>,
    ) -> Option<Vec<Obligation<'ctx>>> {
        use BinaryOperator::*;
        use InferTy::*;
        use TyKind::*;

        let is_same_int = |a: Ty<'ctx>, b: Ty<'ctx>| -> bool {
            match (a.kind(), b.kind()) {
                (Int(ka), Int(kb)) => ka == kb,
                (UInt(ka), UInt(kb)) => ka == kb,
                _ => false,
            }
        };
        let is_same_float = |a: Ty<'ctx>, b: Ty<'ctx>| -> bool {
            matches!((a.kind(), b.kind()), (Float(ka), Float(kb)) if ka == kb)
        };

        let push_rho_eq = |obligations: &mut Vec<_>, ty: Ty<'ctx>| {
            obligations.push(Obligation {
                location: data.span,
                goal: Goal::Equal(data.rho, ty),
            });
        };

        let maybe_defer_literal_fit = |_: &mut Vec<_>, _: Ty<'ctx>| {
            // TODO: range check for numeric literals (u8: 300 is error, etc.)
            // obligations.push(Obligation {
            //     location: goal.span,
            //     goal: Goal::LiteralFits {
            //         node: goal.node_id,
            //         ty,
            //     },
            // });
        };

        // ------ Helper that eagerly unifies inference vars for numeric binops ------
        let unify_numeric_binop =
            |obligations: &mut Vec<_>, lhs: Ty<'ctx>, rhs: Ty<'ctx>| -> Option<()> {
                match (lhs.kind(), rhs.kind()) {
                    // Concrete ⨉ IntVar  ⇒ bind IntVar to concrete, result = concrete
                    (Int(_) | UInt(_), Infer(IntVar(_))) => {
                        obligations.push(Obligation {
                            location: data.span,
                            goal: Goal::Equal(rhs, lhs),
                        });
                        push_rho_eq(obligations, lhs);
                        maybe_defer_literal_fit(obligations, lhs);
                        Some(())
                    }
                    (Float(_), Infer(FloatVar(_))) => {
                        obligations.push(Obligation {
                            location: data.span,
                            goal: Goal::Equal(rhs, lhs),
                        });
                        push_rho_eq(obligations, lhs);
                        maybe_defer_literal_fit(obligations, lhs);
                        Some(())
                    }

                    // IntVar ⨉ concrete ⇒ bind IntVar to concrete, result = concrete
                    (Infer(IntVar(_)), Int(_) | UInt(_)) => {
                        obligations.push(Obligation {
                            location: data.span,
                            goal: Goal::Equal(lhs, rhs),
                        });
                        push_rho_eq(obligations, rhs);
                        maybe_defer_literal_fit(obligations, rhs);
                        Some(())
                    }
                    (Infer(FloatVar(_)), Float(_)) => {
                        obligations.push(Obligation {
                            location: data.span,
                            goal: Goal::Equal(lhs, rhs),
                        });
                        push_rho_eq(obligations, rhs);
                        maybe_defer_literal_fit(obligations, rhs);
                        Some(())
                    }

                    // Both sides inference of the *same* numeric kind ⇒ tie them together; result is that var
                    (Infer(IntVar(_)), Infer(IntVar(_))) => {
                        obligations.push(Obligation {
                            location: data.span,
                            goal: Goal::Equal(lhs, rhs),
                        });
                        push_rho_eq(obligations, lhs);
                        Some(())
                    }
                    (Infer(FloatVar(_)), Infer(FloatVar(_))) => {
                        obligations.push(Obligation {
                            location: data.span,
                            goal: Goal::Equal(lhs, rhs),
                        });
                        push_rho_eq(obligations, lhs);
                        Some(())
                    }

                    _ => None,
                }
            };

        let gcx = self.gcx();
        let mut obligations = vec![];

        match data.operator {
            Add | Sub | Mul | Div | Rem => {
                // Fast path: both sides already same concrete numeric type
                if is_same_int(lhs, rhs) || is_same_float(lhs, rhs) {
                    push_rho_eq(&mut obligations, lhs);
                    if let Some(exp) = data.expectation {
                        obligations.push(Obligation {
                            location: data.span,
                            goal: Goal::Equal(data.rho, exp),
                        });
                    }
                    return Some(obligations);
                }

                // Eagerly unify inference vars with the concrete side (or with each other)
                if unify_numeric_binop(&mut obligations, lhs, rhs).is_some() {
                    if let Some(exp) = data.expectation {
                        obligations.push(Obligation {
                            location: data.span,
                            goal: Goal::Equal(data.rho, exp),
                        });
                    }
                    return Some(obligations);
                }

                // Mixed int/float or non-numeric ⇒ not intrinsic
            }

            // -------- Bitwise & | ^ and Shifts << >> --------
            BitAnd | BitOr | BitXor | BitShl | BitShr => {
                // Allow boolean bitwise (&, |, ^) → bool
                if matches!(data.operator, BitAnd | BitOr | BitXor)
                    && matches!((lhs.kind(), rhs.kind()), (Bool, Bool))
                {
                    obligations.push(Obligation {
                        location: data.span,
                        goal: Goal::Equal(data.rho, gcx.types.bool),
                    });
                    return Some(obligations);
                }

                // Non-shift bitwise: integers, same type after inference; eagerly bind if needed
                if matches!(data.operator, BitAnd | BitOr | BitXor) {
                    if is_same_int(lhs, rhs) {
                        push_rho_eq(&mut obligations, lhs);
                        return Some(obligations);
                    }
                    if unify_numeric_binop(&mut obligations, lhs, rhs).is_some() {
                        return Some(obligations);
                    }
                    // else: not intrinsic
                } else {
                    // Shifts: LHS must be integer; RHS can be any integer type/var; result = LHS
                    match (lhs.kind(), rhs.kind()) {
                        // Concrete LHS integer; any RHS integer kind (incl. IntVar) is OK
                        (Int(_) | UInt(_), Int(_) | UInt(_) | Infer(IntVar(_))) => {
                            push_rho_eq(&mut obligations, lhs);
                            return Some(obligations);
                        }
                        // LHS is IntVar ⇒ say “it’s an integer”; RHS must also be integer-ish
                        (Infer(IntVar(_)), Int(_) | UInt(_) | Infer(IntVar(_))) => {
                            push_rho_eq(&mut obligations, lhs);
                            return Some(obligations);
                        }
                        _ => { /* not intrinsic */ }
                    }
                }
            }
            // -------- Lazy boolean ops (not overloadable) --------
            BoolAnd | BoolOr => {
                if matches!(lhs.kind(), Bool) && matches!(rhs.kind(), Bool) {
                    obligations.push(Obligation {
                        location: data.span,
                        goal: Goal::Equal(data.rho, gcx.types.bool),
                    });
                    return Some(obligations);
                }
            }

            // -------- Comparisons (result is bool) --------
            Eql | Neq | Lt | Gt | Leq | Geq => {
                // Simple: same numeric type
                if is_same_int(lhs, rhs) || is_same_float(lhs, rhs) {
                    obligations.push(Obligation {
                        location: data.span,
                        goal: Goal::Equal(data.rho, gcx.types.bool),
                    });
                    return Some(obligations);
                }
                // Eagerly bind inference vars to the concrete side (or to each other)
                match (lhs.kind(), rhs.kind()) {
                    // Concrete bool <op> bool  → result: bool
                    (Bool, Bool) if matches!(data.operator, Eql | Neq) => {
                        obligations.push(Obligation {
                            location: data.span,
                            goal: Goal::Equal(data.rho, gcx.types.bool),
                        });
                        return Some(obligations);
                    }
                    (Int(_) | UInt(_), Infer(IntVar(_))) | (Infer(IntVar(_)), Int(_) | UInt(_)) => {
                        obligations.push(Obligation {
                            location: data.span,
                            goal: Goal::Equal(lhs, rhs),
                        });
                        obligations.push(Obligation {
                            location: data.span,
                            goal: Goal::Equal(data.rho, gcx.types.bool),
                        });
                        return Some(obligations);
                    }
                    (Float(_), Infer(FloatVar(_))) | (Infer(FloatVar(_)), Float(_)) => {
                        obligations.push(Obligation {
                            location: data.span,
                            goal: Goal::Equal(lhs, rhs),
                        });
                        obligations.push(Obligation {
                            location: data.span,
                            goal: Goal::Equal(data.rho, gcx.types.bool),
                        });
                        return Some(obligations);
                    }
                    (Infer(IntVar(_)), Infer(IntVar(_))) => {
                        obligations.push(Obligation {
                            location: data.span,
                            goal: Goal::Equal(lhs, rhs),
                        });

                        obligations.push(Obligation {
                            location: data.span,
                            goal: Goal::Equal(data.rho, gcx.types.bool),
                        });
                        return Some(obligations);
                    }
                    (Infer(FloatVar(_)), Infer(FloatVar(_))) => {
                        obligations.push(Obligation {
                            location: data.span,
                            goal: Goal::Equal(lhs, rhs),
                        });

                        obligations.push(Obligation {
                            location: data.span,
                            goal: Goal::Equal(data.rho, gcx.types.bool),
                        });
                        return Some(obligations);
                    }
                    _ => { /* not intrinsic */ }
                }
            }
            PtrEq => unreachable!(),
        }

        let numeric_same = |a: Ty<'ctx>, b: Ty<'ctx>| -> bool {
            match (a.kind(), b.kind()) {
                (Int(ka), Int(kb)) => ka == kb,
                (UInt(ka), UInt(kb)) => ka == kb,
                (Float(ka), Float(kb)) => ka == kb,
                _ => false,
            }
        };

        if numeric_same(lhs, rhs) {
            obligations.push(Obligation {
                location: data.span,
                goal: Goal::Equal(data.rho, gcx.types.bool),
            });
            return Some(obligations);
        }

        None
    }
}
