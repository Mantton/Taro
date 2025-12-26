use crate::{
    hir::{BinaryOperator, OperatorKind, UnaryOperator},
    sema::{
        error::TypeError,
        models::{InferTy, Ty, TyKind},
        tycheck::solve::{
            ApplyArgument, ApplyGoalData, BinOpGoalData, BindOverloadGoalData, ConstraintSolver,
            DisjunctionBranch, Goal, Obligation, SolverResult, UnOpGoalData,
        },
    },
    span::Spanned,
};

/// Convert a BinaryOperator to an OperatorKind for operator method lookup.
fn binary_op_to_operator_kind(op: BinaryOperator) -> Option<OperatorKind> {
    match op {
        BinaryOperator::Add => Some(OperatorKind::Add),
        BinaryOperator::Sub => Some(OperatorKind::Sub),
        BinaryOperator::Mul => Some(OperatorKind::Mul),
        BinaryOperator::Div => Some(OperatorKind::Div),
        BinaryOperator::Rem => Some(OperatorKind::Rem),
        BinaryOperator::BitAnd => Some(OperatorKind::BitAnd),
        BinaryOperator::BitOr => Some(OperatorKind::BitOr),
        BinaryOperator::BitXor => Some(OperatorKind::BitXor),
        BinaryOperator::BitShl => Some(OperatorKind::BitShl),
        BinaryOperator::BitShr => Some(OperatorKind::BitShr),
        BinaryOperator::Eql => Some(OperatorKind::Eq),
        BinaryOperator::Neq => Some(OperatorKind::Neq),
        BinaryOperator::Lt => Some(OperatorKind::Lt),
        BinaryOperator::Gt => Some(OperatorKind::Gt),
        BinaryOperator::Leq => Some(OperatorKind::Leq),
        BinaryOperator::Geq => Some(OperatorKind::Geq),
        // Not overloadable
        BinaryOperator::BoolAnd | BinaryOperator::BoolOr | BinaryOperator::PtrEq => None,
    }
}

/// Convert a UnaryOperator to an OperatorKind for operator method lookup.
fn unary_op_to_operator_kind(op: UnaryOperator) -> Option<OperatorKind> {
    match op {
        UnaryOperator::Negate => Some(OperatorKind::Neg),
        UnaryOperator::BitwiseNot => Some(OperatorKind::BitwiseNot),
        UnaryOperator::LogicalNot => Some(OperatorKind::Not),
    }
}

impl<'ctx> ConstraintSolver<'ctx> {
    pub fn solve_unary(&mut self, data: UnOpGoalData<'ctx>) -> SolverResult<'ctx> {
        let ty = self.structurally_resolve(data.lhs);

        // If type is not yet resolved, defer
        if ty.is_infer() {
            return SolverResult::Deferred;
        }

        // Try intrinsic resolution first
        if let Some(obligations) = self.solve_unary_intrinsic(&data, ty) {
            return SolverResult::Solved(obligations);
        }

        // Try operator method resolution
        if let Some(result) = self.solve_unary_method(&data, ty) {
            return result;
        }

        // No intrinsic or method found
        SolverResult::Error(vec![Spanned::new(
            TypeError::InvalidUnaryOp {
                op: data.operator,
                ty,
            },
            data.span,
        )])
    }

    fn solve_unary_method(
        &mut self,
        data: &UnOpGoalData<'ctx>,
        operand_ty: Ty<'ctx>,
    ) -> Option<SolverResult<'ctx>> {
        let op_kind = unary_op_to_operator_kind(data.operator)?;

        // Look up operator candidates on the operand type
        let candidates = self.lookup_operator_candidates(operand_ty, op_kind);
        if candidates.is_empty() {
            return None;
        }

        // Create a type variable for the method type
        let method_ty = self.icx.next_ty_var(data.span);

        // Build disjunction branches for each candidate
        let mut branches = Vec::with_capacity(candidates.len());
        for candidate in candidates {
            let candidate_ty = self.gcx().get_type(candidate);
            branches.push(DisjunctionBranch {
                goal: Goal::BindOverload(BindOverloadGoalData {
                    node_id: data.node_id,
                    var_ty: method_ty,
                    candidate_ty,
                    source: candidate,
                }),
                source: Some(candidate),
            });
        }

        let disjunction_goal = Obligation {
            location: data.span,
            goal: Goal::Disjunction(branches),
        };

        // Build the Apply goal: call the operator method with `self` as the only argument
        let apply_goal = Obligation {
            location: data.span,
            goal: Goal::Apply(ApplyGoalData {
                call_span: data.span,
                callee_ty: method_ty,
                callee_source: None,
                result_ty: data.rho,
                expect_ty: data.expectation,
                arguments: vec![ApplyArgument {
                    id: data.rhs_id,
                    label: None,
                    ty: operand_ty,
                    span: data.span,
                }],
                skip_labels: true,
            }),
        };

        Some(SolverResult::Solved(vec![disjunction_goal, apply_goal]))
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

        // If LHS type is not yet resolved, defer
        if lhs.is_infer() {
            return SolverResult::Deferred;
        }

        // Try intrinsic resolution first (e.g., u8 + u8, bool && bool)
        if let Some(obligations) = self.solve_binary_intrinsic(&data, lhs, rhs) {
            return SolverResult::Solved(obligations);
        }

        // Try operator method resolution
        if let Some(result) = self.solve_binary_method(&data, lhs, rhs) {
            return result;
        }

        // No intrinsic or method found
        SolverResult::Error(vec![Spanned::new(
            TypeError::InvalidBinaryOp {
                op: data.operator,
                lhs,
                rhs,
            },
            data.span,
        )])
    }

    fn solve_binary_method(
        &mut self,
        data: &BinOpGoalData<'ctx>,
        lhs: Ty<'ctx>,
        rhs: Ty<'ctx>,
    ) -> Option<SolverResult<'ctx>> {
        let op_kind = binary_op_to_operator_kind(data.operator)?;

        // Look up operator candidates on the LHS type
        let candidates = self.lookup_operator_candidates(lhs, op_kind);
        if candidates.is_empty() {
            return None;
        }

        // Filter candidates to those whose RHS parameter matches
        let mut matching_candidates = Vec::new();
        for candidate in candidates {
            let sig = self.gcx().get_signature(candidate);
            // Operator methods have signature: (self, rhs: Rhs) -> Result
            // Check if the second parameter type is compatible with rhs
            if sig.inputs.len() >= 2 {
                let rhs_param_ty = sig.inputs[1].ty;
                // Check if RHS can unify with the parameter type
                // For now, just check if they're the same or if RHS is an inference var
                if rhs == rhs_param_ty || rhs.is_infer() {
                    matching_candidates.push(candidate);
                }
            }
        }

        if matching_candidates.is_empty() {
            return None;
        }

        // Create a type variable for the method type
        let method_ty = self.icx.next_ty_var(data.span);

        // Build disjunction branches for each candidate
        let mut branches = Vec::with_capacity(matching_candidates.len());
        for candidate in matching_candidates {
            let candidate_ty = self.gcx().get_type(candidate);
            branches.push(DisjunctionBranch {
                goal: Goal::BindOverload(BindOverloadGoalData {
                    node_id: data.node_id,
                    var_ty: method_ty,
                    candidate_ty,
                    source: candidate,
                }),
                source: Some(candidate),
            });
        }

        let disjunction_goal = Obligation {
            location: data.span,
            goal: Goal::Disjunction(branches),
        };

        // Build the Apply goal: call the operator method with `self` and `rhs` as arguments
        let apply_goal = Obligation {
            location: data.span,
            goal: Goal::Apply(ApplyGoalData {
                call_span: data.span,
                callee_ty: method_ty,
                callee_source: None,
                result_ty: data.rho,
                expect_ty: data.expectation,
                arguments: vec![
                    ApplyArgument {
                        id: data.lhs_id,
                        label: None,
                        ty: lhs,
                        span: data.span,
                    },
                    ApplyArgument {
                        id: data.rhs_id,
                        label: None,
                        ty: rhs,
                        span: data.span,
                    },
                ],
                skip_labels: true,
            }),
        };

        Some(SolverResult::Solved(vec![disjunction_goal, apply_goal]))
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
