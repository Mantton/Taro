use crate::{
    GlobalContext,
    check::{
        nodes::utils::associated_operators_for_ty,
        solver::{
            BinaryOperatorGoal, Goal, MethodCallGoal, Obligation, OverloadArgument, OverloadGoal,
            SolverDelegate, SolverResult, UnaryOperatorGoal,
        },
    },
    error::TypeError,
    ty::{Constraint, InferTy, Ty, TyKind},
};
use taroc_hir::{BinaryOperator, DefinitionID, OperatorKind};
use taroc_span::{Identifier, Span};

impl<'icx, 'ctx> SolverDelegate<'icx, 'ctx> {
    pub fn solve_unary(&mut self, goal: UnaryOperatorGoal<'ctx>) -> SolverResult<'ctx> {
        // Try intrinsic resolution first (e.g., -i32, ~u8, !bool)
        let ty = self.structurally_resolve(goal.operand_ty);
        if ty.is_infer() {
            return SolverResult::Deferred;
        }

        if let Some(obligations) = self.solve_unary_intrinsic(&goal, ty) {
            return SolverResult::Solved(obligations);
        }

        self.solve_unary_via_operator(goal)
    }

    fn solve_unary_via_operator(&mut self, goal: UnaryOperatorGoal<'ctx>) -> SolverResult<'ctx> {
        let ty = self.structurally_resolve(goal.operand_ty);
        if ty.is_infer() {
            return SolverResult::Deferred;
        }
        let kind = OperatorKind::from_unary(goal.operator);
        let candidates = self.collect_all_operator_candidates(ty, goal.span, kind);

        if candidates.is_empty() {
            return SolverResult::Error(TypeError::NoUnaryOperator(ty, kind));
        }

        if let [candidate] = candidates.as_slice() {
            // Record resolved operator association
            self.record_assoc_resolution(goal.node_id, *candidate);
            let obligations =
                self.select_fn_for_method(*candidate, ty, &unary_goal_to_method_goal(goal));
            return SolverResult::Solved(obligations);
        }

        let mut valid = vec![];
        for &candidate in &candidates {
            if self.evaluate_method_candidate(candidate, ty, &unary_goal_to_method_goal(goal)) {
                valid.push(candidate);
            }
        }

        if let [candidate] = valid.as_slice() {
            // Record resolved operator association
            self.record_assoc_resolution(goal.node_id, *candidate);
            let obligations =
                self.select_fn_for_method(*candidate, ty, &unary_goal_to_method_goal(goal));
            return SolverResult::Solved(obligations);
        }

        if valid.is_empty() {
            return SolverResult::Error(TypeError::NoOverloadCandidateMatch);
        }

        SolverResult::Deferred
    }
}

fn unary_goal_to_method_goal<'ctx>(goal: UnaryOperatorGoal<'ctx>) -> MethodCallGoal<'ctx> {
    MethodCallGoal {
        call_span: goal.span,
        method: Identifier::emtpy(goal.span.file),
        receiver_ty: goal.operand_ty,
        result_var: goal.result_var,
        expected_result_ty: goal.expectation,
        arguments: &[],
        label_agnostic: true,
        call_expr_id: goal.node_id,
        reciever_id: goal.rhs_id,
    }
}

impl<'icx, 'ctx> SolverDelegate<'icx, 'ctx> {
    /// Try to resolve “intrinsic” unary operations on primitives without invoking overloads.
    /// Returns Some(obligations) if handled intrinsically; None to fall back to overload search.
    fn solve_unary_intrinsic(
        &self,
        goal: &UnaryOperatorGoal<'ctx>,
        operand: Ty<'ctx>,
    ) -> Option<Vec<Obligation<'ctx>>> {
        use crate::ty::TyKind::*;
        use taroc_ast_ir::UnaryOperator::*;

        let gcx = self.gcx();
        let mut obligations = vec![];

        match goal.operator {
            // Numeric negation on ints, uints, and floats yields same type
            Negate => match operand.kind() {
                Int(_) | UInt(_) | Float(_) => {
                    obligations.push(Obligation {
                        location: goal.span,
                        goal: Goal::Constraint(Constraint::TypeEquality(goal.result_var, operand)),
                    });
                    if let Some(exp) = goal.expectation {
                        obligations.push(Obligation {
                            location: goal.span,
                            goal: Goal::Coerce {
                                from: goal.result_var,
                                to: exp,
                                node: goal.node_id,
                            },
                        });
                    }
                    return Some(obligations);
                }
                _ => {}
            },
            // Bitwise not on integers yields same type
            BitwiseNot => match operand.kind() {
                Int(_) | UInt(_) => {
                    obligations.push(Obligation {
                        location: goal.span,
                        goal: Goal::Constraint(Constraint::TypeEquality(goal.result_var, operand)),
                    });
                    return Some(obligations);
                }
                _ => {}
            },
            // Logical not only on bool; result is bool
            LogicalNot => {
                if matches!(operand.kind(), Bool) {
                    obligations.push(Obligation {
                        location: goal.span,
                        goal: Goal::Constraint(Constraint::TypeEquality(
                            goal.result_var,
                            gcx.store.common_types.bool,
                        )),
                    });
                    return Some(obligations);
                }
            }
        }

        None
    }
}

impl<'icx, 'ctx> SolverDelegate<'icx, 'ctx> {
    pub fn solve_binary(&mut self, goal: BinaryOperatorGoal<'ctx>) -> SolverResult<'ctx> {
        let gcx = self.gcx();
        let lhs = self.structurally_resolve(goal.lhs);
        let rhs = self.structurally_resolve(goal.rhs);
        if lhs.is_infer() {
            return SolverResult::Deferred;
        }

        if let BinaryOperator::PtrEq = goal.operator {
            match (lhs.kind(), rhs.kind()) {
                (
                    TyKind::Pointer(..) | TyKind::Reference(..),
                    TyKind::Pointer(..) | TyKind::Reference(..),
                ) => {
                    let location = goal.span;
                    let goal = Goal::Constraint(Constraint::TypeEquality(
                        gcx.store.common_types.bool,
                        goal.rho,
                    ));
                    return SolverResult::Solved(vec![Obligation { goal, location }]);
                }
                _ => return SolverResult::Error(TypeError::InvalidPointerEquality(lhs)),
            }
        }

        // Try intrinsic resolution first (e.g., u8 + u8, bool && bool)
        if let Some(obligations) = self.solve_binary_intrinsic(&goal, lhs, rhs) {
            return SolverResult::Solved(obligations);
        }

        let mut obligations = vec![];
        let is_infer = matches!(
            rhs.kind(),
            TyKind::Infer(InferTy::TyVar(..) | InferTy::IntVar(..) | InferTy::FloatVar(..))
        );

        if is_infer {
            obligations.push(Obligation {
                location: goal.span,
                goal: Goal::Constraint(Constraint::TypeEquality(lhs, rhs)),
            });
        }

        let kind = if !goal.assigning {
            OperatorKind::from_binary(goal.operator)
        } else {
            OperatorKind::assign_from_binary(goal.operator).expect("Assign Op")
        };
        let candidates = self.collect_all_operator_candidates(lhs, goal.span, kind);

        if candidates.is_empty() {
            return SolverResult::Error(TypeError::NoBinaryOperator(lhs, rhs, kind));
        }

        if let [candidate] = candidates.as_slice() {
            // Record resolved operator association
            self.record_assoc_resolution(goal.node_id, *candidate);
            obligations.extend(self.select_fn_for_method(
                *candidate,
                lhs,
                &binary_goal_to_method_goal(goal, gcx),
            ));
            return SolverResult::Solved(obligations);
        }

        let mut valid = vec![];
        for &candidate in &candidates {
            if self.evaluate_method_candidate(
                candidate,
                lhs,
                &binary_goal_to_method_goal(goal, gcx),
            ) {
                valid.push(candidate);
            }
        }

        if let [candidate] = valid.as_slice() {
            // Record resolved operator association
            self.record_assoc_resolution(goal.node_id, *candidate);
            obligations.extend(self.select_fn_for_method(
                *candidate,
                lhs,
                &binary_goal_to_method_goal(goal, gcx),
            ));
            return SolverResult::Solved(obligations);
        }

        if valid.is_empty() {
            return SolverResult::Error(TypeError::NoOverloadCandidateMatch);
        }

        SolverResult::Deferred
    }
}

impl<'icx, 'ctx> SolverDelegate<'icx, 'ctx> {
    /// Try to resolve “intrinsic” binary operations on primitives without invoking overloads.
    /// Returns Some(obligations) if handled intrinsically; None to fall back to overload search.
    fn solve_binary_intrinsic(
        &self,
        goal: &BinaryOperatorGoal<'ctx>,
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
                location: goal.span,
                goal: Goal::Constraint(Constraint::TypeEquality(goal.rho, ty)),
            });
        };

        let maybe_defer_literal_fit = |obligations: &mut Vec<_>, ty: Ty<'ctx>| {
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
                            location: goal.span,
                            goal: Goal::Constraint(Constraint::TypeEquality(rhs, lhs)),
                        });
                        push_rho_eq(obligations, lhs);
                        maybe_defer_literal_fit(obligations, lhs);
                        Some(())
                    }
                    (Float(_), Infer(FloatVar(_))) => {
                        obligations.push(Obligation {
                            location: goal.span,
                            goal: Goal::Constraint(Constraint::TypeEquality(rhs, lhs)),
                        });
                        push_rho_eq(obligations, lhs);
                        maybe_defer_literal_fit(obligations, lhs);
                        Some(())
                    }

                    // IntVar ⨉ concrete ⇒ bind IntVar to concrete, result = concrete
                    (Infer(IntVar(_)), Int(_) | UInt(_)) => {
                        obligations.push(Obligation {
                            location: goal.span,
                            goal: Goal::Constraint(Constraint::TypeEquality(lhs, rhs)),
                        });
                        push_rho_eq(obligations, rhs);
                        maybe_defer_literal_fit(obligations, rhs);
                        Some(())
                    }
                    (Infer(FloatVar(_)), Float(_)) => {
                        obligations.push(Obligation {
                            location: goal.span,
                            goal: Goal::Constraint(Constraint::TypeEquality(lhs, rhs)),
                        });
                        push_rho_eq(obligations, rhs);
                        maybe_defer_literal_fit(obligations, rhs);
                        Some(())
                    }

                    // Both sides inference of the *same* numeric kind ⇒ tie them together; result is that var
                    (Infer(IntVar(_)), Infer(IntVar(_))) => {
                        obligations.push(Obligation {
                            location: goal.span,
                            goal: Goal::Constraint(Constraint::TypeEquality(lhs, rhs)),
                        });
                        push_rho_eq(obligations, lhs);
                        Some(())
                    }
                    (Infer(FloatVar(_)), Infer(FloatVar(_))) => {
                        obligations.push(Obligation {
                            location: goal.span,
                            goal: Goal::Constraint(Constraint::TypeEquality(lhs, rhs)),
                        });
                        push_rho_eq(obligations, lhs);
                        Some(())
                    }

                    _ => None,
                }
            };

        let gcx = self.gcx();
        let mut obligations = vec![];

        match goal.operator {
            Add | Sub | Mul | Div | Rem => {
                // Fast path: both sides already same concrete numeric type
                if is_same_int(lhs, rhs) || is_same_float(lhs, rhs) {
                    push_rho_eq(&mut obligations, lhs);
                    if let Some(exp) = goal.expectation {
                        obligations.push(Obligation {
                            location: goal.span,
                            goal: Goal::Coerce {
                                from: goal.rho,
                                to: exp,
                                node: goal.node_id,
                            },
                        });
                    }
                    return Some(obligations);
                }

                // Eagerly unify inference vars with the concrete side (or with each other)
                if unify_numeric_binop(&mut obligations, lhs, rhs).is_some() {
                    if let Some(exp) = goal.expectation {
                        obligations.push(Obligation {
                            location: goal.span,
                            goal: Goal::Coerce {
                                from: goal.rho,
                                to: exp,
                                node: goal.node_id,
                            },
                        });
                    }
                    return Some(obligations);
                }

                // Mixed int/float or non-numeric ⇒ not intrinsic
            }

            // -------- Bitwise & | ^ and Shifts << >> --------
            BitAnd | BitOr | BitXor | BitShl | BitShr => {
                // Allow boolean bitwise (&, |, ^) → bool
                if matches!(goal.operator, BitAnd | BitOr | BitXor)
                    && matches!((lhs.kind(), rhs.kind()), (Bool, Bool))
                {
                    obligations.push(Obligation {
                        location: goal.span,
                        goal: Goal::Constraint(Constraint::TypeEquality(
                            goal.rho,
                            gcx.store.common_types.bool,
                        )),
                    });
                    return Some(obligations);
                }

                // Non-shift bitwise: integers, same type after inference; eagerly bind if needed
                if matches!(goal.operator, BitAnd | BitOr | BitXor) {
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
                        location: goal.span,
                        goal: Goal::Constraint(Constraint::TypeEquality(
                            goal.rho,
                            gcx.store.common_types.bool,
                        )),
                    });
                    return Some(obligations);
                }
            }

            // -------- Comparisons (result is bool) --------
            Eql | Neq | Lt | Gt | Leq | Geq => {
                // Simple: same numeric type
                if is_same_int(lhs, rhs) || is_same_float(lhs, rhs) {
                    obligations.push(Obligation {
                        location: goal.span,
                        goal: Goal::Constraint(Constraint::TypeEquality(
                            goal.rho,
                            gcx.store.common_types.bool,
                        )),
                    });
                    return Some(obligations);
                }
                // Eagerly bind inference vars to the concrete side (or to each other)
                match (lhs.kind(), rhs.kind()) {
                    // Concrete bool <op> bool  → result: bool
                    (Bool, Bool) if matches!(goal.operator, Eql | Neq) => {
                        obligations.push(Obligation {
                            location: goal.span,
                            goal: Goal::Constraint(Constraint::TypeEquality(
                                goal.rho,
                                gcx.store.common_types.bool,
                            )),
                        });
                        return Some(obligations);
                    }
                    (Int(_) | UInt(_), Infer(IntVar(_))) | (Infer(IntVar(_)), Int(_) | UInt(_)) => {
                        obligations.push(Obligation {
                            location: goal.span,
                            goal: Goal::Constraint(Constraint::TypeEquality(lhs, rhs)),
                        });
                        obligations.push(Obligation {
                            location: goal.span,
                            goal: Goal::Constraint(Constraint::TypeEquality(
                                goal.rho,
                                gcx.store.common_types.bool,
                            )),
                        });
                        return Some(obligations);
                    }
                    (Float(_), Infer(FloatVar(_))) | (Infer(FloatVar(_)), Float(_)) => {
                        obligations.push(Obligation {
                            location: goal.span,
                            goal: Goal::Constraint(Constraint::TypeEquality(lhs, rhs)),
                        });
                        obligations.push(Obligation {
                            location: goal.span,
                            goal: Goal::Constraint(Constraint::TypeEquality(
                                goal.rho,
                                gcx.store.common_types.bool,
                            )),
                        });
                        return Some(obligations);
                    }
                    (Infer(IntVar(_)), Infer(IntVar(_))) => {
                        obligations.push(Obligation {
                            location: goal.span,
                            goal: Goal::Constraint(Constraint::TypeEquality(lhs, rhs)),
                        });

                        obligations.push(Obligation {
                            location: goal.span,
                            goal: Goal::Constraint(Constraint::TypeEquality(
                                goal.rho,
                                gcx.store.common_types.bool,
                            )),
                        });
                        return Some(obligations);
                    }
                    (Infer(FloatVar(_)), Infer(FloatVar(_))) => {
                        obligations.push(Obligation {
                            location: goal.span,
                            goal: Goal::Constraint(Constraint::TypeEquality(lhs, rhs)),
                        });

                        obligations.push(Obligation {
                            location: goal.span,
                            goal: Goal::Constraint(Constraint::TypeEquality(
                                goal.rho,
                                gcx.store.common_types.bool,
                            )),
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
                location: goal.span,
                goal: Goal::Constraint(Constraint::TypeEquality(
                    goal.rho,
                    gcx.store.common_types.bool,
                )),
            });
            return Some(obligations);
        }

        None
    }
}

impl<'icx, 'ctx> SolverDelegate<'icx, 'ctx> {
    pub fn collect_all_operator_candidates(
        &self,
        recv_ty: Ty<'ctx>,
        recv_span: Span,
        operator: OperatorKind,
    ) -> Vec<DefinitionID> {
        let mut candidates = vec![];
        let mut autoderef = self.autoderef(recv_span, recv_ty);
        while let Some(recv) = autoderef.next() {
            let recv_candidates =
                associated_operators_for_ty(operator, recv, self.gcx(), recv_span.file);
            candidates.extend(recv_candidates);
        }
        candidates.dedup();
        candidates
    }
}

fn binary_goal_to_method_goal<'ctx>(
    goal: BinaryOperatorGoal<'ctx>,
    gcx: GlobalContext<'ctx>,
) -> MethodCallGoal<'ctx> {
    let arguments = gcx.store.interners.intern_slice(&[OverloadArgument {
        ty: if goal.rhs.is_infer() {
            goal.lhs
        } else {
            goal.rhs
        },
        span: goal.span,
        label: None,
        id: goal.rhs_id,
    }]);
    MethodCallGoal {
        call_span: goal.span,
        method: Identifier::emtpy(goal.span.file),
        receiver_ty: goal.lhs,
        result_var: goal.rho,
        expected_result_ty: goal.expectation,
        arguments,
        label_agnostic: true,
        reciever_id: goal.lhs_id,
        call_expr_id: goal.node_id,
    }
}

impl<'icx, 'ctx> SolverDelegate<'icx, 'ctx> {
    pub fn solve_subscript(&mut self, goal: OverloadGoal<'ctx>) -> SolverResult<'ctx> {
        let lhs = self.structurally_resolve(goal.callee_var);
        if lhs.is_infer() {
            return SolverResult::Deferred;
        }

        let candidates =
            self.collect_all_operator_candidates(lhs, goal.callee_span, OperatorKind::Index);
        if candidates.is_empty() {
            return SolverResult::Error(TypeError::NoOverloadCandidateMatch);
        }

        if let [candidate] = candidates.as_slice() {
            // Record resolved operator association
            self.record_assoc_resolution(goal.expr_id, *candidate);
            let obligations = self.select_fn_for_method(
                *candidate,
                lhs,
                &overload_goal_to_method_goal(goal, lhs),
            );
            return SolverResult::Solved(obligations);
        }

        let mut valid = vec![];
        for &candidate in &candidates {
            if self.evaluate_method_candidate(
                candidate,
                lhs,
                &overload_goal_to_method_goal(goal, lhs),
            ) {
                valid.push(candidate);
            }
        }

        if let [candidate] = valid.as_slice() {
            // Record resolved operator association
            self.record_assoc_resolution(goal.expr_id, *candidate);
            let obligations = self.select_fn_for_method(
                *candidate,
                lhs,
                &overload_goal_to_method_goal(goal, lhs),
            );
            return SolverResult::Solved(obligations);
        }

        if valid.is_empty() {
            return SolverResult::Error(TypeError::NoOverloadCandidateMatch);
        }

        SolverResult::Deferred
    }
}

fn overload_goal_to_method_goal<'ctx>(
    goal: OverloadGoal<'ctx>,
    rec: Ty<'ctx>,
) -> MethodCallGoal<'ctx> {
    MethodCallGoal {
        call_span: goal.expr_span,
        method: Identifier::emtpy(goal.callee_span.file),
        receiver_ty: rec,
        result_var: goal.result_var,
        expected_result_ty: goal.expected_result_ty,
        arguments: goal.arguments,
        label_agnostic: false,
        reciever_id: goal.callee_id,
        call_expr_id: goal.expr_id,
    }
}
