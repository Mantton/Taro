use crate::{
    hir::{BinaryOperator, Mutability, OperatorKind, UnaryOperator},
    sema::{
        error::TypeError,
        models::{InferTy, Ty, TyKind},
        tycheck::solve::{
            Adjustment, ApplyArgument, ApplyGoalData, AssignOpGoalData, BinOpGoalData,
            BindOverloadGoalData, ConstraintSolver, DisjunctionBranch, Goal, Obligation,
            SolverResult, UnOpGoalData,
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

/// Convert a BinaryOperator to an OperatorKind for compound assignment operator method lookup.
fn binary_op_to_assign_operator_kind(op: BinaryOperator) -> Option<OperatorKind> {
    match op {
        BinaryOperator::Add => Some(OperatorKind::AddAssign),
        BinaryOperator::Sub => Some(OperatorKind::SubAssign),
        BinaryOperator::Mul => Some(OperatorKind::MulAssign),
        BinaryOperator::Div => Some(OperatorKind::DivAssign),
        BinaryOperator::Rem => Some(OperatorKind::RemAssign),
        BinaryOperator::BitAnd => Some(OperatorKind::BitAndAssign),
        BinaryOperator::BitOr => Some(OperatorKind::BitOrAssign),
        BinaryOperator::BitXor => Some(OperatorKind::BitXorAssign),
        BinaryOperator::BitShl => Some(OperatorKind::BitShlAssign),
        BinaryOperator::BitShr => Some(OperatorKind::BitShrAssign),
        // Comparison and boolean operators don't have assign variants
        BinaryOperator::Eql
        | BinaryOperator::Neq
        | BinaryOperator::Lt
        | BinaryOperator::Gt
        | BinaryOperator::Leq
        | BinaryOperator::Geq
        | BinaryOperator::BoolAnd
        | BinaryOperator::BoolOr
        | BinaryOperator::PtrEq => None,
    }
}

impl<'ctx> ConstraintSolver<'ctx> {
    pub fn solve_unary(&mut self, data: UnOpGoalData<'ctx>) -> SolverResult<'ctx> {
        let ty = self.structurally_resolve(data.lhs);

        if ty.is_error() {
            let obligation = Obligation {
                location: data.span,
                goal: Goal::Equal(data.rho, Ty::error(self.gcx())),
            };
            return SolverResult::Solved(vec![obligation]);
        }

        // If type is not yet resolved, defer
        if ty.contains_inference() {
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
                    instantiation_args: None,
                }),
                source: Some(candidate),
                autoref_cost: 0,
                matches_expectation: false,
                deref_steps: 0,
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
                call_node_id: data.node_id,
                call_span: data.span,
                callee_ty: method_ty,
                callee_source: None,
                result_ty: data.rho,
                _expect_ty: data.expectation,
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

        if lhs.is_error() || rhs.is_error() {
            let obligation = Obligation {
                location: data.span,
                goal: Goal::Equal(data.rho, Ty::error(self.gcx())),
            };
            return SolverResult::Solved(vec![obligation]);
        }

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

    /// Determines if a binary operator is a comparison operator that should use autoref.
    /// Comparison operators implicitly borrow their operands, matching Rust's semantics:
    /// `a == b` is equivalent to `PartialEq::eq(&a, &b)`
    fn is_comparison_operator(op: BinaryOperator) -> bool {
        matches!(
            op,
            BinaryOperator::Eql
                | BinaryOperator::Neq
                | BinaryOperator::Lt
                | BinaryOperator::Gt
                | BinaryOperator::Leq
                | BinaryOperator::Geq
        )
    }

    fn solve_binary_method(
        &mut self,
        data: &BinOpGoalData<'ctx>,
        lhs: Ty<'ctx>,
        rhs: Ty<'ctx>,
    ) -> Option<SolverResult<'ctx>> {
        let op_kind = binary_op_to_operator_kind(data.operator)?;
        let needs_autoref = Self::is_comparison_operator(data.operator);

        // For comparison operators, we try borrowed types first, then fall back to value types.
        // This matches Rust's behavior where `a == b` becomes `PartialEq::eq(&a, &b)`.
        // For other operators (arithmetic, bitwise), we only try value types.
        if needs_autoref {
            // Try with autoref (borrowed operands) first
            if let Some(result) = self.solve_binary_method_with_autoref(data, lhs, rhs, op_kind) {
                return Some(result);
            }
        }

        // Fall back to value types (no autoref)
        self.solve_binary_method_value(data, lhs, rhs, op_kind)
    }

    /// Try to resolve binary operator with autoref (implicit borrowing of operands).
    /// This is used for comparison operators where the trait methods take references.
    fn solve_binary_method_with_autoref(
        &mut self,
        data: &BinOpGoalData<'ctx>,
        lhs: Ty<'ctx>,
        rhs: Ty<'ctx>,
        op_kind: OperatorKind,
    ) -> Option<SolverResult<'ctx>> {
        // Create borrowed types for operands
        let lhs_ref = Ty::new(TyKind::Reference(lhs, Mutability::Immutable), self.gcx());
        let rhs_ref = Ty::new(TyKind::Reference(rhs, Mutability::Immutable), self.gcx());

        // Look up operator candidates on the original LHS type (not the reference)
        // because that's where the impl is defined (e.g., `impl PartialEq for string`)
        let candidates = self.lookup_operator_candidates(lhs, op_kind);
        if candidates.is_empty() {
            return None;
        }

        // Filter candidates to those whose parameters expect references
        let mut matching_candidates = Vec::new();
        for candidate in candidates {
            let sig = self.gcx().get_signature(candidate);
            if sig.inputs.len() >= 2 {
                let self_param_ty = sig.inputs[0].ty;
                let rhs_param_ty = sig.inputs[1].ty;

                // Check if the method expects references
                let self_expects_ref = matches!(self_param_ty.kind(), TyKind::Reference(_, _))
                    || matches!(self_param_ty.kind(), TyKind::Parameter(_));
                let rhs_expects_ref = matches!(rhs_param_ty.kind(), TyKind::Reference(_, _))
                    || matches!(rhs_param_ty.kind(), TyKind::Parameter(_));

                // For autoref, we need methods that expect references for both operands
                if self_expects_ref && rhs_expects_ref {
                    // Verify the reference types are compatible
                    let self_compatible = match self_param_ty.kind() {
                        TyKind::Reference(inner, Mutability::Immutable) => {
                            inner == lhs
                                || inner.is_infer()
                                || matches!(inner.kind(), TyKind::Parameter(_))
                        }
                        TyKind::Parameter(_) => true,
                        _ => false,
                    };

                    let rhs_compatible = match rhs_param_ty.kind() {
                        TyKind::Reference(inner, Mutability::Immutable) => {
                            inner == rhs
                                || inner.is_infer()
                                || matches!(inner.kind(), TyKind::Parameter(_))
                        }
                        TyKind::Parameter(_) => true,
                        _ => false,
                    };

                    if self_compatible && rhs_compatible {
                        matching_candidates.push(candidate);
                    }
                }
            }
        }

        if matching_candidates.is_empty() {
            return None;
        }

        // Record borrowing adjustments for both operands
        self.record_adjustments(data.lhs_id, vec![Adjustment::BorrowImmutable]);
        self.record_adjustments(data.rhs_id, vec![Adjustment::BorrowImmutable]);

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
                    instantiation_args: None,
                }),
                source: Some(candidate),
                autoref_cost: 0,
                matches_expectation: false,
                deref_steps: 0,
            });
        }

        let disjunction_goal = Obligation {
            location: data.span,
            goal: Goal::Disjunction(branches),
        };

        // Build the Apply goal with borrowed types
        let apply_goal = Obligation {
            location: data.span,
            goal: Goal::Apply(ApplyGoalData {
                call_node_id: data.node_id,
                call_span: data.span,
                callee_ty: method_ty,
                callee_source: None,
                result_ty: data.rho,
                _expect_ty: data.expectation,
                arguments: vec![
                    ApplyArgument {
                        id: data.lhs_id,
                        label: None,
                        ty: lhs_ref, // Use borrowed type
                        span: data.span,
                    },
                    ApplyArgument {
                        id: data.rhs_id,
                        label: None,
                        ty: rhs_ref, // Use borrowed type
                        span: data.span,
                    },
                ],
                skip_labels: true,
            }),
        };

        Some(SolverResult::Solved(vec![disjunction_goal, apply_goal]))
    }

    /// Try to resolve binary operator with value types (no autoref).
    /// This is the original behavior, used for arithmetic operators and as fallback.
    fn solve_binary_method_value(
        &mut self,
        data: &BinOpGoalData<'ctx>,
        lhs: Ty<'ctx>,
        rhs: Ty<'ctx>,
        op_kind: OperatorKind,
    ) -> Option<SolverResult<'ctx>> {
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
                // Also allow if the parameter type is generic (e.g. Self or Rhs in interface)
                // because we can't easily check equality without instantiation.
                if rhs == rhs_param_ty
                    || rhs.is_infer()
                    || matches!(rhs_param_ty.kind(), TyKind::Parameter(_))
                {
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
                    instantiation_args: None,
                }),
                source: Some(candidate),
                autoref_cost: 0,
                matches_expectation: false,
                deref_steps: 0,
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
                call_node_id: data.node_id,
                call_span: data.span,
                callee_ty: method_ty,
                callee_source: None,
                result_ty: data.rho,
                _expect_ty: data.expectation,
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
                            goal: Goal::Coerce {
                                node_id: data.node_id,
                                from: data.rho,
                                to: exp,
                            },
                        });
                    }
                    return Some(obligations);
                }

                // Eagerly unify inference vars with the concrete side (or with each other)
                if unify_numeric_binop(&mut obligations, lhs, rhs).is_some() {
                    if let Some(exp) = data.expectation {
                        obligations.push(Obligation {
                            location: data.span,
                            goal: Goal::Coerce {
                                node_id: data.node_id,
                                from: data.rho,
                                to: exp,
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
                    (Rune, Rune) => {
                        obligations.push(Obligation {
                            location: data.span,
                            goal: Goal::Equal(data.rho, gcx.types.bool),
                        });
                        return Some(obligations);
                    }
                    // Generic/existential fallback: permit comparison operators when
                    // interface bounds guarantee comparability.
                    //
                    // This keeps generic code like `func geq[T: Ord](a: T, b: T) -> bool`
                    // type-checking even when operand types are type parameters.
                    _ if lhs == rhs => {
                        let has_bound = |interface_name: &str| -> bool {
                            let Some(interface_id) = gcx.find_std_type(interface_name) else {
                                return false;
                            };

                            let mut bounds = self.bounds_for_type_in_scope(lhs);
                            if let TyKind::BoxedExistential { interfaces } = lhs.kind() {
                                bounds.extend_from_slice(interfaces);
                            }

                            bounds.into_iter().any(|bound| {
                                self.collect_interface_with_supers(bound)
                                    .into_iter()
                                    .any(|iface| iface.id == interface_id)
                            })
                        };

                        let allowed = match data.operator {
                            Eql | Neq => has_bound("PartialEq"),
                            Lt | Gt | Leq | Geq => has_bound("Ord"),
                            _ => false,
                        };

                        if allowed {
                            obligations.push(Obligation {
                                location: data.span,
                                goal: Goal::Equal(data.rho, gcx.types.bool),
                            });
                            return Some(obligations);
                        }
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

impl<'ctx> ConstraintSolver<'ctx> {
    pub fn solve_assign_op(&mut self, data: AssignOpGoalData<'ctx>) -> SolverResult<'ctx> {
        let lhs = self.structurally_resolve(data.lhs);
        let rhs = self.structurally_resolve(data.rhs);

        if lhs.is_error() || rhs.is_error() {
            return SolverResult::Solved(vec![]);
        }

        // If LHS type is not yet resolved, defer
        if lhs.is_infer() {
            return SolverResult::Deferred;
        }

        // Try intrinsic resolution first (primitives: a += b becomes a = a + b)
        if let Some(obligations) = self.solve_assign_op_intrinsic(&data, lhs, rhs) {
            return SolverResult::Solved(obligations);
        }

        // Try operator method resolution (e.g., AddAssign)
        if let Some(result) = self.solve_assign_op_method(&data, lhs, rhs) {
            return result;
        }

        // No intrinsic or method found
        SolverResult::Error(vec![Spanned::new(
            TypeError::InvalidAssignOp {
                op: data.operator,
                lhs,
                rhs,
            },
            data.span,
        )])
    }

    fn solve_assign_op_method(
        &mut self,
        data: &AssignOpGoalData<'ctx>,
        lhs: Ty<'ctx>,
        rhs: Ty<'ctx>,
    ) -> Option<SolverResult<'ctx>> {
        let op_kind = binary_op_to_assign_operator_kind(data.operator)?;

        // Look up assign operator candidates on the LHS type
        let candidates = self.lookup_operator_candidates(lhs, op_kind);
        if candidates.is_empty() {
            return None;
        }

        // Compound assignment operators take &self (mutable reference)
        // Create the reference type for matching
        let lhs_ref_ty = Ty::new(TyKind::Reference(lhs, Mutability::Mutable), self.gcx());

        // Filter candidates to those whose first parameter is &mut T and RHS matches
        let mut matching_candidates = Vec::new();
        for candidate in candidates {
            let sig = self.gcx().get_signature(candidate);
            // Assign operator methods have signature: (&self, rhs: Rhs) -> void
            if sig.inputs.len() >= 2 {
                let self_param_ty = sig.inputs[0].ty;
                let rhs_param_ty = sig.inputs[1].ty;

                // Check if self parameter is &mut T
                let self_matches = self_param_ty == lhs_ref_ty;
                // Check if RHS parameter matches
                let rhs_matches = rhs == rhs_param_ty || rhs.is_infer();

                if self_matches && rhs_matches {
                    matching_candidates.push(candidate);
                }
            }
        }

        if matching_candidates.is_empty() {
            return None;
        }

        // Record that we need to take a mutable reference of the LHS
        self.record_adjustments(data.lhs_id, vec![Adjustment::BorrowMutable]);

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
                    instantiation_args: None,
                }),
                source: Some(candidate),
                autoref_cost: 0,
                matches_expectation: false,
                deref_steps: 0,
            });
        }

        let disjunction_goal = Obligation {
            location: data.span,
            goal: Goal::Disjunction(branches),
        };

        // Build the Apply goal: call the assign operator method with `&self` and `rhs`
        // Assign ops return void
        let apply_goal = Obligation {
            location: data.span,
            goal: Goal::Apply(ApplyGoalData {
                call_node_id: data.node_id,
                call_span: data.span,
                callee_ty: method_ty,
                callee_source: None,
                result_ty: self.gcx().types.void,
                _expect_ty: None,
                arguments: vec![
                    ApplyArgument {
                        id: data.lhs_id,
                        label: None,
                        ty: lhs_ref_ty, // Pass &mut T instead of T
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

    /// Try to resolve intrinsic compound assignment operations on primitives.
    /// For primitives, `a += b` is equivalent to `a = a + b`.
    fn solve_assign_op_intrinsic(
        &self,
        data: &AssignOpGoalData<'ctx>,
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

        let mut obligations = vec![];

        match data.operator {
            // Arithmetic compound assignment: +=, -=, *=, /=, %=
            Add | Sub | Mul | Div | Rem => {
                // Same concrete numeric types
                if is_same_int(lhs, rhs) || is_same_float(lhs, rhs) {
                    return Some(obligations);
                }

                // Handle inference variables
                match (lhs.kind(), rhs.kind()) {
                    // Concrete LHS with inference RHS
                    (Int(_) | UInt(_), Infer(IntVar(_))) | (Float(_), Infer(FloatVar(_))) => {
                        obligations.push(Obligation {
                            location: data.span,
                            goal: Goal::Equal(rhs, lhs),
                        });
                        return Some(obligations);
                    }
                    // LHS inference var with concrete RHS - bind LHS to RHS type
                    (Infer(IntVar(_)), Int(_) | UInt(_)) | (Infer(FloatVar(_)), Float(_)) => {
                        obligations.push(Obligation {
                            location: data.span,
                            goal: Goal::Equal(lhs, rhs),
                        });
                        return Some(obligations);
                    }
                    // Both inference vars of same kind
                    (Infer(IntVar(_)), Infer(IntVar(_)))
                    | (Infer(FloatVar(_)), Infer(FloatVar(_))) => {
                        obligations.push(Obligation {
                            location: data.span,
                            goal: Goal::Equal(lhs, rhs),
                        });
                        return Some(obligations);
                    }
                    _ => {}
                }
            }

            // Bitwise compound assignment: &=, |=, ^=, <<=, >>=
            BitAnd | BitOr | BitXor => {
                // Boolean bitwise
                if matches!((lhs.kind(), rhs.kind()), (Bool, Bool)) {
                    return Some(obligations);
                }

                // Integer bitwise
                if is_same_int(lhs, rhs) {
                    return Some(obligations);
                }

                match (lhs.kind(), rhs.kind()) {
                    (Int(_) | UInt(_), Infer(IntVar(_))) => {
                        obligations.push(Obligation {
                            location: data.span,
                            goal: Goal::Equal(rhs, lhs),
                        });
                        return Some(obligations);
                    }
                    (Infer(IntVar(_)), Int(_) | UInt(_)) => {
                        obligations.push(Obligation {
                            location: data.span,
                            goal: Goal::Equal(lhs, rhs),
                        });
                        return Some(obligations);
                    }
                    (Infer(IntVar(_)), Infer(IntVar(_))) => {
                        obligations.push(Obligation {
                            location: data.span,
                            goal: Goal::Equal(lhs, rhs),
                        });
                        return Some(obligations);
                    }
                    _ => {}
                }
            }

            // Shift compound assignment: <<=, >>=
            BitShl | BitShr => {
                match (lhs.kind(), rhs.kind()) {
                    // LHS must be integer; RHS can be any integer
                    (Int(_) | UInt(_), Int(_) | UInt(_) | Infer(IntVar(_))) => {
                        return Some(obligations);
                    }
                    (Infer(IntVar(_)), Int(_) | UInt(_) | Infer(IntVar(_))) => {
                        return Some(obligations);
                    }
                    _ => {}
                }
            }

            // These operators don't have compound assignment forms
            Eql | Neq | Lt | Gt | Leq | Geq | BoolAnd | BoolOr | PtrEq => {}
        }

        None
    }
}
