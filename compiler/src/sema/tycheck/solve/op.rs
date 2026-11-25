use crate::sema::tycheck::utils::literal::integer_expression_literal_fits;
#[cfg(test)]
mod g38_tests;
#[cfg(test)]
mod tests;
use crate::{
    hir::{BinaryOperator, NodeID, OperatorKind, UnaryOperator},
    sema::{
        error::TypeError,
        models::{AliasKind, InferTy, Ty, TyKind},
        tycheck::solve::{
            ApplyArgument, AssignOpGoalData, BinOpGoalData, ConstraintSolver, Goal, MethodCallData,
            Obligation, SolverResult, UnOpGoalData,
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
        // Membership resolves through `Contains` with swapped operands.
        BinaryOperator::In | BinaryOperator::NotIn => None,
        // Not overloadable
        BinaryOperator::BoolAnd
        | BinaryOperator::BoolOr
        | BinaryOperator::IdentityEql
        | BinaryOperator::IdentityNeq => None,
    }
}

/// Whether a numeric literal variable can take the concrete type `ty`.
/// Two literals already default to the same type.
fn literal_accepts(var: Ty<'_>, ty: Ty<'_>) -> bool {
    match var.kind() {
        TyKind::Infer(InferTy::IntVar(_)) => matches!(ty.kind(), TyKind::Int(_) | TyKind::UInt(_)),
        TyKind::Infer(InferTy::FloatVar(_)) => matches!(ty.kind(), TyKind::Float(_)),
        _ => false,
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
        BinaryOperator::IdentityEql
        | BinaryOperator::IdentityNeq
        | BinaryOperator::Eql
        | BinaryOperator::Neq
        | BinaryOperator::Lt
        | BinaryOperator::Gt
        | BinaryOperator::Leq
        | BinaryOperator::Geq
        | BinaryOperator::BoolAnd
        | BinaryOperator::BoolOr
        | BinaryOperator::In
        | BinaryOperator::NotIn => None,
    }
}

impl<'ctx> ConstraintSolver<'ctx> {
    fn operator_method_name_for_kind(kind: OperatorKind) -> Option<&'static str> {
        match kind {
            OperatorKind::Add => Some("add"),
            OperatorKind::AddAssign => Some("addAssign"),
            OperatorKind::Sub => Some("sub"),
            OperatorKind::SubAssign => Some("subAssign"),
            OperatorKind::Mul => Some("mul"),
            OperatorKind::MulAssign => Some("mulAssign"),
            OperatorKind::Div => Some("div"),
            OperatorKind::DivAssign => Some("divAssign"),
            OperatorKind::Rem => Some("rem"),
            OperatorKind::RemAssign => Some("remAssign"),
            OperatorKind::BitAnd => Some("bitand"),
            OperatorKind::BitAndAssign => Some("bitandAssign"),
            OperatorKind::BitOr => Some("bitor"),
            OperatorKind::BitOrAssign => Some("bitorAssign"),
            OperatorKind::BitXor => Some("bitxor"),
            OperatorKind::BitXorAssign => Some("bitxorAssign"),
            OperatorKind::BitShl => Some("shl"),
            OperatorKind::BitShlAssign => Some("shlAssign"),
            OperatorKind::BitShr => Some("shr"),
            OperatorKind::BitShrAssign => Some("shrAssign"),
            OperatorKind::Neg => Some("neg"),
            OperatorKind::Not => Some("not"),
            OperatorKind::BitwiseNot => Some("bitnot"),
            OperatorKind::Eq => Some("eq"),
            OperatorKind::Neq => Some("neq"),
            OperatorKind::Lt => Some("lt"),
            OperatorKind::Gt => Some("gt"),
            OperatorKind::Leq => Some("le"),
            OperatorKind::Geq => Some("ge"),
            OperatorKind::Contains => Some("contains"),
            OperatorKind::BoolAnd | OperatorKind::BoolOr => None,
        }
    }

    fn check_integer_literal_fit(&self, node_id: NodeID, ty: Ty<'ctx>, span: crate::span::Span) {
        let Some(value) = self.integer_literal_value(node_id) else {
            return;
        };

        if integer_expression_literal_fits(value, ty) {
            return;
        }

        let gcx = self.gcx();
        gcx.dcx().emit_error(
            format!(
                "integer literal '{}' is out of range for type '{}'",
                value,
                ty.format(gcx)
            )
            .into(),
            Some(span),
        );
    }

    pub fn solve_unary(&mut self, data: UnOpGoalData<'ctx>) -> SolverResult<'ctx> {
        let ty = self.structurally_resolve(data.lhs);

        if ty.is_error() {
            let obligation = Obligation {
                location: data.span,
                goal: Goal::Equal(data.rho, Ty::error(self.gcx())),
            };
            return SolverResult::Solved(vec![obligation]);
        }

        // Numeric literal vars are handled by the intrinsics, which tie the
        // result to the operand var so `-56` stays an int literal var instead
        // of defaulting to int32. Any other unresolved type defers.
        if ty.contains_inference() {
            if matches!(
                ty.kind(),
                TyKind::Infer(InferTy::IntVar(_) | InferTy::FloatVar(_))
            ) && let Some(obligations) = self.solve_unary_intrinsic(&data, ty)
            {
                return SolverResult::Solved(obligations);
            }
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
        self.solve_operator_method(
            unary_op_to_operator_kind(data.operator)?,
            data.node_id,
            ApplyArgument {
                is_spread: false,
                is_lazy_wrapped: false,
                contains_await: false,
                deferred_return_scope: None,
                id: data.rhs_id,
                label: None,
                ty: operand_ty,
                span: data.span,
            },
            data.receiver_addressable,
            vec![],
            data.rho,
        )
    }

    /// Operator syntax selects its language interface, then uses ordinary
    /// receiver discovery and argument passing. The RHS is a value argument;
    /// only the receiver can acquire an address through normal autoref.
    fn solve_operator_method(
        &mut self,
        kind: OperatorKind,
        node_id: NodeID,
        receiver: ApplyArgument<'ctx>,
        receiver_addressable: bool,
        arguments: Vec<ApplyArgument<'ctx>>,
        result: Ty<'ctx>,
    ) -> Option<SolverResult<'ctx>> {
        let item = crate::hir::StdItem::from_operator_kind(kind)?;
        self.gcx().std_item_def(item)?;
        let name = Self::operator_method_name_for_kind(kind)?;
        Some(self.solve_method_call(MethodCallData {
            interface: Some(item),
            receiver_addressable,
            selected: None,
            pending_selection: None,
            node_id,
            receiver: receiver.ty,
            reciever_span: receiver.span,
            reciever_node: receiver.id,
            is_unsafe_context: false,
            name: crate::span::Identifier {
                symbol: self.gcx().intern_symbol(name),
                span: receiver.span,
            },
            arguments,
            result,
            method_ty: None,
            prefer_async: false,
            span: receiver.span,
        }))
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
    /// An unresolved associated type can still determine the other operand's
    /// numeric width once its receiver is known. A nominal operand with open
    /// arguments can already participate in ordinary operator lookup.
    pub(super) fn operand_awaits_type(&self, ty: Ty<'ctx>) -> bool {
        ty.is_ty_var()
            || matches!(ty.kind(), TyKind::Alias { kind: AliasKind::Projection, .. }
                if super::has_unresolvable_projection(&self.icx, ty))
    }

    pub fn solve_binary(&mut self, data: BinOpGoalData<'ctx>) -> SolverResult<'ctx> {
        if matches!(data.operator, BinaryOperator::In | BinaryOperator::NotIn) {
            return self.solve_membership(data);
        }
        let lhs = self.structurally_resolve(data.lhs);
        let rhs = self.structurally_resolve(data.rhs);

        if lhs.is_error() || rhs.is_error() {
            let obligation = Obligation {
                location: data.span,
                goal: Goal::Equal(data.rho, Ty::error(self.gcx())),
            };
            return SolverResult::Solved(vec![obligation]);
        }

        if self.operand_awaits_type(lhs) || self.operand_awaits_type(rhs) {
            return SolverResult::Deferred;
        }

        // Preserve `opt == nil`, `nil == opt`, `opt != nil`, `nil != opt` even
        // when the wrapped payload does not conform to `PartialEq`.
        if data.has_nil_operand
            && matches!(data.operator, BinaryOperator::Eql | BinaryOperator::Neq)
            && self.unwrap_optional_type(lhs).is_some()
            && self.unwrap_optional_type(rhs).is_some()
        {
            return SolverResult::Solved(vec![
                Obligation {
                    location: data.span,
                    goal: Goal::Equal(lhs, rhs),
                },
                Obligation {
                    location: data.span,
                    goal: Goal::Equal(data.rho, self.gcx().types.bool),
                },
            ]);
        }

        // If LHS is unresolved, defer — unless it is a numeric literal var,
        // which the intrinsic arms can still make progress on (e.g. `0 - 1`
        // ties both literal vars together and stays a literal var instead of
        // waiting for int defaulting).
        if lhs.is_infer() {
            if matches!(
                lhs.kind(),
                TyKind::Infer(InferTy::IntVar(_) | InferTy::FloatVar(_))
            ) && let Some(obligations) = self.solve_binary_intrinsic(&data, lhs, rhs)
            {
                return SolverResult::Solved(obligations);
            }
            return SolverResult::Deferred;
        }

        if matches!(
            data.operator,
            BinaryOperator::IdentityEql | BinaryOperator::IdentityNeq
        ) && self.gcx().is_class_type(lhs)
            && self.gcx().is_class_type(rhs)
        {
            return SolverResult::Solved(vec![Obligation {
                location: data.span,
                goal: Goal::Equal(data.rho, self.gcx().types.bool),
            }]);
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

    /// `element in container` calls `container.contains(&element)` through
    /// `std::ops::Contains[Element]`. The container is the receiver, so it
    /// selects the conformance; the element is passed by reference, so the
    /// test neither copies it nor asks the caller to write `&`. `!in` negates
    /// the same call. Both yield `bool`.
    fn solve_membership(&mut self, data: BinOpGoalData<'ctx>) -> SolverResult<'ctx> {
        let element = self.structurally_resolve(data.lhs);
        let container = self.structurally_resolve(data.rhs);
        let gcx = self.gcx();

        if element.is_error() || container.is_error() {
            return SolverResult::Solved(vec![Obligation {
                location: data.span,
                goal: Goal::Equal(data.rho, Ty::error(gcx)),
            }]);
        }

        // A literal container (`x in 0..n`, `code in [200, 204]`) takes its
        // numeric element type from the tested value, as `x == 0` does, rather
        // than from the literal's own default.
        if let Some(container_element) = self.literal_container_element(container)
            && literal_accepts(container_element, element)
        {
            return SolverResult::Solved(vec![
                Obligation {
                    location: data.span,
                    goal: Goal::Equal(container_element, element),
                },
                Obligation {
                    location: data.span,
                    goal: Goal::BinaryOp(data),
                },
            ]);
        }

        // Wait for the container's own type, including literal defaults,
        // before looking up its conformance.
        if container.contains_inference() {
            return SolverResult::Deferred;
        }

        let invalid = || {
            // Name a bare literal by the type it would default to.
            let element = match element.kind() {
                TyKind::Infer(InferTy::IntVar(_)) => gcx.types.int32,
                TyKind::Infer(InferTy::FloatVar(_)) => gcx.types.float64,
                _ => element,
            };
            SolverResult::Error(vec![Spanned::new(
                TypeError::InvalidMembership {
                    op: data.operator,
                    element,
                    container,
                },
                data.span,
            )])
        };
        let Some(contains) = gcx.std_item_def(crate::hir::StdItem::Contains) else {
            return invalid();
        };
        if !element.contains_inference() {
            let interface = crate::sema::models::InterfaceReference {
                id: contains,
                arguments: gcx.store.interners.intern_generic_args(vec![
                    crate::sema::models::GenericArgument::Type(container),
                    crate::sema::models::GenericArgument::Type(element),
                ]),
                bindings: &[],
            };
            match self.solve_conforms(data.span, container, interface) {
                SolverResult::Error(_) => return invalid(),
                SolverResult::Deferred => return SolverResult::Deferred,
                SolverResult::Solved(_) => {}
            }
        }

        let result = self.solve_operator_method(
            OperatorKind::Contains,
            data.node_id,
            ApplyArgument {
                is_spread: false,
                is_lazy_wrapped: false,
                contains_await: false,
                deferred_return_scope: None,
                id: data.rhs_id,
                label: None,
                ty: container,
                span: data.span,
            },
            data.receiver_addressable,
            vec![ApplyArgument {
                is_spread: false,
                is_lazy_wrapped: false,
                contains_await: false,
                deferred_return_scope: None,
                id: data.lhs_id,
                label: None,
                ty: Ty::new(TyKind::Reference(element), gcx),
                span: data.span,
            }],
            data.rho,
        );
        match result {
            None | Some(SolverResult::Error(_)) => invalid(),
            Some(result) => result,
        }
    }

    /// The element type of a container that literal syntax can produce:
    /// ranges, List, array, Span and Dictionary keys.
    fn literal_container_element(&self, container: Ty<'ctx>) -> Option<Ty<'ctx>> {
        use crate::hir::StdItem;
        let gcx = self.gcx();
        let element = match container.kind() {
            TyKind::Array { element, .. } => element,
            TyKind::Adt(def, args) => {
                let literal = [
                    StdItem::Range,
                    StdItem::ClosedRange,
                    StdItem::RangeFrom,
                    StdItem::RangeTo,
                    StdItem::RangeToInclusive,
                    StdItem::List,
                    StdItem::Span,
                    StdItem::Dictionary,
                ]
                .into_iter()
                .any(|item| gcx.std_item_def(item) == Some(def.id));
                if !literal {
                    return None;
                }
                args.first()?.ty()?
            }
            _ => return None,
        };
        Some(self.structurally_resolve(element))
    }

    fn solve_binary_method(
        &mut self,
        data: &BinOpGoalData<'ctx>,
        lhs: Ty<'ctx>,
        rhs: Ty<'ctx>,
    ) -> Option<SolverResult<'ctx>> {
        self.solve_operator_method(
            binary_op_to_operator_kind(data.operator)?,
            data.node_id,
            ApplyArgument {
                is_spread: false,
                is_lazy_wrapped: false,
                contains_await: false,
                deferred_return_scope: None,
                id: data.lhs_id,
                label: None,
                ty: lhs,
                span: data.span,
            },
            data.receiver_addressable,
            vec![ApplyArgument {
                is_spread: false,
                is_lazy_wrapped: false,
                contains_await: false,
                deferred_return_scope: None,
                id: data.rhs_id,
                label: None,
                ty: rhs,
                span: data.span,
            }],
            data.rho,
        )
    }
}

impl<'ctx> ConstraintSolver<'ctx> {
    /// Try to resolve “intrinsic” binary operations on primitives without invoking overloads.
    /// Returns Some(obligations) if handled intrinsically; None to fall back to overload search.
    fn solve_binary_intrinsic(
        &mut self,
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

        let check_literal_fit = |node_id: NodeID, ty: Ty<'ctx>| {
            self.check_integer_literal_fit(node_id, ty, data.span);
        };

        if matches!(lhs.kind(), Int(_) | UInt(_)) {
            check_literal_fit(data.lhs_id, lhs);
        }
        if matches!(rhs.kind(), Int(_) | UInt(_)) {
            check_literal_fit(data.rhs_id, rhs);
        }

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
                        check_literal_fit(data.lhs_id, lhs);
                        check_literal_fit(data.rhs_id, lhs);
                        Some(())
                    }
                    (Float(_), Infer(FloatVar(_))) => {
                        obligations.push(Obligation {
                            location: data.span,
                            goal: Goal::Equal(rhs, lhs),
                        });
                        push_rho_eq(obligations, lhs);
                        Some(())
                    }

                    // IntVar ⨉ concrete ⇒ bind IntVar to concrete, result = concrete
                    (Infer(IntVar(_)), Int(_) | UInt(_)) => {
                        obligations.push(Obligation {
                            location: data.span,
                            goal: Goal::Equal(lhs, rhs),
                        });
                        push_rho_eq(obligations, rhs);
                        check_literal_fit(data.lhs_id, rhs);
                        check_literal_fit(data.rhs_id, rhs);
                        Some(())
                    }
                    (Infer(FloatVar(_)), Float(_)) => {
                        obligations.push(Obligation {
                            location: data.span,
                            goal: Goal::Equal(lhs, rhs),
                        });
                        push_rho_eq(obligations, rhs);
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

        // Integer-only variant used by bitwise operators.
        let unify_integer_binop =
            |obligations: &mut Vec<_>, lhs: Ty<'ctx>, rhs: Ty<'ctx>| -> Option<()> {
                match (lhs.kind(), rhs.kind()) {
                    (Int(_) | UInt(_), Infer(IntVar(_))) => {
                        obligations.push(Obligation {
                            location: data.span,
                            goal: Goal::Equal(rhs, lhs),
                        });
                        push_rho_eq(obligations, lhs);
                        check_literal_fit(data.lhs_id, lhs);
                        check_literal_fit(data.rhs_id, lhs);
                        Some(())
                    }
                    (Infer(IntVar(_)), Int(_) | UInt(_)) => {
                        obligations.push(Obligation {
                            location: data.span,
                            goal: Goal::Equal(lhs, rhs),
                        });
                        push_rho_eq(obligations, rhs);
                        check_literal_fit(data.lhs_id, rhs);
                        check_literal_fit(data.rhs_id, rhs);
                        Some(())
                    }
                    (Infer(IntVar(_)), Infer(IntVar(_))) => {
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
            IdentityEql | IdentityNeq | In | NotIn => return None,
            Add | Sub | Mul | Div | Rem => {
                // Fast path: both sides already same concrete numeric type
                if is_same_int(lhs, rhs) || is_same_float(lhs, rhs) {
                    push_rho_eq(&mut obligations, lhs);
                    return Some(obligations);
                }

                // Eagerly unify inference vars with the concrete side (or with each other)
                if unify_numeric_binop(&mut obligations, lhs, rhs).is_some() {
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

                // Bitwise & shift ops: both operands must be the same integer type.
                // Eagerly unify an IntVar operand to the concrete side so that
                // literals like `x << 1` infer the `1` as the same type as `x`.
                if is_same_int(lhs, rhs) {
                    push_rho_eq(&mut obligations, lhs);
                    return Some(obligations);
                }
                if unify_integer_binop(&mut obligations, lhs, rhs).is_some() {
                    return Some(obligations);
                }
                // else: not intrinsic
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
                    _ => { /* not intrinsic */ }
                }
            }
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

        // A pending RHS can still supply the numeric type of a literal LHS.
        // `var total = 0; total += wide` binds total through the intrinsic.
        if self.operand_awaits_type(lhs) || self.operand_awaits_type(rhs) {
            return SolverResult::Deferred;
        }
        if let Some(obligations) = self.solve_assign_op_intrinsic(&data, lhs, rhs) {
            return SolverResult::Solved(obligations);
        }
        if lhs.is_infer() {
            // Custom operators require the receiver's eventual type.
            return SolverResult::Deferred;
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
        self.solve_operator_method(
            binary_op_to_assign_operator_kind(data.operator)?,
            data.node_id,
            ApplyArgument {
                is_spread: false,
                is_lazy_wrapped: false,
                contains_await: false,
                deferred_return_scope: None,
                id: data.lhs_id,
                label: None,
                ty: lhs,
                span: data.span,
            },
            data.receiver_addressable,
            vec![ApplyArgument {
                is_spread: false,
                is_lazy_wrapped: false,
                contains_await: false,
                deferred_return_scope: None,
                id: data.rhs_id,
                label: None,
                ty: rhs,
                span: data.span,
            }],
            self.gcx().types.void,
        )
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
            IdentityEql | IdentityNeq | In | NotIn => return None,
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

            // Bitwise compound assignment: &=, |=, ^=, <<=, >>=. As with the
            // binary operators, shifts take an amount of the operand's own
            // integer type, so `x <<= 1` infers `1` as the type of `x`.
            BitAnd | BitOr | BitXor | BitShl | BitShr => {
                // Boolean bitwise
                if matches!(data.operator, BitAnd | BitOr | BitXor)
                    && matches!((lhs.kind(), rhs.kind()), (Bool, Bool))
                {
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

            // These operators don't have compound assignment forms
            Eql | Neq | Lt | Gt | Leq | Geq | BoolAnd | BoolOr => {}
        }

        None
    }
}
