use crate::{
    compile::context::Gcx,
    hir::{self, DefinitionID, NodeID, Resolution},
    sema::{
        models::{Ty, TyKind},
        resolve::models::DefinitionKind,
        tycheck::{
            check::checker::{Checker, PlaceInfo, PlaceKind},
            solve::{
                ApplyArgument, ApplyGoalData, BinOpGoalData, BindOverloadGoalData,
                ConstraintSystem, DisjunctionBranch, Goal, UnOpGoalData,
            },
        },
    },
    span::Span,
};

impl<'ctx> Checker<'ctx> {
    pub fn gcx(&self) -> Gcx<'ctx> {
        self.context
    }

    pub fn check_function(mut self, id: DefinitionID, node: &hir::Function) {
        let gcx = self.gcx();
        println!("==============================================================");
        let signature = gcx.get_signature(id);
        let signature = Ty::from_labeled_signature(gcx, signature);

        let (param_tys, return_ty) = match signature.kind() {
            TyKind::FnPointer { inputs, output, .. } => (inputs, output),
            _ => unreachable!("function signature must be of function pointer type"),
        };

        self.return_ty = Some(return_ty);

        // Add Parameters To Locals Map
        for (parameter, &parameter_ty) in node.signature.prototype.inputs.iter().zip(param_tys) {
            self.locals.borrow_mut().insert(
                parameter.id,
                crate::sema::tycheck::check::checker::LocalBinding {
                    ty: parameter_ty,
                    mutable: false,
                },
            );
        }

        let Some(body) = &node.block else {
            unreachable!("ICE: Checking Function without Body")
        };

        if let Some(body) = hir::is_expression_bodied(body) {
            // --- single-expression body ---
            // TODO: Mark As return
            self.check_return(body);
        } else {
            // --- regular block body ---
            self.check_block(body);
        }
    }
}

impl<'ctx> Checker<'ctx> {
    fn synth_if_expression(
        &self,
        expression: &hir::Expression,
        node: &hir::IfExpression,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        // Condition must be bool.
        let cond_ty = self.synth(&node.condition, cs);
        cs.equal(self.gcx().types.bool, cond_ty, node.condition.span);

        // then/else branches are expressions; typecheck with shared expectation.
        let then_ty = self.synth_with_expectation(&node.then_block, expectation, cs);
        let else_ty = if let Some(else_expr) = &node.else_block {
            let else_expectation = expectation.or(Some(then_ty));
            Some(self.synth_with_expectation(else_expr, else_expectation, cs))
        } else {
            None
        };

        match else_ty {
            Some(else_ty) => {
                // Branches must agree.
                cs.equal(
                    then_ty,
                    else_ty,
                    node.else_block
                        .as_ref()
                        .map(|e| e.span)
                        .unwrap_or(node.then_block.span),
                );
                then_ty
            }
            None => {
                // No else: coerce the then branch into the expected type if provided,
                // otherwise use void/unit.
                if let Some(exp) = expectation {
                    cs.add_goal(
                        Goal::Coerce {
                            from: then_ty,
                            to: exp,
                        },
                        expression.span,
                    );
                    exp
                } else {
                    self.gcx().types.void
                }
            }
        }
    }

    fn synth_unary_expression(
        &self,
        expression: &hir::Expression,
        operator: hir::UnaryOperator,
        operand: &hir::Expression,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let operand_ty = self.synth(operand, cs);
        let result_ty = cs.infer_cx.next_ty_var(expression.span);

        let data = UnOpGoalData {
            lhs: operand_ty,
            rho: result_ty,
            expectation,
            operator,
            span: expression.span,
            node_id: expression.id,
            rhs_id: operand.id,
        };

        cs.add_goal(Goal::UnaryOp(data), expression.span);
        result_ty
    }

    fn synth_binary_expression(
        &self,
        expression: &hir::Expression,
        operator: hir::BinaryOperator,
        lhs: &hir::Expression,
        rhs: &hir::Expression,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let lhs_ty = self.synth(lhs, cs);
        let rhs_ty = self.synth(rhs, cs);
        let result_ty = cs.infer_cx.next_ty_var(expression.span);

        let data = BinOpGoalData {
            lhs: lhs_ty,
            rhs: rhs_ty,
            rho: result_ty,
            expectation,
            operator,
            span: expression.span,
            assigning: false,
        };

        cs.add_goal(Goal::BinaryOp(data), expression.span);
        result_ty
    }
}

impl<'ctx> Checker<'ctx> {
    fn check_statement(&self, node: &hir::Statement) {
        match &node.kind {
            hir::StatementKind::Declaration(..) => return,
            hir::StatementKind::Expression(node) => {
                self.top_level_check(node, None);
            }
            hir::StatementKind::Variable(node) => {
                self.check_local(node);
            }
            hir::StatementKind::Break => self.check_break(node.span),
            hir::StatementKind::Continue => self.check_continue(node.span),
            hir::StatementKind::Return(expression) => {
                if let Some(expression) = expression {
                    self.check_return(expression);
                }
            }
            hir::StatementKind::Loop { block, .. } => {
                self.check_loop(block);
            }
            hir::StatementKind::Defer(..) => todo!(),
            hir::StatementKind::Guard { .. } => todo!(),
        }

        return;
    }

    fn check_return(&self, node: &hir::Expression) {
        let Some(expectation) = self.return_ty else {
            unreachable!("ICE: return check called outside function body")
        };
        self.top_level_check(node, Some(expectation));
    }

    fn check_block(&self, node: &hir::Block) {
        for statement in &node.statements {
            self.check_statement(statement);
        }
    }

    fn check_local(&self, node: &hir::Local) {
        let expectation = node.ty.as_ref().map(|n| self.lower_type(n));
        match &node.pattern.kind {
            hir::PatternKind::Wildcard => todo!(),
            hir::PatternKind::Identifier(_) => {
                if let Some(expression) = &node.initializer {
                    // Hard code for now
                    let ty = self.top_level_check(expression, expectation);
                    let binding = crate::sema::tycheck::check::checker::LocalBinding {
                        ty,
                        mutable: node.mutability == hir::Mutability::Mutable,
                    };
                    self.set_local(node.pattern.id, binding);
                    self.set_local(node.id, binding);
                    self.gcx().cache_node_type(node.pattern.id, ty);
                    self.gcx().cache_node_type(node.id, ty);
                }
            }
            hir::PatternKind::Tuple(..) => todo!(),
            _ => unreachable!("ICE – invalid let statement pattern"),
        }
    }

    fn check_loop(&self, block: &hir::Block) {
        let depth = self.loop_depth.get();
        self.loop_depth.set(depth + 1);
        self.check_block(block);
        self.loop_depth.set(depth);
    }

    fn check_break(&self, span: Span) {
        if self.loop_depth.get() == 0 {
            self.gcx()
                .dcx()
                .emit_error("`break` used outside of a loop".into(), Some(span));
        }
    }

    fn check_continue(&self, span: Span) {
        if self.loop_depth.get() == 0 {
            self.gcx()
                .dcx()
                .emit_error("`continue` used outside of a loop".into(), Some(span));
        }
    }
}

impl<'ctx> Checker<'ctx> {
    fn top_level_check(
        &self,
        expression: &hir::Expression,
        expectation: Option<Ty<'ctx>>,
    ) -> Ty<'ctx> {
        let mut cs = Cs::new(self.context);
        let provided = self.synth_with_expectation(expression, expectation, &mut cs);
        if let Some(expectation) = expectation {
            cs.equal(expectation, provided, expression.span);
        }
        cs.solve_all();

        for (id, ty) in cs.resolved_expr_types() {
            self.gcx().cache_node_type(id, ty);
        }

        let provided = cs.infer_cx.resolve_vars_if_possible(provided);
        if provided.is_infer() {
            return Ty::error(self.gcx());
        }
        provided
    }
}

type Cs<'c> = ConstraintSystem<'c>;
impl<'ctx> Checker<'ctx> {
    fn synth_with_expectation(
        &self,
        node: &hir::Expression,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let ty = self.synth_expression_kind(node, expectation, cs);
        cs.record_expr_ty(node.id, ty);
        self.gcx().dcx().emit_info(
            format!("Checked {}", ty.format(self.gcx())),
            Some(node.span),
        );
        ty
    }

    fn synth(&self, node: &hir::Expression, cs: &mut Cs<'ctx>) -> Ty<'ctx> {
        self.synth_with_expectation(node, None, cs)
    }

    fn synth_expression_kind(
        &self,
        expression: &hir::Expression,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        match &expression.kind {
            hir::ExpressionKind::Literal(node) => {
                self.synth_expression_literal(node, expectation, cs)
            }
            hir::ExpressionKind::Identifier(_, resolution) => {
                self.synth_identifier_expression(expression.id, expression.span, resolution, cs)
            }
            hir::ExpressionKind::Call(callee, arguments) => {
                self.synth_call_expression(expression, callee, arguments, expectation, cs)
            }
            hir::ExpressionKind::Member { .. } => todo!(),
            hir::ExpressionKind::Specialize { .. } => todo!(),
            hir::ExpressionKind::Array(..) => todo!(),
            hir::ExpressionKind::Tuple(..) => todo!(),
            hir::ExpressionKind::If(expr) => {
                self.synth_if_expression(expression, expr, expectation, cs)
            }
            hir::ExpressionKind::Match(..) => todo!(),
            hir::ExpressionKind::Reference(..) => todo!(),
            hir::ExpressionKind::Dereference(..) => todo!(),
            hir::ExpressionKind::Binary(op, lhs, rhs) => {
                self.synth_binary_expression(expression, *op, lhs, rhs, expectation, cs)
            }
            hir::ExpressionKind::Unary(op, operand) => {
                self.synth_unary_expression(expression, *op, operand, expectation, cs)
            }
            hir::ExpressionKind::TupleAccess(..) => todo!(),
            hir::ExpressionKind::AssignOp(..) => todo!(),
            hir::ExpressionKind::Assign(lhs, rhs) => {
                self.synth_assign_expression(expression, lhs, rhs, cs)
            }
            hir::ExpressionKind::CastAs(..) => todo!(),
            hir::ExpressionKind::PatternBinding(..) => todo!(),
            hir::ExpressionKind::Block(block) => {
                self.synth_block_expression(block, expectation, cs)
            }
            hir::ExpressionKind::Malformed => {
                unreachable!("ICE: trying to typecheck a malformed expression node")
            }
        }
    }
}

impl<'ctx> Checker<'ctx> {
    /// Classify an expression that appears on the left-hand side of an assignment.
    /// Returns its type, mutability, and a minimal place description, or emits an error.
    fn classify_place(
        &self,
        expr: &hir::Expression,
        cs: &mut Cs<'ctx>,
    ) -> Option<PlaceInfo<'ctx>> {
        match &expr.kind {
            hir::ExpressionKind::Identifier(_, res) => match res {
                hir::Resolution::LocalVariable(id) => {
                    let binding = self.get_local(*id);
                    Some(PlaceInfo {
                        ty: binding.ty,
                        mutable: binding.mutable,
                        kind: PlaceKind::Local(*id),
                    })
                }
                _ => {
                    self.gcx().dcx().emit_error(
                        "cannot assign to this expression".into(),
                        Some(expr.span),
                    );
                    None
                }
            },
            hir::ExpressionKind::Dereference(target) => {
                let ptr_ty = self.synth(target, cs);
                match ptr_ty.kind() {
                    TyKind::Pointer(inner, mutbl) | TyKind::Reference(inner, mutbl) => Some(
                        PlaceInfo {
                            ty: inner,
                            mutable: mutbl == hir::Mutability::Mutable,
                            kind: PlaceKind::Deref { ptr_ty },
                        },
                    ),
                    _ => {
                        self.gcx().dcx().emit_error(
                            "cannot assign through a non-pointer/reference value".into(),
                            Some(expr.span),
                        );
                        None
                    }
                }
            }
            _ => {
                self.gcx().dcx().emit_error(
                    "left-hand side of assignment is not assignable".into(),
                    Some(expr.span),
                );
                None
            }
        }
    }

    fn synth_assign_expression(
        &self,
        expr: &hir::Expression,
        lhs: &hir::Expression,
        rhs: &hir::Expression,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        // Determine the type we’re assigning into and whether it’s mutable.
        let place = match self.classify_place(lhs, cs) {
            Some(p) => p,
            None => return Ty::error(self.gcx()),
        };

        if !place.mutable {
            self.gcx().dcx().emit_error(
                "cannot assign to an immutable binding".into(),
                Some(lhs.span),
            );
        }

        // Type-check the RHS against the LHS type.
        let rhs_ty = self.synth_with_expectation(rhs, Some(place.ty), cs);
        cs.add_goal(crate::sema::tycheck::solve::Goal::Equal(place.ty, rhs_ty), expr.span);
        // Assignments evaluate to unit.
        self.gcx().types.void
    }

    fn synth_block_expression(
        &self,
        block: &hir::Block,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        // Evaluate statements in order; the block's value is the last expression statement if any.
        let mut last_expr_ty: Option<Ty<'ctx>> = None;
        for stmt in &block.statements {
            match &stmt.kind {
                hir::StatementKind::Expression(expr) => {
                    last_expr_ty = Some(self.synth_with_expectation(expr, expectation, cs));
                }
                _ => self.check_statement(stmt),
            }
        }

        // If no trailing expression, use unit/void when available; for now create a fresh var.
        last_expr_ty.unwrap_or_else(|| self.gcx().types.void)
    }
}

impl<'ctx> Checker<'ctx> {
    fn synth_expression_literal(
        &self,
        literal: &hir::Literal,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let gcx = self.gcx();
        match literal {
            hir::Literal::Bool(_) => gcx.types.bool,
            hir::Literal::Rune(_) => gcx.types.rune,
            hir::Literal::String(_) => gcx.types.string,
            hir::Literal::Integer(_) => {
                let opt_ty = expectation.and_then(|ty| match ty.kind() {
                    TyKind::Int(_) | TyKind::UInt(_) => Some(ty),
                    _ => None,
                });

                opt_ty.unwrap_or_else(|| cs.infer_cx.next_int_var())
            }
            hir::Literal::Float(_) => {
                let opt_ty = expectation.and_then(|ty| match ty.kind() {
                    TyKind::Float(_) => Some(ty),
                    _ => None,
                });

                opt_ty.unwrap_or_else(|| cs.infer_cx.next_float_var())
            }
            hir::Literal::Nil => {
                todo!();
            }
        }
    }

    fn synth_identifier_expression(
        &self,
        _: NodeID,
        span: Span,
        resolution: &hir::Resolution,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        match resolution {
            hir::Resolution::LocalVariable(id) => self.get_local(*id).ty,
            hir::Resolution::Definition(id, _) => self.gcx().get_type(*id),
            hir::Resolution::SelfConstructor(..) => todo!(),
            hir::Resolution::FunctionSet(candidates) => {
                let ty = cs.infer_cx.next_ty_var(span);
                let mut branches = vec![];
                for &candidate in candidates {
                    let candidate_ty = self.gcx().get_type(candidate);
                    let goal = Goal::BindOverload(BindOverloadGoalData {
                        var_ty: ty,
                        candidate_ty,
                        source: candidate,
                    });
                    branches.push(DisjunctionBranch {
                        goal,
                        source: Some(candidate),
                    });
                }
                cs.add_goal(Goal::Disjunction(branches), span);
                ty
            }
            hir::Resolution::PrimaryType(..)
            | hir::Resolution::InterfaceSelfTypeParameter(..)
            | hir::Resolution::SelfTypeAlias(..)
            | hir::Resolution::ImplicitSelfParameter
            | hir::Resolution::Foundation(..) => todo!(),
            hir::Resolution::Error => unreachable!(),
        }
    }

    fn synth_call_expression(
        &self,
        expression: &hir::Expression,
        callee: &hir::Expression,
        arguments: &[hir::ExpressionArgument],
        expect_ty: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let callee_ty = self.synth(callee, cs);
        let callee_source = self.resolve_callee(callee);
        let arguments = arguments
            .iter()
            .map(|n| ApplyArgument {
                id: n.expression.id,
                label: n.label.map(|n| n.identifier),
                ty: self.synth(&n.expression, cs),
                span: n.expression.span,
            })
            .collect();

        let result_ty = cs.infer_cx.next_ty_var(expression.span);

        let data = ApplyGoalData {
            call_span: expression.span,
            callee_ty,
            callee_source,
            result_ty,
            expect_ty,
            arguments,
        };
        cs.add_goal(Goal::Apply(data), expression.span);

        result_ty
    }
}

impl<'ctx> Checker<'ctx> {
    fn resolve_callee(&self, node: &hir::Expression) -> Option<DefinitionID> {
        match &node.kind {
            hir::ExpressionKind::Identifier(
                _,
                Resolution::Definition(id, DefinitionKind::Function),
            ) => Some(*id),
            _ => None,
        }
    }
}
