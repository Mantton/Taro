use crate::{
    compile::context::Gcx,
    hir::{self, DefinitionID, NodeID, Resolution},
    sema::{
        models::{Ty, TyKind},
        resolve::models::DefinitionKind,
        tycheck::{
            check::checker::Checker,
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
            self.locals.borrow_mut().insert(parameter.id, parameter_ty);
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
            hir::StatementKind::Break => todo!(),
            hir::StatementKind::Continue => todo!(),
            hir::StatementKind::Return(expression) => {
                if let Some(expression) = expression {
                    self.check_return(expression);
                }
            }
            hir::StatementKind::Loop { .. } => todo!(),
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
                    self.set_local_ty(node.pattern.id, ty);
                    self.set_local_ty(node.id, ty);
                }
            }
            hir::PatternKind::Tuple(..) => todo!(),
            _ => unreachable!("ICE – invalid let statement pattern"),
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
            hir::ExpressionKind::If(..) => todo!(),
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
            hir::ExpressionKind::Assign(..) => todo!(),
            hir::ExpressionKind::CastAs(..) => todo!(),
            hir::ExpressionKind::PatternBinding(..) => todo!(),
            hir::ExpressionKind::Block(..) => todo!(),
            hir::ExpressionKind::Malformed => {
                unreachable!("ICE: trying to typecheck a malformed expression node")
            }
        }
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
            hir::Resolution::LocalVariable(id) => self.get_local_ty(*id),
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
