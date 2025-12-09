use crate::{
    hir::{self, DefinitionKind, NodeID},
    sema::{
        models::{CalleeOrigin, InferTy, Ty, TyKind},
        tycheck::{
            check::{context::FnCtx, gather::GatherLocalsVisitor, models::Expectation},
            lower::TypeLowerer,
            solve::{ApplicationArgument, ApplicationGoal, Goal, Obligation},
        },
    },
};

impl<'rcx, 'gcx> FnCtx<'rcx, 'gcx> {
    pub fn error_ty(&self) -> Ty<'gcx> {
        self.gcx.types.error
    }

    pub fn check_statement(&self, statement: &hir::Statement) {
        match &statement.kind {
            hir::StatementKind::Declaration(..) => return,
            hir::StatementKind::Expression(..) => todo!(),
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

    pub fn check_return(&self, expression: &hir::Expression) {
        let Some(return_ty) = self.return_ty else {
            unreachable!("ICE: return check called outside function body")
        };

        let _ = self.check_expression_coercible_to_type(expression, return_ty);
    }

    pub fn check_block(&self, block: &hir::Block) {
        for statement in &block.statements {
            self.check_statement(statement);
        }
    }

    pub fn check_local(&self, local: &hir::Local) {
        GatherLocalsVisitor::from_local(self, local);
        let ty = self.local_ty(local.id);
        if let Some(initializer) = &local.initializer {
            self.check_expression_coercible_to_type(initializer, ty);
        }
    }
}

impl<'rcx, 'ctx> FnCtx<'rcx, 'ctx> {
    pub fn check_expression(&self, expression: &hir::Expression) -> Ty<'ctx> {
        self.check_expression_with_expectation(expression, Expectation::None)
    }

    pub fn check_expression_with_expectation(
        &self,
        expression: &hir::Expression,
        expectation: Expectation<'ctx>,
    ) -> Ty<'ctx> {
        self.check_expression_with_expectation_and_arguments(expression, expectation)
    }

    pub fn check_expression_has_type(
        &self,
        expression: &hir::Expression,
        expectation: Ty<'ctx>,
    ) -> Ty<'ctx> {
        self.check_expression_with_expectation(expression, Expectation::HasType(expectation))
    }

    pub fn check_expression_coercible_to_type(
        &self,
        expression: &hir::Expression,
        expectation: Ty<'ctx>,
    ) -> Ty<'ctx> {
        let ty = self.check_expression_with_hint(expression, expectation);
        self.add_coercion_constraint(ty, expectation, expression.span);
        expectation
    }

    pub fn check_expression_with_hint(
        &self,
        expression: &hir::Expression,
        expectation: Ty<'ctx>,
    ) -> Ty<'ctx> {
        self.check_expression_with_expectation(expression, Expectation::HasType(expectation))
    }

    pub fn check_expression_with_expectation_and_arguments(
        &self,
        expression: &hir::Expression,
        expectation: Expectation<'ctx>,
    ) -> Ty<'ctx> {
        let ty = self.check_expression_kind(expression, expectation);
        self.gcx.dcx().emit_info(
            format!("Type is {}", ty.format(self.gcx)),
            Some(expression.span),
        );
        ty
    }

    fn check_expression_kind(
        &self,
        expression: &hir::Expression,
        expectation: Expectation<'ctx>,
    ) -> Ty<'ctx> {
        match &expression.kind {
            hir::ExpressionKind::Literal(node) => self.check_literal_expression(node, expectation),
            hir::ExpressionKind::Identifier(_, resolution) => {
                self.check_identifier_expression(expression.id, resolution)
            }
            hir::ExpressionKind::Call(c, a) => {
                self.check_call_expression(expression, c, a, expectation)
            }
            hir::ExpressionKind::Member { .. } => todo!(),
            hir::ExpressionKind::Specialize { .. } => todo!(),
            hir::ExpressionKind::Array(..) => todo!(),
            hir::ExpressionKind::Tuple(..) => todo!(),
            hir::ExpressionKind::If(..) => todo!(),
            hir::ExpressionKind::Match(..) => todo!(),
            hir::ExpressionKind::Reference(..) => todo!(),
            hir::ExpressionKind::Dereference(..) => todo!(),
            hir::ExpressionKind::Binary(..) => todo!(),
            hir::ExpressionKind::Unary(..) => todo!(),
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

impl<'rcx, 'ctx> FnCtx<'rcx, 'ctx> {
    fn check_literal_expression(
        &self,
        literal: &hir::Literal,
        expectation: Expectation<'ctx>,
    ) -> Ty<'ctx> {
        let gcx = self.gcx;
        match literal {
            hir::Literal::Bool(_) => gcx.types.bool,
            hir::Literal::Rune(_) => gcx.types.rune,
            hir::Literal::String(_) => gcx.types.string,
            hir::Literal::Integer(_) => {
                let opt_ty = expectation.to_option().and_then(|ty| match ty.kind() {
                    TyKind::Int(_) | TyKind::UInt(_) => Some(ty),
                    _ => None,
                });

                opt_ty.unwrap_or_else(|| self.next_int_var())
            }
            hir::Literal::Float(_) => {
                let opt_ty = expectation.to_option().and_then(|ty| match ty.kind() {
                    TyKind::Float(_) => Some(ty),
                    _ => None,
                });

                opt_ty.unwrap_or_else(|| self.next_float_var())
            }
            hir::Literal::Nil => {
                todo!();
            }
        }
    }

    fn check_identifier_expression(
        &self,
        node_id: NodeID,
        resolution: &hir::Resolution,
    ) -> Ty<'ctx> {
        match resolution {
            hir::Resolution::LocalVariable(id) => self.local_ty(*id),
            hir::Resolution::Definition(id, DefinitionKind::Function) => {
                self.callee_origins
                    .borrow_mut()
                    .insert(node_id, CalleeOrigin::Direct(*id));
                let ty = self.gcx.get_type(*id);
                ty
            }
            hir::Resolution::Definition(id, _) => {
                let ty = self.gcx.get_type(*id);
                ty
            }
            hir::Resolution::SelfConstructor(..) => todo!(),
            hir::Resolution::FunctionSet(ids) => {
                todo!()
            }
            hir::Resolution::PrimaryType(..)
            | hir::Resolution::InterfaceSelfTypeParameter(..)
            | hir::Resolution::SelfTypeAlias(..)
            | hir::Resolution::ImplicitSelfParameter
            | hir::Resolution::Foundation(..) => todo!(),
            hir::Resolution::Error => unreachable!(),
        }
    }
}

impl<'rcx, 'ctx> FnCtx<'rcx, 'ctx> {
    fn check_call_expression(
        &self,
        expression: &hir::Expression,
        callee: &hir::Expression,
        arguments: &[hir::ExpressionArgument],
        expectation: Expectation<'ctx>,
    ) -> Ty<'ctx> {
        let callee_ty = self.check_expression(callee);

        match callee_ty.kind() {
            TyKind::FnPointer { .. } | TyKind::Infer(InferTy::TyVar(..) | InferTy::FnVar(..)) => {
                // continue
            }
            _ => {
                if callee_ty.is_error() {
                    return self.error_ty();
                }

                self.gcx().dcx().emit_error(
                    format!(
                        "cannot invoke non-function type '{}'",
                        callee_ty.format(self.gcx)
                    ),
                    Some(callee.span),
                );
                return self.error_ty();
            }
        };

        let result = self.next_ty_var(expression.span);
        let arguments = self
            .gcx
            .store
            .arenas
            .global
            .alloc_slice_fill_iter(arguments.iter().map(|n| ApplicationArgument {
                id: n.expression.id,
                label: n.label.map(|n| n.identifier),
                ty: self.check_expression(&n.expression),
                span: n.expression.span,
            }));

        let callee_origin = self.callee_origins.borrow().get(&callee.id).cloned();

        let goal = ApplicationGoal {
            callee_ty,
            caller_span: expression.span,
            callee_origin,
            call_id: expression.id,
            callee_id: callee.id,
            arguments,
            result,
            expected: expectation.only_has_type(),
        };

        self.add_obligation(Obligation {
            location: expression.span,
            goal: Goal::Apply(goal),
        });

        result
    }
}
