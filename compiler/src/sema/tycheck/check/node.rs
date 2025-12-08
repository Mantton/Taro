use crate::{
    hir,
    sema::{
        models::{Ty, TyKind},
        tycheck::check::{context::FnCtx, models::Expectation},
    },
};

impl<'rcx, 'gcx> FnCtx<'rcx, 'gcx> {
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
        let annotation = local.ty.as_ref().map(|ty| self.lower_type(ty));
        let init_ty = local.initializer.as_ref().map(|expr| match annotation {
            Some(annotation) => self.check_expression_has_type(expr, annotation),
            None => self.check_expression(expr),
        });
        let ty = annotation.or(init_ty).unwrap_or(self.gcx.types.error);
        self.locals.borrow_mut().insert(local.pattern.id, ty);
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
        let _ = self.check_expression_with_hint(expression, expectation);
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
                self.check_identifier_expression(resolution)
            }
            hir::ExpressionKind::Member { .. } => todo!(),
            hir::ExpressionKind::Specialize { .. } => todo!(),
            hir::ExpressionKind::Array(..) => todo!(),
            hir::ExpressionKind::Tuple(..) => todo!(),
            hir::ExpressionKind::If(..) => todo!(),
            hir::ExpressionKind::Match(..) => todo!(),
            hir::ExpressionKind::Call(..) => todo!(),
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
            hir::Literal::String(_) => todo!(),
            hir::Literal::Integer(_) => {
                let opt_ty = expectation.to_option().and_then(|ty| match ty.kind() {
                    TyKind::Int(_) | TyKind::UInt(_) => Some(ty),
                    _ => None,
                });

                opt_ty.unwrap_or_else(|| todo!())
            }
            hir::Literal::Float(_) => {
                let opt_ty = expectation.to_option().and_then(|ty| match ty.kind() {
                    TyKind::Float(_) => Some(ty),
                    _ => None,
                });

                opt_ty.unwrap_or_else(|| todo!())
            }
            hir::Literal::Nil => {
                todo!();
            }
        }
    }

    fn check_identifier_expression(&self, resolution: &hir::Resolution) -> Ty<'ctx> {
        match resolution {
            hir::Resolution::LocalVariable(id) => self
                .locals
                .borrow()
                .get(id)
                .copied()
                .unwrap_or(self.gcx.types.error),
            hir::Resolution::Definition(..) | hir::Resolution::SelfConstructor(..) => {
                todo!()
            }
            hir::Resolution::FunctionSet(..) => todo!(),
            hir::Resolution::PrimaryType(..)
            | hir::Resolution::InterfaceSelfTypeParameter(..)
            | hir::Resolution::SelfTypeAlias(..)
            | hir::Resolution::ImplicitSelfParameter
            | hir::Resolution::Foundation(..) => todo!(),
            hir::Resolution::Error => unreachable!(),
        }
    }
}
