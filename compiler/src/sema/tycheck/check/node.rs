use crate::{
    compile::context::Gcx,
    hir::{self, DefinitionID, DefinitionKind, NodeID},
    sema::{
        models::{Ty, TyKind},
        tycheck::{check::checker::Checker, solve::ConstraintSystem},
    },
    span::Span,
};

impl<'ctx> Checker<'ctx> {
    pub fn gcx(&self) -> Gcx<'ctx> {
        self.context
    }

    pub fn check_function(mut self, id: DefinitionID, node: &hir::Function) {
        let gcx = self.gcx();
        gcx.dcx()
            .emit_info("Checking".into(), Some(node.signature.span));
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
        let provided = self.synth(expression, expectation, &mut cs);
        if let Some(expectation) = expectation {
            cs.equal(expectation, provided, expression.span);
        }

        cs.solve_all();
        // TODO: Solve & Report
        //
        provided
    }
}

type Cs<'c> = ConstraintSystem<'c>;
impl<'ctx> Checker<'ctx> {
    fn synth(
        &self,
        node: &hir::Expression,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        self.gcx()
            .dcx()
            .emit_info("Checking".into(), Some(node.span));
        let ty = self.synth_expression_kind(node, expectation, cs);
        println!("Ty is `{}`", ty.format(self.gcx()));
        ty
    }

    fn synth_expression_kind(
        &self,
        expression: &hir::Expression,
        expectation: Option<Ty<'ctx>>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        match &expression.kind {
            hir::ExpressionKind::Literal(node) => self.synth_expression_literal(node, expectation),
            hir::ExpressionKind::Identifier(_, resolution) => {
                self.synth_identifier_expression(expression.id, expression.span, resolution)
            }
            hir::ExpressionKind::Call(c, a) => {
                todo!()
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

impl<'ctx> Checker<'ctx> {
    fn synth_expression_literal(
        &self,
        literal: &hir::Literal,
        expectation: Option<Ty<'ctx>>,
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

                opt_ty.unwrap_or_else(|| gcx.types.int)
            }
            hir::Literal::Float(_) => {
                let opt_ty = expectation.and_then(|ty| match ty.kind() {
                    TyKind::Float(_) => Some(ty),
                    _ => None,
                });

                opt_ty.unwrap_or_else(|| gcx.types.float32)
            }
            hir::Literal::Nil => {
                todo!();
            }
        }
    }

    fn synth_identifier_expression(
        &self,
        id: NodeID,
        span: Span,
        resolution: &hir::Resolution,
    ) -> Ty<'ctx> {
        match resolution {
            hir::Resolution::LocalVariable(id) => self.get_local_ty(*id),
            hir::Resolution::Definition(id, DefinitionKind::Function) => {
                todo!()
            }
            hir::Resolution::Definition(id, _) => {
                todo!()
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
