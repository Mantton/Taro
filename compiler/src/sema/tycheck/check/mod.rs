use crate::{
    compile::context::Gcx,
    error::CompileResult,
    hir::{self, DefinitionID, HirVisitor},
    sema::tycheck::results::TypeCheckResults,
};
use std::{cell::RefCell, rc::Rc};

mod checker;
mod gather;
mod node;

pub fn run<'ctx>(
    package: &hir::Package,
    context: Gcx<'ctx>,
) -> CompileResult<TypeCheckResults<'ctx>> {
    let mut actor = Actor::new(context);
    hir::walk_package(&mut actor, package);
    context.dcx().ok()?;
    let results = actor.results.borrow();
    hir::walk_package(
        &mut LiteralValidator {
            context,
            results: &results,
        },
        package,
    );
    context.dcx().ok()?;
    drop(results);
    Ok(std::mem::take(&mut *actor.results.borrow_mut()))
}

// Expectations are optional during inference. Validate every literal once its
// final type is known, including values constrained by a later use.
struct LiteralValidator<'a, 'ctx> {
    context: Gcx<'ctx>,
    results: &'a TypeCheckResults<'ctx>,
}

impl LiteralValidator<'_, '_> {
    fn check(
        &self,
        literal: &hir::Literal,
        id: hir::NodeID,
        span: crate::span::Span,
        pattern: bool,
    ) {
        if let hir::Literal::Integer { value, .. } = literal
            && let Some(ty) = self.results.try_node_type(id)
            && !(if pattern {
                super::utils::literal::integer_literal_fits(*value, ty)
            } else {
                super::utils::literal::integer_expression_literal_fits(*value, ty)
            })
        {
            self.context.dcx().emit_error(
                format!(
                    "integer literal '{}' is out of range for type '{}'",
                    value,
                    ty.format(self.context)
                ),
                Some(span),
            );
        }
    }
}

impl HirVisitor for LiteralValidator<'_, '_> {
    fn visit_expression(&mut self, expression: &hir::Expression) {
        if let hir::ExpressionKind::Literal(literal) = &expression.kind {
            self.check(literal, expression.id, expression.span, false);
        }
        hir::walk_expression(self, expression);
    }

    fn visit_pattern(&mut self, pattern: &hir::Pattern) {
        if let hir::PatternKind::Literal { value } = &pattern.kind {
            self.check(value, pattern.id, pattern.span, true);
        }
        hir::walk_pattern(self, pattern);
    }
}

struct Actor<'ctx> {
    context: Gcx<'ctx>,
    results: Rc<RefCell<TypeCheckResults<'ctx>>>,
}

impl<'ctx> Actor<'ctx> {
    fn new(context: Gcx<'ctx>) -> Actor<'ctx> {
        Actor {
            context,
            results: Rc::new(RefCell::new(TypeCheckResults::default())),
        }
    }
}

impl<'ctx> HirVisitor for Actor<'ctx> {
    fn visit_declaration(&mut self, declaration: &hir::Declaration) -> Self::Result {
        match &declaration.kind {
            hir::DeclarationKind::Constant(node) => {
                self.check_constant(declaration.id, node);
                return;
            }
            hir::DeclarationKind::StaticVariable(node) => {
                self.check_static_variable(declaration.id, node);
                return;
            }
            _ => {}
        }
        hir::walk_declaration(self, declaration);
    }

    fn visit_function(
        &mut self,
        id: hir::DefinitionID,
        node: &hir::Function,
        fn_ctx: hir::FunctionContext,
    ) -> Self::Result {
        self.check_function(id, node, fn_ctx);
    }
}

impl<'ctx> Actor<'ctx> {
    fn check_function(
        &mut self,
        id: DefinitionID,
        node: &hir::Function,
        fn_ctx: hir::FunctionContext,
    ) {
        let mut checker = checker::Checker::new(self.context, id, self.results.clone());
        checker.check_function(id, node, fn_ctx);
    }

    fn check_constant(&mut self, id: DefinitionID, node: &hir::Constant) {
        let mut checker = checker::Checker::new(self.context, id, self.results.clone());
        checker.check_constant(id, node);
    }

    fn check_static_variable(&mut self, id: DefinitionID, node: &hir::StaticVariable) {
        let mut checker = checker::Checker::new(self.context, id, self.results.clone());
        checker.check_static_variable(id, node);
    }
}
