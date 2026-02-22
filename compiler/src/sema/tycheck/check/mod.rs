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
    Ok(std::mem::take(&mut *actor.results.borrow_mut()))
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
        if let hir::DeclarationKind::Constant(node) = &declaration.kind {
            self.check_constant(declaration.id, node);
            return;
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
}
