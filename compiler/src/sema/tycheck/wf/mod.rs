use crate::{
    compile::context::GlobalContext,
    error::CompileResult,
    hir::{self, DefinitionID, HirVisitor},
    sema::tycheck::lower::{DefTyLoweringCtx, TypeLowerer},
};

pub fn run(package: &hir::Package, context: GlobalContext) -> CompileResult<()> {
    Actor::run(package, context)
}

impl<'ctx> Actor<'ctx> {
    fn new(context: GlobalContext<'ctx>) -> Actor<'ctx> {
        Actor { context }
    }

    fn run(package: &hir::Package, context: GlobalContext<'ctx>) -> CompileResult<()> {
        let mut actor = Actor::new(context);
        hir::walk_package(&mut actor, package);
        context.dcx().ok()
    }
}
struct Actor<'ctx> {
    context: GlobalContext<'ctx>,
}

impl<'ctx> HirVisitor for Actor<'ctx> {
    fn visit_declaration(&mut self, node: &hir::Declaration) -> Self::Result {
        match &node.kind {
            hir::DeclarationKind::Interface(..) => todo!(),
            hir::DeclarationKind::Struct(s) => self.check_struct(node.id, s),
            hir::DeclarationKind::Enum(_) => todo!(),
            hir::DeclarationKind::Function(function) => self.check_function(node.id, function),
            hir::DeclarationKind::TypeAlias(..) => todo!(),
            hir::DeclarationKind::Constant(..) => todo!(),
            hir::DeclarationKind::Variable(..) => todo!(),
            hir::DeclarationKind::Import(..) => {}
            hir::DeclarationKind::Export(..) => todo!(),
            hir::DeclarationKind::Namespace(..) => todo!(),
            hir::DeclarationKind::Extension(..) => todo!(),
            hir::DeclarationKind::Malformed => unreachable!(),
        }
    }
}

impl<'ctx> Actor<'ctx> {
    fn check_function(&self, id: DefinitionID, _: &hir::Function) {
        let _ = self.context.get_signature(id);
    }

    fn check_struct(&self, id: DefinitionID, node: &hir::Struct) {
        let ctx = DefTyLoweringCtx::new(id, self.context);
        for field in &node.fields {
            let _ = ctx.lowerer().lower_type(&field.ty);
        }
    }
}
