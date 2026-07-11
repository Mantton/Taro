use crate::{
    compile::context::Gcx,
    error::CompileResult,
    hir::{self, DefinitionID, HirVisitor},
    sema::{
        models::{Const, ConstKind},
        tycheck::{
            lower::{DefTyLoweringCtx, TypeLowerer},
            utils::const_eval::{eval_const_definition, register_const_definition},
        },
    },
};

pub fn register(package: &hir::Package, context: Gcx) -> CompileResult<()> {
    context.clear_const_evaluation_cache();
    let mut actor = DefinitionActor { context };
    hir::walk_package(&mut actor, package);
    context.dcx().ok()
}

pub fn run(package: &hir::Package, context: Gcx) -> CompileResult<()> {
    let mut type_actor = TypeActor { context };
    hir::walk_package(&mut type_actor, package);
    context.dcx().ok()?;

    let mut value_actor = ValueActor { context };
    hir::walk_package(&mut value_actor, package);
    context.dcx().ok()
}

struct DefinitionActor<'ctx> {
    context: Gcx<'ctx>,
}

impl<'ctx> HirVisitor for DefinitionActor<'ctx> {
    fn visit_declaration(&mut self, declaration: &hir::Declaration) -> Self::Result {
        if let hir::DeclarationKind::Constant(node) = &declaration.kind {
            self.register_constant(declaration.id, node);
        }
        hir::walk_declaration(self, declaration)
    }

    fn visit_assoc_declaration(
        &mut self,
        declaration: &hir::AssociatedDeclaration,
        context: hir::AssocContext,
    ) -> Self::Result {
        if let hir::AssociatedDeclarationKind::Constant(node) = &declaration.kind {
            self.register_constant(declaration.id, node);
        }
        hir::walk_assoc_declaration(self, declaration, context)
    }
}

impl<'ctx> DefinitionActor<'ctx> {
    fn register_constant(&self, id: DefinitionID, node: &hir::Constant) {
        if let Some(expression) = &node.expr {
            register_const_definition(self.context, id, expression);
        }
    }
}

struct TypeActor<'ctx> {
    context: Gcx<'ctx>,
}

impl<'ctx> HirVisitor for TypeActor<'ctx> {
    fn visit_declaration(&mut self, declaration: &hir::Declaration) -> Self::Result {
        if let hir::DeclarationKind::Constant(node) = &declaration.kind {
            self.collect_constant_type(declaration.id, node);
        }
        hir::walk_declaration(self, declaration)
    }

    fn visit_assoc_declaration(
        &mut self,
        declaration: &hir::AssociatedDeclaration,
        context: hir::AssocContext,
    ) -> Self::Result {
        if let hir::AssociatedDeclarationKind::Constant(node) = &declaration.kind {
            self.collect_constant_type(declaration.id, node);
        }
        hir::walk_assoc_declaration(self, declaration, context)
    }
}

impl<'ctx> TypeActor<'ctx> {
    fn collect_constant_type(&self, id: DefinitionID, node: &hir::Constant) {
        let icx = DefTyLoweringCtx::new(id, self.context);
        let ty = icx.lowerer().lower_type(&node.ty);
        self.context.cache_type(id, ty);
    }
}

struct ValueActor<'ctx> {
    context: Gcx<'ctx>,
}

impl<'ctx> HirVisitor for ValueActor<'ctx> {
    fn visit_declaration(&mut self, declaration: &hir::Declaration) -> Self::Result {
        if let hir::DeclarationKind::Constant(node) = &declaration.kind {
            self.collect_constant_value(declaration.id, node);
        }
        hir::walk_declaration(self, declaration)
    }

    fn visit_assoc_declaration(
        &mut self,
        declaration: &hir::AssociatedDeclaration,
        context: hir::AssocContext,
    ) -> Self::Result {
        if let hir::AssociatedDeclarationKind::Constant(node) = &declaration.kind {
            self.collect_constant_value(declaration.id, node);
        }
        hir::walk_assoc_declaration(self, declaration, context)
    }
}

impl<'ctx> ValueActor<'ctx> {
    fn collect_constant_value(&self, id: DefinitionID, node: &hir::Constant) {
        let Some(expr) = &node.expr else {
            return;
        };

        let Some(value) = eval_const_definition(self.context, id, expr.span) else {
            return;
        };

        let ty = self.context.get_type(id);

        self.context.cache_const(
            id,
            Const {
                ty,
                kind: ConstKind::Value(value),
            },
        );
    }
}
