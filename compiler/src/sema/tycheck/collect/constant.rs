use crate::{
    compile::context::Gcx,
    error::CompileResult,
    hir::{self, DefinitionID, HirVisitor},
    sema::{
        models::{Const, ConstKind},
        tycheck::{
            lower::{DefTyLoweringCtx, TypeLowerer},
            utils::const_eval::eval_const_definition,
        },
    },
};

pub fn register(package: &hir::Package, context: Gcx) -> CompileResult<()> {
    context.clear_const_evaluation_cache();
    let mut actor = DefinitionActor {
        context,
        members: Default::default(),
    };
    hir::walk_package(&mut actor, package);
    context.dcx().ok()
}

/// Register all constant types before validating conformance witnesses.
/// Initializers can read those witnesses once conformance collection completes.
pub fn run(package: &hir::Package, context: Gcx) -> CompileResult<()> {
    let mut actor = ValueActor {
        context,
        collect_values: false,
    };
    hir::walk_package(&mut actor, package);
    context.dcx().ok()
}

pub fn collect_values(package: &hir::Package, context: Gcx) -> CompileResult<()> {
    let mut value_actor = ValueActor {
        context,
        collect_values: true,
    };
    hir::walk_package(&mut value_actor, package);
    context.dcx().ok()
}

struct DefinitionActor<'ctx> {
    context: Gcx<'ctx>,
    members: rustc_hash::FxHashMap<(DefinitionID, crate::span::Symbol), crate::span::Span>,
}

impl<'ctx> HirVisitor for DefinitionActor<'ctx> {
    fn visit_declaration(&mut self, declaration: &hir::Declaration) -> Self::Result {
        if let hir::DeclarationKind::Constant(node) = &declaration.kind {
            self.context.register_const_definition(declaration.id, node);
        }
        hir::walk_declaration(self, declaration)
    }

    fn visit_assoc_declaration(
        &mut self,
        declaration: &hir::AssociatedDeclaration,
        context: hir::AssocContext,
    ) -> Self::Result {
        if let hir::AssociatedDeclarationKind::Constant(node) = &declaration.kind {
            let owner = match context {
                hir::AssocContext::Interface(owner) | hir::AssocContext::Impl(owner) => owner,
            };
            let name = declaration.identifier;
            if let Some(previous) = self.members.insert((owner, name.symbol), name.span) {
                self.context.dcx().emit_error(
                    format!("invalid redeclaration of '{}'", self.context.symbol_text(name.symbol)),
                    Some(name.span),
                );
                self.context
                    .dcx()
                    .emit_info("associated constant declared here".into(), Some(previous));
            }
            self.context.register_const_definition(declaration.id, node);
        }
        hir::walk_assoc_declaration(self, declaration, context)
    }

    fn visit_function(
        &mut self,
        id: DefinitionID,
        node: &hir::Function,
        fn_ctx: hir::FunctionContext,
    ) -> Self::Result {
        if node.is_const {
            self.context.register_const_fn_definition(id, node, fn_ctx);
        }
        hir::walk_function(self, id, node, fn_ctx)
    }
}

struct ValueActor<'ctx> {
    context: Gcx<'ctx>,
    collect_values: bool,
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
        if !self.collect_values {
            let lowerer = DefTyLoweringCtx::new(id, self.context);
            self.context
                .cache_type(id, lowerer.lowerer().lower_type(&node.ty));
            return;
        }
        let ty = self.context.get_type(id);

        let Some(expr) = &node.expr else {
            return;
        };

        if crate::mir::const_eval::hir_expr_needs_mir_const_eval(expr) {
            return;
        }

        let Some(value) = eval_const_definition(self.context, id, expr.span) else {
            return;
        };

        self.context.cache_const(
            id,
            Const {
                ty,
                kind: ConstKind::Value(value),
            },
        );
    }
}
