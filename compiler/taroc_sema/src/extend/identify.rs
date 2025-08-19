use crate::GlobalContext;
use crate::lower::{ItemCtx, LoweringRequest, TypeLowerer};
use crate::ty::Ty;
use rustc_hash::FxHashMap;
use taroc_error::CompileResult;
use taroc_hir::DefinitionID;
use taroc_hir::{DefinitionKind, visitor::HirVisitor};

pub fn run(package: &taroc_hir::Package, context: GlobalContext) -> CompileResult<()> {
    Actor::run(package, context)
}

/// Extension Binding, Maps Extension Blocks to Nominal Types
struct Actor<'ctx> {
    context: GlobalContext<'ctx>,
    table: FxHashMap<DefinitionID, Ty<'ctx>>,
}

impl<'ctx> Actor<'ctx> {
    fn new(context: GlobalContext<'ctx>) -> Actor<'ctx> {
        Actor {
            context,
            table: Default::default(),
        }
    }

    fn run(package: &taroc_hir::Package, context: GlobalContext<'ctx>) -> CompileResult<()> {
        let mut actor = Actor::new(context);
        taroc_hir::visitor::walk_package(&mut actor, package);
        context.with_type_database(context.session().index(), |db| {
            db.extension_tys = actor.table;
        });
        context.diagnostics.report()
    }
}

impl HirVisitor for Actor<'_> {
    fn visit_declaration(&mut self, declaration: &taroc_hir::Declaration) -> Self::Result {
        let def_id = self.context.def_id(declaration.id);
        let kind = self.context.def_kind(def_id);
        if !matches!(kind, DefinitionKind::Extension) {
            return;
        }

        let node = match &declaration.kind {
            taroc_hir::DeclarationKind::Extend(node) => node,
            _ => unreachable!(),
        };

        let icx = ItemCtx::new(self.context);
        let ty = icx.lowerer().lower_type(&node.ty, &LoweringRequest::new());

        let simple = self.context.try_simple_type(ty);

        if simple.is_none() {
            self.context.diagnostics.error(
                format!("Cannot Extend {}", ty.format(self.context)),
                node.ty.span,
            );
        };

        self.table.insert(def_id, ty);
    }
}
