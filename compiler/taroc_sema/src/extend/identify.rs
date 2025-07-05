use crate::GlobalContext;
use rustc_hash::FxHashMap;
use taroc_error::CompileResult;
use taroc_hir::SelfTypeAlias;
use taroc_hir::{DefinitionID, DefinitionKind, visitor::HirVisitor};

pub fn run(package: &taroc_hir::Package, context: GlobalContext) -> CompileResult<()> {
    Actor::run(package, context)
}

/// Extension Binding, Maps Extension Blocks to Nominal Types
struct Actor<'ctx> {
    context: GlobalContext<'ctx>,
    table: FxHashMap<DefinitionID, SelfTypeAlias>,
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
            db.extension_ty_map = actor.table;
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

        //
        let node = match &declaration.kind {
            taroc_hir::DeclarationKind::Extend(node) => node,
            _ => unreachable!(),
        };

        let resolution = self.context.resolution(node.ty.id);

        let Some(resolution) = resolution.full_resolution() else {
            todo!("report assoc type extension")
        };

        let self_ty = match resolution {
            taroc_hir::Resolution::PrimaryType(k) => taroc_hir::SelfTypeAlias::Primary(k),
            taroc_hir::Resolution::Definition(
                id,
                DefinitionKind::Struct
                | DefinitionKind::Enum
                | DefinitionKind::Interface
                | DefinitionKind::TypeAlias
                | DefinitionKind::Namespace,
            ) => taroc_hir::SelfTypeAlias::Def(id),
            _ => unreachable!("ICE: unextendable node"),
        };

        self.table.insert(def_id, self_ty);
    }
}
