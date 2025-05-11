use rustc_hash::FxHashMap;
use taroc_context::GlobalContext;
use taroc_error::CompileResult;
use taroc_hir::{DefinitionID, DefinitionKind, visitor::HirVisitor};
use taroc_ty::{SimpleType, Ty, TyKind};

use crate::lower::{ItemCtx, LoweringContext, LoweringRequest, TypeLowerer};

pub fn run(package: &taroc_hir::Package, context: GlobalContext) -> CompileResult<()> {
    Actor::run(package, context)
}

/// Extension Binding, Maps Extension Blocks to Nominal Types
struct Actor<'ctx> {
    context: GlobalContext<'ctx>,
    table: FxHashMap<DefinitionID, SimpleType>,
}

impl<'ctx> Actor<'ctx> {
    fn new(context: GlobalContext<'ctx>) -> Actor<'ctx> {
        Actor {
            context,
            table: Default::default(),
        }
    }

    fn run<'a>(package: &taroc_hir::Package, context: GlobalContext<'ctx>) -> CompileResult<()> {
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

        let ctx = ItemCtx::new(self.context);
        let self_ty = ctx.lowerer().lower_type(
            &node.ty,
            &LoweringRequest::new(LoweringContext::ExtensionSelfTy),
        );
        self.identify(def_id, self_ty);
    }
}

impl<'ctx> Actor<'ctx> {
    fn identify(&mut self, extend_id: DefinitionID, self_ty: Ty<'ctx>) {
        match self_ty.kind() {
            TyKind::Bool
            | TyKind::Rune
            | TyKind::String
            | TyKind::Int(_)
            | TyKind::UInt(_)
            | TyKind::Float(_)
            | TyKind::Pointer(..)
            | TyKind::Reference(..)
            | TyKind::Array(..)
            | TyKind::Adt(..) => self.identify_internal(extend_id, self_ty),
            TyKind::Existential(..)
            | TyKind::Opaque(..)
            | TyKind::FnDef(..)
            | TyKind::OverloadedFn(..)
            | TyKind::Infer(..)
            | TyKind::Function { .. }
            | TyKind::Tuple(..)
            | TyKind::AssociatedType(..)
            | TyKind::Parameter(..) => unreachable!(
                "ICE: resolver should have reported extending non-nominal types in prior pass"
            ),
            TyKind::Error => return, // prereported
        }
    }
}

impl<'ctx> Actor<'ctx> {
    fn identify_internal(&mut self, extend_id: DefinitionID, ty: Ty<'ctx>) {
        self.table.insert(extend_id, ty.to_simple_type());
    }
}
