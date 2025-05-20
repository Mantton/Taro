use crate::GlobalContext;
use taroc_error::CompileResult;
use taroc_hir::{DefinitionID, DefinitionKind, visitor::HirVisitor};
use crate::ty::UncheckedConformanceRecord;

use crate::{
    lower::{ItemCtx, LoweringRequest, TypeLowerer},
    utils::ty_from_simple,
};

pub fn run(package: &taroc_hir::Package, context: GlobalContext) -> CompileResult<()> {
    Actor::run(package, context)
}

struct Actor<'ctx> {
    context: GlobalContext<'ctx>,
}

impl<'ctx> Actor<'ctx> {
    fn new(context: GlobalContext<'ctx>) -> Actor<'ctx> {
        Actor { context }
    }

    fn run<'a>(package: &taroc_hir::Package, context: GlobalContext<'ctx>) -> CompileResult<()> {
        let mut actor = Actor::new(context);
        taroc_hir::visitor::walk_package(&mut actor, package);
        context.diagnostics.report()
    }
}

impl<'ctx> HirVisitor for Actor<'ctx> {
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

        self.collect(def_id, &node.generics);
    }
}

impl<'ctx> Actor<'ctx> {
    fn collect(&mut self, extend_id: DefinitionID, node: &taroc_hir::Generics) {
        let Some(conformances) = &node.conformance else {
            return;
        };

        let interafaces = &conformances.interfaces;
        if interafaces.is_empty() {
            return;
        }

        let ty_key = self.context.with_type_database(extend_id.package(), |db| {
            *db.extension_ty_map.get(&extend_id).unwrap()
        });

        let self_ty = ty_from_simple(self.context, ty_key);

        let is_conditional = node.where_clause.is_some();
        let icx = ItemCtx::new(self.context);
        for interface in interafaces {
            let reference = icx.lowerer().lower_interface_reference(
                self_ty,
                interface,
                &LoweringRequest::default(),
            );
            let record = UncheckedConformanceRecord {
                target: ty_key,
                interface: reference,
                extension: extend_id,
                is_conditional,
                location: interface.path.span,
            };

            self.context.with_type_database(extend_id.package(), |db| {
                let entry = db.unchecked_conformances.entry(ty_key).or_default();
                entry.push(record);
            })

            // println!(
            //     "Conforomance {self_ty} to '{}', conditional: {is_conditional}",
            //     self.context.ident_for(reference.id).symbol
            // )
        }
    }
}
