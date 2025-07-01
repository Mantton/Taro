use crate::ty::TyKind;
use crate::{GlobalContext, utils::convert_tuple_variant_signature};
use taroc_error::CompileResult;
use taroc_hir::{
    NodeID,
    visitor::{HirVisitor, walk_function},
};

use crate::utils::convert_to_labeled_signature;

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
    fn visit_function(
        &mut self,
        id: NodeID,
        function: &taroc_hir::Function,
        context: taroc_hir::visitor::FunctionContext,
    ) -> Self::Result {
        // println!("Collect Function");
        let def_id = self.context.def_id(id);
        let signature = convert_to_labeled_signature(function, def_id, self.context);
        let arguments = self.context.type_arguments(def_id);
        let kind = TyKind::FnDef(def_id, arguments);
        let ty = self.context.mk_ty(kind);
        self.context.cache_type(def_id, ty);
        self.context.cache_signature(def_id, signature.clone());
        walk_function(self, id, function, context)
    }

    fn visit_variant(&mut self, v: &taroc_hir::Variant) -> Self::Result {
        let def_id = self.context.def_id(v.id);
        let parent = self.context.parent(def_id);
        let parent_ty = self.context.type_of(parent);
        match &v.kind {
            taroc_hir::VariantKind::Tuple(ctor_id, fields) => {
                let ctor_def_id = self.context.def_id(*ctor_id);
                // Constructor
                let signature =
                    convert_tuple_variant_signature(fields, parent_ty, ctor_def_id, self.context);
                self.context.cache_signature(ctor_def_id, signature);
            }
            _ => {}
        }
    }
}
