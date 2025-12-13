use crate::{
    compile::context::GlobalContext,
    error::CompileResult,
    hir,
    sema::{
        models::{StructDefinition, StructField},
        tycheck::lower::{DefTyLoweringCtx, TypeLowerer},
    },
};

pub fn run(package: &hir::Package, context: GlobalContext) -> CompileResult<()> {
    let mut actor = Actor { context };
    hir::walk_package(&mut actor, package);
    context.dcx().ok()
}

struct Actor<'ctx> {
    context: GlobalContext<'ctx>,
}

impl hir::HirVisitor for Actor<'_> {
    fn visit_declaration(&mut self, node: &hir::Declaration) -> Self::Result {
        if let hir::DeclarationKind::Struct(s) = &node.kind {
            self.collect_struct_fields(node.id, s);
        }
        hir::walk_declaration(self, node)
    }
}

impl<'ctx> Actor<'ctx> {
    fn collect_struct_fields(&self, id: hir::DefinitionID, node: &hir::Struct) {
        let adt_ty = self.context.get_type(id);
        let crate::sema::models::TyKind::Adt(adt_def) = adt_ty.kind() else {
            todo!("expected cached ADT type for struct")
        };

        let ctx = DefTyLoweringCtx::new(id, self.context);
        let mut fields: Vec<StructField<'ctx>> = Vec::with_capacity(node.fields.len());
        for field in &node.fields {
            let ty = ctx.lowerer().lower_type(&field.ty);
            fields.push(StructField {
                name: field.identifier.symbol,
                ty,
                mutability: field.mutability,
            });
        }

        let fields = self.context.store.arenas.global.alloc_slice_copy(&fields);
        let def = StructDefinition { adt_def, fields };
        self.context.cache_struct_definition(id, def);
    }
}
