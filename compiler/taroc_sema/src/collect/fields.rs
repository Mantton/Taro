use crate::{GlobalContext, ty::StructDefinition};
use taroc_error::CompileResult;
use taroc_hir::{
    DefinitionID, attributes_contain,
    visitor::{HirVisitor, walk_declaration, walk_function_declaration},
};
use taroc_span::{Identifier, Symbol};

use crate::lower::{ItemCtx, LoweringRequest, TypeLowerer};

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

impl HirVisitor for Actor<'_> {
    fn visit_declaration(&mut self, d: &taroc_hir::Declaration) -> Self::Result {
        match &d.kind {
            taroc_hir::DeclarationKind::Struct(def) => {
                let is_std = self.context.session().config.is_std;
                if is_std && attributes_contain(&d.attributes, Symbol::with("builtin")) {
                    return;
                }
                self.collect_struct_definition(
                    self.context.def_id(d.id),
                    d.identifier,
                    &def.variant,
                    None,
                );
            }
            taroc_hir::DeclarationKind::Enum(_) => {}
            _ => walk_declaration(self, d),
        }
    }

    fn visit_function_declaration(&mut self, d: &taroc_hir::FunctionDeclaration) -> Self::Result {
        match &d.kind {
            taroc_hir::FunctionDeclarationKind::Struct(def) => {
                self.collect_struct_definition(
                    self.context.def_id(d.id),
                    d.identifier,
                    &def.variant,
                    None,
                );
            }
            taroc_hir::FunctionDeclarationKind::Enum(_) => {}
            _ => walk_function_declaration(self, d),
        }
    }

    fn visit_field_definition(&mut self, f: &taroc_hir::FieldDefinition) -> Self::Result {
        let icx = ItemCtx::new(self.context);
        let _ = icx.lowerer().lower_type(&f.ty, &LoweringRequest::default());
    }
}

impl<'ctx> Actor<'ctx> {
    fn collect_struct_definition(
        &mut self,
        id: DefinitionID,
        ident: Identifier,
        variant: &taroc_hir::VariantKind,
        discrimimant: Option<usize>,
    ) {
        let gcx = self.context;
        let icx = ItemCtx::new(self.context);

        let fields = variant.fields();

        let fields = fields
            .iter()
            .enumerate()
            .map(|(i, f)| {
                return crate::ty::StructField {
                    id: gcx.def_id(f.id),
                    name: f.identifier.symbol,
                    ty: icx.lowerer().lower_type(&f.ty, &LoweringRequest::default()),
                    mutability: f.mutability,
                    index: i,
                };
            })
            .collect();

        let definition = gcx.store.interners.alloc(StructDefinition {
            id,
            name: ident.symbol,
            fields,
            ctor: variant.ctor().map(|(k, id)| (k, gcx.def_id(id))),
            variant_discrimimant: discrimimant,
        });

        let current_sess = gcx.session().index();
        let ok = gcx
            .with_type_database(current_sess, |db| db.structs.insert(id, definition))
            .is_none();

        if !ok {
            unreachable!("ICE: overwriting existing struct definition")
        }
    }
}
