use crate::lower::{ItemCtx, LoweringRequest, TypeLowerer};
use crate::ty::{EnumDefinition, StructDefinition};
use crate::{GlobalContext, ty::VariantDefinition};
use taroc_error::CompileResult;
use taroc_hir::{
    DefinitionID, attributes_contain,
    visitor::{HirVisitor, walk_declaration, walk_function_declaration},
};
use taroc_span::{Identifier, Symbol};

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

    fn run(package: &taroc_hir::Package, context: GlobalContext<'ctx>) -> CompileResult<()> {
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
                );
            }
            taroc_hir::DeclarationKind::Enum(node) => {
                self.collect_enum_definition(self.context.def_id(d.id), d.identifier, node);
            }
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
                );
            }
            taroc_hir::FunctionDeclarationKind::Enum(node) => {
                self.collect_enum_definition(self.context.def_id(d.id), d.identifier, node);
            }
            _ => walk_function_declaration(self, d),
        }
    }

    fn visit_field_definition(&mut self, f: &taroc_hir::FieldDefinition) -> Self::Result {
        let icx = ItemCtx::new(self.context);
        let _ = icx.lowerer().lower_type(&f.ty, &LoweringRequest::default());
    }
}

impl<'ctx> Actor<'ctx> {
    fn collect_variant_definition(
        &mut self,
        id: DefinitionID,
        ident: Identifier,
        variant: &taroc_hir::VariantKind,
        discrimimant: Option<usize>,
    ) -> &'ctx VariantDefinition<'ctx> {
        let gcx = self.context;
        let icx = ItemCtx::new(self.context);

        let fields = variant.fields();

        let fields = fields
            .iter()
            .enumerate()
            .map(|(i, f)| {
                return crate::ty::AdtFieldDefinition {
                    id: gcx.def_id(f.id),
                    name: f.identifier.symbol,
                    ty: icx.lowerer().lower_type(&f.ty, &LoweringRequest::default()),
                    index: i,
                };
            })
            .collect();

        let s_def = VariantDefinition {
            id,
            name: ident.symbol,
            fields,
            ctor: variant.ctor().map(|(k, id)| (k, gcx.def_id(id))),
            discriminant: discrimimant.unwrap_or(0),
        };
        let definition = gcx.alloc(s_def);

        let current_sess = gcx.session().index();
        let ok = gcx
            .with_type_database(current_sess, |db| db.variants.insert(id, definition))
            .is_none();

        if !ok {
            unreachable!("ICE: overwriting existing variant definition")
        }

        definition
    }

    fn collect_struct_definition(
        &mut self,
        id: DefinitionID,
        ident: Identifier,
        variant: &taroc_hir::VariantKind,
    ) {
        let variant = self.collect_variant_definition(id, ident, variant, None);
        let def = self
            .context
            .store
            .interners
            .alloc(StructDefinition { variant });
        let ok = self
            .context
            .with_session_type_database(|db| db.structs.insert(id, def).is_none());

        if !ok {
            unreachable!("ICE: overwriting existing struct definition")
        }
    }

    fn collect_enum_definition(
        &mut self,
        id: DefinitionID,
        _: Identifier,
        enum_def: &taroc_hir::EnumDefinition,
    ) {
        let gcx = self.context;
        let mut variants = Vec::new();
        for (index, variant) in enum_def.variants.iter().enumerate() {
            let variant_id = gcx.def_id(variant.id);
            let variant_def = self.collect_variant_definition(
                variant_id,
                variant.identifier,
                &variant.kind,
                Some(index),
            );

            variants.push(variant_def);
        }

        let definition = gcx.alloc(EnumDefinition { variants });
        let ok = gcx.with_session_type_database(|db| db.enums.insert(id, definition).is_none());
        if !ok {
            unreachable!("ICE: overwriting existing enum definition")
        }
    }
}
