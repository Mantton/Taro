use crate::{
    compile::context::GlobalContext,
    error::CompileResult,
    hir::{self, HirVisitor},
    sema::models::{AdtDef, AdtKind, Ty, TyKind},
};

pub fn run(package: &hir::Package, context: GlobalContext) -> CompileResult<()> {
    let mut actor = Actor { context };
    hir::walk_package(&mut actor, package);
    context.dcx().ok()
}

struct Actor<'ctx> {
    context: GlobalContext<'ctx>,
}

impl HirVisitor for Actor<'_> {
    fn visit_declaration(&mut self, node: &hir::Declaration) -> Self::Result {
        match &node.kind {
            hir::DeclarationKind::Struct(value) => {
                self.cache_adt_type(node.id, AdtKind::Struct);
                if let Some(header) = value.class_header {
                    let TyKind::Adt(adt_def, _) = self.context.get_type(node.id).kind() else {
                        unreachable!()
                    };
                    self.context.cache_struct_definition(
                        node.id,
                        crate::sema::models::StructDefinition {
                            adt_def,
                            class_info: Some(crate::sema::models::ClassInfo {
                                initializers: &[],
                                base: None,
                                methods: &[],
                                payload: None,
                                is_final: header.is_final,
                            }),
                            has_initializer: false,
                            repr: crate::sema::models::StructRepr::Taro,
                            fields: &[],
                        },
                    );
                }
            }
            hir::DeclarationKind::Enum(_) => {
                self.cache_adt_type(node.id, AdtKind::Enum);
            }
            hir::DeclarationKind::OpaqueType => {
                self.cache_opaque_type(node.id);
            }
            _ => {}
        }
        hir::walk_declaration(self, node)
    }
}

impl<'ctx> Actor<'ctx> {
    fn cache_adt_type(&self, id: hir::DefinitionID, kind: AdtKind) {
        let adt_def = AdtDef { kind, id };
        let args = crate::sema::tycheck::utils::generics::GenericsBuilder::identity_for_item(
            self.context,
            id,
        );
        let ty = Ty::new(TyKind::Adt(adt_def, args), self.context);
        self.context.cache_type(id, ty);
    }

    fn cache_opaque_type(&self, id: hir::DefinitionID) {
        let ty = Ty::new(TyKind::Opaque(id), self.context);
        self.context.cache_type(id, ty);
    }
}
