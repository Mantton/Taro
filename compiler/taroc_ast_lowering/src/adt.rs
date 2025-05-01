use super::package::Actor;

impl Actor<'_> {
    pub fn lower_variant(&mut self, variant: taroc_ast::Variant) -> taroc_hir::Variant {
        taroc_hir::Variant {
            id: self.next(),
            identifier: variant.identifier.clone(),
            kind: self.lower_variant_kind(variant.kind),
            discriminant: self.lower_optional(variant.discriminant, |a, ac| a.lower_anon_const(ac)),
            span: variant.span,
        }
    }

    pub fn lower_variant_kind(&mut self, kind: taroc_ast::VariantKind) -> taroc_hir::VariantKind {
        match kind {
            taroc_ast::VariantKind::Unit => taroc_hir::VariantKind::Unit,
            taroc_ast::VariantKind::Tuple(fields) => taroc_hir::VariantKind::Tuple(
                self.lower_sequence(fields, |a, ty| a.lower_field_definition(ty)),
            ),
            taroc_ast::VariantKind::Struct(fields) => taroc_hir::VariantKind::Struct(
                self.lower_sequence(fields, |a, ty| a.lower_field_definition(ty)),
            ),
        }
    }
}

impl Actor<'_> {
    pub fn lower_field_definition(
        &mut self,
        f: taroc_ast::FieldDefinition,
    ) -> taroc_hir::FieldDefinition {
        taroc_hir::FieldDefinition {
            id: self.next(),
            visibility: self.lower_visibility(f.visibility),
            mutability: self.lower_mutability(f.mutability),
            identifier: f.identifier.clone(),
            ty: self.lower_type(f.ty),
            span: f.span,
        }
    }

    pub fn lower_mutability(&mut self, m: taroc_ast::Mutability) -> taroc_hir::Mutability {
        match m {
            taroc_ast::Mutability::Mutable => taroc_hir::Mutability::Mutable,
            taroc_ast::Mutability::Immutable => taroc_hir::Mutability::Mutable,
        }
    }
}
