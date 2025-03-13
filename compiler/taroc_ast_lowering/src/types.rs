use super::package::Actor;

impl Actor<'_> {
    pub fn lower_type(&mut self, ty: Box<taroc_ast::Type>) -> Box<taroc_hir::Type> {
        let ty = taroc_hir::Type {
            id: self.next(),
            span: ty.span,
            kind: self.lower_type_kind(ty.kind),
        };
        Box::new(ty)
    }

    pub fn lower_type_kind(&mut self, kind: taroc_ast::TypeKind) -> taroc_hir::TypeKind {
        match kind {
            taroc_ast::TypeKind::List(_) => todo!(),
            taroc_ast::TypeKind::Optional(_) => todo!(),
            taroc_ast::TypeKind::Dictionary { .. } => todo!(),
            taroc_ast::TypeKind::Pointer(ty, pointer_type) => taroc_hir::TypeKind::Pointer(
                self.lower_type(ty),
                self.lower_mutability(pointer_type),
            ),
            taroc_ast::TypeKind::Reference(ty, mutability) => taroc_hir::TypeKind::Reference(
                self.lower_type(ty),
                self.lower_mutability(mutability),
            ),
            taroc_ast::TypeKind::Parenthesis(ty) => self.lower_type(ty).kind,
            taroc_ast::TypeKind::Tuple(vec) => {
                taroc_hir::TypeKind::Tuple(self.lower_sequence(vec, |a, ty| a.lower_type(ty)))
            }
            taroc_ast::TypeKind::Path(path) => taroc_hir::TypeKind::Path(self.lower_path(path)),
            taroc_ast::TypeKind::Array { size, element } => taroc_hir::TypeKind::Array {
                size: self.lower_anon_const(size),
                element: self.lower_type(element),
            },
            taroc_ast::TypeKind::Slice(ty) => taroc_hir::TypeKind::Slice(self.lower_type(ty)),
            taroc_ast::TypeKind::Composite(tys) => {
                taroc_hir::TypeKind::Composite(self.lower_sequence(tys, |a, ty| a.lower_type(ty)))
            }
            taroc_ast::TypeKind::AnonStruct { fields } => taroc_hir::TypeKind::AnonStruct {
                fields: self.lower_sequence(fields, |a, f| a.lower_field_definition(f)),
            },
            taroc_ast::TypeKind::Function { .. } => todo!(),
            taroc_ast::TypeKind::ImplicitSelf => taroc_hir::TypeKind::ImplicitSelf,
            taroc_ast::TypeKind::InferedClosureParameter => todo!(),
            taroc_ast::TypeKind::SomeOrAny(k, ty) => {
                let kind = match k {
                    taroc_ast::InterfaceType::Some => taroc_hir::InterfaceType::Some,
                    taroc_ast::InterfaceType::Any => taroc_hir::InterfaceType::Any,
                };
                taroc_hir::TypeKind::SomeOrAny(kind, self.lower_type(ty))
            }
            taroc_ast::TypeKind::OptionalReference(..) => todo!(),
        }
    }
}
