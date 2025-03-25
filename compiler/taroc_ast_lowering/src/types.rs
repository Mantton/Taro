use super::package::Actor;
use taroc_span::{Identifier, Span, Symbol};

impl Actor<'_> {
    pub fn lower_type(&mut self, ty: Box<taroc_ast::Type>) -> Box<taroc_hir::Type> {
        let ty = taroc_hir::Type {
            id: self.next(),
            span: ty.span,
            kind: self.lower_type_kind(ty.kind, ty.span),
        };
        Box::new(ty)
    }

    pub fn lower_type_kind(
        &mut self,
        kind: taroc_ast::TypeKind,
        span: Span,
    ) -> taroc_hir::TypeKind {
        match kind {
            taroc_ast::TypeKind::List(ty) => {
                // []T === std::collection::List<T>
                let internal = self.lower_type(ty);
                let mut path = self.mk_path(&["std", "collection", "List"], span);
                let last_index = path.segments.len() - 1;
                let segment = &mut path.segments[last_index];
                segment.arguments = Some(taroc_hir::TypeArguments {
                    span,
                    arguments: vec![internal],
                });

                taroc_hir::TypeKind::Path(path)
            }
            taroc_ast::TypeKind::Optional(ty) => {
                // T? === std::option::Option<T>
                let internal = self.lower_type(ty);
                let mut path = self.mk_path(&["std", "option", "Option"], span);
                let last_index = path.segments.len() - 1;
                let segment = &mut path.segments[last_index];
                segment.arguments = Some(taroc_hir::TypeArguments {
                    span,
                    arguments: vec![internal],
                });
                taroc_hir::TypeKind::Path(path)
            }
            taroc_ast::TypeKind::Dictionary { key, value } => {
                // [K:V] === std::collection::Dictionary<K, V>
                let mut path = self.mk_path(&["std", "collection", "Dictionary"], span);
                let last_index = path.segments.len() - 1;
                let segment = &mut path.segments[last_index];
                segment.arguments = Some(taroc_hir::TypeArguments {
                    span,
                    arguments: vec![self.lower_type(key), self.lower_type(value)],
                });
                taroc_hir::TypeKind::Path(path)
            }
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
            taroc_ast::TypeKind::OptionalReference(ty, mutability) => {
                // ~T == std::option::Option<&T>
                // ~mut T == std::option::Option<&mut T>
                let internal = self.lower_type(ty);
                let internal =
                    self.mk_ty(taroc_hir::TypeKind::Reference(internal, mutability), span);

                let mut path = self.mk_path(&["std", "option", "Option"], span);
                let last_index = path.segments.len() - 1;
                let segment = &mut path.segments[last_index];
                segment.arguments = Some(taroc_hir::TypeArguments {
                    span,
                    arguments: vec![internal],
                });

                taroc_hir::TypeKind::Path(path)
            }
        }
    }
}

impl Actor<'_> {
    fn mk_ty(&mut self, kind: taroc_hir::TypeKind, span: Span) -> Box<taroc_hir::Type> {
        let ty = taroc_hir::Type {
            id: self.next(),
            span,
            kind,
        };
        Box::new(ty)
    }
    fn mk_path(&mut self, components: &[&str], span: Span) -> taroc_hir::Path {
        let mut segments = vec![];

        for component in components {
            let segment = taroc_hir::PathSegment {
                id: self.next(),
                identifier: Identifier {
                    span,
                    symbol: Symbol::with(component),
                },
                arguments: None,
            };

            segments.push(segment);
        }

        taroc_hir::Path { segments, span }
    }
}
