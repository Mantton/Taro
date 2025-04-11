use super::package::Actor;
use taroc_ast::Mutability;
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
                    arguments: vec![taroc_hir::TypeArgument::Type(internal)],
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
                    arguments: vec![taroc_hir::TypeArgument::Type(internal)],
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
                    arguments: vec![
                        taroc_hir::TypeArgument::Type(self.lower_type(key)),
                        taroc_hir::TypeArgument::Type(self.lower_type(value)),
                    ],
                });
                taroc_hir::TypeKind::Path(path)
            }
            taroc_ast::TypeKind::Pointer(ty, mutability) => {
                // *T == std::mem::MutablePointer<T>
                // *const T = std::mem:ImmutablePointer<T>
                let t = match mutability {
                    taroc_ast::Mutability::Mutable => "MutablePointer",
                    taroc_ast::Mutability::Immutable => "ImmutablePointer",
                };

                let mut path = self.mk_path(&["std", "mem", t], span);
                let last_index = path.segments.len() - 1;
                let segment = &mut path.segments[last_index];
                segment.arguments = Some(taroc_hir::TypeArguments {
                    span,
                    arguments: vec![taroc_hir::TypeArgument::Type(self.lower_type(ty))],
                });
                taroc_hir::TypeKind::Path(path)
            }
            taroc_ast::TypeKind::Reference(ty, mutability) => {
                let internal = self.lower_type(ty);
                self.mk_ref(internal, mutability, span)
            }
            taroc_ast::TypeKind::Parenthesis(ty) => self.lower_type(ty).kind,
            taroc_ast::TypeKind::Tuple(vec) => {
                taroc_hir::TypeKind::Tuple(self.lower_sequence(vec, |a, ty| a.lower_type(ty)))
            }
            taroc_ast::TypeKind::Path(path) => taroc_hir::TypeKind::Path(self.lower_path(path)),
            taroc_ast::TypeKind::Array { size, element } => {
                // [N]T == Array<N, T>

                let mut path = self.mk_path(&["std", "collection", "Array"], span);
                let last_index = path.segments.len() - 1;
                let segment = &mut path.segments[last_index];
                segment.arguments = Some(taroc_hir::TypeArguments {
                    span,
                    arguments: vec![
                        taroc_hir::TypeArgument::Const(self.lower_anon_const(size)),
                        taroc_hir::TypeArgument::Type(self.lower_type(element)),
                    ],
                });
                taroc_hir::TypeKind::Path(path)
            }
            taroc_ast::TypeKind::Function {
                inputs,
                output,
                is_async,
            } => {
                let is_variadic = inputs.last().map(|t| t.is_variadic).unwrap_or_default();
                taroc_hir::TypeKind::Function {
                    inputs: self.lower_sequence(inputs, |a, ty| a.lower_type(ty)),
                    output: self.lower_type(output),
                    is_async,
                    is_variadic,
                }
            }
            taroc_ast::TypeKind::ImplicitSelf => {
                let path = self.mk_path(&["Self"], span);
                taroc_hir::TypeKind::Path(path)
            }
            taroc_ast::TypeKind::InferedClosureParameter => taroc_hir::TypeKind::Infer,
            taroc_ast::TypeKind::OptionalReference(ty, mutability) => {
                // ~T == std::option::Option<&T>
                // ~mut T == std::option::Option<&mut T>
                let internal = self.lower_type(ty);
                let kind = self.mk_ref(internal, mutability, span);
                let internal = self.mk_ty(kind, span);

                let mut path = self.mk_path(&["std", "option", "Option"], span);
                let last_index = path.segments.len() - 1;
                let segment = &mut path.segments[last_index];
                segment.arguments = Some(taroc_hir::TypeArguments {
                    span,
                    arguments: vec![taroc_hir::TypeArgument::Type(internal)],
                });

                taroc_hir::TypeKind::Path(path)
            }
            taroc_ast::TypeKind::Opaque(items) => taroc_hir::TypeKind::Opaque(
                self.lower_sequence(items, |a, ty| a.lower_tagged_path(ty)),
            ),
            taroc_ast::TypeKind::Exisitential(items) => taroc_hir::TypeKind::Exisitential(
                self.lower_sequence(items, |a, ty| a.lower_tagged_path(ty)),
            ),
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

    fn mk_ref(
        &mut self,
        ty: Box<taroc_hir::Type>,
        mutability: Mutability,
        span: Span,
    ) -> taroc_hir::TypeKind {
        // &T == std::mem::MutableReference<T>
        // &const T = std::mem:ImmutableReference<T>
        let t = match mutability {
            taroc_ast::Mutability::Mutable => "MutableReference",
            taroc_ast::Mutability::Immutable => "ImmutableReference",
        };

        let mut path = self.mk_path(&["std", "mem", t], span);
        let last_index = path.segments.len() - 1;
        let segment = &mut path.segments[last_index];
        segment.arguments = Some(taroc_hir::TypeArguments {
            span,
            arguments: vec![taroc_hir::TypeArgument::Type(ty)],
        });
        taroc_hir::TypeKind::Path(path)
    }
}
