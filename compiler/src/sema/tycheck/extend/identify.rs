use crate::{
    compile::context::GlobalContext,
    error::CompileResult,
    hir::{self, DefinitionID, HirVisitor, Resolution},
    sema::resolve::models::{DefinitionKind, TypeHead},
};

pub fn run(package: &hir::Package, context: GlobalContext) -> CompileResult<()> {
    let mut actor = Actor { context };
    hir::walk_package(&mut actor, package);
    context.dcx().ok()
}

struct Actor<'ctx> {
    context: GlobalContext<'ctx>,
}

impl<'ctx> Actor<'ctx> {
    fn resolve_extension_identity(&mut self, extension_id: DefinitionID, node: &hir::Extension) {
        let Some(head) = self.type_head_for_node(&node.ty) else {
            return;
        };

        self.context.cache_extension_type_head(extension_id, head);
    }

    fn type_head_for_node(&mut self, ty: &hir::Type) -> Option<TypeHead> {
        match &ty.kind {
            hir::TypeKind::Nominal(path) => self.type_head_for_nominal(ty, path),
            hir::TypeKind::Pointer(.., m) => Some(TypeHead::Pointer(*m)),
            hir::TypeKind::Reference(.., m) => Some(TypeHead::Reference(*m)),
            hir::TypeKind::Tuple(items) => {
                let Ok(arity) = u16::try_from(items.len()) else {
                    self.context.dcx().emit_error(
                        "tuple type is too large to be extended".to_string(),
                        Some(ty.span),
                    );
                    return None;
                };
                Some(TypeHead::Tuple(arity))
            }
            hir::TypeKind::Array { .. } => Some(TypeHead::Array),
            hir::TypeKind::Function { .. } => {
                self.context
                    .dcx()
                    .emit_error("cannot extend function types".to_string(), Some(ty.span));
                None
            }
            hir::TypeKind::BoxedExistential { .. } => {
                self.context.dcx().emit_error(
                    "cannot extend `any` existentials; extend the interface type directly"
                        .to_string(),
                    Some(ty.span),
                );
                None
            }
            hir::TypeKind::Infer => {
                self.context.dcx().emit_error(
                    "cannot extend `_` (inferred type)".to_string(),
                    Some(ty.span),
                );
                None
            }
        }
    }

    fn type_head_for_nominal(
        &mut self,
        ty: &hir::Type,
        path: &hir::ResolvedPath,
    ) -> Option<TypeHead> {
        let resolved = match path {
            hir::ResolvedPath::Resolved(path) => path,
            hir::ResolvedPath::Relative(..) => {
                self.context.dcx().emit_error(
                    "relative nominal types are not supported in extension targets yet".to_string(),
                    Some(ty.span),
                );
                return None;
            }
        };

        match &resolved.resolution {
            Resolution::PrimaryType(p) => Some(TypeHead::Primary(*p)),
            Resolution::Definition(id, kind) => {
                if self.context.is_std_gc_ptr(*id) {
                    return Some(TypeHead::GcPtr);
                }
                match kind {
                    DefinitionKind::Struct | DefinitionKind::Interface | DefinitionKind::Enum => {
                        Some(TypeHead::Nominal(*id))
                    }
                    _ => {
                        self.context.dcx().emit_error(
                            format!(
                                "cannot extend `{}` because it does not name a type",
                                kind.description()
                            ),
                            Some(ty.span),
                        );
                        None
                    }
                }
            }
            Resolution::Error => None,
            _ => {
                self.context
                    .dcx()
                    .emit_error("invalid extension target type".to_string(), Some(ty.span));
                None
            }
        }
    }
}

impl HirVisitor for Actor<'_> {
    fn visit_declaration(&mut self, declaration: &hir::Declaration) -> Self::Result {
        let node = match &declaration.kind {
            hir::DeclarationKind::Extension(node) => node,
            _ => return,
        };

        self.resolve_extension_identity(declaration.id, node);
    }
}
