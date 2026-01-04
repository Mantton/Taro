use crate::constants::STD_PREFIX;
use crate::{
    compile::context::GlobalContext,
    error::CompileResult,
    hir::{self, DefinitionID, HirVisitor, Resolution},
    sema::resolve::models::{DefinitionKind, TypeHead},
    span::Span,
};
use rustc_hash::{FxHashMap, FxHashSet};

pub fn run(package: &hir::Package, context: GlobalContext) -> CompileResult<()> {
    let alias_targets = collect_alias_targets(package);
    let mut actor = Actor {
        context,
        alias_targets,
        alias_visiting: FxHashSet::default(),
    };
    hir::walk_package(&mut actor, package);
    context.dcx().ok()
}

struct Actor<'ctx> {
    context: GlobalContext<'ctx>,
    alias_targets: FxHashMap<DefinitionID, hir::Type>,
    alias_visiting: FxHashSet<DefinitionID>,
}

impl<'ctx> Actor<'ctx> {
    fn resolve_extension_identity(&mut self, extension_id: DefinitionID, node: &hir::Extension) {
        let Some(head) = self.type_head_for_node(&node.ty) else {
            return;
        };

        self.context.cache_extension_type_head(extension_id, head);
    }

    fn is_std_package(&self, pkg: crate::PackageIndex) -> bool {
        matches!(
            self.context.package_ident(pkg).as_ref().map(|s| s.as_str()),
            Some(STD_PREFIX)
        )
    }

    fn extension_owns_type(&self, head: TypeHead, extension_pkg: crate::PackageIndex) -> bool {
        match head {
            TypeHead::Nominal(id) => id.package() == extension_pkg,
            TypeHead::Primary(_)
            | TypeHead::GcPtr
            | TypeHead::Tuple(_)
            | TypeHead::Reference(_)
            | TypeHead::Pointer(_)
            | TypeHead::Array => self.is_std_package(extension_pkg),
        }
    }

    fn validate_inherent_extension(&mut self, extension_id: DefinitionID, node: &hir::Extension) {
        let has_conformance = node
            .conformances
            .as_ref()
            .is_some_and(|c| !c.bounds.is_empty());
        if has_conformance {
            return;
        }

        let Some(head) = self.context.get_extension_type_head(extension_id) else {
            return;
        };

        let extension_pkg = extension_id.package();
        if self.extension_owns_type(head, extension_pkg) {
            return;
        }

        self.context.dcx().emit_error(
            "cannot extend type from another package without interface conformance".to_string(),
            Some(node.ty.span),
        );
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
                    DefinitionKind::TypeAlias => self.type_head_for_alias(*id, ty.span),
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

    fn type_head_for_alias(&mut self, alias_id: DefinitionID, span: Span) -> Option<TypeHead> {
        if !self.alias_visiting.insert(alias_id) {
            self.context.dcx().emit_error(
                "circular type alias in extension target".to_string(),
                Some(span),
            );
            return None;
        }

        let alias_ty = self.alias_targets.get(&alias_id).cloned();
        let head = if let Some(alias_ty) = alias_ty {
            self.type_head_for_node(&alias_ty)
        } else {
            Some(TypeHead::Nominal(alias_id))
        };

        self.alias_visiting.remove(&alias_id);
        head
    }
}

impl HirVisitor for Actor<'_> {
    fn visit_declaration(&mut self, declaration: &hir::Declaration) -> Self::Result {
        let node = match &declaration.kind {
            hir::DeclarationKind::Extension(node) => node,
            _ => return,
        };

        self.resolve_extension_identity(declaration.id, node);
        self.validate_inherent_extension(declaration.id, node);
    }
}

fn collect_alias_targets(package: &hir::Package) -> FxHashMap<DefinitionID, hir::Type> {
    let mut targets = FxHashMap::default();
    collect_alias_targets_in_module(&package.root, &mut targets);
    targets
}

fn collect_alias_targets_in_module(
    module: &hir::Module,
    targets: &mut FxHashMap<DefinitionID, hir::Type>,
) {
    for decl in &module.declarations {
        if let hir::DeclarationKind::TypeAlias(alias) = &decl.kind {
            if let Some(ty) = &alias.ty {
                targets.insert(decl.id, (**ty).clone());
            }
        }
    }

    for submodule in &module.submodules {
        collect_alias_targets_in_module(submodule, targets);
    }
}
