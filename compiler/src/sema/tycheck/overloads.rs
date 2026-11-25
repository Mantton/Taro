//! Declaration identity excludes results: overloads are selected by inputs.
use crate::{
    compile::context::Gcx,
    error::CompileResult,
    hir::{self, DefinitionID, HirVisitor},
    sema::{
        models::{Const, ConstKind, GenericParameter, Ty, TyKind},
        tycheck::{
            fold::{TypeFoldable, TypeFolder, TypeSuperFoldable},
            utils::normalize_aliases,
        },
    },
};
use rustc_hash::{FxHashMap, FxHasher};
use std::hash::{Hash, Hasher};

struct Parameters<'ctx>(Gcx<'ctx>);
impl<'ctx> TypeFolder<'ctx> for Parameters<'ctx> {
    fn gcx(&self) -> Gcx<'ctx> {
        self.0
    }
    fn fold_ty(&mut self, ty: Ty<'ctx>) -> Ty<'ctx> {
        let ty = normalize_aliases(self.0, ty);
        match ty.kind() {
            TyKind::Parameter(parameter) => Ty::new(
                TyKind::Parameter(GenericParameter {
                    name: self.0.intern_symbol(""),
                    ..parameter
                }),
                self.0,
            ),
            _ => ty.super_fold_with(self),
        }
    }
    fn fold_const(&mut self, value: Const<'ctx>) -> Const<'ctx> {
        Const {
            ty: value.ty.fold_with(self),
            kind: match value.kind {
                ConstKind::Param(parameter) => ConstKind::Param(GenericParameter {
                    name: self.0.intern_symbol(""),
                    ..parameter
                }),
                kind => kind,
            },
        }
    }
}

pub(super) fn fingerprint(gcx: Gcx<'_>, id: DefinitionID) -> u64 {
    fingerprint_with_arguments(gcx, id, None, true)
}

pub(super) fn member_fingerprint<'ctx>(
    gcx: Gcx<'ctx>,
    id: DefinitionID,
    interface: Option<crate::sema::models::InterfaceReference<'ctx>>,
) -> u64 {
    let mut hash = FxHasher::default();
    fingerprint(gcx, id).hash(&mut hash);
    // Slot[int32] and Slot[string] are separate declaration groups.
    interface
        .map(|interface| interface.fold_with(&mut Parameters(gcx)))
        .hash(&mut hash);
    hash.finish()
}

pub(super) fn declaration_target<'ctx>(
    gcx: Gcx<'ctx>,
    extension: DefinitionID,
) -> Option<Ty<'ctx>> {
    gcx.get_impl_target_ty(extension)
        .map(|ty| ty.fold_with(&mut Parameters(gcx)))
}

pub(super) fn dispatch_fingerprint<'ctx>(
    gcx: Gcx<'ctx>,
    id: DefinitionID,
    arguments: Option<crate::sema::models::GenericArguments<'ctx>>,
) -> u64 {
    fingerprint_with_arguments(gcx, id, arguments, false)
}

fn fingerprint_with_arguments<'ctx>(
    gcx: Gcx<'ctx>,
    id: DefinitionID,
    arguments: Option<crate::sema::models::GenericArguments<'ctx>>,
    include_target: bool,
) -> u64 {
    let sig = gcx.get_signature(id);
    let signature;
    let sig = if let Some(arguments) = arguments {
        signature = super::utils::instantiate::instantiate_signature_with_args(gcx, sig, arguments);
        &signature
    } else {
        sig
    };
    let mut hash = FxHasher::default();
    let mut parameters = Parameters(gcx);
    gcx.definition_is_async(id).hash(&mut hash);
    sig.is_variadic.hash(&mut hash);
    gcx.generics_of(id).parameters.len().hash(&mut hash);
    if include_target
        && let Some(target) = gcx
            .definition_parent(id)
            .and_then(|parent| gcx.get_impl_target_ty(parent))
    {
        target.fold_with(&mut parameters).hash(&mut hash);
    }
    sig.inputs.len().hash(&mut hash);
    for input in &sig.inputs {
        input.label.hash(&mut hash);
        input.ty.fold_with(&mut parameters).hash(&mut hash);
    }
    hash.finish()
}

pub(super) fn run(package: &hir::Package, gcx: Gcx<'_>) -> CompileResult<()> {
    struct Actor<'ctx>(Gcx<'ctx>);
    impl Actor<'_> {
        fn check(&self, definitions: impl IntoIterator<Item = DefinitionID>) {
            let mut seen = FxHashMap::default();
            for id in definitions {
                let ident = self.0.definition_ident(id);
                if let Some(previous) = seen.insert((ident.symbol, fingerprint(self.0, id)), id) {
                    self.0.dcx().emit_error(format!("invalid redeclaration of '{}'; return type alone cannot distinguish overloads", self.0.symbol_text(ident.symbol).as_str()), Some(ident.span));
                    self.0.dcx().emit_info(
                        "previous declaration is here".into(),
                        Some(self.0.definition_ident(previous).span),
                    );
                }
            }
        }
        fn declarations(&self, declarations: &[hir::Declaration]) {
            self.check(declarations.iter().filter_map(|declaration| {
                matches!(declaration.kind, hir::DeclarationKind::Function(_))
                    .then_some(declaration.id)
            }));
        }
    }
    impl HirVisitor for Actor<'_> {
        fn visit_module(&mut self, module: &hir::Module, root: bool) {
            self.declarations(&module.declarations);
            hir::walk_module(self, module, root);
        }
        fn visit_namespace(&mut self, namespace: &hir::Namespace) {
            self.declarations(&namespace.declarations);
            hir::walk_namespace(self, namespace);
        }
        fn visit_interface(&mut self, interface: &hir::Interface, id: DefinitionID) {
            self.check(interface.declarations.iter().filter_map(|declaration| {
                matches!(
                    declaration.kind,
                    hir::AssociatedDeclarationKind::Function(_)
                )
                .then_some(declaration.id)
            }));
            hir::walk_interface(self, interface, id);
        }
    }
    hir::walk_package(&mut Actor(gcx), package);
    gcx.dcx().ok()
}
