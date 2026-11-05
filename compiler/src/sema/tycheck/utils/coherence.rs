//! Package ownership for conformance inputs (Self, then interface arguments).
use crate::{
    PackageIndex,
    compile::context::Gcx,
    sema::{
        models::{GenericArgument, InterfaceReference, Ty, TyKind},
        tycheck::visit::{TypeSuperVisitable, TypeVisitable, TypeVisitor},
    },
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum OrphanError {
    NoLocalInput,
    UncoveredParameter,
}

enum Input {
    Local,
    Uncovered,
    Foreign,
}

/// `&T` is fundamental: it preserves locality and does not cover parameters.
/// Ordinary constructors (including raw pointers, tuples and arrays) cover
/// parameters, but a local argument does not make a foreign constructor local.
fn input<'ctx>(gcx: Gcx<'ctx>, ty: Ty<'ctx>, package: PackageIndex) -> Input {
    let ty = super::normalize_aliases(gcx, ty);
    match ty.kind() {
        TyKind::Reference(inner) => input(gcx, inner, package),
        TyKind::Parameter(_) => Input::Uncovered,
        TyKind::Adt(def, _) if def.id.package() == package => Input::Local,
        TyKind::Closure { closure_def_id, .. } if closure_def_id.package() == package => {
            Input::Local
        }
        TyKind::Alias { .. } => {
            // An unresolved projection does not introduce an owned constructor
            // or cover the parameters on which its result depends.
            struct Parameter;
            impl<'ctx> TypeVisitor<'ctx> for Parameter {
                fn visit_ty(&mut self, ty: Ty<'ctx>) -> bool {
                    matches!(ty.kind(), TyKind::Parameter(_)) || ty.super_visit_with(self)
                }
            }
            if ty.visit_with(&mut Parameter) {
                Input::Uncovered
            } else {
                Input::Foreign
            }
        }
        TyKind::Bool
        | TyKind::Rune
        | TyKind::String
        | TyKind::Int(_)
        | TyKind::UInt(_)
        | TyKind::Float(_)
        | TyKind::Tuple(_)
        | TyKind::Array { .. }
        | TyKind::Pointer(_, _)
            if gcx.is_std_package(package) =>
        {
            Input::Local
        }
        _ => Input::Foreign,
    }
}

pub(crate) fn check_orphan<'ctx>(
    gcx: Gcx<'ctx>,
    interface: InterfaceReference<'ctx>,
    package: PackageIndex,
) -> Result<(), OrphanError> {
    if interface.id.package() == package {
        return Ok(());
    }
    let mut uncovered = false;
    for argument in interface.arguments {
        let GenericArgument::Type(ty) = argument else {
            continue;
        };
        match input(gcx, *ty, package) {
            Input::Local => {
                return if uncovered {
                    Err(OrphanError::UncoveredParameter)
                } else {
                    Ok(())
                };
            }
            Input::Uncovered => uncovered = true,
            Input::Foreign => {}
        }
    }
    Err(OrphanError::NoLocalInput)
}
