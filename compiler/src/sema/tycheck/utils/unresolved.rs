use crate::compile::context::Gcx;
use crate::sema::{
    models::{Const, ConstKind, GenericArgument, InterfaceGoal, InterfaceReference, Ty, TyKind},
    tycheck::visit::{TypeSuperVisitable, TypeVisitable, TypeVisitor},
};

struct UnresolvedInference;
impl<'ctx> TypeVisitor<'ctx> for UnresolvedInference {
    fn visit_ty(&mut self, ty: Ty<'ctx>) -> bool {
        matches!(ty.kind(), TyKind::Infer(_)) || ty.super_visit_with(self)
    }
    fn visit_const(&mut self, value: Const<'ctx>) -> bool {
        matches!(value.kind, ConstKind::Infer(_)) || value.ty.visit_with(self)
    }
}

pub fn goal_contains_unresolved_inference(goal: InterfaceGoal<'_>) -> bool {
    goal.visit_with(&mut UnresolvedInference)
}

pub fn interface_ref_contains_unresolved_inference(interface: InterfaceReference<'_>) -> bool {
    interface.visit_with(&mut UnresolvedInference)
}

pub fn generic_arg_contains_unresolved_inference(arg: &GenericArgument<'_>) -> bool {
    arg.visit_with(&mut UnresolvedInference)
}

pub fn ty_contains_unresolved_inference(ty: Ty<'_>) -> bool {
    ty.visit_with(&mut UnresolvedInference)
}

/// Concrete code generation requires substitution, inference and alias
/// normalization to have finished, including in constants and closures.
pub(crate) fn contains_unresolved_generics<'ctx>(value: impl TypeVisitable<'ctx>) -> bool {
    struct UnresolvedGenerics {
        depth: u32,
    }
    impl<'ctx> TypeVisitor<'ctx> for UnresolvedGenerics {
        fn visit_ty(&mut self, ty: Ty<'ctx>) -> bool {
            match ty.kind() {
                TyKind::ExistentialSelf(index) => index >= self.depth,
                TyKind::BoxedExistential { .. } => {
                    self.depth += 1;
                    let unresolved = ty.super_visit_with(self);
                    self.depth -= 1;
                    unresolved
                }
                TyKind::Parameter(_) | TyKind::Infer(_) | TyKind::Alias { .. } => true,
                _ => ty.super_visit_with(self),
            }
        }
        fn visit_const(&mut self, value: Const<'ctx>) -> bool {
            matches!(value.kind, ConstKind::Param(_) | ConstKind::Infer(_))
                || value.ty.visit_with(self)
        }
    }
    value.visit_with(&mut UnresolvedGenerics { depth: 0 })
}

/// Storage substitution excludes the Self bound by an existential witness
/// table, but includes free type/const parameters and inference variables.
pub(crate) fn storage_needs_substitution<'ctx>(_gcx: Gcx<'ctx>, ty: Ty<'ctx>) -> bool {
    struct Check;
    impl<'ctx> TypeVisitor<'ctx> for Check {
        fn visit_ty(&mut self, ty: Ty<'ctx>) -> bool {
            matches!(ty.kind(), TyKind::Parameter(_) | TyKind::Infer(_))
                || ty.super_visit_with(self)
        }
        fn visit_const(&mut self, value: crate::sema::models::Const<'ctx>) -> bool {
            matches!(
                value.kind,
                crate::sema::models::ConstKind::Param(_) | crate::sema::models::ConstKind::Infer(_)
            ) || value.ty.visit_with(self)
        }
    }
    super::erased_self::has_free_self(ty) || ty.visit_with(&mut Check)
}
