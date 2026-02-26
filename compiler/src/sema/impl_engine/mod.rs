mod candidate;
mod canonical;
mod goal;
mod select;
mod witness;

use crate::{
    compile::context::Gcx,
    sema::models::{
        ConformanceWitness, GenericArguments, InterfaceGoal, SelectionError, SelectionMode, Ty,
    },
};

pub use select::{prove_interface_goal, select_interface_impl};
pub(crate) use witness::method_signature_matches;

pub fn build_conformance_witness<'ctx>(
    gcx: Gcx<'ctx>,
    goal: InterfaceGoal<'ctx>,
    mode: SelectionMode,
) -> Result<ConformanceWitness<'ctx>, SelectionError<'ctx>> {
    witness::build_conformance_witness(gcx, goal, mode)
}

pub fn deduce_impl_subst<'ctx>(
    gcx: Gcx<'ctx>,
    extension_id: crate::hir::DefinitionID,
    self_ty: Ty<'ctx>,
    _param_env: &'ctx [crate::sema::models::Constraint<'ctx>],
) -> Option<GenericArguments<'ctx>> {
    select::deduce_impl_subst(gcx, extension_id, self_ty)
}
