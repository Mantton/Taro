mod candidate;
mod canonical;
mod goal;
pub mod ref_ops;
mod select;
pub(crate) mod witness;

use crate::{
    compile::context::Gcx,
    sema::models::{
        ConformanceWitness, GenericArguments, InterfaceGoal, SelectionError, SelectionMode, Ty,
    },
};

pub(crate) use select::deduce_conformance_interface;
pub(crate) use select::{builtin_copy_clone, closure_clone_fields};
pub use select::{prove_interface_goal, select_interface_impl};
pub(crate) use witness::{
    class_receiver_requires_dynamic_self, find_method_witness, property_requirement_satisfied,
    validate_class_default_adoptions,
};

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
