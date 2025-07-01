use taroc_span::Span;

use crate::{
    check::solver::{Goal, Obligation, SolverDelegate, SolverResult},
    error::TypeError,
    ty::{ConformanceResult, Constraint, GenericArgument},
    utils::instantiate_constraint_with_args,
};

impl<'icx, 'ctx, 'rcx> SolverDelegate<'icx, 'ctx, 'rcx> {
    pub fn solve_constraint(
        &mut self,
        constraint: Constraint<'ctx>,
        location: Span,
    ) -> SolverResult<'ctx> {
        let gcx = self.gcx();

        match constraint {
            Constraint::Bound { ty, interface } => {
                let ty = self.icx().shallow_resolve(ty);
                let interface = self.icx().resolve_vars_if_possible(interface);

                if self.in_param_env(ty, interface) {
                    // satisfied by environment
                    return SolverResult::Solved(vec![]);
                }

                // TODO: Type Variables should defer?
                if ty.is_ty_var() {
                    return SolverResult::Deferred;
                }

                let simple_ty = gcx.try_simple_type(ty);

                let Some(_) = simple_ty else {
                    unreachable!("try_simple_ty must always pass")
                };

                match gcx.has_conformance(ty, interface) {
                    ConformanceResult::NotConformant => {
                        return SolverResult::Error(TypeError::ConformanceNotMet(ty, interface));
                    }
                    ConformanceResult::Conforms(cond) => {
                        let mut subobligations = vec![];

                        // Conditionally Conforms To Value
                        if let Some(extension) = cond {
                            let predicates = gcx.canon_predicates_of(extension);
                            let generics = gcx.generics_of(extension);
                            let mut args: Vec<GenericArgument<'ctx>> = Vec::new();
                            if generics.has_self {
                                args.push(GenericArgument::Type(ty));
                            }
                            if let Some(_) = ty.adt_def() {
                                if let Some(adt_args) = ty.get_adt_arguments() {
                                    args.extend_from_slice(adt_args);
                                }
                            }
                            let args = gcx.store.interners.intern_generic_args(&args);

                            // Instantiate Function Predicates
                            predicates.iter().for_each(|spanned| {
                                let constraint =
                                    instantiate_constraint_with_args(gcx, spanned.value, args);
                                subobligations.push(Obligation {
                                    location,
                                    goal: Goal::Constraint(constraint),
                                });
                            });
                        }

                        return SolverResult::Solved(subobligations);
                    }
                }
            }
            Constraint::TypeEquality(a, b) => {
                return match self.unify(a, b) {
                    Ok(()) => SolverResult::Solved(vec![]),
                    Err(e) => SolverResult::Error(e),
                };
            }
        }
    }

    fn in_param_env(
        &self,
        ty: crate::ty::Ty<'ctx>,
        iface: crate::ty::InterfaceReference<'ctx>,
    ) -> bool {
        self.param_env.constraints.iter().any(|&c| match c {
            Constraint::Bound {
                ty: b_ty,
                interface: b_iface,
            } => b_ty == ty && b_iface == iface,
            _ => false,
        })
    }
}
