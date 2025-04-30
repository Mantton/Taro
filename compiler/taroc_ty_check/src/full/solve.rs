use rustc_hash::FxHashMap;
use taroc_span::Spanned;
use taroc_ty::{Adjustment, Constraint, InterfaceReference, Ty};

use crate::{
    full::FunctionChecker,
    models::{CollectedConstraint, TaggedAdjustments, UnificationError},
};

// Define the SolverError enum
#[derive(Debug, Clone, Copy)]
pub enum SolverError<'ctx> {
    TypeMismatch {
        expected: Ty<'ctx>,
        found: Ty<'ctx>,
    },
    OccursCheck(Ty<'ctx>, Ty<'ctx>),
    BoundNotSatisfied {
        ty: Ty<'ctx>,
        interface: InterfaceReference<'ctx>,
    },
}

impl<'ctx> FunctionChecker<'ctx> {
    pub fn solve_constraints(
        &mut self,
    ) -> Result<TaggedAdjustments, Vec<Spanned<SolverError<'ctx>>>> {
        println!("\nSolve Constraints");
        let collected_constraints: Vec<CollectedConstraint<'ctx>> = self.context.take_constraints();

        let mut errors: Vec<Spanned<SolverError<'ctx>>> = vec![];
        // Only aggregate adjustments if there are no errors by the end.
        let mut aggregated_adjustments: TaggedAdjustments = FxHashMap::default();

        for collected in collected_constraints {
            // Solve the inner constraint
            let result: Result<Vec<Adjustment>, SolverError<'ctx>> =
                self.solve_constraint(collected.constraint);

            match result {
                Ok(adjustments) => {
                    // Constraint solved successfully.
                    // If we are not failing overall, record adjustments.
                    // We only know if we fail overall *after* the loop, so we
                    // store adjustments speculatively.
                    if !adjustments.is_empty() {
                        aggregated_adjustments
                            .entry(collected.node)
                            .or_default()
                            .extend(adjustments);
                    }
                }
                Err(solver_error_kind) => {
                    // Constraint failed. Collect the error, wrapped with span.
                    errors.push(Spanned {
                        span: collected.span,
                        value: solver_error_kind,
                    });
                }
            }
        }

        // Check if any errors occurred during the process
        if errors.is_empty() {
            Ok(aggregated_adjustments)
        } else {
            Err(errors)
        }
    }

    pub fn solve_constraint(
        &mut self,
        constraint: Constraint<'ctx>, // The constraint enum variant
    ) -> Result<Vec<Adjustment>, SolverError<'ctx>> {
        // Return adjustments on success
        match constraint {
            Constraint::Bound { ty, interface } => {
                println!("Check {} : {}", ty, self.context.def_symbol(interface.id));

                // --- Interface Bound Checking ---
                // TODO: Implement actual interface bound checking logic.
                println!( /* ... TODO message ... */ );
                // Example failure:
                // if !check_bound(...) { return Err(SolverErrorKind::BoundNotSatisfied { ty, interface_id: interface.id, interface_args: interface.arguments }); }

                // Assume success for now. Bound checks typically don't yield adjustments themselves.
                Ok(Vec::new())
            }
            Constraint::TypeEquality(lhs, rhs) => {
                println!("Check {} == {}", lhs, rhs);
                // --- Type Equality Checking (using coerce_or_unify) ---
                // This allows for implicit conversions according to try_coerce rules.
                let result = self.coerce_or_unify(lhs, rhs);
                match result {
                    Ok(adjustments) => Ok(adjustments),
                    Err(unification_error) => match unification_error {
                        UnificationError::TypeMismatch => Err(SolverError::TypeMismatch {
                            expected: rhs,
                            found: lhs,
                        }),
                        UnificationError::OccursCheckFailed => {
                            Err(SolverError::OccursCheck(lhs, rhs))
                        }
                    },
                }
            }
        }
    }
}
