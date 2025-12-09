use crate::sema::{
    models::{CalleeOrigin, LabeledFunctionSignature, Ty, TyKind},
    tycheck::solve::{
        ApplicationArgument, ApplicationGoal, Goal, Obligation,
        apply::{ValidationError, match_arguments_to_parameters, validate_arity},
        solver::{SolverDelegate, SolverResult},
    },
};

impl<'icx, 'ctx> SolverDelegate<'icx, 'ctx> {
    pub fn solve_equality(&mut self, lhs: Ty<'ctx>, rhs: Ty<'ctx>) -> SolverResult<'ctx> {
        match self.unify(lhs, rhs) {
            Ok(_) => SolverResult::Solved(vec![]),
            Err(e) => SolverResult::Error(e),
        }
    }
}

impl<'icx, 'ctx> SolverDelegate<'icx, 'ctx> {
    pub fn solve_application(&mut self, application: ApplicationGoal<'ctx>) -> SolverResult<'ctx> {
        let callee_ty = self.structurally_resolve(application.callee_ty);
        let callee_origin = application.callee_origin;

        let (inputs, output) = match callee_ty.kind() {
            TyKind::FnPointer { inputs, output } => (inputs, output),
            TyKind::Infer(_) => return SolverResult::Deferred, // No Progress
            _ => unreachable!("not callable"),
        };

        let mut subobligations = vec![];
        match callee_origin {
            Some(CalleeOrigin::Direct(id)) => {
                let signature = self.gcx().get_signature(id);
                let _ = validate_arity(signature, application.arguments).expect("arity validation");
                let result = match_arguments_to_parameters(signature, application.arguments);
                let positions = result.expect("resolution");
                let obligations = produce_application_subobligations(
                    positions,
                    signature,
                    inputs,
                    application.arguments,
                )
                .expect("mapping");
                subobligations.extend(obligations);
            }
            Some(CalleeOrigin::Overloaded(candidates)) => {}
            None => {
                todo!("simple arity checks")
            }
        }

        subobligations.push(Obligation {
            location: application.caller_span,
            goal: Goal::Equal(output, application.result),
        });

        return SolverResult::Solved(subobligations);
    }
}

fn produce_application_subobligations<'c>(
    positions: Vec<Option<usize>>,
    signature: &LabeledFunctionSignature<'c>,
    inputs: &[Ty<'c>],
    arguments: &[ApplicationArgument<'c>],
) -> Result<Vec<Obligation<'c>>, ValidationError> {
    let mut o = vec![];
    for (param_idx, arg_idx) in positions.iter().enumerate() {
        let param_defaults = signature.inputs[param_idx].has_default;
        let param_ty = inputs[param_idx];

        if let Some(arg_idx) = arg_idx {
            let argument = arguments[*arg_idx];
            let arg_ty = argument.ty;
            let constraint = Goal::Equal(arg_ty, param_ty);
            let obligatin = Obligation {
                location: argument.span,
                goal: constraint,
            };
            o.push(obligatin);
        } else if !param_defaults {
            let err = ValidationError::MissingRequiredParameter {
                param_index: param_idx,
                param_name: signature.inputs[param_idx].name,
            };
            return Err(err);
        }
    }

    return Ok(o);
}
