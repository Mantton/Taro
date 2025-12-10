use crate::{
    compile::context::Gcx,
    hir::DefinitionID,
    sema::{
        models::{CalleeOrigin, InferTy, LabeledFunctionSignature, Ty, TyKind},
        tycheck::solve::{
            ApplicationArgument, ApplicationGoal, Goal, Obligation,
            apply::{ValidationError, match_arguments_to_parameters, validate_arity},
            solver::{SolverDelegate, SolverResult},
        },
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
    pub fn solve_application(&mut self, application: &ApplicationGoal<'ctx>) -> SolverResult<'ctx> {
        let callee_ty = self.structurally_resolve(application.callee_ty);
        let gcx = self.gcx();
        // Must be Invoke-Able
        if !matches!(
            callee_ty.kind(),
            TyKind::FnPointer { .. } | TyKind::Infer(InferTy::FnVar(..) | InferTy::TyVar(..))
        ) {
            todo!("report non callable")
        }

        let callee_origin = &application.callee_origin;
        match callee_origin {
            Some(CalleeOrigin::Direct(id)) => {
                let TyKind::FnPointer { inputs, output } = callee_ty.kind() else {
                    unreachable!("ICE – Callee Ty Must be Function Pointer")
                };
                let signature = self.gcx().get_signature(*id);
                let _ =
                    validate_arity(signature, &application.arguments).expect("arity validation");
                let result = match_arguments_to_parameters(signature, &application.arguments);
                let positions = result.expect("resolution");
                let mut obligations = produce_application_subobligations(
                    positions,
                    signature,
                    inputs,
                    &application.arguments,
                )
                .expect("mapping");

                obligations.push(Obligation {
                    location: application.caller_span,
                    goal: Goal::Equal(output, application.result),
                });
                return SolverResult::Solved(obligations);
            }
            Some(CalleeOrigin::Overloaded(candidates)) => {
                // Quick Prunes
                let candidates: Vec<_> = candidates
                    .iter()
                    .filter(|&&c| quick_match(c, &application.arguments, gcx))
                    .collect();

                if candidates.len() == 0 {
                    todo!("report – no valid overloads")
                }

                // single survivor, add obligations as subgoals
                if let [candidate] = candidates.as_slice() {
                    let obligations = self.select_fn_for_application(**candidate, application);
                    return SolverResult::Solved(obligations);
                }

                todo!("multiple candidates work!");
            }
            None => {
                todo!("no callee origin – is this a valid state?")
            }
        }
    }

    fn select_fn_for_application(
        &mut self,
        candidate: DefinitionID,
        application: &ApplicationGoal<'ctx>,
    ) -> Vec<Obligation<'ctx>> {
        todo!()
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

/// Fast syntactic filter.  *No instantiation, no unification.*
fn quick_match<'ctx>(
    candidate: DefinitionID,
    call_arguments: &[ApplicationArgument<'ctx>],
    gcx: Gcx<'ctx>,
) -> bool {
    let fn_sig = gcx.get_signature(candidate);
    let call_arity = call_arguments.len();
    let min_required = fn_sig.min_parameter_count();
    let param_count = fn_sig.inputs.len();
    // ---- arity / defaults / variadic --------------------------------
    if call_arity < min_required {
        return false;
    }
    if call_arity > param_count && !fn_sig.is_variadic {
        return false;
    }

    // Labels
    let upto = call_arity.min(param_count);

    for index in 0..upto {
        let call_label = call_arguments[index].label.map(|f| f.symbol);
        let decl_label = fn_sig.inputs[index].label;
        let decl_defaulted = min_required < param_count && index >= min_required;

        match (decl_label, decl_defaulted, call_label) {
            // ❶ parameter is *unlabelled* in decl
            (None, _, Some(_)) => return false, // label where none exists
            // ❷ parameter has compulsory label
            (Some(_), false, None) => return false, // label missing
            (Some(d), false, Some(c)) if c != d => return false, // wrong label
            // ❸ parameter label is optional (defaulted) – always accept
            _ => {}
        }
    }

    return true;
}
