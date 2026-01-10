use crate::{
    sema::{
        error::{ApplyValidationError, TypeError},
        models::{LabeledFunctionParameter, LabeledFunctionSignature, Ty, TyKind},
        tycheck::solve::{
            ApplyArgument, ApplyGoalData, ConstraintSolver, Goal, Obligation, SolverResult,
        },
    },
    span::{Spanned, Symbol},
};

impl<'ctx> ConstraintSolver<'ctx> {
    pub fn solve_apply(&mut self, data: ApplyGoalData<'ctx>) -> SolverResult<'ctx> {
        let callee_ty = self.icx.resolve_vars_if_possible(data.callee_ty);
        if callee_ty.is_error() {
            // Avoid cascading errors when the callee already failed to type-check.
            return SolverResult::Solved(vec![]);
        }
        let callee_source = data
            .callee_source
            .or_else(|| self.icx.overload_binding_for_ty(data.callee_ty));

        let (inputs, output) = match callee_ty.kind() {
            TyKind::FnPointer { inputs, output } => (inputs, output),
            TyKind::Infer(_) => return SolverResult::Deferred,
            _ => {
                return SolverResult::Error(vec![Spanned::new(
                    TypeError::NotCallable { found: callee_ty },
                    data.call_span,
                )]);
            }
        };

        let signature = if let Some(id) = callee_source {
            self.gcx().get_signature(id)
        } else {
            &LabeledFunctionSignature {
                inputs: inputs
                    .iter()
                    .map(|&t| LabeledFunctionParameter {
                        label: None,
                        name: Symbol::new(""),
                        ty: t,
                        default_provider: None,
                    })
                    .collect(),
                output,
                is_variadic: false,
                abi: None,
            }
        };

        // 1 - Arity
        let result = validate_arity(signature, &data.arguments);
        match result {
            Err(e) => {
                return SolverResult::Error(vec![Spanned::new(
                    TypeError::Apply(e),
                    data.call_span,
                )]);
            }
            _ => {}
        }

        // 2 - Matching
        let result = match_arguments_to_parameters(signature, &data.arguments, data.skip_labels);
        let positions = match result {
            Ok(v) => v,
            Err(e) => {
                return SolverResult::Error(vec![Spanned::new(TypeError::Apply(e.value), e.span)]);
            }
        };

        let result =
            produce_application_subobligations(positions, signature, inputs, &data.arguments);
        let mut obligations = match result {
            Ok(v) => v,
            Err(e) => {
                return SolverResult::Error(vec![Spanned::new(
                    TypeError::Apply(e),
                    data.call_span,
                )]);
            }
        };

        obligations.push(Obligation {
            location: data.call_span,
            goal: Goal::Coerce {
                node_id: data.call_node_id,
                from: data.result_ty,
                to: output,
            },
        });

        return SolverResult::Solved(obligations);
    }
}

pub fn validate_arity<'ctx>(
    signature: &LabeledFunctionSignature,
    arguments: &[ApplyArgument],
) -> Result<(), ApplyValidationError> {
    let call_arity = arguments.len();
    let min_required = signature.min_parameter_count();
    let param_count = signature.inputs.len();
    let max_params = if signature.is_variadic {
        None
    } else {
        Some(signature.inputs.len())
    };

    // ---- arity / defaults / variadic --------------------------------
    let effective_min = if signature.is_variadic && min_required > 0 {
        min_required - 1
    } else {
        min_required
    };

    if call_arity < effective_min {
        // Report Arity Mismatch, Expected At Least
        return Err(ApplyValidationError::ArityMismatch {
            expected_min: effective_min,
            expected_max: max_params,
            provided: arguments.len(),
        });
    }

    if call_arity > param_count && !signature.is_variadic {
        // Report Arity Mismatch, Expected At Most
        return Err(ApplyValidationError::ArityMismatch {
            expected_min: effective_min,
            expected_max: max_params,
            provided: arguments.len(),
        });
    }

    return Ok(());
}

// Match arguments to parameters considering labels
pub fn match_arguments_to_parameters(
    signature: &LabeledFunctionSignature,
    arguments: &[ApplyArgument],
    skip_labels: bool,
) -> Result<Vec<Vec<usize>>, Spanned<ApplyValidationError>> {
    let mut param_to_arg: Vec<Vec<usize>> = vec![vec![]; signature.inputs.len()];
    let mut used_args = vec![false; arguments.len()];

    // First pass: match labeled arguments (skip if skip_labels is true)
    if !skip_labels {
        for (arg_idx, arg) in arguments.iter().enumerate() {
            if let Some(arg_label) = &arg.label {
                let mut found = false;
                for (param_idx, param) in signature.inputs.iter().enumerate() {
                    if param.label.as_ref() == Some(&arg_label.symbol) {
                        if !param_to_arg[param_idx].is_empty() {
                            // Duplicate label - this is an error
                            return Err(Spanned::new(
                                ApplyValidationError::LabelMismatch {
                                    param_index: param_idx,
                                    expected: param.label.clone(),
                                    provided: arg.label.map(|f| f.symbol),
                                },
                                arg.span,
                            ));
                        }
                        param_to_arg[param_idx].push(arg_idx);
                        used_args[arg_idx] = true;
                        found = true;
                        break;
                    }
                }
                if !found {
                    return Err(Spanned::new(
                        ApplyValidationError::LabelMismatch {
                            param_index: 0, // We don't know which parameter this was meant for
                            expected: None,
                            provided: arg.label.map(|f| f.symbol),
                        },
                        arg.span,
                    ));
                }
            }
        }
    }

    // Second pass: match positional arguments
    let mut param_idx = 0;
    for (arg_idx, arg) in arguments.iter().enumerate() {
        if used_args[arg_idx] {
            continue; // Already matched by label
        }

        if !skip_labels && arg.label.is_some() {
            continue; // This was a labeled argument that didn't match
        }

        // Find next available parameter
        while param_idx < signature.inputs.len() && !param_to_arg[param_idx].is_empty() {
            param_idx += 1;
        }

        // If we are out of parameters, check if the last one is variadic
        if param_idx >= signature.inputs.len() {
            if signature.is_variadic {
                // Determine the index of the variadic parameter (always the last one)
                let variadic_idx = signature.inputs.len() - 1;
                param_to_arg[variadic_idx].push(arg_idx);
                used_args[arg_idx] = true;
                continue;
            }

            return Err(Spanned::new(
                ApplyValidationError::ExtraArgument { arg_index: arg_idx },
                arg.span,
            ));
        }

        let param = &signature.inputs[param_idx];

        // Check if this parameter expects a label (skip if skip_labels is true)
        if !skip_labels && param.label.is_some() {
            return Err(Spanned::new(
                ApplyValidationError::LabelMismatch {
                    param_index: param_idx,
                    expected: param.label.clone(),
                    provided: None,
                },
                arg.span,
            ));
        }

        param_to_arg[param_idx].push(arg_idx);
        used_args[arg_idx] = true;

        // If this is NOT the variadic parameter, advance.
        // If it IS variadic, we stay on it to collect more positional args.
        if !(signature.is_variadic && param_idx == signature.inputs.len() - 1) {
            param_idx += 1;
        }
    }

    Ok(param_to_arg)
}

fn produce_application_subobligations<'c>(
    positions: Vec<Vec<usize>>,
    signature: &LabeledFunctionSignature<'c>,
    inputs: &[Ty<'c>],
    arguments: &[ApplyArgument<'c>],
) -> Result<Vec<Obligation<'c>>, ApplyValidationError> {
    let mut obligations = vec![];
    for (param_idx, arg_indices) in positions.iter().enumerate() {
        let param_defaults = signature.inputs[param_idx].default_provider.is_some();
        let param_ty = inputs[param_idx];

        if !arg_indices.is_empty() {
            // Determine expected type for the arguments
            // If this is the variadic parameter, we need to extract T from List[T]
            let expected_ty = if signature.is_variadic && param_idx == signature.inputs.len() - 1 {
                 if let TyKind::Adt(_, args) = param_ty.kind() {
                     if let Some(crate::sema::models::GenericArgument::Type(inner)) = args.get(0) {
                         *inner
                     } else {
                         // Should not happen if well-formed
                         param_ty 
                     }
                 } else {
                     param_ty
                 }
            } else {
                 param_ty
            };

            for &arg_idx in arg_indices {
                let argument = arguments[arg_idx];
                let arg_ty = argument.ty;
                let constraint = Goal::Coerce {
                    node_id: argument.id,
                    from: arg_ty,
                    to: expected_ty,
                };
                let obligatin = Obligation {
                    location: argument.span,
                    goal: constraint,
                };
                obligations.push(obligatin);
            }
        } else if !param_defaults {
            // If it is variadic main parameter, it is allowed to be empty (it will be an empty list)
            let is_variadic_param = signature.is_variadic && param_idx == signature.inputs.len() - 1;
            
            if !is_variadic_param {
                let err = ApplyValidationError::MissingRequiredParameter {
                    param_index: param_idx,
                    param_name: signature.inputs[param_idx].name,
                };
                return Err(err);
            }
        }
    }

    return Ok(obligations);
}
