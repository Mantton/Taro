use crate::{
    sema::{models::LabeledFunctionSignature, tycheck::solve::ApplicationArgument},
    span::Symbol,
};

// Validation errors
#[derive(Debug, Clone)]
pub enum ValidationError {
    ArityMismatch {
        expected_min: usize,
        expected_max: Option<usize>,
        provided: usize,
    },
    LabelMismatch {
        param_index: usize,
        expected: Option<Symbol>,
        provided: Option<Symbol>,
    },
    MissingRequiredParameter {
        param_index: usize,
        param_name: Symbol,
    },
    ExtraArgument {
        arg_index: usize,
    },
}

impl std::fmt::Display for ValidationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ValidationError::ArityMismatch {
                expected_min,
                expected_max,
                provided,
            } => match expected_max {
                Some(max) if max == expected_min => {
                    write!(
                        f,
                        "Expected exactly {} argument{}, but {} {} provided",
                        expected_min,
                        if *expected_min == 1 { "" } else { "s" },
                        provided,
                        if *provided == 1 { "was" } else { "were" }
                    )
                }
                Some(max) => {
                    write!(
                        f,
                        "Expected {}-{} arguments, but {} {} provided",
                        expected_min,
                        max,
                        provided,
                        if *provided == 1 { "was" } else { "were" }
                    )
                }
                None => {
                    write!(
                        f,
                        "Expected at least {} argument{}, but {} {} provided",
                        expected_min,
                        if *expected_min == 1 { "" } else { "s" },
                        provided,
                        if *provided == 1 { "was" } else { "were" }
                    )
                }
            },
            ValidationError::LabelMismatch {
                param_index,
                expected,
                provided,
            } => match (expected, provided) {
                (Some(exp), Some(prov)) => {
                    write!(
                        f,
                        "Argument label mismatch at parameter {}: expected '{}', but '{}' was provided",
                        param_index + 1,
                        exp,
                        prov
                    )
                }
                (Some(exp), None) => {
                    write!(
                        f,
                        "Missing argument label at parameter {}: expected '{}', but no label was provided",
                        param_index + 1,
                        exp
                    )
                }
                (None, Some(prov)) => {
                    write!(
                        f,
                        "Unexpected argument label at parameter {}: '{}' was provided, but no label was expected",
                        param_index + 1,
                        prov
                    )
                }
                (None, None) => {
                    write!(f, "Label validation error at parameter {}", param_index + 1)
                }
            },
            ValidationError::MissingRequiredParameter {
                param_index,
                param_name,
            } => {
                write!(
                    f,
                    "Missing required parameter '{}' at position {}",
                    param_name,
                    param_index + 1
                )
            }
            ValidationError::ExtraArgument { arg_index } => {
                write!(
                    f,
                    "Extra argument at position {}: no corresponding parameter",
                    arg_index + 1
                )
            }
        }
    }
}

impl std::error::Error for ValidationError {}

pub fn validate_arity<'ctx>(
    signature: &LabeledFunctionSignature,
    arguments: &[ApplicationArgument],
) -> Result<(), ValidationError> {
    let call_arity = arguments.len();
    let min_required = signature.min_parameter_count();
    let param_count = signature.inputs.len();
    let max_params = if signature.is_variadic {
        None
    } else {
        Some(signature.inputs.len())
    };

    // ---- arity / defaults / variadic --------------------------------
    if call_arity < min_required {
        // Report Arity Mismatch, Expected At Least
        return Err(ValidationError::ArityMismatch {
            expected_min: min_required,
            expected_max: max_params,
            provided: arguments.len(),
        });
    }

    if call_arity > param_count && !signature.is_variadic {
        // Report Arity Mismatch, Expected At Most
        return Err(ValidationError::ArityMismatch {
            expected_min: min_required,
            expected_max: max_params,
            provided: arguments.len(),
        });
    }

    return Ok(());
}

// Match arguments to parameters considering labels
pub fn match_arguments_to_parameters(
    signature: &LabeledFunctionSignature,
    arguments: &[ApplicationArgument],
) -> Result<Vec<Option<usize>>, ValidationError> {
    let mut param_to_arg: Vec<Option<usize>> = vec![None; signature.inputs.len()];
    let mut used_args = vec![false; arguments.len()];

    // First pass: match labeled arguments
    for (arg_idx, arg) in arguments.iter().enumerate() {
        if let Some(arg_label) = &arg.label {
            let mut found = false;
            for (param_idx, param) in signature.inputs.iter().enumerate() {
                if param.label.as_ref() == Some(&arg_label.symbol) {
                    if param_to_arg[param_idx].is_some() {
                        // Duplicate label - this is an error
                        return Err(ValidationError::LabelMismatch {
                            param_index: param_idx,
                            expected: param.label.clone(),
                            provided: arg.label.map(|f| f.symbol),
                        });
                    }
                    param_to_arg[param_idx] = Some(arg_idx);
                    used_args[arg_idx] = true;
                    found = true;
                    break;
                }
            }
            if !found {
                return Err(ValidationError::LabelMismatch {
                    param_index: 0, // We don't know which parameter this was meant for
                    expected: None,
                    provided: arg.label.map(|f| f.symbol),
                });
            }
        }
    }

    // Second pass: match positional arguments
    let mut param_idx = 0;
    for (arg_idx, arg) in arguments.iter().enumerate() {
        if used_args[arg_idx] {
            continue; // Already matched by label
        }

        if arg.label.is_some() {
            continue; // This was a labeled argument that didn't match
        }

        // Find next available parameter
        while param_idx < signature.inputs.len() && param_to_arg[param_idx].is_some() {
            param_idx += 1;
        }

        if param_idx >= signature.inputs.len() {
            return Err(ValidationError::ExtraArgument { arg_index: arg_idx });
        }

        let param = &signature.inputs[param_idx];

        // Check if this parameter expects a label
        if param.label.is_some() {
            return Err(ValidationError::LabelMismatch {
                param_index: param_idx,
                expected: param.label.clone(),
                provided: None,
            });
        }

        param_to_arg[param_idx] = Some(arg_idx);
        used_args[arg_idx] = true;
        param_idx += 1;
    }

    Ok(param_to_arg)
}
