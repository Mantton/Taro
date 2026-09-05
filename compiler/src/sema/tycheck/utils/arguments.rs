use crate::{
    sema::{
        error::ApplyValidationError,
        models::{LabeledFunctionParameter, LabeledFunctionSignature},
    },
    span::{Identifier, Span, Spanned},
};

pub(crate) fn validate_arity(
    signature: &LabeledFunctionSignature,
    call_arity: usize,
) -> Result<(), ApplyValidationError> {
    let min_required = signature.min_parameter_count();
    let param_count = signature.inputs.len();
    let max_params = if signature.is_variadic {
        None
    } else {
        Some(signature.inputs.len())
    };

    let effective_min = min_required.saturating_sub(usize::from(signature.is_variadic));
    if call_arity < effective_min || (!signature.is_variadic && call_arity > param_count) {
        return Err(ApplyValidationError::ArityMismatch {
            expected_min: effective_min,
            expected_max: max_params,
            provided: call_arity,
        });
    }
    Ok(())
}

/// Match labels first, then positional arguments, retaining source indices per parameter.
/// Missing arguments are checked separately so callers can supply default providers.
pub(crate) fn match_arguments_to_parameters(
    parameters: &[LabeledFunctionParameter<'_>],
    is_variadic: bool,
    arguments: impl Iterator<Item = (Option<Identifier>, Span)> + Clone,
    skip_labels: bool,
) -> Result<Vec<Vec<usize>>, Spanned<ApplyValidationError>> {
    let mut positions = vec![Vec::new(); parameters.len()];
    if !skip_labels {
        for (arg_index, (label, span)) in arguments.clone().enumerate() {
            let Some(label) = label else { continue };
            let Some(param_index) = parameters
                .iter()
                .position(|param| param.label == Some(label.symbol))
            else {
                return Err(Spanned::new(
                    ApplyValidationError::LabelMismatch {
                        param_index: 0,
                        expected: None,
                        provided: Some(label.symbol),
                    },
                    span,
                ));
            };
            if !positions[param_index].is_empty() {
                return Err(Spanned::new(
                    ApplyValidationError::LabelMismatch {
                        param_index,
                        expected: parameters[param_index].label,
                        provided: Some(label.symbol),
                    },
                    span,
                ));
            }
            positions[param_index].push(arg_index);
        }
    }

    let mut param_index = 0;
    for (arg_index, (label, span)) in arguments.enumerate() {
        if !skip_labels && label.is_some() {
            continue;
        }
        while param_index < parameters.len() {
            let param = &parameters[param_index];
            if positions[param_index].is_empty()
                && (skip_labels || param.label.is_none() || param.default_provider.is_none())
            {
                break;
            }
            param_index += 1;
        }
        let Some(param) = parameters.get(param_index) else {
            if is_variadic && !parameters.is_empty() {
                positions.last_mut().unwrap().push(arg_index);
                continue;
            }
            return Err(Spanned::new(
                ApplyValidationError::ExtraArgument { arg_index },
                span,
            ));
        };
        if !skip_labels && param.label.is_some() {
            return Err(Spanned::new(
                ApplyValidationError::LabelMismatch {
                    param_index,
                    expected: param.label,
                    provided: None,
                },
                span,
            ));
        }
        positions[param_index].push(arg_index);
        param_index += 1;
    }
    Ok(positions)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{hir::DefinitionID, mir::test_support::with_test_gcx, span::FileID};

    #[test]
    fn labels_defaults_and_variadics_share_parameter_order() {
        with_test_gcx(|gcx| {
            let span = Span::empty(FileID::new(0));
            let label = gcx.intern_symbol("option");
            let param = LabeledFunctionParameter {
                label: None,
                name: label,
                ty: gcx.types.int,
                default_provider: None,
            };
            let mut optional = param.clone();
            optional.label = Some(label);
            optional.default_provider = Some(DefinitionID::new(gcx.package_index(), 0.into()));
            let parameters = [param.clone(), optional, param];
            let labeled = Some(Identifier::new(label, span));
            for (labels, variadic, skip_labels, expected) in [
                (
                    vec![None, None],
                    false,
                    false,
                    vec![vec![0], vec![], vec![1]],
                ),
                (
                    vec![labeled, None, None],
                    false,
                    false,
                    vec![vec![1], vec![0], vec![2]],
                ),
                (
                    vec![None, None, None, None],
                    true,
                    false,
                    vec![vec![0], vec![], vec![1, 2, 3]],
                ),
                (
                    vec![None, None, None],
                    false,
                    true,
                    vec![vec![0], vec![1], vec![2]],
                ),
            ] {
                let actual = match_arguments_to_parameters(
                    &parameters,
                    variadic,
                    labels.into_iter().map(|label| (label, span)),
                    skip_labels,
                )
                .unwrap();
                assert_eq!(actual, expected);
            }
            // Method receivers are already lowered; match only the remaining parameters.
            let actual = match_arguments_to_parameters(
                &parameters[1..],
                false,
                [(None, span)].into_iter(),
                false,
            )
            .unwrap();
            assert_eq!(actual, vec![vec![], vec![0]]);
        });
    }

    #[test]
    fn label_errors_identify_the_offending_argument() {
        with_test_gcx(|gcx| {
            let first = Span::empty(FileID::new(1));
            let second = Span::empty(FileID::new(2));
            let label = gcx.intern_symbol("value");
            let unknown = gcx.intern_symbol("unknown");
            let parameters = [LabeledFunctionParameter {
                label: Some(label),
                name: label,
                ty: gcx.types.int,
                default_provider: None,
            }];
            for (arguments, expected_label, provided) in [
                (
                    vec![
                        (Some(Identifier::new(label, first)), first),
                        (Some(Identifier::new(label, second)), second),
                    ],
                    Some(label),
                    Some(label),
                ),
                (
                    vec![(Some(Identifier::new(unknown, second)), second)],
                    None,
                    Some(unknown),
                ),
                (vec![(None, second)], Some(label), None),
            ] {
                let error =
                    match_arguments_to_parameters(&parameters, false, arguments.into_iter(), false)
                        .unwrap_err();
                assert_eq!(error.span, second);
                assert!(matches!(error.value, ApplyValidationError::LabelMismatch {
                    param_index: 0, expected, provided: actual,
                } if expected == expected_label && actual == provided));
            }
        });
    }
}
