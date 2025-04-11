use taroc_context::GlobalContext;
use taroc_ty::{LabeledFunctionParameter, LabeledFunctionSignature};

use crate::lower::lower_type;

pub fn convert_to_labeled_signature<'ctx>(
    func: &taroc_hir::Function,
    context: GlobalContext<'ctx>,
) -> LabeledFunctionSignature<'ctx> {
    let is_async = func.signature.is_async;
    let inputs: Vec<LabeledFunctionParameter> = func
        .signature
        .prototype
        .inputs
        .iter()
        .map(|i| convert_to_labeled_parameter(i, context))
        .collect();

    let output = if let Some(output) = &func.signature.prototype.output {
        lower_type(output, context, Default::default())
    } else {
        context.store.common_types.void
    };

    LabeledFunctionSignature {
        inputs,
        output,
        is_async,
        receiver: None,
    }
}

pub fn convert_to_labeled_parameter<'ctx>(
    param: &taroc_hir::FunctionParameter,
    context: GlobalContext<'ctx>,
) -> LabeledFunctionParameter<'ctx> {
    let label = param.label.as_ref().map(|f| f.identifier.symbol);
    LabeledFunctionParameter {
        label,
        ty: lower_type(&param.annotated_type, context, Default::default()),
        is_variadic: param.is_variadic,
    }
}
