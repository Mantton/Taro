use std::rc::Rc;

use taroc_context::CompilerSession;
use taroc_ty::{LabeledFunctionParameter, LabeledFunctionSignature};

use crate::lower::lower_type;

pub fn convert_to_labeled_signature<'ctx>(
    func: &taroc_hir::Function,
    session: Rc<CompilerSession<'ctx>>,
) -> LabeledFunctionSignature<'ctx> {
    let is_async = func.signature.is_async;
    let inputs: Vec<LabeledFunctionParameter> = func
        .signature
        .prototype
        .inputs
        .iter()
        .map(|i| convert_to_labeled_parameter(i, session.clone()))
        .collect();

    let output = if let Some(output) = &func.signature.prototype.output {
        lower_type(output, session.context, session.index, Default::default())
    } else {
        session.context.store.common_types.void
    };

    LabeledFunctionSignature {
        inputs,
        output,
        is_async,
    }
}

pub fn convert_to_labeled_parameter<'ctx>(
    param: &taroc_hir::FunctionParameter,
    session: Rc<CompilerSession<'ctx>>,
) -> LabeledFunctionParameter<'ctx> {
    let label = param.label.as_ref().map(|f| f.identifier.symbol);
    LabeledFunctionParameter {
        label,
        ty: lower_type(
            &param.annotated_type,
            session.context,
            session.index,
            Default::default(),
        ),
        is_variadic: param.is_variadic,
    }
}
