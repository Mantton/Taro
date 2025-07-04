use crate::GlobalContext;
use crate::ty::{LabeledFunctionParameter, LabeledFunctionSignature, Ty, TyKind};
use taroc_hir::DefinitionID;
use taroc_span::Symbol;

use crate::lower::{ItemCtx, TypeLowerer};

pub fn convert_to_labeled_signature<'ctx>(
    func: &taroc_hir::Function,
    id: DefinitionID,
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
        let icx = ItemCtx::new(context);
        icx.lowerer().lower_type(output, &Default::default())
    } else {
        context.store.common_types.void
    };

    let is_variadic = func
        .signature
        .prototype
        .inputs
        .iter()
        .any(|p| p.is_variadic);

    LabeledFunctionSignature {
        inputs,
        output,
        is_async,
        is_variadic,
        id,
    }
}

pub fn convert_to_labeled_parameter<'ctx>(
    param: &taroc_hir::FunctionParameter,
    context: GlobalContext<'ctx>,
) -> LabeledFunctionParameter<'ctx> {
    let icx = ItemCtx::new(context);
    let label = param.label.as_ref().map(|f| f.identifier.symbol);
    LabeledFunctionParameter {
        label,
        name: param.name.symbol,
        ty: icx
            .lowerer()
            .lower_type(&param.annotated_type, &Default::default()),
        has_default: param.default_value.is_some(),
    }
}

pub fn labeled_signature_to_ty<'ctx>(
    sig: &LabeledFunctionSignature<'ctx>,
    context: GlobalContext<'ctx>,
) -> Ty<'ctx> {
    let inputs: Vec<Ty<'ctx>> = sig.inputs.iter().map(|param| param.ty).collect();
    let output = sig.output;

    let kind = TyKind::Function {
        inputs: context.store.interners.intern_ty_list(&inputs),
        output,
    };

    return context.store.interners.intern_ty(kind);
}

pub fn convert_tuple_variant_signature<'ctx>(
    fields: &[taroc_hir::FieldDefinition],
    return_ty: Ty<'ctx>,
    id: DefinitionID,
    context: GlobalContext<'ctx>,
) -> LabeledFunctionSignature<'ctx> {
    let icx = ItemCtx::new(context);
    let inputs: Vec<LabeledFunctionParameter<'ctx>> = fields
        .iter()
        .map(|f| LabeledFunctionParameter {
            label: None,
            name: Symbol::with(""),
            ty: icx.lowerer().lower_type(&f.ty, &Default::default()),
            has_default: false,
        })
        .collect();

    LabeledFunctionSignature {
        inputs,
        output: return_ty,
        is_async: false,
        is_variadic: false,
        id,
    }
}
