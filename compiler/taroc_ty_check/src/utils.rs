use taroc_context::GlobalContext;
use taroc_hir::DefinitionID;
use taroc_ty::{
    ConformanceRecord, GenericArgument, GenericArguments, LabeledFunctionParameter,
    LabeledFunctionSignature, Ty, TyKind,
};

use crate::{lower::lower_type, models::SubstitutionMap};

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
        lower_type(output, context)
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
        ty: lower_type(&param.annotated_type, context),
    }
}

pub fn convert_labeled_signature_to_signature<'ctx>(
    sig: &LabeledFunctionSignature<'ctx>,
    context: GlobalContext<'ctx>,
) -> Ty<'ctx> {
    let inputs: Vec<Ty<'ctx>> = sig.inputs.iter().map(|param| param.ty).collect();
    let output = sig.output;

    let kind = TyKind::Function {
        inputs: context.store.interners.intern_ty_list(&inputs),
        output,
        is_async: sig.is_async,
    };

    return context.store.interners.intern_ty(kind);
}

pub fn compare_signature_labels<'ctx>(
    a: &LabeledFunctionSignature<'ctx>,
    b: &LabeledFunctionSignature<'ctx>,
) -> bool {
    if a.inputs.len() != b.inputs.len() {
        return false;
    }

    let iter = a.inputs.iter().zip(b.inputs.iter());

    for (a, b) in iter {
        if a.label != b.label {
            return false;
        }
    }

    return true;
}

pub fn create_substitution_map<'ctx>(
    def_id: DefinitionID,
    arguments: GenericArguments<'ctx>,
    context: GlobalContext<'ctx>,
) -> SubstitutionMap<'ctx> {
    let generics = context.generics_of(def_id);

    if generics.total_count() == 0 {
        debug_assert!(arguments.len() == 0, "must have 0 arguments");
        return SubstitutionMap::default();
    }

    let mut map = SubstitutionMap::new();
    for (index, parameter) in generics.parameters.iter().enumerate() {
        let argument = arguments
            .get(index)
            .expect("ICE: during substitution type parameter and argument counts MUST match");
        map.insert(
            taroc_ty::GenericParameter {
                index: parameter.index,
                name: parameter.name,
            },
            *argument,
        );
    }

    return map;
}

pub fn substitute<'ctx>(
    ty: Ty<'ctx>,
    substitutions: &SubstitutionMap<'ctx>,
    conformance: Option<&ConformanceRecord<'ctx>>,
    context: GlobalContext<'ctx>,
) -> Ty<'ctx> {
    match ty.kind() {
        taroc_ty::TyKind::Pointer(ty, mutability) => {
            let ty = substitute(ty, substitutions, conformance, context);
            return context
                .store
                .interners
                .intern_ty(TyKind::Pointer(ty, mutability));
        }
        taroc_ty::TyKind::Reference(ty, mutability) => {
            let ty = substitute(ty, substitutions, conformance, context);
            return context
                .store
                .interners
                .intern_ty(TyKind::Reference(ty, mutability));
        }
        taroc_ty::TyKind::Variadic(ty) => {
            let ty = substitute(ty, substitutions, conformance, context);
            return context.store.interners.intern_ty(TyKind::Variadic(ty));
        }
        taroc_ty::TyKind::Array(ty, len) => {
            let ty = substitute(ty, substitutions, conformance, context);
            return context.store.interners.intern_ty(TyKind::Array(ty, len));
        }
        taroc_ty::TyKind::Tuple(items) => {
            let tys: Vec<Ty<'ctx>> = items
                .into_iter()
                .cloned()
                .map(|ty| substitute(ty, substitutions, conformance, context))
                .collect();

            let tys = context.store.interners.intern_ty_list(&tys);
            return context.store.interners.intern_ty(TyKind::Tuple(tys));
        }
        taroc_ty::TyKind::Adt(definition_id, generic_arguments, ty) => {
            let arguments: Vec<GenericArgument<'ctx>> = generic_arguments
                .into_iter()
                .cloned()
                .map(|argument| match argument {
                    taroc_ty::GenericArgument::Type(ty) => {
                        GenericArgument::Type(substitute(ty, substitutions, conformance, context))
                    }
                    taroc_ty::GenericArgument::Const(_) => todo!(),
                })
                .collect();

            let arguments = context.store.interners.intern_generic_args(&arguments);
            return context
                .store
                .interners
                .intern_ty(TyKind::Adt(definition_id, arguments, ty));
        }
        taroc_ty::TyKind::Existential(..) => {
            todo!()
        }
        taroc_ty::TyKind::Parameter(param) => {
            let binding = substitutions.get(&param);
            let Some(binding) = binding else {
                return ty;
            };
            match binding {
                GenericArgument::Type(ty) => {
                    if ty == ty {
                        return *ty;
                    }
                    return substitute(*ty, substitutions, conformance, context);
                }
                GenericArgument::Const(_) => panic!("ICE: binding maps to const argument"),
            }
        }
        taroc_ty::TyKind::AssociatedType(id) if let Some(conformance) = conformance => {
            let name = context.def_symbol(id);
            let witness = conformance.type_witnesses.get(&name).cloned();
            let Some(witness) = witness else { return ty };
            return substitute(witness, substitutions, Some(conformance), context);
        }
        taroc_ty::TyKind::Function {
            inputs,
            output,
            is_async,
        } => {
            let inputs: Vec<Ty<'ctx>> = inputs
                .into_iter()
                .cloned()
                .map(|ty| substitute(ty, substitutions, conformance, context))
                .collect();
            let inputs = context.store.interners.intern_ty_list(&inputs);
            let output = substitute(output, substitutions, conformance, context);

            let kind = TyKind::Function {
                inputs,
                output,
                is_async,
            };
            return context.store.interners.intern_ty(kind);
        }
        _ => return ty,
    }
}
