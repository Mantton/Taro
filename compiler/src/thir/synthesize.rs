//! THIR synthesis for compiler-generated method bodies.
//!
//! This module generates actual THIR function bodies for synthesized interface methods
//! that flow through the normal MIR/codegen pipeline.

use crate::{
    compile::context::GlobalContext,
    hir::{DefinitionID, StdItem},
    sema::{
        models::{
            GenericArgument, GenericArguments, GenericParameter, SyntheticMethodKind, Ty, TyKind,
            callable_args_ty,
        },
        resolve::models::TypeHead,
        tycheck::derive::SyntheticMethodInfo,
    },
    span::{FileID, Span},
    thir::{
        AdtExpression, Arm, ArmId, Block, BlockId, Constant, ConstantKind, Expr, ExprId, ExprKind,
        FieldExpression, FieldIndex, FieldPattern, Param, Pattern, PatternKind, Stmt, StmtId,
        StmtKind, ThirFunction, VariantIndex,
    },
};
use index_vec::IndexVec;
use rustc_hash::FxHashMap;

mod codable;
mod debug_text;
mod default_value;
mod enum_cases;
mod ordering;

/// Generate THIR functions for all registered synthetic methods.
pub fn synthesize_all<'ctx>(gcx: GlobalContext<'ctx>) -> Vec<ThirFunction<'ctx>> {
    let synthetic_methods = gcx.get_synthetic_methods();
    let mut functions = Vec::new();

    let adapters: Vec<_> = gcx.store.synthetic_definitions.borrow().iter()
        .filter_map(|(id, definition)| (id.package() == gcx.package_index()
            && matches!(definition.kind, crate::sema::models::SyntheticDefinitionKind::AdoptedClassDefault { .. }
                | crate::sema::models::SyntheticDefinitionKind::DelegatedMethod { .. }
                | crate::sema::models::SyntheticDefinitionKind::AdoptedClassDefaultArgument { .. }))
            .then_some((*id, definition.kind))).collect();
    for (id, kind) in adapters {
        functions.push(synthesize_conformance_adapter(gcx, id, kind));
    }

    let erased: Vec<_> = gcx
        .store
        .synthetic_definitions
        .borrow()
        .iter()
        .filter_map(|(id, definition)| {
            (id.package() == gcx.package_index()
                && matches!(
                    definition.kind,
                    crate::sema::models::SyntheticDefinitionKind::ErasedTakeAs { .. }
                        | crate::sema::models::SyntheticDefinitionKind::ErasedAsRef { .. }
                ))
            .then_some(*id)
        })
        .collect();
    for id in erased {
        let kind = gcx.store.synthetic_definitions.borrow()[&id].kind;
        if let crate::sema::models::SyntheticDefinitionKind::ErasedAsRef { .. } = kind {
            functions.push(synthesize_erased_reference(gcx, id));
        } else {
            functions.push(synthesize_erased_take(gcx, id));
        }
    }

    // We collect them first to avoid borrow conflicts
    let methods: Vec<_> = synthetic_methods.into_iter().collect();

    for ((type_head, method_id), mut info) in methods {
        // Intrinsic Clone uses a generic declaration whose implementation is
        // materialized per complete type, not this nominal/head cache.
        if info.syn_id.is_some_and(|id| gcx.is_instance_generated(id)) {
            continue;
        }
        // Allocate a stable synthetic ID for this synthesized method.
        let syn_id = info
            .syn_id
            .unwrap_or_else(|| gcx.allocate_synthetic_id(gcx.package_index()));
        info.syn_id = Some(syn_id);

        // Publish the assigned ID before building the body so recursive
        // witness resolution observes the same synthetic definition.
        gcx.with_session_type_database(|db| {
            if let Some(entry) = db.synthetic_methods.get_mut(&(type_head, method_id)) {
                *entry = info;
            }
        });

        // 2. Register Definition (Generics, Signature)
        register_definition(gcx, syn_id, type_head, info);

        if gcx.is_class_type(info.self_ty) && info.kind == SyntheticMethodKind::MemberwiseDecode {
            functions.extend(codable::synthesize_class(gcx, info, syn_id));
            continue;
        }
        // 3. Synthesize Body
        if let Some(func) = synthesize_method(gcx, type_head, method_id, info, syn_id) {
            functions.push(func);
        }

        // Synthesis may resolve nested conformances which revisit and update
        // this method entry. Re-publish the authoritative assigned ID so
        // dependency metadata can reconstruct the synthetic witness later.
        gcx.with_session_type_database(|db| {
            db.synthetic_methods.insert((type_head, method_id), info);
        });
    }

    functions
}

/// Defaults run in their concrete generic environment while the caller keeps
/// its already evaluated argument alive. These are ordinary Native-checked
/// functions, so panic cleanup and owning results use the common MIR path.
pub(crate) fn synthesize_opened_defaults<'ctx>(
    gcx: GlobalContext<'ctx>,
) -> Vec<ThirFunction<'ctx>> {
    let definitions: Vec<_> =
        gcx.store
            .synthetic_definitions
            .borrow()
            .iter()
            .filter_map(|(id, definition)| match definition.kind {
                crate::sema::models::SyntheticDefinitionKind::ErasedDefault {
                    provider, ..
                } if id.package() == gcx.package_index() => Some((*id, provider)),
                _ => None,
            })
            .collect();
    definitions
        .into_iter()
        .map(|(id, provider)| {
            let signature = gcx.get_signature(id);
            let span = gcx.definition_ident(id).span;
            let arguments =
                crate::sema::tycheck::utils::generics::GenericsBuilder::identity_for_item(gcx, id);
            let provider_signature =
                crate::sema::tycheck::utils::instantiate::instantiate_signature_with_args(
                    gcx,
                    gcx.get_signature(provider),
                    arguments,
                );
            let mut builder = ThirBuilder::new(gcx, span);
            let params: Vec<_> = signature
                .inputs
                .iter()
                .enumerate()
                .map(|(index, input)| Param {
                    id: synthetic_node_id(id, index as u32),
                    name: input.name,
                    ty: input.ty,
                    span,
                })
                .collect();
            let args = params
                .iter()
                .skip(1)
                .map(|p| builder.push_expr(ExprKind::Local(p.id), p.ty))
                .collect();
            let callee = builder.push_expr(
                ExprKind::Zst {
                    id: provider,
                    generic_args: Some(arguments),
                },
                Ty::from_labeled_signature(gcx, &provider_signature),
            );
            let result = builder.push_expr(
                ExprKind::Call {
                    callee,
                    args,
                    is_async: false,
                    argument_evaluation_order: None,
                },
                signature.output,
            );
            let body = builder.push_block(vec![], Some(result));
            ThirFunction {
                id,
                span,
                body: Some(body),
                constructor_self: None,
                params,
                stmts: builder.stmts,
                blocks: builder.blocks,
                exprs: builder.exprs,
                arms: builder.arms,
                match_reports: FxHashMap::default(),
                is_async: false,
            }
        })
        .collect()
}

/// These are ordinary managed functions. Borrow forwarding, panic cleanup and
/// suspension use the same source-MIR/Native pipeline as handwritten methods.
fn synthesize_conformance_adapter<'ctx>(
    gcx: GlobalContext<'ctx>,
    id: DefinitionID,
    kind: crate::sema::models::SyntheticDefinitionKind,
) -> ThirFunction<'ctx> {
    use crate::sema::{
        models::SyntheticDefinitionKind,
        tycheck::utils::{generics::GenericsBuilder, instantiate::instantiate_signature_with_args},
    };
    let span = gcx.definition_ident(id).span;
    let signature = gcx.get_signature(id);
    let identity = GenericsBuilder::identity_for_item(gcx, id);
    let mut delegate = None;
    let (target, arguments) = match kind {
        SyntheticDefinitionKind::AdoptedClassDefault { .. } => {
            let (source, arguments) = gcx
                .adapter_source_arguments(id, identity)
                .expect("adopted method environment");
            (
                gcx.class_default_body(source)
                    .expect("checked exact source"),
                arguments,
            )
        }
        SyntheticDefinitionKind::DelegatedMethod {
            conformance,
            field,
            borrow_field,
            ..
        } => {
            let (source, arguments) = gcx
                .adapter_source_arguments(id, identity)
                .expect("delegated method environment");
            let wrapper = gcx
                .conformance_record(conformance)
                .unwrap()
                .interface
                .self_ty()
                .unwrap();
            let wrapper = crate::sema::tycheck::utils::normalize_aliases(gcx, wrapper);
            let owner = crate::sema::tycheck::utils::normalize_aliases(
                gcx,
                match wrapper.kind() {
                    TyKind::Reference(inner) => inner,
                    _ => wrapper,
                },
            );
            let TyKind::Adt(definition, owner_args) = owner.kind() else {
                unreachable!()
            };
            let storage = crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args(
                gcx,
                gcx.get_struct_definition(definition.id).fields[field as usize].ty,
                owner_args,
            );
            let mut arguments = arguments.to_vec();
            arguments[0] = GenericArgument::Type(if borrow_field {
                Ty::new(TyKind::Reference(storage), gcx)
            } else {
                storage
            });
            delegate = Some((owner, field, storage));
            (source, gcx.store.interners.intern_generic_args(arguments))
        }
        SyntheticDefinitionKind::AdoptedClassDefaultArgument { method, provider } => {
            let (_, arguments) = gcx
                .adapter_source_arguments(method, identity)
                .expect("adopted argument environment");
            (provider, arguments)
        }
        _ => unreachable!(),
    };
    let target_signature =
        instantiate_signature_with_args(gcx, gcx.get_signature(target), arguments);
    let mut builder = ThirBuilder::new(gcx, span);
    let params: Vec<_> = signature
        .inputs
        .iter()
        .enumerate()
        .map(|(index, input)| Param {
            id: synthetic_node_id(id, index as u32),
            name: input.name,
            ty: input.ty,
            span,
        })
        .collect();
    let args = params
        .iter()
        .enumerate()
        .map(|(index, parameter)| {
            let value = builder.push_expr(ExprKind::Local(parameter.id), parameter.ty);
            if index == 0
                && let Some((owner, field, storage)) = delegate
            {
                let mut base = value;
                let mut base_ty = parameter.ty;
                while let TyKind::Reference(inner) = base_ty.kind() {
                    base = builder.push_expr(ExprKind::Deref(base), inner);
                    base_ty = inner;
                }
                debug_assert_eq!(base_ty, owner);
                let mut receiver = builder.push_expr(
                    ExprKind::Field {
                        lhs: base,
                        index: FieldIndex::from_raw(field),
                    },
                    storage,
                );
                let mut borrows = Vec::new();
                let mut ty = target_signature.inputs[0].ty;
                while ty != storage {
                    let TyKind::Reference(inner) = ty.kind() else {
                        unreachable!("checked delegation receiver")
                    };
                    borrows.push(ty);
                    ty = inner;
                }
                for ty in borrows.into_iter().rev() {
                    receiver = builder.push_expr(ExprKind::Reference { expr: receiver }, ty);
                }
                return receiver;
            }
            // Forward the referent without duplicating a mutable-reference token.
            if let TyKind::Reference(inner) = parameter.ty.kind() {
                let place = builder.push_expr(ExprKind::Deref(value), inner);
                builder.push_expr(ExprKind::Reference { expr: place }, parameter.ty)
            } else {
                value
            }
        })
        .collect();
    let callee = builder.push_expr(
        ExprKind::Zst {
            id: target,
            generic_args: Some(arguments),
        },
        Ty::from_labeled_signature(gcx, &target_signature),
    );
    let is_async = gcx.definition_is_async(id);
    let call = builder.push_expr(
        ExprKind::Call {
            callee,
            args,
            is_async,
            argument_evaluation_order: None,
        },
        target_signature.output,
    );
    let value = if is_async {
        builder.push_expr(
            ExprKind::Await { future: call },
            gcx.function_body_output(id),
        )
    } else {
        call
    };
    let body = builder.push_block(vec![], Some(value));
    ThirFunction {
        id,
        body: Some(body),
        constructor_self: None,
        span,
        params,
        stmts: builder.stmts,
        blocks: builder.blocks,
        exprs: builder.exprs,
        arms: builder.arms,
        match_reports: FxHashMap::default(),
        is_async,
    }
}

/// Test the stored concrete type before consuming the container. The failure
/// arm returns that exact owner; it never clones or destroys a mismatched value.
/// Both branches then use the normal move/drop and panic-cleanup machinery.
fn synthesize_erased_take<'ctx>(gcx: GlobalContext<'ctx>, id: DefinitionID) -> ThirFunction<'ctx> {
    use crate::sema::tycheck::utils::{
        generics::GenericsBuilder,
        instantiate::{instantiate_signature_with_args, instantiate_ty_with_args},
    };
    let signature = gcx.get_signature(id);
    let span = gcx.definition_ident(id).span;
    let identity = GenericsBuilder::identity_for_item(gcx, id);
    let target = identity[gcx.generics_of(id).parent_count]
        .ty()
        .expect("extraction target");
    let erased = signature.inputs[0].ty;
    let parameter = Param {
        id: synthetic_node_id(id, 0),
        name: gcx.intern_symbol("self"),
        ty: erased,
        span,
    };
    let mut builder = ThirBuilder::new(gcx, span);
    let local = builder.push_expr(ExprKind::Local(parameter.id), erased);
    let borrow_ty = Ty::new(TyKind::Reference(erased), gcx);
    let borrow = builder.push_expr(ExprKind::Reference { expr: local }, borrow_ty);
    let condition = builder.push_expr(
        ExprKind::ExistentialTypeIs {
            value: borrow,
            target,
        },
        gcx.types.bool,
    );
    let optional = gcx
        .std_item_def(StdItem::Optional)
        .expect("takeAs requires Optional");
    let target_arguments = gcx
        .store
        .interners
        .intern_generic_args(vec![GenericArgument::Type(target)]);
    let optional_ty = instantiate_ty_with_args(gcx, gcx.get_type(optional), target_arguments);
    let moved = builder.push_expr(ExprKind::Local(parameter.id), erased);
    let cast = builder.push_expr(
        ExprKind::ExistentialTryCast {
            value: moved,
            target,
        },
        optional_ty,
    );
    let head =
        crate::sema::tycheck::utils::type_head_from_value_ty(optional_ty).expect("Optional head");
    let unwrap_name = gcx.intern_symbol("unwrap");
    let unwrap = gcx.collect_from_databases(|database| {
        database
            .type_head_to_members
            .get(&head)
            .and_then(|members| members.inherent_instance.get(&unwrap_name))
            .map(|methods| methods.members.iter().copied().collect())
            .unwrap_or_default()
    })[0];
    let unwrap_args = crate::sema::impl_engine::deduce_impl_subst(
        gcx,
        gcx.definition_parent(unwrap).unwrap(),
        optional_ty,
        &[],
    )
    .expect("Optional unwrap arguments");
    let unwrap_sig = instantiate_signature_with_args(gcx, gcx.get_signature(unwrap), unwrap_args);
    let callee = builder.push_expr(
        ExprKind::Zst {
            id: unwrap,
            generic_args: Some(unwrap_args),
        },
        Ty::from_labeled_signature(gcx, &unwrap_sig),
    );
    let extracted = builder.push_expr(
        ExprKind::Call {
            callee,
            args: vec![cast],
            is_async: false,
            argument_evaluation_order: None,
        },
        target,
    );
    let result_ty = signature.output;
    let TyKind::Adt(definition, arguments) = result_ty.kind() else {
        unreachable!("Result type");
    };
    let variants = gcx.get_enum_definition(definition.id);
    let result = |builder: &mut ThirBuilder<'ctx>, item: StdItem, payload| {
        let variant = gcx.std_item_def(item).expect("Result variant");
        let index = variants
            .variants
            .iter()
            .position(|entry| entry.def_id == variant)
            .expect("Result variant belongs to Result");
        builder.push_expr(
            ExprKind::Adt(AdtExpression {
                base: None,
                definition,
                variant_index: Some(VariantIndex::from_usize(index)),
                generic_args: arguments,
                fields: vec![FieldExpression {
                    index: FieldIndex::from_usize(0),
                    expression: payload,
                }],
            }),
            result_ty,
        )
    };
    let success = result(&mut builder, StdItem::ResultOkVariant, extracted);
    let original = builder.push_expr(ExprKind::Local(parameter.id), erased);
    let failure = result(&mut builder, StdItem::ResultErrVariant, original);
    let value = builder.push_expr(
        ExprKind::If {
            cond: condition,
            then_expr: success,
            else_expr: Some(failure),
        },
        result_ty,
    );
    let body = builder.push_block(vec![], Some(value));
    ThirFunction {
        id,
        body: Some(body),
        constructor_self: None,
        span,
        params: vec![parameter],
        stmts: builder.stmts,
        blocks: builder.blocks,
        exprs: builder.exprs,
        arms: builder.arms,
        match_reports: FxHashMap::default(),
        is_async: false,
    }
}

/// Borrow the container for the complete checked view. Exact stored-type
/// comparison happens before projecting its payload. A mutable class result is
/// a borrow of the stored handle slot, never a dynamic-subclass reinterpretation.
fn synthesize_erased_reference<'ctx>(
    gcx: GlobalContext<'ctx>,
    id: DefinitionID,
) -> ThirFunction<'ctx> {
    use crate::sema::tycheck::utils::{
        generics::GenericsBuilder, instantiate::instantiate_signature_with_args,
    };
    let signature = gcx.get_signature(id);
    let span = gcx.definition_ident(id).span;
    let identity = GenericsBuilder::identity_for_item(gcx, id);
    let target = identity[gcx.generics_of(id).parent_count]
        .ty()
        .expect("inspection target");
    let input_ty = signature.inputs[0].ty;
    let TyKind::Reference(erased) = input_ty.kind() else {
        unreachable!()
    };
    let parameter = Param {
        id: synthetic_node_id(id, 0),
        name: gcx.intern_symbol("self"),
        ty: input_ty,
        span,
    };
    let mut builder = ThirBuilder::new(gcx, span);
    let local = builder.push_expr(ExprKind::Local(parameter.id), input_ty);
    let place = builder.push_expr(ExprKind::Deref(local), erased);
    let shared = Ty::new(TyKind::Reference(erased), gcx);
    let read = builder.push_expr(ExprKind::Reference { expr: place }, shared);
    let condition = builder.push_expr(
        ExprKind::ExistentialTypeIs {
            value: read,
            target,
        },
        gcx.types.bool,
    );
    let local = builder.push_expr(ExprKind::Local(parameter.id), input_ty);
    let place = builder.push_expr(ExprKind::Deref(local), erased);
    let input = builder.push_expr(ExprKind::Reference { expr: place }, input_ty);
    let helper = gcx.erased_payload_reference(id);
    let helper_sig = instantiate_signature_with_args(gcx, gcx.get_signature(helper), identity);
    let callee = builder.push_expr(
        ExprKind::Zst {
            id: helper,
            generic_args: Some(identity),
        },
        Ty::from_labeled_signature(gcx, &helper_sig),
    );
    let reference_ty = Ty::new(TyKind::Reference(target), gcx);
    let reference = builder.push_expr(
        ExprKind::Call {
            callee,
            args: vec![input],
            is_async: false,
            argument_evaluation_order: None,
        },
        reference_ty,
    );
    let TyKind::Adt(definition, arguments) = signature.output.kind() else {
        unreachable!()
    };
    let variants = gcx.get_enum_definition(definition.id);
    let mut variant = |item: StdItem, payload: Option<ExprId>| {
        let variant = gcx.std_item_def(item).expect("Optional variant");
        let index = variants
            .variants
            .iter()
            .position(|entry| entry.def_id == variant)
            .expect("Optional variant belongs to Optional");
        builder.push_expr(
            ExprKind::Adt(AdtExpression {
                base: None,
                definition,
                variant_index: Some(VariantIndex::from_usize(index)),
                generic_args: arguments,
                fields: payload
                    .map(|expression| {
                        vec![FieldExpression {
                            index: FieldIndex::from_usize(0),
                            expression,
                        }]
                    })
                    .unwrap_or_default(),
            }),
            signature.output,
        )
    };
    let success = variant(StdItem::OptionalSomeVariant, Some(reference));
    let failure = variant(StdItem::OptionalNoneVariant, None);
    let value = builder.push_expr(
        ExprKind::If {
            cond: condition,
            then_expr: success,
            else_expr: Some(failure),
        },
        signature.output,
    );
    let body = builder.push_block(vec![], Some(value));
    ThirFunction {
        id,
        body: Some(body),
        constructor_self: None,
        span,
        params: vec![parameter],
        stmts: builder.stmts,
        blocks: builder.blocks,
        exprs: builder.exprs,
        arms: builder.arms,
        match_reports: FxHashMap::default(),
        is_async: false,
    }
}

pub(crate) fn register_definition<'ctx>(
    gcx: GlobalContext<'ctx>,
    syn_id: DefinitionID,
    _type_head: TypeHead,
    info: SyntheticMethodInfo<'ctx>,
) {
    if matches!(
        gcx.store
            .synthetic_definitions
            .borrow()
            .get(&syn_id)
            .map(|value| value.kind),
        Some(crate::sema::models::SyntheticDefinitionKind::ClassDecoder { .. })
    ) {
        return;
    }
    let (generics, signature, async_output) = match info.kind {
        SyntheticMethodKind::ClosureCall => {
            let TyKind::Closure { inputs, output, .. } = info.self_ty.kind() else {
                return;
            };
            let args_ty = callable_args_ty(gcx, inputs);
            let is_async = gcx.std_item_def(StdItem::AsyncFn) == Some(info.interface_id);

            let self_ty = info.self_ty;

            let signature = crate::sema::models::LabeledFunctionSignature {
                inputs: vec![
                    crate::sema::models::LabeledFunctionParameter {
                        name: gcx.intern_symbol("self"),
                        ty: self_ty,
                        label: None,
                        is_lazy: false,
                        default_provider: None,
                    },
                    crate::sema::models::LabeledFunctionParameter {
                        name: gcx.intern_symbol("args"),
                        ty: args_ty,
                        label: None,
                        is_lazy: false,
                        default_provider: None,
                    },
                ],
                output,
                is_variadic: false,
                abi: None,
            };

            let TyKind::Closure { closure_def_id, .. } = info.self_ty.kind() else {
                return;
            };
            let generics = gcx.generics_of(closure_def_id).clone();
            (generics, signature, is_async.then_some(output))
        }
        SyntheticMethodKind::CopyClone | SyntheticMethodKind::MemberwiseClone => {
            let generics = self_type_generics(gcx, info.self_ty);
            let self_ref_ty = info.self_ty;
            let signature = crate::sema::models::LabeledFunctionSignature {
                inputs: vec![crate::sema::models::LabeledFunctionParameter {
                    name: gcx.intern_symbol("self"),
                    ty: self_ref_ty,
                    label: None,
                    is_lazy: false,
                    default_provider: None,
                }],
                output: info.self_ty,
                is_variadic: false,
                abi: None,
            };
            (generics, signature, None)
        }
        SyntheticMethodKind::MemberwiseEquality => {
            let rhs_ty = match crate::sema::tycheck::derive::equality_rhs(
                gcx,
                info.interface_args,
                info.self_ty,
            ) {
                Some(rhs) => rhs,
                None => return,
            };
            let generics = self_type_generics(gcx, info.self_ty);
            let self_ref_ty = info.self_ty;
            let signature = crate::sema::models::LabeledFunctionSignature {
                inputs: vec![
                    crate::sema::models::LabeledFunctionParameter {
                        name: gcx.intern_symbol("self"),
                        ty: self_ref_ty,
                        label: None,
                        is_lazy: false,
                        default_provider: None,
                    },
                    crate::sema::models::LabeledFunctionParameter {
                        name: gcx.intern_symbol("other"),
                        ty: rhs_ty,
                        label: None,
                        is_lazy: false,
                        default_provider: None,
                    },
                ],
                output: gcx.types.bool,
                is_variadic: false,
                abi: None,
            };
            (generics, signature, None)
        }
        SyntheticMethodKind::MemberwiseHash => {
            let mut generics = self_type_generics(gcx, info.self_ty);
            let method_generics = gcx.generics_of(info.method_id);
            if method_generics.parameters.is_empty() {
                return;
            }

            let mut hasher_param = None;
            for param in &method_generics.parameters {
                let mut cloned = param.clone();
                cloned.index = generics.parent_count + generics.parameters.len();
                if hasher_param.is_none() {
                    hasher_param = Some(GenericParameter {
                        index: cloned.index,
                        name: cloned.name,
                    });
                }
                generics.parameters.push(cloned);
            }

            let hasher_param = hasher_param.expect("hash synthesis requires method generic");
            let hasher_ty = Ty::new(TyKind::Parameter(hasher_param), gcx);
            let self_ref_ty = info.self_ty;
            let hasher_ref_ty = hasher_ty;
            let signature = crate::sema::models::LabeledFunctionSignature {
                inputs: vec![
                    crate::sema::models::LabeledFunctionParameter {
                        name: gcx.intern_symbol("self"),
                        ty: self_ref_ty,
                        label: None,
                        is_lazy: false,
                        default_provider: None,
                    },
                    crate::sema::models::LabeledFunctionParameter {
                        name: gcx.intern_symbol("hasher"),
                        ty: hasher_ref_ty,
                        label: Some(gcx.intern_symbol("into")),
                        is_lazy: false,
                        default_provider: None,
                    },
                ],
                output: gcx.types.void,
                is_variadic: false,
                abi: None,
            };
            (generics, signature, None)
        }
        SyntheticMethodKind::MemberwiseEncode | SyntheticMethodKind::MemberwiseDecode => {
            let (generics, signature) = codable::register_signature(gcx, info);
            (generics, signature, None)
        }
        SyntheticMethodKind::MemberwisePartialOrder | SyntheticMethodKind::MemberwiseTotalOrder => {
            let generics = self_type_generics(gcx, info.self_ty);
            let parameter = |name: &str| crate::sema::models::LabeledFunctionParameter {
                name: gcx.intern_symbol(name),
                ty: info.self_ty,
                label: None,
                is_lazy: false,
                default_provider: None,
            };
            let signature = crate::sema::models::LabeledFunctionSignature {
                inputs: vec![parameter("self"), parameter("other")],
                output: crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args(
                    gcx,
                    gcx.get_signature(info.method_id).output,
                    info.interface_args,
                ),
                is_variadic: false,
                abi: None,
            };
            (generics, signature, None)
        }
        SyntheticMethodKind::EnumRawValue | SyntheticMethodKind::EnumFromRawValue => {
            let (generics, signature) = enum_cases::raw_signature(gcx, info);
            (generics, signature, None)
        }
        SyntheticMethodKind::MemberwiseDebug
        | SyntheticMethodKind::EnumCaseName
        | SyntheticMethodKind::EnumCaseAt => {
            let generics = self_type_generics(gcx, info.self_ty);
            let arguments = gcx
                .store
                .interners
                .intern_generic_args(vec![GenericArgument::Type(info.self_ty)]);
            let signature = crate::sema::tycheck::utils::instantiate::instantiate_signature_with_args(
                gcx,
                gcx.get_signature(info.method_id),
                arguments,
            );
            (generics, signature, None)
        }
        SyntheticMethodKind::MemberwiseDefault => {
            let generics = self_type_generics(gcx, info.self_ty);
            let signature = crate::sema::models::LabeledFunctionSignature {
                inputs: vec![],
                output: info.self_ty,
                is_variadic: false,
                abi: None,
            };
            (generics, signature, None)
        }
        SyntheticMethodKind::PropertyFieldGetter(_) => {
            let generics = self_type_generics(gcx, info.self_ty);
            let requirement = gcx.get_signature(info.method_id);
            let inputs = requirement
                .inputs
                .iter()
                .map(|input| crate::sema::models::LabeledFunctionParameter {
                    name: input.name,
                    ty: crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args(
                        gcx,
                        input.ty,
                        info.interface_args,
                    ),
                    label: input.label,
                    is_lazy: input.is_lazy,
                    default_provider: None,
                })
                .collect();
            let signature = crate::sema::models::LabeledFunctionSignature {
                inputs,
                output: crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args(
                    gcx,
                    requirement.output,
                    info.interface_args,
                ),
                is_variadic: false,
                abi: None,
            };
            (generics, signature, None)
        }
    };
    let labeled_sig = gcx.store.arenas.function_signatures.alloc(signature);

    // Alloc generics on arena
    let generics = gcx.store.arenas.generics.alloc(generics);

    let def = crate::sema::models::SyntheticDefinition {
        kind: if gcx.is_class_type(info.self_ty)
            && info.kind == SyntheticMethodKind::MemberwiseEncode
        {
            let TypeHead::Nominal(class) = _type_head else {
                unreachable!()
            };
            crate::sema::models::SyntheticDefinitionKind::ClassEncoder { class }
        } else {
            crate::sema::models::SyntheticDefinitionKind::Ordinary
        },
        name: info.method_name,
        generics,
        signature: labeled_sig,
        span: synthetic_span(),
    };

    gcx.register_synthetic_definition(syn_id, def);
    if gcx.is_class_type(info.self_ty)
        && matches!(
            info.kind,
            SyntheticMethodKind::MemberwiseEncode | SyntheticMethodKind::MemberwiseDecode
        )
    {
        gcx.cache_type(syn_id, Ty::from_labeled_signature(gcx, labeled_sig));
        let arguments = gcx.store.interners.intern_generic_args(
            std::iter::once(GenericArgument::Type(info.self_ty))
                .chain(generics.parameters.iter().map(|parameter| {
                    GenericArgument::Type(Ty::new(
                        TyKind::Parameter(GenericParameter {
                            index: parameter.index,
                            name: parameter.name,
                        }),
                        gcx,
                    ))
                }))
                .collect(),
        );
        gcx.update_constraints(
            syn_id,
            gcx.constraints_of(info.method_id)
                .into_iter()
                .map(|constraint| {
                    crate::span::Spanned::new(
                        crate::sema::tycheck::utils::instantiate::instantiate_constraint_with_args(
                            gcx,
                            constraint.value,
                            arguments,
                        ),
                        constraint.span,
                    )
                })
                .collect(),
        );
    }
    if gcx.is_class_type(info.self_ty) && info.kind == SyntheticMethodKind::MemberwiseDecode {
        crate::sema::lowering::class_codable::register(gcx, info, syn_id);
    }
    if let Some(output) = async_output {
        gcx.cache_async_body_output(syn_id, output);
    }
}

/// Synthesize a single THIR function for a synthetic method.
fn synthesize_method<'ctx>(
    gcx: GlobalContext<'ctx>,
    type_head: TypeHead,
    method_id: DefinitionID,
    info: SyntheticMethodInfo<'ctx>,
    syn_id: DefinitionID,
) -> Option<ThirFunction<'ctx>> {
    match info.kind {
        SyntheticMethodKind::CopyClone => {
            synthesize_copy_clone(gcx, type_head, method_id, info, syn_id)
        }
        SyntheticMethodKind::MemberwiseClone => {
            synthesize_memberwise_clone(gcx, type_head, method_id, info, syn_id)
        }
        SyntheticMethodKind::MemberwiseHash => {
            synthesize_memberwise_hash(gcx, type_head, method_id, info, syn_id)
        }
        SyntheticMethodKind::MemberwiseEquality => {
            synthesize_memberwise_equality(gcx, type_head, method_id, info, syn_id)
        }
        SyntheticMethodKind::ClosureCall => synthesize_closure_call(gcx, info, syn_id),
        SyntheticMethodKind::MemberwisePartialOrder | SyntheticMethodKind::MemberwiseTotalOrder => {
            ordering::synthesize(gcx, type_head, info, syn_id)
        }
        SyntheticMethodKind::MemberwiseDefault => {
            default_value::synthesize(gcx, type_head, info, syn_id)
        }
        SyntheticMethodKind::EnumRawValue
        | SyntheticMethodKind::EnumFromRawValue
        | SyntheticMethodKind::EnumCaseName
        | SyntheticMethodKind::EnumCaseAt => enum_cases::synthesize(gcx, type_head, info, syn_id),
        SyntheticMethodKind::MemberwiseDebug => debug_text::synthesize(gcx, type_head, info, syn_id),
        SyntheticMethodKind::MemberwiseEncode | SyntheticMethodKind::MemberwiseDecode => {
            codable::synthesize(gcx, info, syn_id)
        }
        SyntheticMethodKind::PropertyFieldGetter(field_index) => {
            synthesize_property_field_getter(gcx, info, syn_id, field_index)
        }
    }
}

fn synthesize_property_field_getter<'ctx>(
    gcx: GlobalContext<'ctx>,
    info: SyntheticMethodInfo<'ctx>,
    syn_id: DefinitionID,
    field_index: usize,
) -> Option<ThirFunction<'ctx>> {
    let span = synthetic_span();
    let signature = gcx.get_signature(syn_id);
    let receiver_ty = signature.inputs.first()?.ty;
    let self_node_id = synthetic_node_id(syn_id, 0);
    let self_param = Param {
        id: self_node_id,
        name: gcx.intern_symbol("self"),
        ty: receiver_ty,
        span,
    };
    let mut builder = ThirBuilder::new(gcx, span);
    let receiver = builder.push_expr(ExprKind::Local(self_node_id), receiver_ty);
    let TyKind::Adt(definition, arguments) = info.self_ty.kind() else {
        return None;
    };
    let stored = gcx
        .get_struct_definition(definition.id)
        .fields
        .get(field_index)?;
    let storage_ty = crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args(
        gcx, stored.ty, arguments,
    );
    let field = builder.push_expr(
        ExprKind::Field {
            lhs: receiver,
            index: FieldIndex::from_usize(field_index),
        },
        storage_ty,
    );
    let body = builder.push_block(vec![], Some(field));
    Some(ThirFunction {
        id: syn_id,
        body: Some(body),
        constructor_self: None,
        span,
        params: vec![self_param],
        stmts: builder.stmts,
        blocks: builder.blocks,
        exprs: builder.exprs,
        arms: IndexVec::new(),
        match_reports: FxHashMap::default(),
        is_async: false,
    })
}

fn synthetic_span() -> Span {
    // Use FileID 0 as a synthetic/builtin file
    Span::empty(FileID::from_raw(0))
}

/// Create a synthetic NodeID for generated code elements.
/// The syn_id is unique per synthetic method, and offset differentiates within a method.
fn synthetic_node_id(syn_id: DefinitionID, offset: u32) -> crate::hir::NodeID {
    // Use the synthetic ID's raw representation as base, which is unique per method.
    // The offset differentiates multiple nodes within the same method.
    // Use high values to avoid collision with user code.
    let base = syn_id.package().raw().wrapping_mul(0x1000);
    let seed = base.wrapping_add(offset);
    crate::hir::NodeID::from_raw(u32::MAX - seed)
}

/// Builder helper for constructing THIR functions.
struct ThirBuilder<'ctx> {
    _gcx: GlobalContext<'ctx>,
    stmts: IndexVec<StmtId, Stmt<'ctx>>,
    blocks: IndexVec<BlockId, Block>,
    exprs: IndexVec<ExprId, Expr<'ctx>>,
    arms: IndexVec<ArmId, Arm<'ctx>>,
    span: Span,
}

impl<'ctx> ThirBuilder<'ctx> {
    fn new(gcx: GlobalContext<'ctx>, span: Span) -> Self {
        ThirBuilder {
            _gcx: gcx,
            stmts: IndexVec::new(),
            blocks: IndexVec::new(),
            exprs: IndexVec::new(),
            arms: IndexVec::new(),
            span,
        }
    }

    fn push_expr(&mut self, kind: ExprKind<'ctx>, ty: Ty<'ctx>) -> ExprId {
        let id = ExprId::from_raw(self.exprs.len() as u32);
        self.exprs.push(Expr {
            kind,
            ty,
            span: self.span,
        });
        id
    }

    fn push_block(&mut self, stmts: Vec<StmtId>, expr: Option<ExprId>) -> BlockId {
        let id = BlockId::from_raw(self.blocks.len() as u32);
        self.blocks.push(Block { id, stmts, expr });
        id
    }

    fn push_stmt(&mut self, kind: StmtKind<'ctx>) -> StmtId {
        let id = StmtId::from_raw(self.stmts.len() as u32);
        self.stmts.push(Stmt {
            kind,
            span: self.span,
        });
        id
    }

    fn push_stmt_expr(&mut self, expr: ExprId) -> StmtId {
        self.push_stmt(StmtKind::Expr(expr))
    }
}

fn self_type_generics<'ctx>(
    gcx: GlobalContext<'ctx>,
    self_ty: Ty<'ctx>,
) -> crate::sema::models::Generics {
    match self_ty.kind() {
        TyKind::Adt(def, _) => gcx.generics_of(def.id).clone(),
        _ => crate::sema::models::Generics {
            parameters: vec![],
            has_self: false,
            parent: None,
            parent_count: 0,
        },
    }
}

fn bool_literal<'ctx>(
    gcx: GlobalContext<'ctx>,
    builder: &mut ThirBuilder<'ctx>,
    value: bool,
) -> ExprId {
    builder.push_expr(
        ExprKind::Literal(Constant {
            ty: gcx.types.bool,
            value: ConstantKind::Bool(value),
        }),
        gcx.types.bool,
    )
}

fn make_zst_callee<'ctx>(
    gcx: GlobalContext<'ctx>,
    builder: &mut ThirBuilder<'ctx>,
    callee_id: DefinitionID,
    generic_args: GenericArguments<'ctx>,
) -> ExprId {
    let sig = gcx.get_signature(callee_id);
    let inputs: Vec<_> = sig.inputs.iter().map(|p| p.ty).collect();
    let inputs = gcx.store.interners.intern_ty_list(inputs);
    let callee_ty = gcx.store.interners.intern_ty(TyKind::FnPointer {
        effects: Default::default(),
        inputs,
        output: sig.output,
    });
    builder.push_expr(
        ExprKind::Zst {
            id: callee_id,
            generic_args: Some(generic_args),
        },
        callee_ty,
    )
}

fn emit_hash_call<'ctx>(
    gcx: GlobalContext<'ctx>,
    builder: &mut ThirBuilder<'ctx>,
    hash_method_id: DefinitionID,
    value_expr: ExprId,
    value_ty: Ty<'ctx>,
    hasher_param_id: crate::hir::NodeID,
    hasher_ref_ty: Ty<'ctx>,
    hasher_ty: Ty<'ctx>,
) -> ExprId {
    let hasher_local = builder.push_expr(ExprKind::Local(hasher_param_id), hasher_ref_ty);
    let hasher_argument = hasher_local;

    let generic_args = gcx.store.interners.intern_generic_args(vec![
        GenericArgument::Type(value_ty),
        GenericArgument::Type(hasher_ty),
    ]);
    let callee = make_zst_callee(gcx, builder, hash_method_id, generic_args);

    builder.push_expr(
        ExprKind::Call {
            argument_evaluation_order: None,
            callee,
            args: vec![value_expr, hasher_argument],
            is_async: false,
        },
        gcx.types.void,
    )
}

fn emit_eq_call<'ctx>(
    gcx: GlobalContext<'ctx>,
    builder: &mut ThirBuilder<'ctx>,
    eq_method_id: DefinitionID,
    lhs_expr: ExprId,
    rhs_expr: ExprId,
    value_ty: Ty<'ctx>,
) -> ExprId {
    let generic_args = gcx.store.interners.intern_generic_args(vec![
        GenericArgument::Type(value_ty),
        GenericArgument::Type(value_ty),
    ]);
    let callee = make_zst_callee(gcx, builder, eq_method_id, generic_args);
    builder.push_expr(
        ExprKind::Call {
            argument_evaluation_order: None,
            callee,
            args: vec![lhs_expr, rhs_expr],
            is_async: false,
        },
        gcx.types.bool,
    )
}

/// Synthesize scalar Clone by returning the copied receiver.
fn synthesize_copy_clone<'ctx>(
    gcx: GlobalContext<'ctx>,
    _type_head: TypeHead,
    _method_id: DefinitionID,
    info: SyntheticMethodInfo<'ctx>,
    syn_id: DefinitionID,
) -> Option<ThirFunction<'ctx>> {
    let span = synthetic_span();
    let mut builder = ThirBuilder::new(gcx, span);

    let self_node_id = synthetic_node_id(syn_id, 0);
    let self_ref_ty = info.self_ty;

    let self_param = Param {
        id: self_node_id,
        name: gcx.intern_symbol("self"),
        ty: self_ref_ty,
        span,
    };

    let self_local = builder.push_expr(ExprKind::Local(self_node_id), self_ref_ty);
    let deref_self = self_local;
    let body_block = builder.push_block(vec![], Some(deref_self));

    Some(ThirFunction {
        id: syn_id,
        body: Some(body_block),
        constructor_self: None,
        span,
        params: vec![self_param],
        stmts: builder.stmts,
        blocks: builder.blocks,
        exprs: builder.exprs,
        arms: IndexVec::new(),
        match_reports: FxHashMap::default(),
        is_async: false,
    })
}

/// Synthesize nominal Clone by calling every component's Clone, even for Copy fields.
fn synthesize_memberwise_clone<'ctx>(
    gcx: GlobalContext<'ctx>,
    type_head: TypeHead,
    _method_id: DefinitionID,
    info: SyntheticMethodInfo<'ctx>,
    syn_id: DefinitionID,
) -> Option<ThirFunction<'ctx>> {
    let TypeHead::Nominal(def_id) = type_head else {
        return None;
    };

    let span = synthetic_span();
    let mut builder = ThirBuilder::new(gcx, span);

    let self_node_id = synthetic_node_id(syn_id, 0);
    let self_ref_ty = info.self_ty;

    let self_param = Param {
        id: self_node_id,
        name: gcx.intern_symbol("self"),
        ty: self_ref_ty,
        span,
    };

    let clone_def = gcx.std_item_def(StdItem::Clone)?;

    if let Some(struct_def) = gcx.try_get_struct_definition(def_id) {
        let adt_def = struct_def.adt_def;
        let mut field_exprs = Vec::new();
        let generic_args = match info.self_ty.kind() {
            TyKind::Adt(_, args) => args,
            _ => GenericArguments::empty(),
        };

        for (idx, field) in struct_def.fields.iter().enumerate() {
            let self_local = builder.push_expr(ExprKind::Local(self_node_id), self_ref_ty);
            let deref_self = self_local;
            let field_access = builder.push_expr(
                ExprKind::Field {
                    lhs: deref_self,
                    index: FieldIndex::from_usize(idx),
                },
                field.ty,
            );

            let cloned_field = clone_field(gcx, &mut builder, field_access, field.ty, clone_def)?;

            field_exprs.push(FieldExpression {
                index: FieldIndex::from_usize(idx),
                expression: cloned_field,
            });
        }

        let adt_expr = if gcx.is_class_type(info.self_ty) {
            // Clone constructs a new object from cloned storage, bypassing
            // initializers/default expressions. A class handle itself must
            // never be constructed as an inline source-field aggregate.
            let payload = gcx.ensure_class_payload(info.self_ty)?;
            let fields: Vec<_> = field_exprs
                .into_iter()
                .map(|field| field.expression)
                .collect();
            let mut next = 0;
            let initialized = cloned_class_payload(gcx, &mut builder, payload, &fields, &mut next)?;
            debug_assert_eq!(next, fields.len());
            publish_cloned_class(gcx, &mut builder, payload, initialized, info.self_ty)?
        } else {
            builder.push_expr(
                ExprKind::Adt(AdtExpression {
                    base: None,
                    definition: adt_def,
                    variant_index: None,
                    generic_args,
                    fields: field_exprs,
                }),
                info.self_ty,
            )
        };

        let body_block = builder.push_block(vec![], Some(adt_expr));
        return Some(ThirFunction {
            id: syn_id,
            body: Some(body_block),
            constructor_self: None,
            span,
            params: vec![self_param],
            stmts: builder.stmts,
            blocks: builder.blocks,
            exprs: builder.exprs,
            arms: IndexVec::new(),
            match_reports: FxHashMap::default(),
            is_async: false,
        });
    }

    let enum_def = gcx.try_get_enum_definition(def_id)?;
    synthesize_enum_clone(
        gcx,
        builder,
        self_param,
        self_node_id,
        self_ref_ty,
        info,
        syn_id,
        enum_def,
        clone_def,
    )
}

/// Rebuild the physical base-prefix layout from source fields in base-first
/// declaration order. Normal aggregate lowering owns every completed clone,
/// so a later component panic destroys just that initialized prefix in reverse.
fn cloned_class_payload<'ctx>(
    gcx: GlobalContext<'ctx>,
    builder: &mut ThirBuilder<'ctx>,
    payload: Ty<'ctx>,
    clones: &[ExprId],
    next: &mut usize,
) -> Option<ExprId> {
    let TyKind::Adt(definition, generic_args) = payload.kind() else {
        return None;
    };
    let layout = gcx.get_struct_definition(definition.id);
    let class = gcx.class_for_payload(payload)?;
    let mut fields = Vec::new();
    for (index, field) in layout.fields.iter().enumerate() {
        let expression = if index == 0 && gcx.class_base(class).is_some() {
            let base_payload = crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args(
                gcx,
                field.ty,
                generic_args,
            );
            cloned_class_payload(gcx, builder, base_payload, clones, next)?
        } else {
            let expression = *clones.get(*next)?;
            *next += 1;
            expression
        };
        fields.push(FieldExpression {
            index: FieldIndex::from_usize(index),
            expression,
        });
    }
    Some(builder.push_expr(
        ExprKind::Adt(AdtExpression {
            base: None,
            definition,
            generic_args,
            variant_index: None,
            fields,
        }),
        payload,
    ))
}

/// Use the same unique payload allocation and dynamic-class publication path
/// as construction, without invoking init or repeating stored-field defaults.
fn publish_cloned_class<'ctx>(
    gcx: GlobalContext<'ctx>,
    builder: &mut ThirBuilder<'ctx>,
    payload: Ty<'ctx>,
    initialized: ExprId,
    class: Ty<'ctx>,
) -> Option<ExprId> {
    let span = builder.span;
    let allocate = crate::mir::optimize::async_transform::find_std_function(
        gcx,
        "runtime",
        "__classAllocatePayload",
        span,
    )
    .ok()?;
    let arguments = gcx
        .store
        .interners
        .intern_generic_args(vec![GenericArgument::Type(payload)]);
    let callee = make_zst_callee(gcx, builder, allocate, arguments);
    let handle_ty = gcx.get_type(gcx.std_item_def(StdItem::ClassHandle)?);
    let handle = builder.push_expr(
        ExprKind::Call {
            callee,
            args: vec![initialized],
            is_async: false,
            argument_evaluation_order: None,
        },
        handle_ty,
    );
    let transfer = crate::mir::optimize::async_transform::find_std_function(
        gcx,
        "intrinsic",
        "__intrinsic_class_from_handle",
        span,
    )
    .ok()?;
    let arguments = gcx
        .store
        .interners
        .intern_generic_args(vec![GenericArgument::Type(class)]);
    let callee = make_zst_callee(gcx, builder, transfer, arguments);
    Some(builder.push_expr(
        ExprKind::Call {
            callee,
            args: vec![handle],
            is_async: false,
            argument_evaluation_order: None,
        },
        class,
    ))
}

fn synthesize_memberwise_hash<'ctx>(
    gcx: GlobalContext<'ctx>,
    type_head: TypeHead,
    method_id: DefinitionID,
    info: SyntheticMethodInfo<'ctx>,
    syn_id: DefinitionID,
) -> Option<ThirFunction<'ctx>> {
    let TypeHead::Nominal(def_id) = type_head else {
        return None;
    };

    let method_generics = gcx.generics_of(method_id);
    let hasher_name = method_generics
        .parameters
        .first()
        .map(|param| param.name)
        .unwrap_or_else(|| gcx.intern_symbol("H"));

    let self_generics = self_type_generics(gcx, info.self_ty);
    let hasher_index = self_generics.parent_count + self_generics.parameters.len();
    let hasher_ty = Ty::new(
        TyKind::Parameter(GenericParameter {
            index: hasher_index,
            name: hasher_name,
        }),
        gcx,
    );

    let span = synthetic_span();
    let mut builder = ThirBuilder::new(gcx, span);

    let self_node_id = synthetic_node_id(syn_id, 0);
    let hasher_node_id = synthetic_node_id(syn_id, 1);

    let self_ref_ty = info.self_ty;
    let hasher_ref_ty = hasher_ty;

    let self_param = Param {
        id: self_node_id,
        name: gcx.intern_symbol("self"),
        ty: self_ref_ty,
        span,
    };
    let hasher_param = Param {
        id: hasher_node_id,
        name: gcx.intern_symbol("hasher"),
        ty: hasher_ref_ty,
        span,
    };

    if let Some(struct_def) = gcx.try_get_struct_definition(def_id) {
        let mut stmts = Vec::new();
        for (idx, field) in struct_def.fields.iter().enumerate() {
            let self_local = builder.push_expr(ExprKind::Local(self_node_id), self_ref_ty);
            let deref_self = self_local;
            let field_value = builder.push_expr(
                ExprKind::Field {
                    lhs: deref_self,
                    index: FieldIndex::from_usize(idx),
                },
                field.ty,
            );
            let call = emit_hash_call(
                gcx,
                &mut builder,
                method_id,
                field_value,
                field.ty,
                hasher_node_id,
                hasher_ref_ty,
                hasher_ty,
            );
            stmts.push(builder.push_stmt_expr(call));
        }

        let body_block = builder.push_block(stmts, None);
        return Some(ThirFunction {
            id: syn_id,
            body: Some(body_block),
            constructor_self: None,
            span,
            params: vec![self_param, hasher_param],
            stmts: builder.stmts,
            blocks: builder.blocks,
            exprs: builder.exprs,
            arms: IndexVec::new(),
            match_reports: FxHashMap::default(),
            is_async: false,
        });
    }

    let enum_def = gcx.try_get_enum_definition(def_id)?;
    synthesize_enum_hash(
        gcx,
        builder,
        self_param,
        self_node_id,
        self_ref_ty,
        hasher_param,
        hasher_node_id,
        hasher_ref_ty,
        hasher_ty,
        info,
        syn_id,
        enum_def,
        method_id,
    )
}

fn synthesize_memberwise_equality<'ctx>(
    gcx: GlobalContext<'ctx>,
    type_head: TypeHead,
    method_id: DefinitionID,
    info: SyntheticMethodInfo<'ctx>,
    syn_id: DefinitionID,
) -> Option<ThirFunction<'ctx>> {
    let TypeHead::Nominal(def_id) = type_head else {
        return None;
    };
    let rhs_ty =
        crate::sema::tycheck::derive::equality_rhs(gcx, info.interface_args, info.self_ty)?;
    if rhs_ty != info.self_ty {
        return None;
    }

    let span = synthetic_span();
    let mut builder = ThirBuilder::new(gcx, span);

    let self_node_id = synthetic_node_id(syn_id, 0);
    let other_node_id = synthetic_node_id(syn_id, 1);

    let self_ref_ty = info.self_ty;
    let other_ref_ty = rhs_ty;

    let self_param = Param {
        id: self_node_id,
        name: gcx.intern_symbol("self"),
        ty: self_ref_ty,
        span,
    };
    let other_param = Param {
        id: other_node_id,
        name: gcx.intern_symbol("other"),
        ty: other_ref_ty,
        span,
    };

    if let Some(struct_def) = gcx.try_get_struct_definition(def_id) {
        let mut result = bool_literal(gcx, &mut builder, true);
        for (idx, field) in struct_def.fields.iter().enumerate() {
            let self_local = builder.push_expr(ExprKind::Local(self_node_id), self_ref_ty);
            let self_deref = self_local;
            let lhs = builder.push_expr(
                ExprKind::Field {
                    lhs: self_deref,
                    index: FieldIndex::from_usize(idx),
                },
                field.ty,
            );

            let other_local = builder.push_expr(ExprKind::Local(other_node_id), other_ref_ty);
            let rhs = builder.push_expr(
                ExprKind::Field {
                    lhs: other_local,
                    index: FieldIndex::from_usize(idx),
                },
                field.ty,
            );

            let field_eq = emit_eq_call(gcx, &mut builder, method_id, lhs, rhs, field.ty);
            result = builder.push_expr(
                ExprKind::Logical {
                    op: crate::mir::LogicalOperator::And,
                    lhs: result,
                    rhs: field_eq,
                },
                gcx.types.bool,
            );
        }

        let body_block = builder.push_block(vec![], Some(result));
        return Some(ThirFunction {
            id: syn_id,
            body: Some(body_block),
            constructor_self: None,
            span,
            params: vec![self_param, other_param],
            stmts: builder.stmts,
            blocks: builder.blocks,
            exprs: builder.exprs,
            arms: IndexVec::new(),
            match_reports: FxHashMap::default(),
            is_async: false,
        });
    }

    let enum_def = gcx.try_get_enum_definition(def_id)?;
    synthesize_enum_equality(
        gcx,
        builder,
        self_param,
        self_node_id,
        self_ref_ty,
        other_param,
        other_node_id,
        other_ref_ty,
        info,
        syn_id,
        enum_def,
        method_id,
    )
}

fn synthesize_enum_hash<'ctx>(
    gcx: GlobalContext<'ctx>,
    mut builder: ThirBuilder<'ctx>,
    self_param: Param<'ctx>,
    self_node_id: crate::hir::NodeID,
    self_ref_ty: Ty<'ctx>,
    hasher_param: Param<'ctx>,
    hasher_node_id: crate::hir::NodeID,
    hasher_ref_ty: Ty<'ctx>,
    hasher_ty: Ty<'ctx>,
    info: SyntheticMethodInfo<'ctx>,
    syn_id: DefinitionID,
    enum_def: &crate::sema::models::EnumDefinition<'ctx>,
    hash_method_id: DefinitionID,
) -> Option<ThirFunction<'ctx>> {
    use crate::sema::models::EnumVariantKind;

    let span = synthetic_span();
    let adt_def = enum_def.adt_def;
    let self_local = builder.push_expr(ExprKind::Local(self_node_id), self_ref_ty);
    let scrutinee = self_local;

    let mut node_offset = 2u32;
    let mut arm_ids = Vec::new();

    for (variant_idx, variant) in enum_def.variants.iter().enumerate() {
        let mut subpatterns = Vec::new();
        let mut field_binding_ids = Vec::new();
        let mut field_tys = Vec::new();

        if let EnumVariantKind::Tuple(fields) | EnumVariantKind::Struct(fields) = &variant.kind {
            for (field_idx, field) in fields.iter().enumerate() {
                let binding_node_id = synthetic_node_id(syn_id, node_offset);
                node_offset += 1;
                let binding_name = gcx.intern_symbol(&format!("_f{}", field_idx));
                subpatterns.push(FieldPattern {
                    index: FieldIndex::from_usize(field_idx),
                    pattern: Pattern {
                        ty: field.ty,
                        span,
                        kind: PatternKind::Binding {
                            name: binding_name,
                            local: binding_node_id,
                            ty: field.ty,
                        },
                    },
                });
                field_binding_ids.push(binding_node_id);
                field_tys.push(field.ty);
            }
        }

        let pattern = Pattern {
            ty: info.self_ty,
            span,
            kind: PatternKind::Variant {
                definition: adt_def,
                variant: *variant,
                subpatterns,
            },
        };

        let tag_ty = gcx.types.uint32;
        let tag_expr = builder.push_expr(
            ExprKind::Literal(Constant {
                ty: tag_ty,
                value: ConstantKind::Integer(variant_idx as u64),
            }),
            tag_ty,
        );

        let mut stmts = Vec::new();
        let tag_hash = emit_hash_call(
            gcx,
            &mut builder,
            hash_method_id,
            tag_expr,
            tag_ty,
            hasher_node_id,
            hasher_ref_ty,
            hasher_ty,
        );
        stmts.push(builder.push_stmt_expr(tag_hash));

        for (binding_id, field_ty) in field_binding_ids.into_iter().zip(field_tys.into_iter()) {
            let field_local = builder.push_expr(ExprKind::Local(binding_id), field_ty);
            let field_hash = emit_hash_call(
                gcx,
                &mut builder,
                hash_method_id,
                field_local,
                field_ty,
                hasher_node_id,
                hasher_ref_ty,
                hasher_ty,
            );
            stmts.push(builder.push_stmt_expr(field_hash));
        }

        let block = builder.push_block(stmts, None);
        let body = builder.push_expr(ExprKind::Block(block), gcx.types.void);

        let arm_id = ArmId::from_raw(builder.arms.len() as u32);
        builder.arms.push(Arm {
            pattern: Box::new(pattern),
            guard: None,
            body,
            span,
        });
        arm_ids.push(arm_id);
    }

    let match_expr = builder.push_expr(
        ExprKind::Match {
            scrutinee,
            arms: arm_ids,
            binding_condition: false,
        },
        gcx.types.void,
    );
    let body_block = builder.push_block(vec![], Some(match_expr));

    Some(ThirFunction {
        id: syn_id,
        body: Some(body_block),
        constructor_self: None,
        span,
        params: vec![self_param, hasher_param],
        stmts: builder.stmts,
        blocks: builder.blocks,
        exprs: builder.exprs,
        arms: builder.arms,
        match_reports: FxHashMap::default(),
        is_async: false,
    })
}

fn synthesize_enum_equality<'ctx>(
    gcx: GlobalContext<'ctx>,
    mut builder: ThirBuilder<'ctx>,
    self_param: Param<'ctx>,
    self_node_id: crate::hir::NodeID,
    self_ref_ty: Ty<'ctx>,
    other_param: Param<'ctx>,
    other_node_id: crate::hir::NodeID,
    other_ref_ty: Ty<'ctx>,
    info: SyntheticMethodInfo<'ctx>,
    syn_id: DefinitionID,
    enum_def: &crate::sema::models::EnumDefinition<'ctx>,
    eq_method_id: DefinitionID,
) -> Option<ThirFunction<'ctx>> {
    use crate::sema::models::EnumVariantKind;

    let span = synthetic_span();
    let adt_def = enum_def.adt_def;
    let self_local = builder.push_expr(ExprKind::Local(self_node_id), self_ref_ty);
    let self_scrutinee = self_local;

    let mut node_offset = 2u32;
    let mut outer_arms = Vec::new();

    for variant in enum_def.variants.iter() {
        let mut self_subpatterns = Vec::new();
        let mut self_binding_ids = Vec::new();
        let mut field_tys = Vec::new();

        if let EnumVariantKind::Tuple(fields) | EnumVariantKind::Struct(fields) = &variant.kind {
            for (field_idx, field) in fields.iter().enumerate() {
                let binding_node_id = synthetic_node_id(syn_id, node_offset);
                node_offset += 1;
                let binding_name = gcx.intern_symbol(&format!("_lhs{}", field_idx));
                self_subpatterns.push(FieldPattern {
                    index: FieldIndex::from_usize(field_idx),
                    pattern: Pattern {
                        ty: field.ty,
                        span,
                        kind: PatternKind::Binding {
                            name: binding_name,
                            local: binding_node_id,
                            ty: field.ty,
                        },
                    },
                });
                self_binding_ids.push(binding_node_id);
                field_tys.push(field.ty);
            }
        }

        let outer_pattern = Pattern {
            ty: info.self_ty,
            span,
            kind: PatternKind::Variant {
                definition: adt_def,
                variant: *variant,
                subpatterns: self_subpatterns,
            },
        };

        let other_local = builder.push_expr(ExprKind::Local(other_node_id), other_ref_ty);
        let other_scrutinee = other_local;

        let mut inner_arms = Vec::new();
        let mut other_subpatterns = Vec::new();
        let mut other_binding_ids = Vec::new();

        if let EnumVariantKind::Tuple(fields) | EnumVariantKind::Struct(fields) = &variant.kind {
            for (field_idx, field) in fields.iter().enumerate() {
                let binding_node_id = synthetic_node_id(syn_id, node_offset);
                node_offset += 1;
                let binding_name = gcx.intern_symbol(&format!("_rhs{}", field_idx));
                other_subpatterns.push(FieldPattern {
                    index: FieldIndex::from_usize(field_idx),
                    pattern: Pattern {
                        ty: field.ty,
                        span,
                        kind: PatternKind::Binding {
                            name: binding_name,
                            local: binding_node_id,
                            ty: field.ty,
                        },
                    },
                });
                other_binding_ids.push(binding_node_id);
            }
        }

        let mut same_variant_result = bool_literal(gcx, &mut builder, true);
        for ((lhs_id, rhs_id), field_ty) in self_binding_ids
            .iter()
            .zip(other_binding_ids.iter())
            .zip(field_tys.iter())
        {
            let lhs = builder.push_expr(ExprKind::Local(*lhs_id), *field_ty);
            let rhs = builder.push_expr(ExprKind::Local(*rhs_id), *field_ty);
            let field_eq = emit_eq_call(gcx, &mut builder, eq_method_id, lhs, rhs, *field_ty);
            same_variant_result = builder.push_expr(
                ExprKind::Logical {
                    op: crate::mir::LogicalOperator::And,
                    lhs: same_variant_result,
                    rhs: field_eq,
                },
                gcx.types.bool,
            );
        }

        let same_pattern = Pattern {
            ty: info.self_ty,
            span,
            kind: PatternKind::Variant {
                definition: adt_def,
                variant: *variant,
                subpatterns: other_subpatterns,
            },
        };
        let same_arm_id = ArmId::from_raw(builder.arms.len() as u32);
        builder.arms.push(Arm {
            pattern: Box::new(same_pattern),
            guard: None,
            body: same_variant_result,
            span,
        });
        inner_arms.push(same_arm_id);

        let false_expr = bool_literal(gcx, &mut builder, false);
        let fallback_arm_id = ArmId::from_raw(builder.arms.len() as u32);
        builder.arms.push(Arm {
            pattern: Box::new(Pattern {
                ty: info.self_ty,
                span,
                kind: PatternKind::Wild,
            }),
            guard: None,
            body: false_expr,
            span,
        });
        inner_arms.push(fallback_arm_id);

        let inner_match = builder.push_expr(
            ExprKind::Match {
                scrutinee: other_scrutinee,
                arms: inner_arms,
                binding_condition: false,
            },
            gcx.types.bool,
        );

        let outer_arm_id = ArmId::from_raw(builder.arms.len() as u32);
        builder.arms.push(Arm {
            pattern: Box::new(outer_pattern),
            guard: None,
            body: inner_match,
            span,
        });
        outer_arms.push(outer_arm_id);
    }

    let outer_match = builder.push_expr(
        ExprKind::Match {
            scrutinee: self_scrutinee,
            arms: outer_arms,
            binding_condition: false,
        },
        gcx.types.bool,
    );
    let body_block = builder.push_block(vec![], Some(outer_match));

    Some(ThirFunction {
        id: syn_id,
        body: Some(body_block),
        constructor_self: None,
        span,
        params: vec![self_param, other_param],
        stmts: builder.stmts,
        blocks: builder.blocks,
        exprs: builder.exprs,
        arms: builder.arms,
        match_reports: FxHashMap::default(),
        is_async: false,
    })
}

fn synthesize_closure_call<'ctx>(
    gcx: GlobalContext<'ctx>,
    info: SyntheticMethodInfo<'ctx>,
    syn_id: DefinitionID,
) -> Option<ThirFunction<'ctx>> {
    let TyKind::Closure { inputs, output, .. } = info.self_ty.kind() else {
        return None;
    };
    let is_async = gcx.std_item_def(StdItem::AsyncFn) == Some(info.interface_id);

    let span = synthetic_span();
    let mut builder = ThirBuilder::new(gcx, span);

    let args_ty = callable_args_ty(gcx, inputs);

    let self_param_ty = info.self_ty;

    let self_node_id = synthetic_node_id(syn_id, 0);
    let args_node_id = synthetic_node_id(syn_id, 1);

    let self_param = Param {
        id: self_node_id,
        name: gcx.intern_symbol("self"),
        ty: self_param_ty,
        span,
    };

    let args_param = Param {
        id: args_node_id,
        name: gcx.intern_symbol("args"),
        ty: args_ty,
        span,
    };

    let self_local = builder.push_expr(ExprKind::Local(self_node_id), self_param_ty);
    let body_stmts = Vec::new();
    let callee = self_local;

    let mut call_args = Vec::new();
    for (idx, &input_ty) in inputs.iter().enumerate() {
        let args_local = builder.push_expr(ExprKind::Local(args_node_id), args_ty);
        let field = builder.push_expr(
            ExprKind::Field {
                lhs: args_local,
                index: FieldIndex::from_usize(idx),
            },
            input_ty,
        );
        call_args.push(field);
    }

    let call_expr = builder.push_expr(
        ExprKind::Call {
            argument_evaluation_order: None,
            callee,
            args: call_args,
            is_async,
        },
        output,
    );

    let body_expr = if is_async {
        builder.push_expr(ExprKind::Await { future: call_expr }, output)
    } else {
        call_expr
    };
    let body_block = builder.push_block(body_stmts, Some(body_expr));

    Some(ThirFunction {
        id: syn_id,
        body: Some(body_block),
        constructor_self: None,
        span,
        params: vec![self_param, args_param],
        stmts: builder.stmts,
        blocks: builder.blocks,
        exprs: builder.exprs,
        arms: IndexVec::new(),
        match_reports: FxHashMap::default(),
        is_async,
    })
}

fn synthesize_enum_clone<'ctx>(
    gcx: GlobalContext<'ctx>,
    mut builder: ThirBuilder<'ctx>,
    self_param: Param<'ctx>,
    self_node_id: crate::hir::NodeID,
    self_ref_ty: Ty<'ctx>,
    info: SyntheticMethodInfo<'ctx>,
    syn_id: DefinitionID,
    enum_def: &crate::sema::models::EnumDefinition<'ctx>,
    clone_def: DefinitionID,
) -> Option<ThirFunction<'ctx>> {
    use crate::sema::models::EnumVariantKind;

    let span = synthetic_span();
    let adt_def = enum_def.adt_def;
    let generic_args = match info.self_ty.kind() {
        TyKind::Adt(_, args) => args,
        _ => GenericArguments::empty(),
    };

    let self_local = builder.push_expr(ExprKind::Local(self_node_id), self_ref_ty);
    let scrutinee = self_local;

    let mut arm_ids = Vec::new();
    let mut node_offset = 1u32;

    for (variant_idx, variant) in enum_def.variants.iter().enumerate() {
        let variant_index = VariantIndex::from_usize(variant_idx);

        match &variant.kind {
            EnumVariantKind::Unit => {
                let pattern = Pattern {
                    ty: info.self_ty,
                    span,
                    kind: PatternKind::Variant {
                        definition: adt_def,
                        variant: *variant,
                        subpatterns: vec![],
                    },
                };

                let body_expr = builder.push_expr(
                    ExprKind::Adt(AdtExpression {
                        base: None,
                        definition: adt_def,
                        variant_index: Some(variant_index),
                        generic_args,
                        fields: vec![],
                    }),
                    info.self_ty,
                );

                let arm_id = ArmId::from_raw(builder.arms.len() as u32);
                builder.arms.push(Arm {
                    pattern: Box::new(pattern),
                    guard: None,
                    body: body_expr,
                    span,
                });
                arm_ids.push(arm_id);
            }
            EnumVariantKind::Tuple(fields) | EnumVariantKind::Struct(fields) => {
                let mut subpatterns = Vec::new();
                let mut field_exprs = Vec::new();

                for (field_idx, field) in fields.iter().enumerate() {
                    let binding_node_id = synthetic_node_id(syn_id, node_offset);
                    node_offset += 1;

                    let binding_name = gcx.intern_symbol(&format!("_f{}", field_idx));

                    subpatterns.push(FieldPattern {
                        index: FieldIndex::from_usize(field_idx),
                        pattern: Pattern {
                            ty: field.ty,
                            span,
                            kind: PatternKind::Binding {
                                name: binding_name,
                                local: binding_node_id,
                                ty: field.ty,
                            },
                        },
                    });

                    let field_local = builder.push_expr(ExprKind::Local(binding_node_id), field.ty);
                    let cloned_field =
                        clone_field(gcx, &mut builder, field_local, field.ty, clone_def)?;

                    field_exprs.push(FieldExpression {
                        index: FieldIndex::from_usize(field_idx),
                        expression: cloned_field,
                    });
                }

                let pattern = Pattern {
                    ty: info.self_ty,
                    span,
                    kind: PatternKind::Variant {
                        definition: adt_def,
                        variant: *variant,
                        subpatterns,
                    },
                };

                let body_expr = builder.push_expr(
                    ExprKind::Adt(AdtExpression {
                        base: None,
                        definition: adt_def,
                        variant_index: Some(variant_index),
                        generic_args,
                        fields: field_exprs,
                    }),
                    info.self_ty,
                );

                let arm_id = ArmId::from_raw(builder.arms.len() as u32);
                builder.arms.push(Arm {
                    pattern: Box::new(pattern),
                    guard: None,
                    body: body_expr,
                    span,
                });
                arm_ids.push(arm_id);
            }
        }
    }

    let match_expr = builder.push_expr(
        ExprKind::Match {
            scrutinee,
            arms: arm_ids,
            binding_condition: false,
        },
        info.self_ty,
    );

    let body_block = builder.push_block(vec![], Some(match_expr));

    Some(ThirFunction {
        id: syn_id,
        body: Some(body_block),
        constructor_self: None,
        span,
        params: vec![self_param],
        stmts: builder.stmts,
        blocks: builder.blocks,
        exprs: builder.exprs,
        arms: builder.arms,
        match_reports: FxHashMap::default(),
        is_async: false,
    })
}

fn clone_field<'ctx>(
    gcx: GlobalContext<'ctx>,
    builder: &mut ThirBuilder<'ctx>,
    field_access: ExprId,
    field_ty: Ty<'ctx>,
    clone_def: DefinitionID,
) -> Option<ExprId> {
    // Call the requirement with its actual field type. Normal witness
    // selection after substitution handles primitive, nominal, and generic
    // fields uniformly; a missing implementation must never become a copy.
    let reqs = gcx.get_interface_requirements(clone_def)?;
    let clone_method = reqs
        .methods
        .iter()
        .find(|m| gcx.symbol_eq(m.name, "clone"))?;
    let generic_args = gcx
        .store
        .interners
        .intern_generic_args(vec![GenericArgument::Type(field_ty)]);
    let callee = make_zst_callee(gcx, builder, clone_method.id, generic_args);

    Some(builder.push_expr(
        ExprKind::Call {
            argument_evaluation_order: None,
            callee,
            args: vec![field_access],
            is_async: false,
        },
        field_ty,
    ))
}
