//! Reify async Self at its ready-value boundary using checked generic wrappers.
//! Run over every THIR body, including bound-method closure bodies, before MIR.
use super::*;
use crate::{
    compile::context::Gcx,
    hir::{DefinitionID, NodeID},
    sema::{
        models::{GenericArgument, SyntheticDefinitionKind, Ty, TyKind},
        tycheck::utils::{generics::GenericsBuilder, instantiate::instantiate_signature_with_args},
    },
};
use rustc_hash::FxHashMap;

fn push<'ctx>(function: &mut ThirFunction<'ctx>, kind: ExprKind<'ctx>, ty: Ty<'ctx>) -> ExprId {
    function.exprs.push(Expr {
        kind,
        ty,
        span: function.span,
    })
}
fn empty<'ctx>(gcx: Gcx<'ctx>, id: DefinitionID, is_async: bool) -> ThirFunction<'ctx> {
    ThirFunction {
        id,
        body: None,
        constructor_self: None,
        span: gcx.definition_ident(id).span,
        params: vec![],
        stmts: IndexVec::new(),
        blocks: IndexVec::new(),
        exprs: IndexVec::new(),
        arms: IndexVec::new(),
        match_reports: FxHashMap::default(),
        is_async,
    }
}
fn finish(function: &mut ThirFunction<'_>, result: ExprId) {
    let id = BlockId::from_raw(0);
    function.blocks.push(Block {
        id,
        stmts: vec![],
        expr: Some(result),
    });
    function.body = Some(id);
}

pub(super) fn run<'ctx>(
    gcx: Gcx<'ctx>,
    functions: &mut FxHashMap<DefinitionID, ThirFunction<'ctx>>,
) {
    let mut ids: Vec<_> = functions.keys().copied().collect();
    ids.sort();
    for id in ids {
        let function = functions.get_mut(&id).unwrap();
        let expressions: Vec<_> = function.exprs.indices().collect();
        for expression in expressions {
            let ExprKind::Call {
                callee,
                mut args,
                mut argument_evaluation_order,
                is_async: true,
            } = function.exprs[expression].kind.clone()
            else {
                continue;
            };
            let ExprKind::Zst {
                id: method,
                generic_args: Some(source_args),
            } = function.exprs[callee].kind
            else {
                continue;
            };
            if !gcx.definition_is_async(method)
                || !crate::sema::tycheck::utils::erased_self::returns_owned_self(gcx, method)
                || !gcx
                    .definition_parent(method)
                    .is_some_and(|parent| gcx.get_interface_definition(parent).is_some())
            {
                continue;
            }
            let Some(receiver) = args.first().copied() else {
                continue;
            };
            let receiver_ty = crate::sema::lowering::erased_async_self::receiver_type(
                function.exprs[receiver].ty,
            );
            let result_ty = function.exprs[expression].ty;
            if !matches!(receiver_ty.kind(), TyKind::BoxedExistential { .. })
                || !matches!(result_ty.kind(), TyKind::BoxedExistential { .. })
            {
                continue;
            }
            let adapter = gcx.erased_async_self_adapter(id, method, source_args, result_ty);
            let mut actual = GenericsBuilder::identity_for_item(gcx, id).to_vec();
            actual.push(GenericArgument::Type(receiver_ty));
            let actual = gcx.store.interners.intern_generic_args(actual);
            let adapter_signature = gcx.get_signature(adapter);
            // Replace only omitted providers. Explicit user expressions keep
            // their source order and never invoke a hidden default.
            for index in 1..args.len() {
                let Some(original_provider) =
                    gcx.get_signature(method).inputs[index].default_provider
                else {
                    continue;
                };
                let ExprKind::Call {
                    callee: default_callee,
                    args: ref default_args,
                    ..
                } = function.exprs[args[index]].kind
                else {
                    continue;
                };
                if !default_args.is_empty()
                    || !matches!(function.exprs[default_callee].kind,
                    ExprKind::Zst {id,..} if id==original_provider)
                {
                    continue;
                }
                let provider = adapter_signature.inputs[index].default_provider.unwrap();
                let opened =
                    gcx.erased_default(adapter, provider, gcx.generics_of(adapter).parent_count);
                let source = if let TyKind::Reference(inner) = function.exprs[receiver].ty.kind() {
                    push(function, ExprKind::Deref(receiver), inner)
                } else {
                    receiver
                };
                let borrowed_ty = Ty::new(TyKind::Reference(receiver_ty), gcx);
                let borrowed = push(function, ExprKind::Reference { expr: source }, borrowed_ty);
                let signature =
                    instantiate_signature_with_args(gcx, gcx.get_signature(opened), actual);
                let callee = push(
                    function,
                    ExprKind::Zst {
                        id: opened,
                        generic_args: Some(actual),
                    },
                    Ty::from_labeled_signature(gcx, &signature),
                );
                args[index] = push(
                    function,
                    ExprKind::Call {
                        callee,
                        args: vec![borrowed],
                        argument_evaluation_order: None,
                        is_async: false,
                    },
                    signature.output,
                );
                argument_evaluation_order
                    .get_or_insert_with(|| (0..adapter_signature.inputs.len()).collect());
            }
            let signature = instantiate_signature_with_args(gcx, adapter_signature, actual);
            let callee = push(
                function,
                ExprKind::Zst {
                    id: adapter,
                    generic_args: Some(actual),
                },
                Ty::from_labeled_signature(gcx, &signature),
            );
            function.exprs[expression].kind = ExprKind::Call {
                callee,
                args,
                argument_evaluation_order,
                is_async: true,
            };
        }
    }
    let mut definitions: Vec<_> = gcx
        .store
        .synthetic_definitions
        .borrow()
        .iter()
        .filter_map(|(id, definition)| {
            (id.package() == gcx.package_index()
                && matches!(
                    definition.kind,
                    SyntheticDefinitionKind::ErasedAsyncSelf { .. }
                        | SyntheticDefinitionKind::ErasedAsyncSelfDefault { .. }
                ))
            .then_some((*id, definition.kind))
        })
        .collect();
    definitions.sort_by_key(|(id, _)| *id);
    for (id, kind) in definitions {
        let (adapter, target, is_async) = match kind {
            SyntheticDefinitionKind::ErasedAsyncSelf { method, .. } => (id, method, true),
            SyntheticDefinitionKind::ErasedAsyncSelfDefault { adapter, provider } => {
                (adapter, provider, false)
            }
            _ => unreachable!(),
        };
        let arguments = gcx.with_type_database(adapter.package(), |db| {
            db.erased_async_self_arguments[&adapter]
        });
        let signature = gcx.get_signature(id);
        let target_signature =
            instantiate_signature_with_args(gcx, gcx.get_signature(target), arguments);
        let mut function = empty(gcx, id, is_async);
        function.params = signature
            .inputs
            .iter()
            .enumerate()
            .map(|(index, input)| Param {
                id: NodeID::from_raw(u32::MAX - index as u32),
                name: input.name,
                ty: input.ty,
                span: function.span,
            })
            .collect();
        let mut args = vec![];
        for parameter in function.params.clone() {
            let value = push(&mut function, ExprKind::Local(parameter.id), parameter.ty);
            let value = if let TyKind::Reference(inner) = parameter.ty.kind() {
                let place = push(&mut function, ExprKind::Deref(value), inner);
                push(
                    &mut function,
                    ExprKind::Reference { expr: place },
                    parameter.ty,
                )
            } else {
                value
            };
            args.push(value);
        }
        let callee = push(
            &mut function,
            ExprKind::Zst {
                id: target,
                generic_args: Some(arguments),
            },
            Ty::from_labeled_signature(gcx, &target_signature),
        );
        let call = push(
            &mut function,
            ExprKind::Call {
                callee,
                args,
                argument_evaluation_order: None,
                is_async,
            },
            target_signature.output,
        );
        let result = if is_async {
            let concrete = crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args(
                gcx,
                gcx.function_body_output(target),
                arguments,
            );
            let ready = push(&mut function, ExprKind::Await { future: call }, concrete);
            let TyKind::BoxedExistential { interfaces } = signature.output.kind() else {
                unreachable!()
            };
            push(
                &mut function,
                ExprKind::BoxExistential {
                    value: ready,
                    interfaces,
                },
                signature.output,
            )
        } else {
            call
        };
        finish(&mut function, result);
        functions.insert(id, function);
    }
}
