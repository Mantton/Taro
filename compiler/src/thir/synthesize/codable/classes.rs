//! Class decoding builds private payload values, then uses ordinary constructor
//! publication. Inherited codecs select a required initializer specialization;
//! they never reinterpret a base Result as a subclass Result.
use super::*;
use crate::sema::{models::SyntheticDefinitionKind, tycheck::utils::generics::GenericsBuilder};

impl<'ctx> CodecBuilder<'ctx> {
    fn definition_call(
        &mut self,
        id: DefinitionID,
        arguments: GenericArguments<'ctx>,
        values: Vec<ExprId>,
    ) -> ExprId {
        let signature =
            instantiate_signature_with_args(self.gcx, self.gcx.get_signature(id), arguments);
        let callee = self.body.push_expr(
            ExprKind::Zst {
                id,
                generic_args: Some(arguments),
            },
            Ty::from_labeled_signature(self.gcx, &signature),
        );
        self.body.push_expr(
            ExprKind::Call {
                callee,
                args: values,
                is_async: false,
                argument_evaluation_order: None,
            },
            signature.output,
        )
    }

    fn finish(
        self,
        params: Vec<Param<'ctx>>,
        statements: Vec<StmtId>,
        value: ExprId,
    ) -> ThirFunction<'ctx> {
        let mut body = self.body;
        let block = body.push_block(statements, Some(value));
        ThirFunction {
            id: self.id,
            body: Some(block),
            constructor_self: None,
            span: synthetic_span(),
            params,
            stmts: body.stmts,
            blocks: body.blocks,
            exprs: body.exprs,
            arms: body.arms,
            match_reports: FxHashMap::default(),
            is_async: false,
        }
    }
}

fn builder<'ctx>(
    gcx: GlobalContext<'ctx>,
    id: DefinitionID,
) -> (CodecBuilder<'ctx>, Vec<Param<'ctx>>) {
    let signature = gcx.get_signature(id);
    let params: Vec<_> = signature
        .inputs
        .iter()
        .enumerate()
        .map(|(index, input)| Param {
            id: synthetic_node_id(id, index as u32),
            name: input.name,
            ty: input.ty,
            span: synthetic_span(),
        })
        .collect();
    (
        CodecBuilder {
            gcx,
            body: ThirBuilder::new(gcx, synthetic_span()),
            id,
            next_local: params.len() as u32,
            output: signature.output,
        },
        params,
    )
}

pub(in crate::thir::synthesize) fn synthesize_class<'ctx>(
    gcx: GlobalContext<'ctx>,
    info: SyntheticMethodInfo<'ctx>,
    factory: DefinitionID,
) -> Vec<ThirFunction<'ctx>> {
    let kind = gcx.store.synthetic_definitions.borrow()[&factory].kind;
    let SyntheticDefinitionKind::ClassDecoder { initializer, .. } = kind else {
        unreachable!()
    };
    let (mut forward, params) = builder(gcx, factory);
    let identity = GenericsBuilder::identity_for_item(gcx, factory);
    let own = gcx
        .store
        .interners
        .intern_generic_args_slice(&identity[gcx.generics_of(factory).parent_count..]);
    let arguments = gcx
        .class_method_arguments(info.self_ty, initializer, own)
        .expect("decoding initializer arguments");
    let values = params
        .iter()
        .map(|parameter| forward.read(parameter.id, parameter.ty))
        .collect();
    let value = forward.definition_call(initializer, arguments, values);
    let mut functions = vec![forward.finish(params, vec![], value)];
    let generated = gcx
        .store
        .synthetic_definitions
        .borrow()
        .get(&initializer)
        .is_some_and(|value| {
            matches!(
                value.kind,
                SyntheticDefinitionKind::ClassDecodingInitializer { .. }
            )
        });
    if !generated {
        return functions;
    }

    let helper = gcx
        .class_payload_initializer(initializer)
        .expect("decoder payload helper");
    let (mut decoder, params) = builder(gcx, helper);
    let codec = params.last().expect("decoder input");
    let payload = gcx.initializer_target(helper);
    let TyKind::Adt(payload_def, payload_args) = payload.kind() else {
        unreachable!()
    };
    let TyKind::Adt(class, class_args) = info.self_ty.kind() else {
        unreachable!()
    };
    let offset = crate::sema::tycheck::derive::codec_field_offset(gcx, info.self_ty);
    let fields = &gcx.get_struct_definition(class.id).fields[offset..];
    let mut statements = vec![];
    let mut defaults = Vec::new();
    // Swift evaluates stored defaults during decoding, even when a mutable
    // field is subsequently replaced. Readonly presets retain their value.
    for field in fields {
        let default = field.default_provider.map(|provider| {
            let value = decoder.definition_call(provider, class_args, vec![]);
            let (statement, local) = decoder.bind(value, false);
            statements.push(statement);
            (local, field.ty)
        });
        defaults.push(default);
    }
    let decoded_fields: Vec<_> = fields
        .iter()
        .filter(|field| {
            !field.coding_skip
                && (field.default_provider.is_none()
                    || field.mutability == crate::hir::Mutability::Mutable)
        })
        .map(|field| (field.coding_key.unwrap_or(field.name), field.ty))
        .collect();
    let decoded = decoder.decode_fields(codec, &decoded_fields, &mut statements);
    let mut decoded = decoded.into_iter();
    let mut values = vec![];
    if gcx.class_base(info.self_ty).is_some() {
        let (base, arguments) =
            crate::sema::lowering::class_codable::base_initializer(gcx, info.self_ty)
                .expect("validated base init()");
        let base = gcx
            .class_payload_initializer(base)
            .expect("superclass private initializer");
        let value = decoder.definition_call(base, arguments, vec![]);
        let (statement, local) = decoder.bind(value, false);
        statements.push(statement);
        let ty = decoder.gcx.initializer_target(base);
        // The helper's abstract result must use this base instantiation.
        let ty =
            crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args(gcx, ty, arguments);
        let expression = decoder.read(local, ty);
        values.push(FieldExpression {
            index: FieldIndex::from_raw(0),
            expression,
        });
    }
    let prefix = values.len();
    for (index, (field, default)) in fields.iter().zip(defaults).enumerate() {
        let expression = if field.coding_skip {
            if let Some((local, ty)) = default {
                decoder.read(local, ty)
            } else {
                let value = decoder.skipped_field_value(field, class_args);
                let (statement, local) = decoder.bind(value, false);
                statements.push(statement);
                decoder.read(local, field.ty)
            }
        } else if field.mutability == crate::hir::Mutability::Immutable && default.is_some() {
            let (local, ty) = default.unwrap();
            decoder.read(local, ty)
        } else {
            decoded.next().expect("decoded stored field").expression
        };
        values.push(FieldExpression {
            index: FieldIndex::from_usize(prefix + index),
            expression,
        });
    }
    let value = decoder.body.push_expr(
        ExprKind::Adt(AdtExpression {
            definition: payload_def,
            generic_args: payload_args,
            variant_index: None,
            fields: values,
            base: None,
        }),
        payload,
    );
    let value = decoder.variant(decoder.output, StdItem::ResultOkVariant, Some(value));
    let body = decoder.finish(params, statements, value);
    functions.push(crate::thir::package::class_codec_wrapper(
        gcx,
        initializer,
        helper,
        &body,
    ));
    functions.push(body);
    functions
}
