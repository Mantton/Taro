//! Adjacent enum tags: a stable `kind` string and, for payload variants, a
//! `content` value. Tuple payloads are exact-length sequences; struct payloads
//! reuse ordinary object-field decoding. Discriminant integers stay internal.
use super::*;
use crate::sema::models::{EnumDefinition, EnumVariantKind};

impl<'ctx> CodecBuilder<'ctx> {
    fn boolean(&mut self, value: bool) -> ExprId {
        self.body.push_expr(
            ExprKind::Literal(Constant {
                ty: self.gcx.types.bool,
                value: ConstantKind::Bool(value),
            }),
            self.gcx.types.bool,
        )
    }

    fn count(&mut self, value: usize) -> ExprId {
        self.body.push_expr(
            ExprKind::Literal(Constant {
                ty: self.gcx.types.uint,
                value: ConstantKind::Integer(value as u64),
            }),
            self.gcx.types.uint,
        )
    }

    fn operation(
        &mut self,
        statements: &mut Vec<StmtId>,
        name: &str,
        arguments: Vec<Ty<'ctx>>,
        values: Vec<ExprId>,
    ) {
        let value = self.checked(name, arguments, values);
        statements.push(self.body.push_stmt_expr(value));
    }
}

pub(super) fn synthesize<'ctx>(
    gcx: GlobalContext<'ctx>,
    info: SyntheticMethodInfo<'ctx>,
    syn_id: DefinitionID,
    enumeration: &EnumDefinition<'ctx>,
) -> Option<ThirFunction<'ctx>> {
    let signature = gcx.get_signature(syn_id);
    let params: Vec<_> = signature
        .inputs
        .iter()
        .enumerate()
        .map(|(index, input)| Param {
            id: synthetic_node_id(syn_id, index as u32),
            name: input.name,
            ty: input.ty,
            span: synthetic_span(),
        })
        .collect();
    let mut builder = CodecBuilder {
        gcx,
        body: ThirBuilder::new(gcx, synthetic_span()),
        id: syn_id,
        next_local: params.len() as u32,
        output: signature.output,
    };
    let codec = params.last()?;
    let encode = info.kind == SyntheticMethodKind::MemberwiseEncode;
    let mut statements = vec![];
    let scrutinee = if encode {
        builder.read(params[0].id, info.self_ty)
    } else {
        let decoder = builder.read(codec.id, codec.ty);
        let kind = builder.checked("__derivedDecodeEnumBegin", vec![codec.ty], vec![decoder]);
        let (statement, id) = builder.bind(kind, false);
        statements.push(statement);
        builder.read(id, gcx.types.string)
    };
    let TyKind::Adt(definition, generic_args) = info.self_ty.kind() else {
        return None;
    };
    let mut arms = vec![];
    for (variant_index, variant) in enumeration.variants.iter().enumerate() {
        let fields = match variant.kind {
            EnumVariantKind::Unit => &[][..],
            EnumVariantKind::Tuple(fields) | EnumVariantKind::Struct(fields) => fields,
        };
        let has_payload = !matches!(variant.kind, EnumVariantKind::Unit);
        let tuple = matches!(variant.kind, EnumVariantKind::Tuple(_));
        let mut subpatterns = vec![];
        let mut bound = vec![];
        let mut body = vec![];
        if encode {
            for (index, field) in fields.iter().enumerate() {
                let (id, pattern) = builder.local(field.ty);
                subpatterns.push(FieldPattern {
                    index: FieldIndex::from_usize(index),
                    pattern,
                });
                bound.push(builder.read(id, field.ty));
            }
            let encoder = builder.read(codec.id, codec.ty);
            let name = builder.string(&gcx.symbol_text(variant.name));
            let payload = builder.boolean(has_payload);
            builder.operation(
                &mut body,
                "__derivedEncodeEnumBegin",
                vec![codec.ty],
                vec![encoder, name, payload],
            );
            if has_payload {
                let encoder = builder.read(codec.id, codec.ty);
                let count = builder.count(fields.len());
                builder.operation(
                    &mut body,
                    if tuple {
                        "__derivedEncodeTupleBegin"
                    } else {
                        "__derivedEncodeBegin"
                    },
                    vec![codec.ty],
                    vec![encoder, count],
                );
                for (field, value) in fields.iter().zip(bound) {
                    let encoder = builder.read(codec.id, codec.ty);
                    if tuple {
                        builder.operation(
                            &mut body,
                            "__derivedEncodeTupleElement",
                            vec![field.ty, codec.ty],
                            vec![value, encoder],
                        );
                    } else {
                        let key = builder
                            .string(&gcx.symbol_text(field.label.expect("struct variant field")));
                        builder.operation(
                            &mut body,
                            "__derivedEncodeField",
                            vec![field.ty, codec.ty],
                            vec![value, encoder, key],
                        );
                    }
                }
                let encoder = builder.read(codec.id, codec.ty);
                builder.operation(
                    &mut body,
                    if tuple {
                        "__derivedEncodeTupleEnd"
                    } else {
                        "__derivedEncodeEnd"
                    },
                    vec![codec.ty],
                    vec![encoder],
                );
            }
        } else {
            let decoder = builder.read(codec.id, codec.ty);
            let payload = builder.boolean(has_payload);
            builder.operation(
                &mut body,
                "__derivedDecodeEnumContent",
                vec![codec.ty],
                vec![decoder, payload],
            );
        }
        let value = if encode {
            let encoder = builder.read(codec.id, codec.ty);
            builder.call("__derivedEncodeEnd", vec![codec.ty], vec![encoder])
        } else {
            let values = if tuple {
                let decoder = builder.read(codec.id, codec.ty);
                builder.operation(
                    &mut body,
                    "__derivedDecodeTupleBegin",
                    vec![codec.ty],
                    vec![decoder],
                );
                let mut values = vec![];
                for (index, field) in fields.iter().enumerate() {
                    let decoder = builder.read(codec.id, codec.ty);
                    let value = builder.checked(
                        "__derivedDecodeTupleElement",
                        vec![field.ty, codec.ty],
                        vec![decoder],
                    );
                    let (statement, id) = builder.bind(value, false);
                    body.push(statement);
                    values.push(FieldExpression {
                        index: FieldIndex::from_usize(index),
                        expression: builder.read(id, field.ty),
                    });
                }
                let decoder = builder.read(codec.id, codec.ty);
                builder.operation(
                    &mut body,
                    "__derivedDecodeTupleEnd",
                    vec![codec.ty],
                    vec![decoder],
                );
                values
            } else if has_payload {
                builder.decode_fields(
                    codec,
                    &fields
                        .iter()
                        .map(|field| (field.label.expect("struct variant field"), field.ty))
                        .collect::<Vec<_>>(),
                    &mut body,
                )
            } else {
                vec![]
            };
            let decoder = builder.read(codec.id, codec.ty);
            builder.operation(
                &mut body,
                "__derivedDecodeEnd",
                vec![codec.ty],
                vec![decoder],
            );
            let value = builder.body.push_expr(
                ExprKind::Adt(AdtExpression {
                    base: None,
                    definition,
                    generic_args,
                    variant_index: Some(VariantIndex::from_usize(variant_index)),
                    fields: values,
                }),
                info.self_ty,
            );
            builder.variant(signature.output, StdItem::ResultOkVariant, Some(value))
        };
        let block = builder.body.push_block(body, Some(value));
        let value = builder
            .body
            .push_expr(ExprKind::Block(block), signature.output);
        let pattern = Pattern {
            ty: if encode {
                info.self_ty
            } else {
                gcx.types.string
            },
            span: synthetic_span(),
            kind: if encode {
                PatternKind::Variant {
                    definition,
                    variant: *variant,
                    subpatterns,
                }
            } else {
                PatternKind::Constant {
                    value: Constant {
                        ty: gcx.types.string,
                        value: ConstantKind::String(variant.name),
                    },
                }
            },
        };
        arms.push(builder.body.arms.push(Arm {
            pattern: Box::new(pattern),
            guard: None,
            body: value,
            span: synthetic_span(),
        }));
    }
    if !encode {
        let decoder = builder.read(codec.id, codec.ty);
        let error = builder.call(
            "__derivedDecodeEnumUnknown",
            vec![info.self_ty, codec.ty],
            vec![decoder],
        );
        arms.push(builder.body.arms.push(Arm {
            pattern: Box::new(Pattern {
                ty: gcx.types.string,
                span: synthetic_span(),
                kind: PatternKind::Wild,
            }),
            guard: None,
            body: error,
            span: synthetic_span(),
        }));
    }
    let value = builder.body.push_expr(
        ExprKind::Match {
            scrutinee,
            arms,
            binding_condition: false,
        },
        signature.output,
    );
    let body = builder.body.push_block(statements, Some(value));
    Some(ThirFunction {
        id: syn_id,
        body: Some(body),
        constructor_self: None,
        span: synthetic_span(),
        params,
        stmts: builder.body.stmts,
        blocks: builder.body.blocks,
        exprs: builder.body.exprs,
        arms: builder.body.arms,
        match_reports: FxHashMap::default(),
        is_async: false,
    })
}
