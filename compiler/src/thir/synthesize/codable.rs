//! Struct and enum codec synthesis. Generated functions use the existing generic codec
//! protocol and normal THIR control flow, including ordinary error propagation,
//! GC-rooted locals and loop safepoints. There is no runtime reflection or DOM
//! dependency here.
use super::*;
use crate::span::Symbol;

mod classes;
mod enums;
use crate::sema::tycheck::utils::{
    instantiate::instantiate_signature_with_args, normalize_aliases,
};
pub(super) use classes::synthesize_class;

pub(super) fn register_signature<'ctx>(
    gcx: GlobalContext<'ctx>,
    info: SyntheticMethodInfo<'ctx>,
) -> (
    crate::sema::models::Generics,
    crate::sema::models::LabeledFunctionSignature<'ctx>,
) {
    let mut generics = self_type_generics(gcx, info.self_ty);
    if gcx.is_class_type(info.self_ty) {
        let TyKind::Adt(owner, _) = info.self_ty.kind() else {
            unreachable!()
        };
        generics = crate::sema::models::Generics {
            parent: Some(owner.id),
            parent_count: generics.parent_count + generics.total_count(),
            parameters: vec![],
            has_self: false,
        };
    }
    let mut arguments = vec![GenericArgument::Type(info.self_ty)];
    for parameter in &gcx.generics_of(info.method_id).parameters {
        let mut parameter = parameter.clone();
        parameter.index = generics.parent_count + generics.parameters.len();
        arguments.push(GenericArgument::Type(Ty::new(
            TyKind::Parameter(GenericParameter {
                index: parameter.index,
                name: parameter.name,
            }),
            gcx,
        )));
        generics.parameters.push(parameter);
    }
    let arguments = gcx.store.interners.intern_generic_args(arguments);
    let signature =
        instantiate_signature_with_args(gcx, gcx.get_signature(info.method_id), arguments);
    (generics, signature)
}

struct CodecBuilder<'ctx> {
    gcx: GlobalContext<'ctx>,
    body: ThirBuilder<'ctx>,
    id: DefinitionID,
    next_local: u32,
    output: Ty<'ctx>,
}

impl<'ctx> CodecBuilder<'ctx> {
    fn local(&mut self, ty: Ty<'ctx>) -> (crate::hir::NodeID, Pattern<'ctx>) {
        let id = synthetic_node_id(self.id, self.next_local);
        self.next_local += 1;
        (
            id,
            Pattern {
                ty,
                span: self.body.span,
                kind: PatternKind::Binding {
                    name: self
                        .gcx
                        .intern_symbol(&format!("$codec{}", self.next_local)),
                    local: id,
                    ty,
                },
            },
        )
    }

    fn read(&mut self, id: crate::hir::NodeID, ty: Ty<'ctx>) -> ExprId {
        self.body.push_expr(ExprKind::Local(id), ty)
    }

    fn bind(&mut self, value: ExprId, mutable: bool) -> (StmtId, crate::hir::NodeID) {
        let ty = self.body.exprs[value].ty;
        let (id, pattern) = self.local(ty);
        let statement = self.body.push_stmt(StmtKind::Let {
            id,
            pattern,
            expr: Some(value),
            ty,
            mutable,
        });
        (statement, id)
    }

    fn string(&mut self, value: &str) -> ExprId {
        let ty = self.gcx.types.string;
        self.body.push_expr(
            ExprKind::Literal(Constant {
                ty,
                value: ConstantKind::String(self.gcx.intern_symbol(value)),
            }),
            ty,
        )
    }

    fn variant(&mut self, ty: Ty<'ctx>, item: StdItem, payload: Option<ExprId>) -> ExprId {
        let TyKind::Adt(definition, generic_args) = normalize_aliases(self.gcx, ty).kind() else {
            unreachable!("codec enum")
        };
        let variant = self.gcx.std_item_def(item).expect("codec variant");
        let index = self
            .gcx
            .get_enum_definition(definition.id)
            .variants
            .iter()
            .position(|v| v.def_id == variant)
            .expect("codec enum variant");
        self.body.push_expr(
            ExprKind::Adt(AdtExpression {
                base: None,
                definition,
                generic_args,
                variant_index: Some(VariantIndex::from_usize(index)),
                fields: payload
                    .map(|expression| {
                        vec![FieldExpression {
                            index: FieldIndex::from_usize(0),
                            expression,
                        }]
                    })
                    .unwrap_or_default(),
            }),
            ty,
        )
    }

    fn arm(
        &mut self,
        ty: Ty<'ctx>,
        item: StdItem,
        payload: Option<Pattern<'ctx>>,
        value: ExprId,
    ) -> ArmId {
        let TyKind::Adt(definition, _) = ty.kind() else {
            unreachable!("codec enum")
        };
        let variant = self.gcx.std_item_def(item).expect("codec variant");
        let variant = *self
            .gcx
            .get_enum_definition(definition.id)
            .variants
            .iter()
            .find(|v| v.def_id == variant)
            .expect("codec variant belongs to enum");
        let pattern = Pattern {
            ty,
            span: self.body.span,
            kind: PatternKind::Variant {
                definition,
                variant,
                subpatterns: payload
                    .map(|pattern| {
                        vec![FieldPattern {
                            index: FieldIndex::from_usize(0),
                            pattern,
                        }]
                    })
                    .unwrap_or_default(),
            },
        };
        self.body.arms.push(Arm {
            pattern: Box::new(pattern),
            guard: None,
            body: value,
            span: self.body.span,
        })
    }

    /// The same two-arm control flow as source-level `!`: bind successful
    /// storage once, or return the enclosing Result's error immediately.
    fn propagate(&mut self, call: ExprId) -> ExprId {
        let result = self.body.exprs[call].ty;
        let TyKind::Adt(_, arguments) = result.kind() else {
            unreachable!("codec Result")
        };
        let success = arguments[0].ty().expect("Result success");
        let error = arguments[1].ty().expect("Result error");
        let (ok_id, ok_pattern) = self.local(success);
        let ok_value = self.read(ok_id, success);
        let ok_arm = self.arm(result, StdItem::ResultOkVariant, Some(ok_pattern), ok_value);
        let (error_id, error_pattern) = self.local(error);
        let error_value = self.read(error_id, error);
        let error_result = self.variant(self.output, StdItem::ResultErrVariant, Some(error_value));
        let returned = self.body.push_expr(
            ExprKind::Return {
                value: Some(error_result),
            },
            Ty::new(TyKind::Never, self.gcx),
        );
        let error_arm = self.arm(
            result,
            StdItem::ResultErrVariant,
            Some(error_pattern),
            returned,
        );
        self.body.push_expr(
            ExprKind::Match {
                scrutinee: call,
                arms: vec![ok_arm, error_arm],
                binding_condition: false,
            },
            success,
        )
    }

    fn call(&mut self, name: &str, arguments: Vec<Ty<'ctx>>, values: Vec<ExprId>) -> ExprId {
        let id = crate::mir::optimize::async_transform::find_std_function(
            self.gcx,
            "encoding",
            name,
            self.body.span,
        )
        .unwrap_or_else(|_| panic!("derived codec support in std"));
        let arguments = self
            .gcx
            .store
            .interners
            .intern_generic_args(arguments.into_iter().map(GenericArgument::Type).collect());
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

    fn checked(&mut self, name: &str, arguments: Vec<Ty<'ctx>>, values: Vec<ExprId>) -> ExprId {
        let call = self.call(name, arguments, values);
        self.propagate(call)
    }

    fn skipped_field_value(
        &mut self,
        field: &crate::sema::models::StructField<'ctx>,
        owner_args: GenericArguments<'ctx>,
    ) -> ExprId {
        if let Some(provider) = field.default_provider {
            let signature = instantiate_signature_with_args(
                self.gcx,
                self.gcx.get_signature(provider),
                owner_args,
            );
            let callee = self.body.push_expr(
                ExprKind::Zst {
                    id: provider,
                    generic_args: Some(owner_args),
                },
                Ty::from_labeled_signature(self.gcx, &signature),
            );
            return self.body.push_expr(
                ExprKind::Call {
                    callee,
                    args: vec![],
                    is_async: false,
                    argument_evaluation_order: None,
                },
                field.ty,
            );
        }
        let optional = self.gcx.std_item_def(StdItem::Optional).expect("Optional");
        if matches!(normalize_aliases(self.gcx, field.ty).kind(), TyKind::Adt(def, _) if def.id == optional)
        {
            return self.variant(field.ty, StdItem::OptionalNoneVariant, None);
        }
        let default_iface = self.gcx.std_item_def(StdItem::Default).expect("Default");
        let default_method = self
            .gcx
            .get_interface_requirements(default_iface)
            .and_then(|reqs| {
                reqs.methods
                    .iter()
                    .find(|m| self.gcx.symbol_eq(m.name, "default"))
                    .map(|m| m.id)
            })
            .expect("Default::default method");
        let args = self
            .gcx
            .store
            .interners
            .intern_generic_args(vec![GenericArgument::Type(field.ty)]);
        let callee = make_zst_callee(self.gcx, &mut self.body, default_method, args);
        self.body.push_expr(
            ExprKind::Call {
                callee,
                args: vec![],
                is_async: false,
                argument_evaluation_order: None,
            },
            field.ty,
        )
    }

    /// Decode one object payload using the same optional and missing-field rules
    /// for structs and struct-style enum variants.
    fn decode_fields(
        &mut self,
        codec: &Param<'ctx>,
        fields: &[(Symbol, Ty<'ctx>)],
        statements: &mut Vec<StmtId>,
    ) -> Vec<FieldExpression> {
        let codec_ty = codec.ty;
        let codec_value = self.read(codec.id, codec_ty);
        let begin = self.checked("__derivedDecodeBegin", vec![codec_ty], vec![codec_value]);
        statements.push(self.body.push_stmt_expr(begin));
        let optional = self.gcx.std_item_def(StdItem::Optional).expect("Optional");
        let mut slots = Vec::new();
        for (_, ty) in fields {
            let TyKind::Adt(optional_def, _) = self.gcx.get_type(optional).kind() else {
                unreachable!()
            };
            let optional_ty = Ty::new(
                TyKind::Adt(
                    optional_def,
                    self.gcx
                        .store
                        .interners
                        .intern_generic_args(vec![GenericArgument::Type(*ty)]),
                ),
                self.gcx,
            );
            let initial = if matches!(normalize_aliases(self.gcx, *ty).kind(), TyKind::Adt(def, _) if def.id == optional)
            {
                let none = self.variant(*ty, StdItem::OptionalNoneVariant, None);
                self.variant(optional_ty, StdItem::OptionalSomeVariant, Some(none))
            } else {
                self.variant(optional_ty, StdItem::OptionalNoneVariant, None)
            };
            let (statement, id) = self.bind(initial, true);
            statements.push(statement);
            slots.push((id, optional_ty));
        }
        let codec_value = self.read(codec.id, codec_ty);
        let next = self.checked("__derivedDecodeNext", vec![codec_ty], vec![codec_value]);
        let next_ty = self.body.exprs[next].ty;
        let (key_id, key_pattern) = self.local(self.gcx.types.string);
        let selected = self.read(key_id, self.gcx.types.string);
        let some = self.arm(
            next_ty,
            StdItem::OptionalSomeVariant,
            Some(key_pattern),
            selected,
        );
        let stop = self.body.push_expr(
            ExprKind::Break {
                label: None,
                value: None,
            },
            Ty::new(TyKind::Never, self.gcx),
        );
        let none = self.arm(next_ty, StdItem::OptionalNoneVariant, None, stop);
        let next_key = self.body.push_expr(
            ExprKind::Match {
                scrutinee: next,
                arms: vec![some, none],
                binding_condition: false,
            },
            self.gcx.types.string,
        );
        let (key_statement, current_key) = self.bind(next_key, false);
        let mut loop_statements = vec![key_statement];
        for ((name, ty), (slot, slot_ty)) in fields.iter().zip(&slots) {
            let codec_value = self.read(codec.id, codec_ty);
            let key = self.read(current_key, self.gcx.types.string);
            let expected = self.string(&self.gcx.symbol_text(*name));
            let local = self.read(*slot, *slot_ty);
            let reference = self.body.push_expr(
                ExprKind::Reference { expr: local },
                Ty::new(TyKind::Reference(*slot_ty), self.gcx),
            );
            let handled = self.checked(
                "__derivedDecodeField",
                vec![*ty, codec_ty],
                vec![codec_value, key, expected, reference],
            );
            let next_iteration = self.body.push_expr(
                ExprKind::Continue { label: None },
                Ty::new(TyKind::Never, self.gcx),
            );
            let condition = self.body.push_expr(
                ExprKind::If {
                    cond: handled,
                    then_expr: next_iteration,
                    else_expr: None,
                },
                self.gcx.types.void,
            );
            loop_statements.push(self.body.push_stmt_expr(condition));
        }
        let codec_value = self.read(codec.id, codec_ty);
        let skip = self.checked("__derivedDecodeSkip", vec![codec_ty], vec![codec_value]);
        loop_statements.push(self.body.push_stmt_expr(skip));
        let block = self.body.push_block(loop_statements, None);
        statements.push(self.body.push_stmt(StmtKind::Loop { label: None, block }));
        let mut values = Vec::new();
        for ((name, ty), (slot, slot_ty)) in fields.iter().zip(&slots) {
            let slot = self.read(*slot, *slot_ty);
            let codec_value = self.read(codec.id, codec_ty);
            let key = self.string(&self.gcx.symbol_text(*name));
            let value = self.checked(
                "__derivedDecodeRequire",
                vec![*ty, codec_ty],
                vec![slot, codec_value, key],
            );
            let (statement, id) = self.bind(value, false);
            statements.push(statement);
            values.push((id, *ty));
        }
        let codec_value = self.read(codec.id, codec_ty);
        let end = self.checked("__derivedDecodeEnd", vec![codec_ty], vec![codec_value]);
        statements.push(self.body.push_stmt_expr(end));
        values
            .into_iter()
            .enumerate()
            .map(|(index, (id, ty))| FieldExpression {
                index: FieldIndex::from_usize(index),
                expression: self.read(id, ty),
            })
            .collect()
    }
}

pub(super) fn synthesize<'ctx>(
    gcx: GlobalContext<'ctx>,
    info: SyntheticMethodInfo<'ctx>,
    syn_id: DefinitionID,
) -> Option<ThirFunction<'ctx>> {
    let TyKind::Adt(definition, generic_args) = info.self_ty.kind() else {
        return None;
    };
    if let Some(enumeration) = gcx.try_get_enum_definition(definition.id) {
        return enums::synthesize(gcx, info, syn_id, enumeration);
    }
    let field_offset = crate::sema::tycheck::derive::codec_field_offset(gcx, info.self_ty);
    let fields = &gcx.try_get_struct_definition(definition.id)?.fields[field_offset..];
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
    let mut statements = Vec::new();
    let codec = params.last()?;
    let codec_ty = codec.ty;
    let codec_value = builder.read(codec.id, codec_ty);
    let value = if info.kind == SyntheticMethodKind::MemberwiseEncode {
        let encoded_count = fields.iter().filter(|field| !field.coding_skip).count();
        let count = builder.body.push_expr(
            ExprKind::Literal(Constant {
                ty: gcx.types.uint,
                value: ConstantKind::Integer(encoded_count as u64),
            }),
            gcx.types.uint,
        );
        let begin = builder.checked(
            "__derivedEncodeBegin",
            vec![codec_ty],
            vec![codec_value, count],
        );
        statements.push(builder.body.push_stmt_expr(begin));
        for (index, field) in fields.iter().enumerate() {
            if field.coding_skip {
                continue;
            }
            let receiver = builder.read(params[0].id, info.self_ty);
            let value = builder.body.push_expr(
                ExprKind::Field {
                    lhs: receiver,
                    index: FieldIndex::from_usize(index + field_offset),
                },
                field.ty,
            );
            let key_sym = field.coding_key.unwrap_or(field.name);
            let key = builder.string(&gcx.symbol_text(key_sym));
            let codec_value = builder.read(codec.id, codec_ty);
            let encoded = builder.checked(
                "__derivedEncodeField",
                vec![field.ty, codec_ty],
                vec![value, codec_value, key],
            );
            statements.push(builder.body.push_stmt_expr(encoded));
        }
        let codec_value = builder.read(codec.id, codec_ty);
        builder.call("__derivedEncodeEnd", vec![codec_ty], vec![codec_value])
    } else {
        let coded_specs: Vec<_> = fields
            .iter()
            .filter(|field| !field.coding_skip)
            .map(|field| (field.coding_key.unwrap_or(field.name), field.ty))
            .collect();
        let mut decoded = builder
            .decode_fields(codec, &coded_specs, &mut statements)
            .into_iter();
        let mut all_fields = Vec::with_capacity(fields.len());
        for (index, field) in fields.iter().enumerate() {
            let expression = if field.coding_skip {
                let value = builder.skipped_field_value(field, generic_args);
                let (statement, id) = builder.bind(value, false);
                statements.push(statement);
                builder.read(id, field.ty)
            } else {
                decoded.next().expect("decoded field").expression
            };
            all_fields.push(FieldExpression {
                index: FieldIndex::from_usize(index),
                expression,
            });
        }
        let value = builder.body.push_expr(
            ExprKind::Adt(AdtExpression {
                base: None,
                definition,
                generic_args,
                fields: all_fields,
                variant_index: None,
            }),
            info.self_ty,
        );
        builder.variant(signature.output, StdItem::ResultOkVariant, Some(value))
    };
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
