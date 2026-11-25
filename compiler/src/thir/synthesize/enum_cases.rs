//! Enum witnesses match declaration-order indices for CaseIterable and source
//! discriminants for RawValue. Both construct ordinary enum variants.

use super::{ThirBuilder, self_type_generics, synthetic_node_id, synthetic_span};
use crate::{
    compile::context::Gcx,
    hir::{DefinitionID, StdItem},
    sema::{
        models::{
            GenericArgument, GenericArguments, GenericParameter, Generics,
            LabeledFunctionSignature, SyntheticMethodKind, Ty, TyKind,
        },
        resolve::models::TypeHead,
        tycheck::{
            derive::SyntheticMethodInfo, utils::instantiate::instantiate_signature_with_args,
        },
    },
    thir::{
        AdtExpression, Arm, ArmId, Constant, ConstantKind, ExprId, ExprKind, FieldExpression,
        FieldIndex, Param, Pattern, PatternKind, ThirFunction, VariantIndex,
    },
};
use rustc_hash::FxHashMap;

pub(super) fn raw_signature<'ctx>(
    gcx: Gcx<'ctx>,
    info: SyntheticMethodInfo<'ctx>,
) -> (Generics, LabeledFunctionSignature<'ctx>) {
    let mut generics = self_type_generics(gcx, info.self_ty);
    let mut raw = gcx
        .generics_of(info.interface_id)
        .parameters
        .last()
        .expect("RawValue[Raw]")
        .clone();
    raw.index = generics.total_count();
    let raw_ty = Ty::new(
        TyKind::Parameter(GenericParameter {
            name: raw.name,
            index: raw.index,
        }),
        gcx,
    );
    generics.parameters.push(raw);
    let args = gcx.store.interners.intern_generic_args(vec![
        GenericArgument::Type(info.self_ty),
        GenericArgument::Type(raw_ty),
    ]);
    (
        generics,
        instantiate_signature_with_args(gcx, gcx.get_signature(info.method_id), args),
    )
}

fn variant<'ctx>(
    builder: &mut ThirBuilder<'ctx>,
    ty: Ty<'ctx>,
    index: usize,
    payload: Option<ExprId>,
) -> ExprId {
    let TyKind::Adt(definition, generic_args) = ty.kind() else {
        unreachable!("enum variant requires an enum")
    };
    let fields = payload
        .into_iter()
        .map(|expression| FieldExpression {
            index: FieldIndex::from_usize(0),
            expression,
        })
        .collect();
    builder.push_expr(
        ExprKind::Adt(AdtExpression {
            base: None,
            definition,
            generic_args,
            variant_index: Some(VariantIndex::from_usize(index)),
            fields,
        }),
        ty,
    )
}

pub(super) fn synthesize<'ctx>(
    gcx: Gcx<'ctx>,
    head: TypeHead,
    info: SyntheticMethodInfo<'ctx>,
    id: DefinitionID,
) -> Option<ThirFunction<'ctx>> {
    let TypeHead::Nominal(owner) = head else {
        return None;
    };
    let definition = gcx.try_get_enum_definition(owner)?;
    let sig = gcx.get_signature(id);
    let input = sig.inputs.first()?;
    let span = synthetic_span();
    let mut builder = ThirBuilder::new(gcx, span);
    let param = Param {
        id: synthetic_node_id(id, 0),
        name: input.name,
        ty: input.ty,
        span,
    };
    let scrutinee = builder.push_expr(ExprKind::Local(param.id), param.ty);
    let mut arms = Vec::new();
    let mut arm = |builder: &mut ThirBuilder<'ctx>, kind, body| {
        arms.push(ArmId::from_raw(builder.arms.len() as u32));
        builder.arms.push(Arm {
            pattern: Box::new(Pattern {
                ty: input.ty,
                span,
                kind,
            }),
            guard: None,
            body,
            span,
        });
    };
    if matches!(
        info.kind,
        SyntheticMethodKind::EnumRawValue | SyntheticMethodKind::EnumCaseName
    ) {
        for case in definition.variants {
            let value = builder.push_expr(
                ExprKind::Literal(Constant {
                    ty: sig.output,
                    value: if info.kind == SyntheticMethodKind::EnumCaseName {
                        ConstantKind::String(case.name)
                    } else {
                        ConstantKind::Integer(case.discriminant)
                    },
                }),
                sig.output,
            );
            arm(
                &mut builder,
                PatternKind::Variant {
                    definition: definition.adt_def,
                    variant: *case,
                    subpatterns: Vec::new(),
                },
                value,
            );
        }
    } else {
        let TyKind::Adt(optional, _) = sig.output.kind() else {
            return None;
        };
        let optional_cases = gcx.get_enum_definition(optional.id).variants;
        let index_of = |item| {
            optional_cases
                .iter()
                .position(|case| Some(case.def_id) == gcx.std_item_def(item))
        };
        let some = index_of(StdItem::OptionalSomeVariant)?;
        let none = index_of(StdItem::OptionalNoneVariant)?;
        for (index, case) in definition.variants.iter().enumerate() {
            let value = variant(&mut builder, info.self_ty, index, None);
            let wrapped = variant(&mut builder, sig.output, some, Some(value));
            arm(
                &mut builder,
                PatternKind::Constant {
                    value: Constant {
                        ty: input.ty,
                        value: ConstantKind::Integer(
                            if info.kind == SyntheticMethodKind::EnumCaseAt {
                                index as u64
                            } else {
                                case.discriminant
                            },
                        ),
                    },
                },
                wrapped,
            );
        }
        let missing = variant(&mut builder, sig.output, none, None);
        arm(&mut builder, PatternKind::Wild, missing);
    }
    let value = if arms.is_empty() {
        // No receiver of an empty enum exists. Source matches require an arm.
        let unreachable = crate::mir::optimize::async_transform::find_std_function(
            gcx,
            "panic",
            "unreachable",
            span,
        )
        .ok()?;
        let callee =
            super::make_zst_callee(gcx, &mut builder, unreachable, GenericArguments::empty());
        builder.push_expr(
            ExprKind::Call {
                callee,
                args: vec![],
                is_async: false,
                argument_evaluation_order: None,
            },
            gcx.get_signature(unreachable).output,
        )
    } else {
        builder.push_expr(
            ExprKind::Match {
                scrutinee,
                arms,
                binding_condition: false,
            },
            sig.output,
        )
    };
    let body = builder.push_block(vec![], Some(value));
    Some(ThirFunction {
        id,
        span,
        params: vec![param],
        body: Some(body),
        constructor_self: None,
        is_async: false,
        blocks: builder.blocks,
        exprs: builder.exprs,
        stmts: builder.stmts,
        arms: builder.arms,
        match_reports: FxHashMap::default(),
    })
}
