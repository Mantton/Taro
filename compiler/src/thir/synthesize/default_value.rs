//! Body for a derived `Default.default` on a struct.
//!
//! Fields are initialized in declaration order: a field's declared default
//! expression when it has one, otherwise its type's `Default.default()`.
//! Like derived `Clone` and `Decodable`, the value is built directly from its
//! fields, so initializers do not run.

use super::{ThirBuilder, make_zst_callee, synthetic_span};
use crate::{
    compile::context::GlobalContext,
    hir::DefinitionID,
    sema::{
        models::{GenericArgument, GenericArguments, Ty, TyKind},
        resolve::models::TypeHead,
        tycheck::{
            derive::SyntheticMethodInfo, utils::instantiate::instantiate_signature_with_args,
        },
    },
    thir::{AdtExpression, ExprKind, FieldExpression, FieldIndex, ThirFunction},
};
use rustc_hash::FxHashMap;

pub(super) fn synthesize<'ctx>(
    gcx: GlobalContext<'ctx>,
    type_head: TypeHead,
    info: SyntheticMethodInfo<'ctx>,
    syn_id: DefinitionID,
) -> Option<ThirFunction<'ctx>> {
    let TypeHead::Nominal(owner) = type_head else {
        return None;
    };
    let definition = gcx.try_get_struct_definition(owner)?;
    let arguments = match info.self_ty.kind() {
        TyKind::Adt(_, arguments) => arguments,
        _ => GenericArguments::empty(),
    };
    let span = synthetic_span();
    let mut builder = ThirBuilder::new(gcx, span);
    let mut fields = Vec::new();
    for (index, field) in definition.fields.iter().enumerate() {
        let expression = match field.default_provider {
            Some(provider) => {
                let signature =
                    instantiate_signature_with_args(gcx, gcx.get_signature(provider), arguments);
                let callee = builder.push_expr(
                    ExprKind::Zst {
                        id: provider,
                        generic_args: Some(arguments),
                    },
                    Ty::from_labeled_signature(gcx, &signature),
                );
                call(&mut builder, callee, field.ty)
            }
            None => {
                let arguments = gcx
                    .store
                    .interners
                    .intern_generic_args(vec![GenericArgument::Type(field.ty)]);
                let callee = make_zst_callee(gcx, &mut builder, info.method_id, arguments);
                call(&mut builder, callee, field.ty)
            }
        };
        fields.push(FieldExpression {
            index: FieldIndex::from_usize(index),
            expression,
        });
    }
    let value = builder.push_expr(
        ExprKind::Adt(AdtExpression {
            base: None,
            definition: definition.adt_def,
            variant_index: None,
            generic_args: arguments,
            fields,
        }),
        info.self_ty,
    );
    let body = builder.push_block(vec![], Some(value));
    Some(ThirFunction {
        id: syn_id,
        body: Some(body),
        constructor_self: None,
        span,
        params: vec![],
        stmts: builder.stmts,
        blocks: builder.blocks,
        exprs: builder.exprs,
        arms: builder.arms,
        match_reports: FxHashMap::default(),
        is_async: false,
    })
}

fn call<'ctx>(
    builder: &mut ThirBuilder<'ctx>,
    callee: crate::thir::ExprId,
    ty: Ty<'ctx>,
) -> crate::thir::ExprId {
    builder.push_expr(
        ExprKind::Call {
            callee,
            args: vec![],
            is_async: false,
            argument_evaluation_order: None,
        },
        ty,
    )
}
