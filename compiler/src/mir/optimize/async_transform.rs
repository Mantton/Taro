use crate::{
    compile::context::Gcx,
    error::CompileResult,
    hir::StdItem,
    mir::{
        AggregateKind, BasicBlockId, Body, LocalDecl, LocalKind, Operand, Place, Rvalue,
        Statement, StatementKind, TerminatorKind,
    },
    sema::models::{GenericArgument, TyKind},
    thir::VariantIndex,
};

use super::MirPass;

/// Async transform pass (Phase 5a: trivial case).
///
/// For async functions with **no** `Yield` terminators (i.e., they never
/// suspend), this pass rewrites the body so that:
///
///   1. A new return local with type `Poll[T]` is created.
///   2. Every `Return` terminator is preceded by wrapping the original
///      return value in `Poll.ready(value)` and assigning to the new local.
///   3. `body.return_local` is updated to the new local.
///
/// Functions that contain `Yield` terminators are left untouched for now
/// (full state machine transform is Phase 5b).
pub struct AsyncTransform;

impl<'ctx> MirPass<'ctx> for AsyncTransform {
    fn name(&self) -> &'static str {
        "AsyncTransform"
    }

    fn run(&mut self, gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
        if !body.is_async {
            return Ok(());
        }

        let has_yields = body.basic_blocks.iter().any(|bb| {
            bb.terminator
                .as_ref()
                .is_some_and(|t| matches!(t.kind, TerminatorKind::Yield { .. }))
        });

        if has_yields {
            // Full state machine transform — not yet implemented.
            return Ok(());
        }

        transform_trivially_ready(gcx, body);
        Ok(())
    }
}

/// Transform a trivially-ready async function (no suspension points).
///
/// Keeps the original return local (type `T`) for intermediate computations,
/// creates a new return local (type `Poll[T]`), and wraps the value at each
/// `Return` terminator.
fn transform_trivially_ready<'ctx>(gcx: Gcx<'ctx>, body: &mut Body<'ctx>) {
    // Look up the Poll enum definition.
    let Some(poll_def_id) = gcx.std_item_def(StdItem::Poll) else {
        return;
    };
    let enum_def = gcx.get_enum_definition(poll_def_id);

    // The original return type is T (what the user declared).
    let original_return_local = body.return_local;
    let original_return_ty = body.locals[original_return_local].ty;

    // Build Poll[T] type.
    let poll_generic_args = gcx
        .store
        .interners
        .intern_generic_args(vec![GenericArgument::Type(original_return_ty)]);
    let poll_ty = gcx
        .store
        .interners
        .intern_ty(TyKind::Adt(enum_def.adt_def, poll_generic_args));

    // Create a NEW return local with type Poll[T].
    let poll_return_local = body.locals.push(LocalDecl {
        ty: poll_ty,
        kind: LocalKind::Return,
        mutable: true,
        name: Some(gcx.intern_symbol("$async_ret")),
        span: body.locals[original_return_local].span,
    });
    body.escape_locals.push(false);

    // Demote the old return local to a temp (it still holds the T value).
    body.locals[original_return_local].kind = LocalKind::Temp;

    // Update body to use the new return local.
    body.return_local = poll_return_local;

    // Wrap each Return terminator: assign Poll.ready(old_ret) to new_ret.
    let ready_variant_index = VariantIndex::from_raw(0);

    for bb_idx in 0..body.basic_blocks.len() {
        let bb_id = BasicBlockId::from_raw(bb_idx as u32);
        let is_return = body.basic_blocks[bb_id]
            .terminator
            .as_ref()
            .is_some_and(|t| matches!(t.kind, TerminatorKind::Return));

        if !is_return {
            continue;
        }

        let span = body.basic_blocks[bb_id]
            .terminator
            .as_ref()
            .unwrap()
            .span;

        // Build Poll.ready(original_return_local) and assign to poll_return_local.
        let ready_fields = {
            let mut fields = index_vec::IndexVec::new();
            fields.push(Operand::Copy(Place::from_local(original_return_local)));
            fields
        };
        let wrap_stmt = Statement {
            kind: StatementKind::Assign(
                Place::from_local(poll_return_local),
                Rvalue::Aggregate {
                    kind: AggregateKind::Adt {
                        def_id: enum_def.adt_def.id,
                        variant_index: Some(ready_variant_index),
                        generic_args: poll_generic_args,
                    },
                    fields: ready_fields,
                },
            ),
            span,
        };

        body.basic_blocks[bb_id].statements.push(wrap_stmt);
    }

    // Mark the function as no longer async (transform complete).
    body.is_async = false;
}
