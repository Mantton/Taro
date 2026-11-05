//! Checked casts are owned conversions. Test before transferring the operand so
//! a mismatch destroys its still-owned value through ordinary unwind-aware drop.
use crate::{
    mir::{
        AggregateKind, BasicBlockId, BlockAnd, BlockAndExtension, CastKind, Operand, Place, Rvalue,
        TerminatorKind, builder::MirBuilder,
    },
    sema::models::{Ty, TyKind},
    span::Span,
    thir::{ExprId, VariantIndex},
    unpack,
};
use index_vec::IndexVec;

impl<'ctx, 'thir> MirBuilder<'ctx, 'thir> {
    pub(super) fn checked_cast_rvalue(
        &mut self,
        mut block: BasicBlockId,
        value: ExprId,
        target: Ty<'ctx>,
        result_ty: Ty<'ctx>,
        span: Span,
    ) -> BlockAnd<Rvalue<'ctx>> {
        // Materialization applies ordinary Copy/move rules exactly once. The
        // inspection below does not create a second ownership obligation.
        let source = unpack!(block = self.as_temp(block, value));
        let source_place = Place::from_local(source);
        let result = self.new_temp_with_ty(result_ty, span);
        // The mismatch arm initializes none before destroying the source.
        // Arm result cleanup now so a source destructor panic also consumes
        // that initialized result on its unwind path.

        let test = self.new_temp_with_ty(self.gcx.types.bool, span);
        self.push_assign(
            block,
            Place::from_local(test),
            Rvalue::Cast {
                operand: Operand::Copy(source_place.clone()),
                ty: self.gcx.types.bool,
                kind: CastKind::ExistentialTypeIs { target },
            },
            span,
        );
        let success = self.new_block_with_note("checked cast match".into());
        let failure = self.new_block_with_note("checked cast mismatch".into());
        let join = self.new_block_with_note("checked cast join".into());
        self.terminate(
            block,
            span,
            TerminatorKind::SwitchInt {
                discr: Operand::Copy(Place::from_local(test)),
                targets: vec![(1, success)],
                otherwise: failure,
            },
        );
        self.push_assign(
            success,
            Place::from_local(result),
            Rvalue::Cast {
                operand: Operand::Copy(source_place.clone()),
                ty: result_ty,
                kind: CastKind::ExistentialTryCast { target },
            },
            span,
        );
        self.goto(success, join, span);

        let TyKind::Adt(optional, args) = result_ty.kind() else {
            panic!("checked cast result must be Optional");
        };
        let definition = self.gcx.get_enum_definition(optional.id);
        let none = definition
            .variants
            .iter()
            .position(|variant| self.gcx.symbol_eq(variant.name, "none"))
            .expect("Optional must declare none");
        self.push_assign(
            failure,
            Place::from_local(result),
            Rvalue::Aggregate {
                kind: AggregateKind::Adt {
                    def_id: optional.id,
                    variant_index: Some(VariantIndex::from_usize(none)),
                    generic_args: args,
                },
                fields: IndexVec::new(),
            },
            span,
        );
        let failure = { failure };
        self.goto(failure, join, span);
        // This compiler temporary forwards its one initialized result; copying
        // it would add an unnecessary hidden owning temporary for Copy results.
        join.and(Rvalue::Use(Operand::Copy(Place::from_local(result))))
    }
}
