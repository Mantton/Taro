//! Sequentially consistent, naturally aligned scalar atomic intrinsics.
use super::*;
use inkwell::{AtomicOrdering, AtomicRMWBinOp};

impl<'llvm, 'gcx> Emitter<'llvm, 'gcx> {
    pub(super) fn lower_intrinsic_atomic(
        &mut self,
        name: &str,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        call_args: GenericArguments<'gcx>,
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
    ) -> CompileResult<()> {
        let ty = self.substitute_ty_current(call_args[0].ty().unwrap());
        // Reject invalid monomorphizations before calling LLVM's scalar-only
        // atomic builders. Bool uses a uint8 slot in the standard library.
        let Some(llvm_ty) = self.lower_ty(ty) else {
            self.gcx.dcx().emit_error(
                "atomic storage must be an integer or raw pointer".into(),
                self.current_span,
            );
            return Err(crate::error::ReportedError);
        };
        if !matches!(
            ty.kind(),
            TyKind::Int(_) | TyKind::UInt(_) | TyKind::Pointer(..)
        ) {
            self.gcx.dcx().emit_error(
                "atomic storage must be an integer or raw pointer".into(),
                self.current_span,
            );
            return Err(crate::error::ReportedError);
        }
        let slot = self
            .eval_operand(body, locals, &args[0])?
            .unwrap()
            .into_pointer_value();
        let mut values = Vec::new();
        for arg in &args[1..] {
            values.push(self.eval_operand(body, locals, arg)?.unwrap());
        }
        let order = AtomicOrdering::SequentiallyConsistent;
        let align = self.target_data.get_abi_alignment(&llvm_ty);
        let result: Option<BasicValueEnum<'llvm>> = match name {
            "__intrinsic_atomic_load" => {
                let result = self
                    .builder
                    .build_load(llvm_ty, slot, "atomic.load")
                    .unwrap();
                let instruction = result.as_instruction_value().unwrap();
                instruction.set_atomic_ordering(order).unwrap();
                instruction.set_alignment(align).unwrap();
                Some(result)
            }
            "__intrinsic_atomic_store" => {
                let instruction = self.builder.build_store(slot, values[0]).unwrap();
                instruction.set_atomic_ordering(order).unwrap();
                instruction.set_alignment(align).unwrap();
                None
            }
            "__intrinsic_atomic_compare_exchange" => {
                let pair = self
                    .builder
                    .build_cmpxchg(slot, values[0], values[1], order, order)
                    .unwrap();
                Some(
                    self.builder
                        .build_extract_value(pair, 1, "atomic.exchanged")
                        .unwrap(),
                )
            }
            "__intrinsic_atomic_swap" | "__intrinsic_atomic_add" => {
                let add = name == "__intrinsic_atomic_add";
                let pointer = values[0].is_pointer_value();
                if add && pointer {
                    self.gcx.dcx().emit_error(
                        "atomic add requires integer storage".into(),
                        self.current_span,
                    );
                    return Err(crate::error::ReportedError);
                }
                // LLVM's xchg supports pointers; Inkwell's RMW builder accepts
                // integers only. Nonmoving GC addresses round-trip through a
                // native word here, with no intervening safepoint.
                let value = if pointer {
                    self.builder
                        .build_ptr_to_int(
                            values[0].into_pointer_value(),
                            self.usize_ty,
                            "atomic.address",
                        )
                        .unwrap()
                } else {
                    values[0].into_int_value()
                };
                let old = self
                    .builder
                    .build_atomicrmw(
                        if add {
                            AtomicRMWBinOp::Add
                        } else {
                            AtomicRMWBinOp::Xchg
                        },
                        slot,
                        value,
                        order,
                    )
                    .unwrap();
                Some(if pointer {
                    self.builder
                        .build_int_to_ptr(old, llvm_ty.into_pointer_type(), "atomic.previous")
                        .unwrap()
                        .into()
                } else if add {
                    // add returns the new value, wrapping at the storage width.
                    self.builder
                        .build_int_add(old, value, "atomic.new")
                        .unwrap()
                        .into()
                } else {
                    old.into()
                })
            }
            _ => unreachable!("unknown scalar atomic intrinsic"),
        };
        if let Some(result) = result {
            self.store_place(destination, body, locals, result)?;
        }
        Ok(())
    }
}
