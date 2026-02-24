use super::{Emitter, LocalStorage};
use crate::{
    error::CompileResult,
    mir::{self, Operand, Place},
    sema::models::{GenericArguments, TyKind},
};
use inkwell::{AddressSpace, types::BasicType};

impl<'llvm, 'gcx> Emitter<'llvm, 'gcx> {
    pub(super) fn lower_intrinsic_array_read(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
    ) -> CompileResult<()> {
        let arr = args.first().expect("array intrinsic missing array");
        let idx = args.get(1).expect("array intrinsic missing index");

        let Some(arr_val) = self.eval_operand(body, locals, arr)? else {
            let _ = self.builder.build_unreachable().unwrap();
            return Ok(());
        };
        let Some(idx_val) = self.eval_operand(body, locals, idx)? else {
            let _ = self.builder.build_unreachable().unwrap();
            return Ok(());
        };

        // Get operand type and canonicalize it for codegen use.
        let arr_ty = self.mono_ty(self.operand_ty(body, arr));
        let arr_ty = match arr_ty.kind() {
            TyKind::Reference(inner, _) | TyKind::Pointer(inner, _) => inner,
            _ => arr_ty,
        };
        let arr_ty = self.normalize_post_mono_ty(arr_ty);
        let TyKind::Array { .. } = arr_ty.kind() else {
            self.gcx
                .dcx()
                .emit_error("array intrinsic used with non-array type".into(), None);
            return Ok(());
        };

        let arr_llvm = self
            .lower_ty(arr_ty)
            .expect("array type lowered")
            .into_array_type();
        let arr_ptr = arr_val.into_pointer_value();

        let mut idx_val = idx_val.into_int_value();
        if idx_val.get_type() != self.usize_ty {
            idx_val = self
                .builder
                .build_int_cast(idx_val, self.usize_ty, "idx_cast")
                .unwrap();
        }

        let zero = self.usize_ty.const_zero();
        let elem_ptr = unsafe {
            self.builder
                .build_gep(arr_llvm, arr_ptr, &[zero, idx_val], "array_elem_ptr")
                .unwrap()
        };

        self.store_place(destination, body, locals, elem_ptr.into())
    }

    pub(super) fn lower_intrinsic_array_write(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        args: &[Operand<'gcx>],
    ) -> CompileResult<()> {
        let arr = args.first().expect("array intrinsic missing array");
        let idx = args.get(1).expect("array intrinsic missing index");
        let value = args.get(2).expect("array intrinsic missing value");

        let Some(arr_val) = self.eval_operand(body, locals, arr)? else {
            let _ = self.builder.build_unreachable().unwrap();
            return Ok(());
        };
        let Some(idx_val) = self.eval_operand(body, locals, idx)? else {
            let _ = self.builder.build_unreachable().unwrap();
            return Ok(());
        };
        let Some(value_val) = self.eval_operand(body, locals, value)? else {
            let _ = self.builder.build_unreachable().unwrap();
            return Ok(());
        };

        // Get operand type and canonicalize it for codegen use.
        let arr_ty = self.mono_ty(self.operand_ty(body, arr));
        let arr_ty = match arr_ty.kind() {
            TyKind::Reference(inner, _) | TyKind::Pointer(inner, _) => inner,
            _ => arr_ty,
        };
        let arr_ty = self.normalize_post_mono_ty(arr_ty);
        let TyKind::Array { .. } = arr_ty.kind() else {
            self.gcx
                .dcx()
                .emit_error("array intrinsic used with non-array type".into(), None);
            return Ok(());
        };

        let arr_llvm = self
            .lower_ty(arr_ty)
            .expect("array type lowered")
            .into_array_type();
        let arr_ptr = arr_val.into_pointer_value();

        let mut idx_val = idx_val.into_int_value();
        if idx_val.get_type() != self.usize_ty {
            idx_val = self
                .builder
                .build_int_cast(idx_val, self.usize_ty, "idx_cast")
                .unwrap();
        }

        let zero = self.usize_ty.const_zero();
        let elem_ptr = unsafe {
            self.builder
                .build_gep(arr_llvm, arr_ptr, &[zero, idx_val], "array_elem_ptr")
                .unwrap()
        };

        let _ = self.builder.build_store(elem_ptr, value_val).unwrap();
        Ok(())
    }

    /// Intrinsic: __intrinsic_gc_desc[T]() -> *const GcDesc
    /// Returns a pointer to the GC descriptor for type T.
    pub(super) fn lower_intrinsic_gc_desc(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        call_args: GenericArguments<'gcx>,
        destination: &Place<'gcx>,
    ) -> CompileResult<()> {
        // Get the type from the generic arguments
        let Some(crate::sema::models::GenericArgument::Type(ty)) = call_args.get(0) else {
            self.gcx
                .dcx()
                .emit_error("gc_desc intrinsic requires a type argument".into(), None);
            return Ok(());
        };

        // Canonicalize with current generic context.
        let ty = self.mono_ty(*ty);

        // Get or create the GC descriptor for this type
        let desc_ptr = self.gc_desc_for(ty);

        self.store_place(destination, body, locals, desc_ptr.into())
    }

    /// Intrinsic: __intrinsic_list_write[T](buffer: GcPtr, index: usize, value: T)
    /// Writes a value to the buffer at the given element index.
    pub(super) fn lower_intrinsic_list_write(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        call_args: GenericArguments<'gcx>,
        args: &[Operand<'gcx>],
    ) -> CompileResult<()> {
        // Get the element type from generic arguments
        let Some(crate::sema::models::GenericArgument::Type(elem_ty)) = call_args.get(0) else {
            self.gcx
                .dcx()
                .emit_error("list_write intrinsic requires a type argument".into(), None);
            return Ok(());
        };

        let elem_ty = self.mono_ty(*elem_ty);

        let Some(llvm_elem_ty) = self.lower_ty(elem_ty) else {
            return Ok(()); // ZST - nothing to write
        };

        // Get arguments: buffer, index, value
        let buffer = args.get(0).expect("list_write missing buffer");
        let index = args.get(1).expect("list_write missing index");
        let value = args.get(2).expect("list_write missing value");

        let Some(buffer_val) = self.eval_operand(body, locals, buffer)? else {
            let _ = self.builder.build_unreachable().unwrap();
            return Ok(());
        };
        let Some(index_val) = self.eval_operand(body, locals, index)? else {
            let _ = self.builder.build_unreachable().unwrap();
            return Ok(());
        };
        let Some(value_val) = self.eval_operand(body, locals, value)? else {
            return Ok(());
        };

        let mut index_val = index_val.into_int_value();
        if index_val.get_type() != self.usize_ty {
            index_val = self
                .builder
                .build_int_cast(index_val, self.usize_ty, "idx_cast")
                .unwrap();
        }

        let buffer_ptr = buffer_val.into_pointer_value();
        let elem_ptr = self
            .builder
            .build_bit_cast(
                buffer_ptr,
                self.context.ptr_type(AddressSpace::default()),
                "list_buf_cast",
            )
            .unwrap()
            .into_pointer_value();
        let elem_ptr = unsafe {
            self.builder
                .build_gep(llvm_elem_ty, elem_ptr, &[index_val], "list_elem_ptr")
                .unwrap()
        };

        let _ = self.builder.build_store(elem_ptr, value_val).unwrap();

        Ok(())
    }

    /// Intrinsic: __intrinsic_list_read_unchecked[T](buffer: GcPtr, index: usize) -> &T
    /// Intrinsic: __intrinsic_list_read_mut_unchecked[T](buffer: GcPtr, index: usize) -> &mut T
    /// Returns a pointer to the element at the given index.
    pub(super) fn lower_intrinsic_list_read_ref(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        call_args: GenericArguments<'gcx>,
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
    ) -> CompileResult<()> {
        let Some(crate::sema::models::GenericArgument::Type(elem_ty)) = call_args.get(0) else {
            self.gcx
                .dcx()
                .emit_error("list_read intrinsic requires a type argument".into(), None);
            return Ok(());
        };

        let elem_ty = self.mono_ty(*elem_ty);

        let Some(llvm_elem_ty) = self.lower_ty(elem_ty) else {
            return Ok(());
        };

        let buffer = args.get(0).expect("list_read missing buffer");
        let index = args.get(1).expect("list_read missing index");

        let Some(buffer_val) = self.eval_operand(body, locals, buffer)? else {
            let _ = self.builder.build_unreachable().unwrap();
            return Ok(());
        };
        let Some(index_val) = self.eval_operand(body, locals, index)? else {
            let _ = self.builder.build_unreachable().unwrap();
            return Ok(());
        };

        let mut index_val = index_val.into_int_value();
        if index_val.get_type() != self.usize_ty {
            index_val = self
                .builder
                .build_int_cast(index_val, self.usize_ty, "idx_cast")
                .unwrap();
        }

        let buffer_ptr = buffer_val.into_pointer_value();
        let elem_ptr = self
            .builder
            .build_bit_cast(
                buffer_ptr,
                self.context.ptr_type(AddressSpace::default()),
                "list_buf_cast",
            )
            .unwrap()
            .into_pointer_value();
        let elem_ptr = unsafe {
            self.builder
                .build_gep(llvm_elem_ty, elem_ptr, &[index_val], "list_elem_ptr")
                .unwrap()
        };

        self.store_place(destination, body, locals, elem_ptr.into())
    }

    /// Intrinsic: __intrinsic_ref_to_ptr[T](&T) -> *const T
    /// Intrinsic: __intrinsic_mut_ref_to_ptr[T](&mut T) -> *mut T
    /// Reinterprets a reference value as a raw pointer.
    pub(super) fn lower_intrinsic_ref_to_ptr(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
    ) -> CompileResult<()> {
        let value = args.first().expect("ref_to_ptr missing value");
        let Some(val) = self.eval_operand(body, locals, value)? else {
            let _ = self.builder.build_unreachable().unwrap();
            return Ok(());
        };

        self.store_place(destination, body, locals, val)
    }

    /// Intrinsic: __intrinsic_ptr_add[T](ptr: *T, count: usize) -> *T
    pub(super) fn lower_intrinsic_ptr_add(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        call_args: GenericArguments<'gcx>,
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
    ) -> CompileResult<()> {
        self.lower_intrinsic_ptr_op(body, locals, call_args, args, destination, false)
    }

    /// Intrinsic: __intrinsic_ptr_sub[T](ptr: *T, count: usize) -> *T
    pub(super) fn lower_intrinsic_ptr_sub(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        call_args: GenericArguments<'gcx>,
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
    ) -> CompileResult<()> {
        self.lower_intrinsic_ptr_op(body, locals, call_args, args, destination, true)
    }

    /// Intrinsic: __intrinsic_ptr_offset[T](ptr: *T, count: isize) -> *T
    pub(super) fn lower_intrinsic_ptr_offset(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        call_args: GenericArguments<'gcx>,
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
    ) -> CompileResult<()> {
        // Offset is same as Add but with signed/isize count.
        // For now sharing logic if possible or duplicating.
        // The underlying GEP works same for signed offset.
        self.lower_intrinsic_ptr_op(body, locals, call_args, args, destination, false)
    }

    fn lower_intrinsic_ptr_op(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        call_args: GenericArguments<'gcx>,
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
        negate: bool,
    ) -> CompileResult<()> {
        let Some(crate::sema::models::GenericArgument::Type(elem_ty)) = call_args.get(0) else {
            // Error handling ignored for brevity/ICE
            return Ok(());
        };
        let elem_ty = self.substitute_ty_current(*elem_ty);
        let Some(llvm_elem_ty) = self.lower_ty(elem_ty) else {
            return Ok(());
        };

        let ptr_op = args.get(0).unwrap();
        let count_op = args.get(1).unwrap();

        let ptr_val = self
            .eval_operand(body, locals, ptr_op)?
            .unwrap()
            .into_pointer_value();
        let mut count_val = self
            .eval_operand(body, locals, count_op)?
            .unwrap()
            .into_int_value();

        if negate {
            count_val = self.builder.build_int_neg(count_val, "neg_count").unwrap();
        }

        let new_ptr = unsafe {
            self.builder
                .build_gep(llvm_elem_ty, ptr_val, &[count_val], "ptr_op")
                .unwrap()
        };

        self.store_place(destination, body, locals, new_ptr.into())
    }

    pub(super) fn lower_intrinsic_ptr_byte_add(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        call_args: GenericArguments<'gcx>,
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
    ) -> CompileResult<()> {
        self.lower_intrinsic_ptr_byte_op(body, locals, call_args, args, destination, false)
    }

    pub(super) fn lower_intrinsic_ptr_byte_sub(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        call_args: GenericArguments<'gcx>,
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
    ) -> CompileResult<()> {
        self.lower_intrinsic_ptr_byte_op(body, locals, call_args, args, destination, true)
    }

    fn lower_intrinsic_ptr_byte_op(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        _: GenericArguments<'gcx>,
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
        negate: bool,
    ) -> CompileResult<()> {
        let ptr_op = args.get(0).unwrap();
        let count_op = args.get(1).unwrap();

        let ptr_val = self
            .eval_operand(body, locals, ptr_op)?
            .unwrap()
            .into_pointer_value();
        let mut count_val = self
            .eval_operand(body, locals, count_op)?
            .unwrap()
            .into_int_value();

        if negate {
            count_val = self.builder.build_int_neg(count_val, "neg_count").unwrap();
        }

        let i8_ty = self.context.i8_type();
        let i8_ptr_ty = self.context.ptr_type(AddressSpace::default());

        let raw_ptr = self
            .builder
            .build_bit_cast(ptr_val, i8_ptr_ty, "raw_ptr")
            .unwrap()
            .into_pointer_value();
        let new_raw_ptr = unsafe {
            self.builder
                .build_gep(i8_ty, raw_ptr, &[count_val], "byte_op")
                .unwrap()
        };

        // Cast back to original pointer type
        let new_ptr = self
            .builder
            .build_bit_cast(new_raw_ptr, ptr_val.get_type(), "new_ptr")
            .unwrap();

        self.store_place(destination, body, locals, new_ptr.into())
    }

    pub(super) fn lower_intrinsic_ptr_read(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        call_args: GenericArguments<'gcx>,
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
    ) -> CompileResult<()> {
        let Some(crate::sema::models::GenericArgument::Type(elem_ty)) = call_args.get(0) else {
            return Ok(());
        };
        let elem_ty = self.substitute_ty_current(*elem_ty);
        let Some(llvm_elem_ty) = self.lower_ty(elem_ty) else {
            return Ok(());
        };

        let ptr_op = args.get(0).unwrap();
        let ptr_val = self
            .eval_operand(body, locals, ptr_op)?
            .unwrap()
            .into_pointer_value();

        let val = self
            .builder
            .build_load(llvm_elem_ty, ptr_val, "read_val")
            .unwrap();
        self.store_place(destination, body, locals, val.into())
    }

    pub(super) fn lower_intrinsic_ptr_write(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        _: GenericArguments<'gcx>,
        args: &[Operand<'gcx>],
        _destination: &Place<'gcx>, // returns void
    ) -> CompileResult<()> {
        let ptr_op = args.get(0).unwrap();
        let val_op = args.get(1).unwrap();

        let ptr_val = self
            .eval_operand(body, locals, ptr_op)?
            .unwrap()
            .into_pointer_value();
        let val_val = self.eval_operand(body, locals, val_op)?.unwrap();

        let _ = self.builder.build_store(ptr_val, val_val).unwrap();
        Ok(())
    }

    pub(super) fn lower_intrinsic_memcpy(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        _call_args: GenericArguments<'gcx>,
        args: &[Operand<'gcx>],
    ) -> CompileResult<()> {
        // args: src, dst, count (bytes)
        let src = self
            .eval_operand(body, locals, args.get(0).unwrap())?
            .unwrap()
            .into_pointer_value();
        let dst = self
            .eval_operand(body, locals, args.get(1).unwrap())?
            .unwrap()
            .into_pointer_value();
        let count = self
            .eval_operand(body, locals, args.get(2).unwrap())?
            .unwrap()
            .into_int_value();

        // alignments? assuming 1 for now or reading from type if available?
        // intrinsics usually just take pointers.
        let _ = self.builder.build_memcpy(dst, 1, src, 1, count).unwrap();
        Ok(())
    }

    pub(super) fn lower_intrinsic_memmove(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        _call_args: GenericArguments<'gcx>,
        args: &[Operand<'gcx>],
    ) -> CompileResult<()> {
        let src = self
            .eval_operand(body, locals, args.get(0).unwrap())?
            .unwrap()
            .into_pointer_value();
        let dst = self
            .eval_operand(body, locals, args.get(1).unwrap())?
            .unwrap()
            .into_pointer_value();
        let count = self
            .eval_operand(body, locals, args.get(2).unwrap())?
            .unwrap()
            .into_int_value();

        let _ = self.builder.build_memmove(dst, 1, src, 1, count).unwrap();
        Ok(())
    }

    pub(super) fn lower_intrinsic_memset(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        _call_args: GenericArguments<'gcx>,
        args: &[Operand<'gcx>],
    ) -> CompileResult<()> {
        // args: dst, val (u8), count
        let dst = self
            .eval_operand(body, locals, args.get(0).unwrap())?
            .unwrap()
            .into_pointer_value();
        let val = self
            .eval_operand(body, locals, args.get(1).unwrap())?
            .unwrap()
            .into_int_value();
        let count = self
            .eval_operand(body, locals, args.get(2).unwrap())?
            .unwrap()
            .into_int_value();

        let _ = self.builder.build_memset(dst, 1, val, count).unwrap();
        Ok(())
    }

    pub(super) fn lower_intrinsic_size_of(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        call_args: GenericArguments<'gcx>,
        _args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
    ) -> CompileResult<()> {
        let Some(crate::sema::models::GenericArgument::Type(elem_ty)) = call_args.get(0) else {
            return Ok(());
        };
        let elem_ty = self.substitute_ty_current(*elem_ty);
        let Some(llvm_elem_ty) = self.lower_ty(elem_ty) else {
            return Ok(());
        };

        let size = llvm_elem_ty.size_of().unwrap();
        // size_of returns an IntValue (i64 usually on 64bit). Cast to usize (which is pointer sized int).
        let size = self
            .builder
            .build_int_cast(size, self.usize_ty, "size_of_cast")
            .unwrap();

        self.store_place(destination, body, locals, size.into())
    }

    pub(super) fn lower_intrinsic_align_of(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        call_args: GenericArguments<'gcx>,
        _args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
    ) -> CompileResult<()> {
        let Some(crate::sema::models::GenericArgument::Type(elem_ty)) = call_args.get(0) else {
            return Ok(());
        };
        let elem_ty = self.substitute_ty_current(*elem_ty);
        let Some(llvm_elem_ty) = self.lower_ty(elem_ty) else {
            return Ok(());
        };

        let align = self.target_data.get_abi_alignment(&llvm_elem_ty);
        let align = self.usize_ty.const_int(align as u64, false);

        self.store_place(destination, body, locals, align.into())
    }
}
