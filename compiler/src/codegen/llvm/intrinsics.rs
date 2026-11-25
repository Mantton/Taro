use super::{Emitter, LocalStorage};
use crate::{
    error::CompileResult,
    mir::{self, Operand, Place},
    sema::models::{GenericArguments, TyKind},
};
use inkwell::{
    AddressSpace,
    types::{BasicType, BasicTypeEnum},
};

impl<'llvm, 'gcx> Emitter<'llvm, 'gcx> {
    fn lower_intrinsic_type_arg(
        &self,
        call_args: GenericArguments<'gcx>,
        intrinsic_name: &str,
    ) -> Option<BasicTypeEnum<'llvm>> {
        let Some(crate::sema::models::GenericArgument::Type(elem_ty)) = call_args.get(0) else {
            self.gcx.dcx().emit_error(
                format!("{intrinsic_name} intrinsic requires a type argument"),
                None,
            );
            return None;
        };
        let elem_ty = self.substitute_ty_current(*elem_ty);
        self.lower_ty(elem_ty)
    }

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
            TyKind::Reference(inner) | TyKind::Pointer(inner, _) => inner,
            _ => arr_ty,
        };
        let arr_ty = self.normalize_post_mono_ty(arr_ty);
        let TyKind::Array { .. } = arr_ty.kind() else {
            self.gcx
                .dcx()
                .emit_error("array intrinsic used with non-array type".into(), None);
            return Ok(());
        };

        let arr_llvm = self.lower_ty(arr_ty).map(|ty| ty.into_array_type());
        let arr_ptr = self.reference_data(arr_val);

        let mut idx_val = idx_val.into_int_value();
        if idx_val.get_type() != self.usize_ty {
            idx_val = self
                .builder
                .build_int_cast(idx_val, self.usize_ty, "idx_cast")
                .unwrap();
        }

        let zero = self.usize_ty.const_zero();
        let elem_ptr = if let Some(arr_llvm) = arr_llvm {
            unsafe {
                self.builder
                    .build_gep(arr_llvm, arr_ptr, &[zero, idx_val], "array_elem_ptr")
                    .unwrap()
            }
        } else {
            // Unit elements have no bytes, but their references still carry
            // access controllers and must initialize/transfer both words.
            arr_ptr
        };

        self.store_intrinsic_reference(body, locals, destination, elem_ptr)
    }

    /// Reviewed unsafe projection used by guard-bearing views. The caller
    /// proves that data remains valid under the source's protection; no raw
    /// pointer provenance or bounds proof is inferred by this operation.
    pub(super) fn lower_intrinsic_borrow_projection(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
    ) -> CompileResult<()> {
        if self.eval_operand(body, locals, &args[0])?.is_none() {
            self.builder.build_unreachable().unwrap();
            return Ok(());
        }
        let Some(data) = self.eval_operand(body, locals, &args[1])? else {
            self.builder.build_unreachable().unwrap();
            return Ok(());
        };
        self.store_intrinsic_reference(body, locals, destination, data.into_pointer_value())
    }

    /// Derive a field address from the compiler's constant logical path. Never
    /// accept a raw address or load field data before acquiring permission.
    pub(super) fn lower_intrinsic_class_field(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
        name: &str,
        unwind_bb: Option<inkwell::basic_block::BasicBlock<'llvm>>,
    ) -> CompileResult<()> {
        use crate::{
            mir::ConstantKind, sema::tycheck::utils::instantiate::instantiate_ty_with_args,
        };
        let span = self
            .current_span
            .unwrap_or(body.locals[destination.local].span);
        let fail = |message: &str| {
            self.gcx.dcx().emit_error(message.into(), Some(span));
            crate::error::ReportedError
        };
        let expected_args = match name {
            "__intrinsic_class_field_write" => 3,
            "__intrinsic_class_field_modify" => 4,
            _ => 2,
        };
        if args.len() != expected_args {
            return Err(fail("class field intrinsic has an invalid argument count"));
        }
        let Operand::Constant(mir::Constant {
            value: ConstantKind::String(path),
            ..
        }) = &args[1]
        else {
            return Err(fail(
                "class field access requires a constant compiler field path",
            ));
        };
        let path: Vec<u32> = path
            .as_str()
            .split('.')
            .map(str::parse)
            .collect::<Result<_, _>>()
            .map_err(|_| fail("invalid class field path"))?;
        let TyKind::Reference(class) = self.mono_ty(self.operand_ty(body, &args[0])).kind() else {
            return Err(fail(
                "class field access requires a shared class-handle slot",
            ));
        };
        if !matches!(class.kind(), TyKind::Adt(..)) {
            return Err(fail("class field access requires a nominal class"));
        }
        let mut ty = self
            .gc_class_payload_ty(class)
            .ok_or_else(|| fail("GC class payload metadata is missing"))?;
        // Validate the entire layout before emitting any access.
        let mut layouts = vec![];
        // Payload field 0 is the class header, so source field paths start at 1.
        let mut storage_path = if let Some(first) = path.first() {
            vec![
                first
                    .checked_add(1)
                    .ok_or_else(|| fail("invalid GC class field"))?,
            ]
        } else {
            vec![]
        };
        storage_path.extend_from_slice(&path[1.min(path.len())..]);
        for index in &storage_path {
            let field = match ty.kind() {
                TyKind::Adt(definition, arguments) if !self.gcx.is_class_type(ty) => self
                    .gcx
                    .get_struct_definition(definition.id)
                    .fields
                    .get(*index as usize)
                    .map(|field| instantiate_ty_with_args(self.gcx, field.ty, arguments)),
                TyKind::Tuple(fields) => fields.get(*index as usize).copied(),
                _ => None,
            }
            .ok_or_else(|| fail("class field path crosses invalid or reference storage"))?;
            // Access paths use logical field identities for overlap checks;
            // LLVM GEPs must use the layout's reordered physical indices.
            let physical = match ty.kind() {
                TyKind::Adt(definition, arguments) => {
                    let stored = self.gcx.get_struct_definition(definition.id);
                    let layout = super::struct_field_layout(
                        self.context,
                        self.gcx,
                        &self.target_data,
                        definition.id,
                        arguments,
                        GenericArguments::empty(),
                        stored.repr,
                    );
                    *layout
                        .logical_to_physical
                        .get(*index as usize)
                        .ok_or_else(|| fail("class field has no physical layout index"))?
                }
                _ => *index,
            };
            layouts.push((
                self.lower_ty(ty)
                    .ok_or_else(|| fail("class payload has no layout"))?
                    .into_struct_type(),
                physical,
            ));
            ty = self.mono_ty(field);
        }
        let result_ty = self.mono_ty(body.place_ty(self.gcx, destination));
        let consistent = match name {
            "__intrinsic_class_field_read" => result_ty == ty,
            "__intrinsic_class_field_write" => self.mono_ty(self.operand_ty(body, &args[2])) == ty,
            "__intrinsic_class_field_modify" => {
                self.mono_ty(self.operand_ty(body, &args[3])) == ty
                    && matches!(
                        ty.kind(),
                        TyKind::Int(_) | TyKind::UInt(_) | TyKind::Float(_) | TyKind::Bool
                    )
            }
            _ => matches!(result_ty.kind(), TyKind::Reference(field) if field == ty),
        };
        if path.is_empty() || !consistent {
            return Err(fail("class field result disagrees with stored field type"));
        }
        let Some(slot) = self.eval_operand(body, locals, &args[0])? else {
            self.builder.build_unreachable().unwrap();
            return Ok(());
        };
        let class_layout = self.lower_ty(class).expect("class layout");
        let handle = self
            .build_shared_load(class_layout, self.reference_data(slot), "class_handle")
            .into_struct_value();
        let object = self
            .builder
            .build_extract_value(handle, 0, "class_object")
            .unwrap()
            .into_pointer_value();
        let mut data = object;
        for (layout, index) in &layouts {
            data = self
                .builder
                .build_struct_gep(*layout, data, *index, "class_field")
                .unwrap();
        }
        match name {
            "__intrinsic_class_field_modify" => {
                self.lower_class_field_modify(body, locals, args, data, ty, span, unwind_bb)
            }
            // A zero-sized stored value has no operand and no bytes to write.
            "__intrinsic_class_field_write" => {
                if let Some(value) = self.eval_operand(body, locals, &args[2])? {
                    self.build_shared_store(data, value);
                }
                Ok(())
            }
            "__intrinsic_class_field_read" => match self.lower_ty(ty) {
                Some(layout) => {
                    let loaded = self.build_shared_load(layout, data, "class_field_value");
                    self.store_place(destination, body, locals, loaded)
                }
                None => Ok(()),
            },
            _ => self.store_place(destination, body, locals, self.lexical_reference(data)),
        }
    }

    /// Intercept compound field assignment before generic intrinsic dispatch:
    /// its checked arithmetic needs the call's unwind edge.
    pub(super) fn try_lower_class_field_modify(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        func: &Operand<'gcx>,
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
        normal_bb: inkwell::basic_block::BasicBlock<'llvm>,
        unwind_bb: Option<inkwell::basic_block::BasicBlock<'llvm>>,
    ) -> CompileResult<bool> {
        let Operand::Constant(mir::Constant {
            value: mir::ConstantKind::Function(id, ..),
            ..
        }) = func
        else {
            return Ok(false);
        };
        if self.gcx.get_signature(*id).abi != Some(crate::hir::Abi::Intrinsic)
            || self.gcx.definition_ident(*id).symbol.as_str() != "__intrinsic_class_field_modify"
        {
            return Ok(false);
        }
        self.lower_intrinsic_class_field(
            body,
            locals,
            args,
            destination,
            "__intrinsic_class_field_modify",
            unwind_bb,
        )?;
        self.builder.build_unconditional_branch(normal_bb).unwrap();
        Ok(true)
    }

    /// Compound assignment to a primitive class field as one exclusive
    /// instantaneous access. Divisor and shift-amount checks depend only on
    /// the RHS and panic before locking. Value overflow stores the old value
    /// back, ends the access, and only then panics, so no unwind runs while
    /// the object's access state is locked.
    #[allow(clippy::too_many_arguments)]
    fn lower_class_field_modify(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        args: &[Operand<'gcx>],
        data: inkwell::values::PointerValue<'llvm>,
        ty: crate::sema::models::Ty<'gcx>,
        span: crate::span::Span,
        unwind_bb: Option<inkwell::basic_block::BasicBlock<'llvm>>,
    ) -> CompileResult<()> {
        use inkwell::{IntPredicate, intrinsics::Intrinsic, types::BasicType};
        use mir::BinaryOperator as Op;
        let Operand::Constant(mir::Constant {
            value: mir::ConstantKind::String(spelling),
            ..
        }) = &args[2]
        else {
            self.gcx.dcx().emit_error(
                "compound class field access requires a constant operator".into(),
                Some(span),
            );
            return Err(crate::error::ReportedError);
        };
        let (checked, name) = match spelling.as_str().strip_prefix("checked.") {
            Some(name) => (true, name),
            None => (false, spelling.as_str()),
        };
        let Some(op) = Op::from_compound_name(name) else {
            self.gcx
                .dcx()
                .emit_error("unknown compound class field operator".into(), Some(span));
            return Err(crate::error::ReportedError);
        };
        let checked = checked && matches!(ty.kind(), TyKind::Int(_) | TyKind::UInt(_));
        let signed = super::is_signed(ty);
        let rhs = self
            .eval_operand(body, locals, &args[3])?
            .expect("primitive compound operand has a value");
        let layout = self.lower_ty(ty).expect("primitive field layout");

        // RHS-only failures (divisor, shift amount) panic before the field is read.
        let guard = |emitter: &mut Self, failed, message: &str| -> CompileResult<()> {
            let panic_bb = emitter.append_block_to_current_fn("class_field_modify_panic");
            let cont_bb = emitter.append_block_to_current_fn("class_field_modify_cont");
            emitter
                .builder
                .build_conditional_branch(failed, panic_bb, cont_bb)
                .unwrap();
            emitter.builder.position_at_end(panic_bb);
            emitter.emit_arith_panic(message, span, unwind_bb)?;
            emitter.builder.position_at_end(cont_bb);
            Ok(())
        };
        if checked {
            let rhs = rhs.into_int_value();
            let bits = rhs.get_type().get_bit_width() as u64;
            match op {
                Op::Div | Op::Rem => {
                    let zero = self
                        .builder
                        .build_int_compare(
                            IntPredicate::EQ,
                            rhs,
                            rhs.get_type().const_zero(),
                            "field_div_zero",
                        )
                        .unwrap();
                    let message = if matches!(op, Op::Div) {
                        "attempt to divide by zero"
                    } else {
                        "attempt to calculate the remainder with a divisor of zero"
                    };
                    guard(self, zero, message)?;
                }
                Op::BitShl | Op::BitShr => {
                    let too_big = self
                        .builder
                        .build_int_compare(
                            IntPredicate::UGE,
                            rhs,
                            rhs.get_type().const_int(bits, false),
                            "field_shift_ovf",
                        )
                        .unwrap();
                    let direction = if matches!(op, Op::BitShl) {
                        "left"
                    } else {
                        "right"
                    };
                    guard(
                        self,
                        too_big,
                        &format!("attempt to shift {direction} with overflow"),
                    )?;
                }
                _ => {}
            }
        }
        let old = self
            .builder
            .build_load(layout, data, "class_field_old")
            .unwrap();
        let (value, overflow) = match op {
            Op::Add | Op::Sub | Op::Mul if checked => {
                let name = match op {
                    Op::Add => "add",
                    Op::Sub => "sub",
                    _ => "mul",
                };
                let intrinsic_name = format!(
                    "llvm.{}{name}.with.overflow",
                    if signed { "s" } else { "u" }
                );
                let intrinsic = Intrinsic::find(&intrinsic_name)
                    .unwrap_or_else(|| panic!("ICE: missing LLVM intrinsic {intrinsic_name}"));
                let declaration = intrinsic
                    .get_declaration(&self.module, &[layout.as_basic_type_enum()])
                    .unwrap_or_else(|| {
                        panic!("ICE: cannot declare LLVM intrinsic {intrinsic_name}")
                    });
                let pair = self
                    .builder
                    .build_call(declaration, &[old.into(), rhs.into()], name)
                    .unwrap()
                    .try_as_basic_value()
                    .basic()
                    .expect("overflow intrinsic returns {value, flag}")
                    .into_struct_value();
                let verb = match op {
                    Op::Add => "add",
                    Op::Sub => "subtract",
                    _ => "multiply",
                };
                (
                    self.builder
                        .build_extract_value(pair, 0, "field_arith")
                        .unwrap(),
                    Some((
                        self.builder
                            .build_extract_value(pair, 1, "field_arith_ovf")
                            .unwrap()
                            .into_int_value(),
                        format!("attempt to {verb} with overflow"),
                    )),
                )
            }
            Op::Div | Op::Rem if checked && signed => {
                // MIN / -1 overflows; divide by 1 instead and keep the old value.
                let (lhs, divisor) = (old.into_int_value(), rhs.into_int_value());
                let int_ty = lhs.get_type();
                let bits = int_ty.get_bit_width() as u64;
                let is_min = self
                    .builder
                    .build_int_compare(
                        IntPredicate::EQ,
                        lhs,
                        int_ty.const_int(1u64 << (bits - 1), false),
                        "field_div_lhs_min",
                    )
                    .unwrap();
                let is_negative_one = self
                    .builder
                    .build_int_compare(
                        IntPredicate::EQ,
                        divisor,
                        int_ty.const_all_ones(),
                        "field_div_rhs_m1",
                    )
                    .unwrap();
                let overflowed = self
                    .builder
                    .build_and(is_min, is_negative_one, "field_div_ovf")
                    .unwrap();
                let safe = self
                    .builder
                    .build_select(
                        overflowed,
                        int_ty.const_int(1, false),
                        divisor,
                        "field_divisor",
                    )
                    .unwrap();
                let message = if matches!(op, Op::Div) {
                    "attempt to divide with overflow"
                } else {
                    "attempt to calculate the remainder with overflow"
                };
                (
                    self.lower_binary(ty, op, old, safe)
                        .expect("primitive compound operator"),
                    Some((overflowed, message.to_owned())),
                )
            }
            _ => (
                self.lower_binary(ty, op, old, rhs)
                    .expect("primitive compound operator"),
                None,
            ),
        };
        let stored = match &overflow {
            Some((overflowed, _)) => self
                .builder
                .build_select(*overflowed, old, value, "class_field_new")
                .unwrap(),
            None => value,
        };
        self.builder.build_store(data, stored).unwrap();
        if let Some((overflowed, message)) = overflow {
            let panic_bb = self.append_block_to_current_fn("class_field_ovf_panic");
            let cont_bb = self.append_block_to_current_fn("class_field_ovf_cont");
            self.builder
                .build_conditional_branch(overflowed, panic_bb, cont_bb)
                .unwrap();
            self.builder.position_at_end(panic_bb);
            self.emit_arith_panic(&message, span, unwind_bb)?;
            self.builder.position_at_end(cont_bb);
        }
        Ok(())
    }

    fn store_intrinsic_reference(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        destination: &Place<'gcx>,
        data: inkwell::values::PointerValue<'llvm>,
    ) -> CompileResult<()> {
        self.store_place(destination, body, locals, self.lexical_reference(data))
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
            TyKind::Reference(inner) | TyKind::Pointer(inner, _) => inner,
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
        let arr_ptr = self.reference_data(arr_val);

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

    /// Compiler-private frame shell allocation. The descriptor is generated
    /// from the concrete frame layout; source code cannot name this intrinsic.
    pub(super) fn lower_intrinsic_gc_frame_allocate(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        arguments: GenericArguments<'gcx>,
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
    ) -> CompileResult<()> {
        let fail = || {
            self.gcx.dcx().emit_error(
                "invalid GC async frame allocation contract".into(),
                self.current_span,
            );
            crate::error::ReportedError
        };
        let [crate::sema::models::GenericArgument::Type(ty)] = arguments.as_ref() else {
            return Err(fail());
        };
        if !args.is_empty()
            || !matches!(self.place_ty(body, destination).kind(), TyKind::Pointer(inner, crate::hir::Mutability::Mutable) if inner == self.gcx.types.uint8)
        {
            return Err(fail());
        }
        let ty = self.mono_ty(*ty);
        if !matches!(ty.kind(), TyKind::Tuple(fields) if fields.first() == Some(&self.gcx.types.uint))
            || crate::sema::tycheck::utils::unresolved::storage_needs_substitution(self.gcx, ty)
        {
            self.gcx.dcx().emit_error(
                "GC async frame requires a concrete generated layout".into(),
                self.current_span,
            );
            return Err(crate::error::ReportedError);
        }
        // GC storage allocates the frame in the collected heap with its exact
        // layout; the runtime roots it while suspended.
        let (descriptor, symbol) = { (self.gc_descriptor_for(ty), "__gc__async_frame_allocate") };
        let pointer = self.context.ptr_type(AddressSpace::default());
        let allocate = self.module.get_function(symbol).unwrap_or_else(|| {
            self.module.add_function(
                symbol,
                pointer.fn_type(&[pointer.into()], false),
                Some(inkwell::module::Linkage::External),
            )
        });
        // Allocating the frame can collect while the caller still holds the
        // callee's arguments in temporaries, so publish them first.
        {
            self.emit_source_typed_gc_stack_map(
                self.current_span.expect("frame allocation source span"),
                crate::codegen::gc_stack_maps::StackMapSiteKind::Allocation,
            );
        }
        let owner = self
            .builder
            .build_call(allocate, &[descriptor.into()], "gc_frame_owner")
            .unwrap()
            .try_as_basic_value()
            .basic()
            .unwrap();
        self.store_place(destination, body, locals, owner)
    }

    pub(super) fn lower_intrinsic_gc_sync_generator_frame_allocate(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        arguments: GenericArguments<'gcx>,
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
    ) -> CompileResult<()> {
        let fail = || {
            self.gcx.dcx().emit_error(
                "invalid GC sync generator frame allocation contract".into(),
                self.current_span,
            );
            crate::error::ReportedError
        };
        let [crate::sema::models::GenericArgument::Type(ty)] = arguments.as_ref() else {
            return Err(fail());
        };
        if !args.is_empty()
            || !matches!(self.place_ty(body, destination).kind(), TyKind::Pointer(inner, crate::hir::Mutability::Mutable) if inner == self.gcx.types.uint8)
        {
            return Err(fail());
        }
        let ty = self.mono_ty(*ty);
        if !matches!(ty.kind(), TyKind::Tuple(fields) if fields.first() == Some(&self.gcx.types.uint))
            || crate::sema::tycheck::utils::unresolved::storage_needs_substitution(self.gcx, ty)
        {
            self.gcx.dcx().emit_error(
                "GC generator frame requires a concrete generated layout".into(),
                self.current_span,
            );
            return Err(crate::error::ReportedError);
        }
        let lowered = self.lower_ty(ty).ok_or_else(fail)?;
        let size = self.target_data.get_abi_size(&lowered).max(1);
        let descriptor = self.gc_descriptor_for(ty);
        let pointer = self.context.ptr_type(AddressSpace::default());
        let allocate = self.module.get_function("__gc__alloc").unwrap_or_else(|| {
            self.module.add_function(
                "__gc__alloc",
                pointer.fn_type(&[self.usize_ty.into(), pointer.into()], false),
                Some(inkwell::module::Linkage::External),
            )
        });
        {
            self.emit_source_typed_gc_stack_map(
                self.current_span.expect("generator frame allocation source span"),
                crate::codegen::gc_stack_maps::StackMapSiteKind::Allocation,
            );
        }
        let frame = self
            .builder
            .build_call(
                allocate,
                &[self.usize_ty.const_int(size, false).into(), descriptor.into()],
                "gc_gen_frame",
            )
            .unwrap()
            .try_as_basic_value()
            .basic()
            .unwrap();
        self.store_place(destination, body, locals, frame)
    }

    pub(super) fn lower_intrinsic_maybe_uninit(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        destination: &Place<'gcx>,
    ) -> CompileResult<()> {
        let dest_ty = self.place_ty(body, destination);
        let Some(llvm_ty) = self.lower_ty(dest_ty) else {
            return Ok(());
        };

        self.store_place(destination, body, locals, llvm_ty.const_zero().into())
    }

    /// Intrinsic: __intrinsic_ref_to_ptr[T](&T) -> *const T
    /// Intrinsic: __intrinsic_mut_ref_to_ptr[T](&T) -> *mut T
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

        let data = self.reference_data(val);
        // The raw address has the same pointee; its use remains unsafe.
        self.store_place(destination, body, locals, data.into())
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
        let llvm_elem_ty = self.lower_ty(elem_ty);

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

        // An element with no storage has zero stride. Returning without a
        // store leaves the pointer result uninitialized; the correct address
        // is the original one, for addition, subtraction and signed offset.
        let Some(llvm_elem_ty) = llvm_elem_ty else {
            return self.store_place(destination, body, locals, ptr_val.into());
        };

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

    /// Copy initialized typed storage. Pointer words obey the same shared
    /// access contract as a dereferenced source place.
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

        let val = self.build_typed_shared_load(elem_ty, llvm_elem_ty, ptr_val, "read_val");
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
        // Zero-sized values have no LLVM representation and nothing to store.
        let Some(val_val) = self.eval_operand(body, locals, val_op)? else {
            return Ok(());
        };

        let ty = self.operand_ty(body, val_op);
        self.build_typed_shared_store(ty, ptr_val, val_val);
        Ok(())
    }

    pub(super) fn lower_intrinsic_memcpy(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        call_args: GenericArguments<'gcx>,
        args: &[Operand<'gcx>],
    ) -> CompileResult<()> {
        // args: dst, src, count (bytes)
        let dst = self
            .eval_operand(body, locals, args.get(0).unwrap())?
            .unwrap()
            .into_pointer_value();
        let src = self
            .eval_operand(body, locals, args.get(1).unwrap())?
            .unwrap()
            .into_pointer_value();
        let count = self
            .eval_operand(body, locals, args.get(2).unwrap())?
            .unwrap()
            .into_int_value();

        if let Some(word) = self.pointer_copy_atomic_word(call_args) {
            self.validate_atomic_copy_count(count, word)?;
            self.build_element_atomic_memmove(dst, src, count, word);
            return Ok(());
        }
        let _ = self.builder.build_memcpy(dst, 1, src, 1, count).unwrap();
        Ok(())
    }

    pub(super) fn lower_intrinsic_memmove(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        call_args: GenericArguments<'gcx>,
        args: &[Operand<'gcx>],
    ) -> CompileResult<()> {
        let dst = self
            .eval_operand(body, locals, args.get(0).unwrap())?
            .unwrap()
            .into_pointer_value();
        let src = self
            .eval_operand(body, locals, args.get(1).unwrap())?
            .unwrap()
            .into_pointer_value();
        let count = self
            .eval_operand(body, locals, args.get(2).unwrap())?
            .unwrap()
            .into_int_value();

        if let Some(word) = self.pointer_copy_atomic_word(call_args) {
            self.validate_atomic_copy_count(count, word)?;
            self.build_element_atomic_memmove(dst, src, count, word);
        } else {
            let _ = self.builder.build_memmove(dst, 1, src, 1, count).unwrap();
        }
        Ok(())
    }

    fn validate_atomic_copy_count(
        &self,
        count: inkwell::values::IntValue<'llvm>,
        word: u32,
    ) -> CompileResult<()> {
        if let Some(bytes) = count.get_zero_extended_constant()
            && bytes % u64::from(word) != 0
        {
            self.gcx.dcx().emit_error(
                format!(
                    "pointer-bearing copy count must be a multiple of {word} bytes; found {bytes}"
                ),
                self.current_span,
            );
            return Err(crate::error::ReportedError);
        }
        Ok(())
    }

    /// Typed pointer copies pass a byte count for whole, aligned T elements.
    /// Byte-oriented callers instantiate T=uint8 and retain ordinary byte copy.
    fn pointer_copy_atomic_word(&mut self, arguments: GenericArguments<'gcx>) -> Option<u32> {
        let ty = self.substitute_ty_current(arguments.first()?.ty()?);
        if self.gc_layout_nodes_for_ty(ty).is_empty() {
            return None;
        }
        let llvm_ty = self.lower_ty(ty)?;
        let word = self.target_data.get_pointer_byte_size(None);
        (self.target_data.get_abi_alignment(&llvm_ty) >= word
            && self.target_data.get_store_size(&llvm_ty) % u64::from(word) == 0)
            .then_some(word)
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
        let Some(llvm_elem_ty) = self.lower_intrinsic_type_arg(call_args, "size_of") else {
            // Types without an LLVM storage representation (e.g. `!`) have size 0.
            return self.store_place(destination, body, locals, self.usize_ty.const_zero().into());
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
        let Some(llvm_elem_ty) = self.lower_intrinsic_type_arg(call_args, "align_of") else {
            return self.store_place(
                destination,
                body,
                locals,
                self.usize_ty.const_int(1, false).into(),
            );
        };

        let align = self.target_data.get_abi_alignment(&llvm_elem_ty);
        let align = self.usize_ty.const_int(align as u64, false);

        self.store_place(destination, body, locals, align.into())
    }
}
