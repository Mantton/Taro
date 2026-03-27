use super::{Emitter, LocalStorage};
use crate::{
    mir,
    sema::{
        models::{AdtKind, Ty, TyKind},
        tycheck::utils::instantiate::instantiate_ty_with_args,
    },
};
use inkwell::{AddressSpace, types::BasicType, values::PointerValue};

impl<'llvm, 'gcx> Emitter<'llvm, 'gcx> {
    /// Zero-initialize Rc-containing non-param stack slots so that unconditional
    /// release_walk on scope exit is safe (null Rc pointer → rc_dec is a no-op).
    /// Params are skipped because they receive real values from allocate_locals.
    pub(super) fn zero_init_rc_locals(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &[LocalStorage<'llvm>],
    ) {
        for (idx, decl) in body.locals.iter().enumerate() {
            // Skip params — they are initialized with actual values.
            if matches!(decl.kind, mir::LocalKind::Param) {
                continue;
            }
            let ty = self.mono_ty(decl.ty);
            if !self.contains_rc(ty) {
                continue;
            }
            let LocalStorage::Stack(slot) = locals[idx] else {
                continue;
            };
            let Some(llvm_ty) = self.lower_ty(ty) else {
                continue;
            };
            let size = self.target_data.get_store_size(&llvm_ty);
            if size == 0 {
                continue;
            }
            let size_val = self.usize_ty.const_int(size, false);
            self.builder
                .build_memset(slot, 1, self.context.i8_type().const_zero(), size_val)
                .unwrap();
        }
    }

    /// Retain Rc fields of incoming function parameters.
    /// Parameters are byte-copies from the caller, so we need to retain
    /// to account for the new reference the callee holds.
    /// Uses non-branching retain (no null check) since params are always valid.
    pub(super) fn retain_rc_params(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &[LocalStorage<'llvm>],
    ) {
        for (idx, decl) in body.locals.iter().enumerate() {
            if !matches!(decl.kind, mir::LocalKind::Param) {
                continue;
            }
            let ty = self.mono_ty(decl.ty);
            if !self.contains_rc(ty) {
                continue;
            }
            let LocalStorage::Stack(slot) = locals[idx] else {
                continue;
            };
            self.emit_rc_walk_no_null_check(slot, ty, true);
        }
    }

    /// Like emit_rc_walk but without null checks. Used for values known to be initialized
    /// (e.g., function parameters). Does not create new basic blocks.
    fn emit_rc_walk_no_null_check(
        &mut self,
        base_ptr: PointerValue<'llvm>,
        ty: Ty<'gcx>,
        retain: bool,
    ) {
        if self.is_rc_ty(ty) {
            let rc_ptr = self
                .builder
                .build_load(
                    self.context.ptr_type(AddressSpace::default()),
                    base_ptr,
                    "rc_load",
                )
                .unwrap()
                .into_pointer_value();
            if retain {
                self.emit_rc_retain(rc_ptr);
            } else {
                self.emit_rc_release(rc_ptr);
            }
            return;
        }

        match ty.kind() {
            TyKind::Adt(def, adt_args) => match def.kind {
                AdtKind::Struct => {
                    let defn = self.gcx.get_struct_definition(def.id);
                    let fields: Vec<_> = defn.fields.to_vec();
                    let llvm_ty = self.lower_ty(ty).unwrap().into_struct_type();
                    for (idx, field) in fields.iter().enumerate() {
                        let resolved = crate::sema::tycheck::utils::normalize_post_monomorphization(
                            self.gcx,
                            instantiate_ty_with_args(self.gcx, field.ty, adt_args),
                        );
                        if !self.contains_rc(resolved) {
                            continue;
                        }
                        let field_ptr = self
                            .builder
                            .build_struct_gep(llvm_ty, base_ptr, idx as u32, "rc_field_ptr")
                            .unwrap();
                        self.emit_rc_walk_no_null_check(field_ptr, resolved, retain);
                    }
                }
                AdtKind::Enum => {
                    // Enums need branching — use the full walk.
                    self.emit_rc_walk(base_ptr, ty, retain);
                }
            },
            TyKind::Tuple(items) => {
                let items: Vec<_> = items.to_vec();
                let llvm_ty = self.lower_ty(ty).unwrap().into_struct_type();
                for (idx, item) in items.iter().enumerate() {
                    let item = crate::sema::tycheck::utils::normalize_post_monomorphization(
                        self.gcx, *item,
                    );
                    if !self.contains_rc(item) {
                        continue;
                    }
                    let field_ptr = self
                        .builder
                        .build_struct_gep(llvm_ty, base_ptr, idx as u32, "rc_tuple_ptr")
                        .unwrap();
                    self.emit_rc_walk_no_null_check(field_ptr, item, retain);
                }
            }
            TyKind::Closure { closure_def_id, .. } => {
                if let Some(captures) = self.gcx.get_closure_captures(closure_def_id) {
                    let llvm_ty = self.lower_ty(ty).unwrap().into_struct_type();
                    for capture in &captures.captures {
                        let resolved = crate::sema::tycheck::utils::normalize_post_monomorphization(
                            self.gcx, capture.ty,
                        );
                        if !self.contains_rc(resolved) {
                            continue;
                        }
                        let field_ptr = self
                            .builder
                            .build_struct_gep(
                                llvm_ty,
                                base_ptr,
                                capture.field_index.index() as u32,
                                "rc_closure_ptr",
                            )
                            .unwrap();
                        self.emit_rc_walk_no_null_check(field_ptr, resolved, retain);
                    }
                }
            }
            _ => {
                self.emit_rc_walk(base_ptr, ty, retain);
            }
        }
    }

    /// Emit release_walk for all Rc-containing locals at function exit.
    /// Called before return and unwind.
    pub(super) fn emit_rc_cleanup(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &[LocalStorage<'llvm>],
    ) {
        for (idx, decl) in body.locals.iter().enumerate() {
            // Skip the return local — its value is being transferred to the caller.
            if idx == body.return_local.index() {
                continue;
            }
            let ty = self.mono_ty(decl.ty);
            if !self.contains_rc(ty) {
                continue;
            }
            let LocalStorage::Stack(slot) = locals[idx] else {
                continue;
            };
            self.emit_release_walk(slot, ty);
        }
    }

    /// Pre-assignment: save old value before the store overwrites it.
    /// Returns the temp pointer to pass to `emit_rc_post_assign`.
    pub(super) fn emit_rc_pre_assign(
        &mut self,
        dest_ptr: PointerValue<'llvm>,
        ty: Ty<'gcx>,
    ) -> Option<PointerValue<'llvm>> {
        let llvm_ty = self.lower_ty(ty)?;
        let size = self.target_data.get_store_size(&llvm_ty);
        if size == 0 {
            return None;
        }

        let tmp = self.builder.build_alloca(llvm_ty, "rc_old_tmp").unwrap();
        let size_val = self.usize_ty.const_int(size, false);
        let align = self.target_data.get_abi_alignment(&llvm_ty).max(1);
        self.builder
            .build_memmove(tmp, align, dest_ptr, align, size_val)
            .unwrap();

        Some(tmp)
    }

    /// Emit an inline `rc_inc`: load strong count, add 1, store.
    pub(super) fn emit_rc_retain(&self, rc_ptr: PointerValue<'llvm>) {
        let strong_ptr = rc_ptr;
        let old = self
            .builder
            .build_load(self.usize_ty, strong_ptr, "rc_strong")
            .unwrap()
            .into_int_value();
        let new = self
            .builder
            .build_int_add(old, self.usize_ty.const_int(1, false), "rc_inc")
            .unwrap();
        self.builder.build_store(strong_ptr, new).unwrap();
    }

    /// Emit an inline `rc_dec`: load strong count, sub 1, store.
    pub(super) fn emit_rc_release(&self, rc_ptr: PointerValue<'llvm>) {
        let strong_ptr = rc_ptr;
        let old = self
            .builder
            .build_load(self.usize_ty, strong_ptr, "rc_strong")
            .unwrap()
            .into_int_value();
        let new = self
            .builder
            .build_int_sub(old, self.usize_ty.const_int(1, false), "rc_dec")
            .unwrap();
        self.builder.build_store(strong_ptr, new).unwrap();
    }

    /// Walk the type structure at `base_ptr` and retain (rc_inc) all Rc pointer fields.
    /// `base_ptr` points to the start of a value of type `ty`.
    pub(super) fn emit_retain_walk(&mut self, base_ptr: PointerValue<'llvm>, ty: Ty<'gcx>) {
        self.emit_rc_walk(base_ptr, ty, true);
    }

    /// Walk the type structure at `base_ptr` and release (rc_dec) all Rc pointer fields.
    /// `base_ptr` points to the start of a value of type `ty`.
    pub(super) fn emit_release_walk(&mut self, base_ptr: PointerValue<'llvm>, ty: Ty<'gcx>) {
        self.emit_rc_walk(base_ptr, ty, false);
    }

    fn emit_rc_walk(&mut self, base_ptr: PointerValue<'llvm>, ty: Ty<'gcx>, retain: bool) {
        if self.is_rc_ty(ty) {
            // The value at base_ptr is an Rc[T] — it's a pointer (the Rc ptr field).
            // Load it to get the actual Rc header pointer, then retain/release.
            let rc_ptr = self
                .builder
                .build_load(
                    self.context.ptr_type(AddressSpace::default()),
                    base_ptr,
                    "rc_load",
                )
                .unwrap()
                .into_pointer_value();

            // Null check: skip retain/release for null Rc pointers (zero-init slots).
            let current_fn = self.current_fn.unwrap();
            let then_bb = self.context.append_basic_block(current_fn, "rc_nonnull");
            let merge_bb = self.context.append_basic_block(current_fn, "rc_merge");
            let is_null = self.builder.build_is_null(rc_ptr, "rc_is_null").unwrap();
            self.builder
                .build_conditional_branch(is_null, merge_bb, then_bb)
                .unwrap();

            self.builder.position_at_end(then_bb);
            if retain {
                self.emit_rc_retain(rc_ptr);
            } else {
                self.emit_rc_release(rc_ptr);
            }
            self.builder.build_unconditional_branch(merge_bb).unwrap();

            self.builder.position_at_end(merge_bb);
            return;
        }

        match ty.kind() {
            TyKind::Adt(def, adt_args) => match def.kind {
                AdtKind::Struct => {
                    let defn = self.gcx.get_struct_definition(def.id);
                    let fields: Vec<_> = defn.fields.to_vec();
                    let llvm_ty = self.lower_ty(ty).unwrap().into_struct_type();

                    for (idx, field) in fields.iter().enumerate() {
                        let resolved = crate::sema::tycheck::utils::normalize_post_monomorphization(
                            self.gcx,
                            instantiate_ty_with_args(self.gcx, field.ty, adt_args),
                        );
                        if !self.contains_rc(resolved) {
                            continue;
                        }
                        let field_ptr = self
                            .builder
                            .build_struct_gep(llvm_ty, base_ptr, idx as u32, "rc_field_ptr")
                            .unwrap();
                        self.emit_rc_walk(field_ptr, resolved, retain);
                    }
                }
                AdtKind::Enum => {
                    self.emit_rc_walk_enum(base_ptr, ty, def.id, adt_args, retain);
                }
            },
            TyKind::Tuple(items) => {
                let items: Vec<_> = items.to_vec();
                let llvm_ty = self.lower_ty(ty).unwrap().into_struct_type();

                for (idx, item) in items.iter().enumerate() {
                    let item = crate::sema::tycheck::utils::normalize_post_monomorphization(
                        self.gcx, *item,
                    );
                    if !self.contains_rc(item) {
                        continue;
                    }
                    let field_ptr = self
                        .builder
                        .build_struct_gep(llvm_ty, base_ptr, idx as u32, "rc_tuple_ptr")
                        .unwrap();
                    self.emit_rc_walk(field_ptr, item, retain);
                }
            }
            TyKind::Array { element, len } => {
                let element =
                    crate::sema::tycheck::utils::normalize_post_monomorphization(self.gcx, element);
                if !self.contains_rc(element) {
                    return;
                }
                if let crate::sema::models::ConstKind::Value(
                    crate::sema::models::ConstValue::Integer(n),
                ) = len.kind
                {
                    let elem_llvm_ty = self.lower_ty(element).unwrap();
                    let arr_llvm_ty = elem_llvm_ty.as_basic_type_enum().array_type(n as u32);
                    for i in 0..(n as u32) {
                        let zero = self.usize_ty.const_zero();
                        let idx = self.usize_ty.const_int(i as u64, false);
                        let elem_ptr = unsafe {
                            self.builder
                                .build_gep(arr_llvm_ty, base_ptr, &[zero, idx], "rc_arr_elem")
                                .unwrap()
                        };
                        self.emit_rc_walk(elem_ptr, element, retain);
                    }
                }
            }
            TyKind::Closure { closure_def_id, .. } => {
                if let Some(captures) = self.gcx.get_closure_captures(closure_def_id) {
                    let llvm_ty = self.lower_ty(ty).unwrap().into_struct_type();
                    for capture in &captures.captures {
                        let resolved = crate::sema::tycheck::utils::normalize_post_monomorphization(
                            self.gcx, capture.ty,
                        );
                        if !self.contains_rc(resolved) {
                            continue;
                        }
                        let field_ptr = self
                            .builder
                            .build_struct_gep(
                                llvm_ty,
                                base_ptr,
                                capture.field_index.index() as u32,
                                "rc_closure_ptr",
                            )
                            .unwrap();
                        self.emit_rc_walk(field_ptr, resolved, retain);
                    }
                }
            }
            _ => {}
        }
    }

    fn emit_rc_walk_enum(
        &mut self,
        base_ptr: PointerValue<'llvm>,
        ty: Ty<'gcx>,
        def_id: crate::hir::DefinitionID,
        adt_args: crate::sema::models::GenericArguments<'gcx>,
        retain: bool,
    ) {
        let enum_def = self.gcx.get_enum_definition(def_id);
        let variants: Vec<_> = enum_def.variants.to_vec();

        // Check if any variant contains Rc at all.
        let has_rc_variants: Vec<bool> = variants
            .iter()
            .map(|v| {
                if let crate::sema::models::EnumVariantKind::Tuple(fields) = v.kind {
                    fields.iter().any(|f| {
                        let resolved = crate::sema::tycheck::utils::normalize_post_monomorphization(
                            self.gcx,
                            instantiate_ty_with_args(self.gcx, f.ty, adt_args),
                        );
                        self.contains_rc(resolved)
                    })
                } else {
                    false
                }
            })
            .collect();

        if !has_rc_variants.iter().any(|&b| b) {
            return;
        }

        // Load discriminant.
        let discr_ty = self.context.ptr_sized_int_type(&self.target_data, None);
        let llvm_ty = self.lower_ty(ty).unwrap().into_struct_type();
        let discr_ptr = self
            .builder
            .build_struct_gep(llvm_ty, base_ptr, 0, "rc_enum_discr_ptr")
            .unwrap();
        let discr_val = self
            .builder
            .build_load(discr_ty, discr_ptr, "rc_enum_discr")
            .unwrap()
            .into_int_value();

        // Payload pointer (field index 1 in the enum struct layout).
        let payload_ptr = self
            .builder
            .build_struct_gep(llvm_ty, base_ptr, 1, "rc_enum_payload_ptr")
            .unwrap();

        let current_fn = self.current_fn.unwrap();
        let merge_bb = self.context.append_basic_block(current_fn, "rc_enum_merge");

        // Build switch on discriminant.
        let default_bb = merge_bb;
        let mut cases = Vec::new();

        for (i, variant) in variants.iter().enumerate() {
            if !has_rc_variants[i] {
                continue;
            }
            let variant_bb = self
                .context
                .append_basic_block(current_fn, &format!("rc_enum_v{}", i));
            cases.push((discr_ty.const_int(variant.discriminant, false), variant_bb));

            self.builder.position_at_end(variant_bb);
            if let crate::sema::models::EnumVariantKind::Tuple(fields) = variant.kind {
                // Build a struct type for this variant's payload.
                let field_tys: Vec<_> = fields
                    .iter()
                    .filter_map(|f| {
                        let resolved = crate::sema::tycheck::utils::normalize_post_monomorphization(
                            self.gcx,
                            instantiate_ty_with_args(self.gcx, f.ty, adt_args),
                        );
                        self.lower_ty(resolved)
                    })
                    .collect();
                let variant_struct = self.context.struct_type(&field_tys, false);

                for (fidx, field) in fields.iter().enumerate() {
                    let resolved = crate::sema::tycheck::utils::normalize_post_monomorphization(
                        self.gcx,
                        instantiate_ty_with_args(self.gcx, field.ty, adt_args),
                    );
                    if !self.contains_rc(resolved) {
                        continue;
                    }
                    let field_ptr = self
                        .builder
                        .build_struct_gep(
                            variant_struct,
                            payload_ptr,
                            fidx as u32,
                            "rc_enum_field_ptr",
                        )
                        .unwrap();
                    self.emit_rc_walk(field_ptr, resolved, retain);
                }
            }
            self.builder.build_unconditional_branch(merge_bb).unwrap();
        }

        // Position back to emit the switch.
        // We need to be at the block that loaded the discriminant.
        // Actually, the switch needs to be at the end of the block where we loaded the discr.
        // Let's re-position: the discr load was in whatever block we were in before the switch.
        // We need to insert the switch after the discr load.
        // Since we've been appending basic blocks, we need to go back.
        // The discr load was emitted before the merge_bb was created.
        // Let's handle this properly:

        // The discr_val's parent block is where we need the switch.
        let switch_bb = discr_val.as_instruction().unwrap().get_parent().unwrap();
        self.builder.position_at_end(switch_bb);
        self.builder
            .build_switch(discr_val, default_bb, &cases)
            .unwrap();

        self.builder.position_at_end(merge_bb);
    }
}
