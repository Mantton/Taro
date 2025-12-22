use crate::{
    codegen::mangle::mangle,
    compile::context::{Gcx, GlobalContext},
    error::CompileResult,
    hir,
    mir::{self, Operand},
    sema::models::{FloatTy, IntTy, Ty, TyKind, UIntTy},
    span::Symbol,
};
use inkwell::{
    AddressSpace, FloatPredicate, IntPredicate, OptimizationLevel,
    builder::Builder,
    context::Context,
    module::{Linkage, Module},
    passes::PassManager,
    targets::{
        CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetData, TargetMachine,
    },
    types::{
        BasicMetadataTypeEnum, BasicType, BasicTypeEnum, FloatType, FunctionType, IntType,
        StructType,
    },
    values::{BasicMetadataValueEnum, BasicValue, BasicValueEnum, FunctionValue, PointerValue},
};
use rustc_hash::FxHashMap;
use std::{fs, path::PathBuf};

/// Lower MIR for a package into a single LLVM module and cache its IR.
pub fn emit_package<'gcx>(
    package: &'gcx mir::MirPackage<'gcx>,
    gcx: GlobalContext<'gcx>,
) -> CompileResult<PathBuf> {
    let context = Context::create();
    let module = context.create_module(&gcx.config.identifier);
    let builder = context.create_builder();

    // Initialize target for host and set data layout early.
    Target::initialize_native(&InitializationConfig::default())
        .map_err(|_| crate::error::ReportedError)?;
    let triple = TargetMachine::get_default_triple();
    let target = Target::from_triple(&triple).map_err(|_| crate::error::ReportedError)?;
    let cpu = TargetMachine::get_host_cpu_name();
    let features = TargetMachine::get_host_cpu_features();
    let target_machine = target
        .create_target_machine(
            &triple,
            cpu.to_str().unwrap_or(""),
            features.to_str().unwrap_or(""),
            OptimizationLevel::Default,
            RelocMode::Default,
            CodeModel::Default,
        )
        .ok_or(crate::error::ReportedError)?;

    module.set_data_layout(&target_machine.get_target_data().get_data_layout());
    module.set_triple(&triple);

    let mut emitter = Emitter::new(&context, module, builder, gcx, target_machine);
    emitter.declare_functions(package);
    emitter.lower_functions(package)?;
    emitter.emit_start_shim(package);
    emitter.run_function_passes();

    // let ir = emitter.module.print_to_string().to_string();
    // println!("{ir}");

    let obj = emitter.emit_object_file()?;
    gcx.cache_object_file(obj.clone());
    Ok(obj)
}

struct Emitter<'llvm, 'gcx> {
    context: &'llvm Context,
    module: Module<'llvm>,
    builder: Builder<'llvm>,
    gcx: GlobalContext<'gcx>,
    functions: FxHashMap<hir::DefinitionID, FunctionValue<'llvm>>,
    strings: FxHashMap<Symbol, PointerValue<'llvm>>,
    target_machine: TargetMachine,
    target_data: inkwell::targets::TargetData,
    gc_descs: FxHashMap<Ty<'gcx>, PointerValue<'llvm>>,
    gc_desc_ty: inkwell::types::StructType<'llvm>,
    usize_ty: inkwell::types::IntType<'llvm>,
    shadow: Option<ShadowStackInfo<'llvm, 'gcx>>,
}

#[derive(Clone, Copy)]
enum LocalStorage<'llvm> {
    Value(Option<BasicValueEnum<'llvm>>),
    Stack(PointerValue<'llvm>),
}

struct ShadowStackInfo<'llvm, 'gcx> {
    frame_ptr: PointerValue<'llvm>,
    slots_ptr: PointerValue<'llvm>,
    slot_defs: Vec<ShadowSlotDef<'gcx>>,
    slot_map: Vec<Vec<usize>>,
}

#[derive(Clone)]
struct ShadowSlotDef<'gcx> {
    local: mir::LocalId,
    kind: ShadowSlotKind<'gcx>,
}

#[derive(Clone)]
enum ShadowSlotKind<'gcx> {
    Local(Ty<'gcx>),
    Field(crate::thir::FieldIndex, Ty<'gcx>),
}

impl<'llvm, 'gcx> Emitter<'llvm, 'gcx> {
    fn new(
        context: &'llvm Context,
        module: Module<'llvm>,
        builder: Builder<'llvm>,
        gcx: GlobalContext<'gcx>,
        target_machine: TargetMachine,
    ) -> Self {
        let target_data = target_machine.get_target_data();
        let usize_ty = context.ptr_sized_int_type(&target_data, None);
        let opaque_ptr = context.ptr_type(AddressSpace::default());
        let gc_desc_ty = context.struct_type(
            &[
                usize_ty.into(),   // size
                usize_ty.into(),   // align
                opaque_ptr.into(), // ptr_offsets
                usize_ty.into(),   // ptr_count
            ],
            false,
        );
        Emitter {
            context,
            module,
            builder,
            gcx,
            functions: FxHashMap::default(),
            strings: FxHashMap::default(),
            target_machine,
            target_data,
            gc_descs: FxHashMap::default(),
            gc_desc_ty,
            usize_ty,
            shadow: None,
        }
    }

    fn declare_functions(&mut self, package: &mir::MirPackage<'gcx>) {
        for (&def_id, _) in &package.functions {
            let sig = self.gcx.get_signature(def_id);
            let fn_ty = lower_fn_sig(self.context, self.gcx, &self.target_data, sig);
            let name = mangle(self.gcx, def_id);
            let f = self.module.add_function(&name, fn_ty, None);
            self.functions.insert(def_id, f);
        }
    }

    fn lower_functions(&mut self, package: &mir::MirPackage<'gcx>) -> CompileResult<()> {
        for (&def_id, body) in &package.functions {
            // let ident = self.gcx.definition_ident(def_id);
            // println!("{} IR Lowering", ident.symbol);
            self.lower_body(def_id, body)?;
        }
        Ok(())
    }

    fn emit_start_shim(&mut self, package: &mir::MirPackage<'gcx>) {
        let Some(entry) = package.entry else {
            return;
        };
        let Some(&user_fn) = self.functions.get(&entry) else {
            return;
        };
        let entry_sig = self.gcx.get_signature(entry);

        let i32_ty = self.context.i32_type();
        let start_ty = i32_ty.fn_type(&[], false);
        let start_fn = self.module.add_function("taro_start", start_ty, None);

        let builder = self.context.create_builder();
        let bb = self.context.append_basic_block(start_fn, "entry");
        builder.position_at_end(bb);
        let call = builder.build_call(user_fn, &[], "call_main").unwrap();

        let exit_code = match (entry_sig.output.kind(), call.try_as_basic_value().basic()) {
            (TyKind::Infer(_) | TyKind::Error, _) => {
                i32_ty.const_int(0, false).as_basic_value_enum()
            }
            (TyKind::Tuple(items), _) if items.is_empty() => {
                i32_ty.const_int(0, false).as_basic_value_enum()
            }
            (TyKind::Bool, Some(val)) => {
                let int = builder
                    .build_int_z_extend_or_bit_cast(val.into_int_value(), i32_ty, "bool_to_i32")
                    .unwrap();
                int.as_basic_value_enum()
            }
            (TyKind::Int(_) | TyKind::UInt(_) | TyKind::Rune, Some(val)) => {
                let int_val = val.into_int_value();
                let cast = builder
                    .build_int_cast(int_val, i32_ty, "int_to_i32")
                    .unwrap();
                cast.as_basic_value_enum()
            }
            (TyKind::Float(_), Some(val)) => builder
                .build_float_to_signed_int(val.into_float_value(), i32_ty, "float_to_i32")
                .unwrap()
                .as_basic_value_enum(),
            (TyKind::Pointer(..) | TyKind::Reference(..) | TyKind::GcPtr, Some(val)) => {
                let ptr = val.into_pointer_value();
                let int64 = builder
                    .build_ptr_to_int(ptr, self.context.i64_type(), "ptr_to_int")
                    .unwrap();
                builder
                    .build_int_cast(int64, i32_ty, "ptr_to_i32")
                    .unwrap()
                    .as_basic_value_enum()
            }
            (_, Some(val)) => val,
            _ => i32_ty.const_int(0, false).as_basic_value_enum(),
        };

        let _ = builder.build_return(Some(&exit_code)).unwrap();

        // Provide a conventional `main` that forwards to `taro_start` for easier linking.
        let main_fn = self.module.add_function("main", start_ty, None);
        let main_builder = self.context.create_builder();
        let main_bb = self.context.append_basic_block(main_fn, "entry");
        main_builder.position_at_end(main_bb);
        let start_call = main_builder
            .build_call(start_fn, &[], "call_start")
            .unwrap();
        let main_ret = start_call
            .try_as_basic_value()
            .basic()
            .map(|v| v.into_int_value())
            .unwrap_or_else(|| i32_ty.const_int(0, false));
        let _ = main_builder.build_return(Some(&main_ret)).unwrap();
    }

    fn run_function_passes(&self) {
        let fpm = PassManager::create(&self.module);
        fpm.add_instruction_combining_pass();
        fpm.add_reassociate_pass();
        fpm.add_gvn_pass();
        fpm.add_cfg_simplification_pass();
        fpm.add_promote_memory_to_register_pass();
        fpm.initialize();

        for func in self.module.get_functions() {
            let _ = fpm.run_on(&func);
        }
    }

    fn emit_object_file(&mut self) -> CompileResult<PathBuf> {
        let tm = &self.target_machine;
        let out_dir = self.gcx.output_root().clone();
        if let Err(e) = fs::create_dir_all(&out_dir) {
            let msg = format!("failed to create output directory: {e}");
            self.gcx.dcx().emit_error(msg.into(), None);
            return Err(crate::error::ReportedError);
        }
        let obj_path = out_dir.join(format!("{}.o", self.gcx.config.identifier));

        tm.write_to_file(&self.module, FileType::Object, &obj_path)
            .map_err(|e| {
                let msg = format!("failed to write object file: {e}");
                self.gcx.dcx().emit_error(msg.into(), None);
                crate::error::ReportedError
            })?;

        Ok(obj_path)
    }

    fn lower_body(
        &mut self,
        def_id: hir::DefinitionID,
        body: &mir::Body<'gcx>,
    ) -> CompileResult<()> {
        let function = *self
            .functions
            .get(&def_id)
            .expect("function must be declared");

        let llvm_blocks = self.create_blocks(function, body);
        let entry_block = llvm_blocks[body.start_block.index()];
        let mut locals = self.allocate_locals(body, entry_block, function);
        self.builder.position_at_end(entry_block);
        self.setup_shadow_stack(body, entry_block, &locals)?;

        for (bb_id, bb) in body.basic_blocks.iter_enumerated() {
            let llvm_bb = llvm_blocks[bb_id.index()];
            self.builder.position_at_end(llvm_bb);

            for stmt in &bb.statements {
                self.lower_statement(body, &mut locals, stmt)?;
            }

            if let Some(term) = &bb.terminator {
                self.lower_terminator(body, &mut locals, term, &llvm_blocks)?;
            } else if llvm_bb.get_terminator().is_none() {
                let _ = self.builder.build_unreachable().unwrap();
            }
        }

        self.shadow = None;
        Ok(())
    }

    fn create_blocks(
        &self,
        function: FunctionValue<'llvm>,
        body: &mir::Body<'gcx>,
    ) -> Vec<inkwell::basic_block::BasicBlock<'llvm>> {
        let mut blocks = Vec::with_capacity(body.basic_blocks.len());
        for (idx, _) in body.basic_blocks.iter().enumerate() {
            blocks.push(
                self.context
                    .append_basic_block(function, &format!("bb{idx}")),
            );
        }
        blocks
    }

    fn allocate_locals(
        &self,
        body: &mir::Body<'gcx>,
        entry_block: inkwell::basic_block::BasicBlock<'llvm>,
        function: FunctionValue<'llvm>,
    ) -> Vec<LocalStorage<'llvm>> {
        let alloc_builder = self.context.create_builder();
        alloc_builder.position_at_end(entry_block);

        let mut locals = Vec::with_capacity(body.locals.len());
        for (idx, decl) in body.locals.iter().enumerate() {
            let name = decl
                .name
                .map(|s| s.as_str().to_string())
                .unwrap_or_else(|| format!("tmp{idx}"));
            // Use stack slots for all locals with a representable LLVM type.
            // This avoids incorrect behavior at control-flow joins when "locals"
            // are tracked purely in the emitter (would require PHI construction).
            let storage = match lower_type(self.context, self.gcx, &self.target_data, decl.ty) {
                Some(ty) => {
                    let slot = alloc_builder.build_alloca(ty, &name).unwrap();
                    LocalStorage::Stack(slot)
                }
                None => LocalStorage::Value(None),
            };
            locals.push(storage);
        }

        // Seed parameters with incoming SSA arguments.
        let mut params = function.get_param_iter();
        for (idx, decl) in body.locals.iter().enumerate() {
            if let mir::LocalKind::Param = decl.kind {
                if let Some(arg) = params.next() {
                    match locals[idx] {
                        LocalStorage::Value(_) => {
                            locals[idx] = LocalStorage::Value(Some(arg));
                        }
                        LocalStorage::Stack(slot) => {
                            let _ = alloc_builder.build_store(slot, arg).unwrap();
                        }
                    }
                }
            }
        }

        locals
    }

    fn setup_shadow_stack(
        &mut self,
        body: &mir::Body<'gcx>,
        entry_block: inkwell::basic_block::BasicBlock<'llvm>,
        locals: &[LocalStorage<'llvm>],
    ) -> CompileResult<()> {
        let (slot_defs, slot_map) = self.collect_shadow_slots(body);
        if slot_defs.is_empty() {
            self.shadow = None;
            return Ok(());
        }

        let ptr_ty = self.context.ptr_type(AddressSpace::default());
        let slot_count = slot_defs.len() as u64;
        let slots_ptr = self
            .builder
            .build_array_alloca(
                ptr_ty,
                self.usize_ty.const_int(slot_count, false),
                "gc_slots",
            )
            .unwrap();

        let frame_ty = self.shadow_frame_ty();
        let frame_ptr = self
            .builder
            .build_alloca(frame_ty, "gc_shadow_frame")
            .unwrap();

        let prev_ptr = self
            .builder
            .build_struct_gep(frame_ty, frame_ptr, 0, "gc_frame_prev")
            .unwrap();
        let slots_ptr_gep = self
            .builder
            .build_struct_gep(frame_ty, frame_ptr, 1, "gc_frame_slots")
            .unwrap();
        let count_ptr = self
            .builder
            .build_struct_gep(frame_ty, frame_ptr, 2, "gc_frame_count")
            .unwrap();
        let _ = self
            .builder
            .build_store(prev_ptr, ptr_ty.const_null())
            .unwrap();
        let _ = self.builder.build_store(slots_ptr_gep, slots_ptr).unwrap();
        let _ = self
            .builder
            .build_store(count_ptr, self.usize_ty.const_int(slot_count, false))
            .unwrap();

        let push_ty = self.context.void_type().fn_type(&[ptr_ty.into()], false);
        let push_fn = self
            .module
            .get_function("__rt__gc_push_frame")
            .unwrap_or_else(|| {
                self.module
                    .add_function("__rt__gc_push_frame", push_ty, Some(Linkage::External))
            });
        let _ = self
            .builder
            .build_call(push_fn, &[frame_ptr.into()], "gc_push")
            .unwrap();

        let shadow = ShadowStackInfo {
            frame_ptr,
            slots_ptr,
            slot_defs,
            slot_map,
        };
        self.shadow = Some(shadow);

        // Initialize slots to null before any user code runs.
        for idx in 0..slot_count as usize {
            self.store_shadow_slot(idx, ptr_ty.const_null());
        }

        // Seed parameter locals into the shadow stack.
        for (idx, decl) in body.locals.iter().enumerate() {
            if matches!(decl.kind, mir::LocalKind::Param) {
                self.update_shadow_for_local(body, locals, mir::LocalId::from_raw(idx as u32))?;
            }
        }

        // Ensure setup happens before any user instructions in the entry block.
        self.builder.position_at_end(entry_block);
        Ok(())
    }

    fn collect_shadow_slots(
        &self,
        body: &mir::Body<'gcx>,
    ) -> (Vec<ShadowSlotDef<'gcx>>, Vec<Vec<usize>>) {
        let mut slot_defs = Vec::new();
        let mut slot_map = vec![Vec::new(); body.locals.len()];

        for (local, decl) in body.locals.iter_enumerated() {
            let ty = decl.ty;
            let mut local_slots = Vec::new();
            match ty.kind() {
                TyKind::Reference(..) | TyKind::GcPtr | TyKind::String => {
                    local_slots.push(ShadowSlotKind::Local(ty));
                }
                TyKind::Adt(def) => {
                    let defn = self.gcx.get_struct_definition(def.id);
                    for (idx, field) in defn.fields.iter().enumerate() {
                        if is_pointer_ty(field.ty) {
                            let field_idx = crate::thir::FieldIndex::new(idx);
                            local_slots.push(ShadowSlotKind::Field(field_idx, field.ty));
                        }
                    }
                }
                TyKind::Tuple(items) => {
                    for (idx, item_ty) in items.iter().enumerate() {
                        if is_pointer_ty(*item_ty) {
                            let field_idx = crate::thir::FieldIndex::new(idx);
                            local_slots.push(ShadowSlotKind::Field(field_idx, *item_ty));
                        }
                    }
                }
                _ => {}
            }

            for kind in local_slots {
                let slot_index = slot_defs.len();
                slot_defs.push(ShadowSlotDef { local, kind });
                slot_map[local.index()].push(slot_index);
            }
        }

        (slot_defs, slot_map)
    }

    fn shadow_frame_ty(&self) -> StructType<'llvm> {
        if let Some(ty) = self.context.get_struct_type("_gcShadowFrame") {
            if ty.is_opaque() {
                let ptr_ty = self.context.ptr_type(AddressSpace::default());
                ty.set_body(&[ptr_ty.into(), ptr_ty.into(), self.usize_ty.into()], false);
            }
            return ty;
        }

        let ty = self.context.opaque_struct_type("_gcShadowFrame");
        let ptr_ty = self.context.ptr_type(AddressSpace::default());
        ty.set_body(&[ptr_ty.into(), ptr_ty.into(), self.usize_ty.into()], false);
        ty
    }

    fn store_shadow_slot(&mut self, slot_idx: usize, value: PointerValue<'llvm>) {
        let Some(shadow) = &self.shadow else {
            return;
        };
        let idx = self.usize_ty.const_int(slot_idx as u64, false);
        let slot_ptr = unsafe {
            self.builder
                .build_gep(
                    self.context.ptr_type(AddressSpace::default()),
                    shadow.slots_ptr,
                    &[idx],
                    "gc_slot_ptr",
                )
                .unwrap()
        };
        let _ = self.builder.build_store(slot_ptr, value).unwrap();
    }

    fn update_shadow_for_local(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &[LocalStorage<'llvm>],
        local: mir::LocalId,
    ) -> CompileResult<()> {
        let Some(shadow) = self.shadow.as_ref() else {
            return Ok(());
        };
        let slot_indices = shadow
            .slot_map
            .get(local.index())
            .cloned()
            .unwrap_or_default();
        if slot_indices.is_empty() {
            return Ok(());
        }
        let slot_defs = shadow.slot_defs.clone();

        for slot_idx in slot_indices {
            let def = slot_defs.get(slot_idx).cloned().expect("shadow slot def");
            let place = match def.kind.clone() {
                ShadowSlotKind::Local(_) => mir::Place::from_local(def.local),
                ShadowSlotKind::Field(field_idx, field_ty) => mir::Place {
                    local: def.local,
                    projection: vec![mir::PlaceElem::Field(field_idx, field_ty)],
                },
            };

            let value = match self.load_place(body, locals, &place) {
                Some(v) => v,
                None => {
                    self.store_shadow_slot(
                        slot_idx,
                        self.context.ptr_type(AddressSpace::default()).const_null(),
                    );
                    continue;
                }
            };

            let slot_ty = match def.kind {
                ShadowSlotKind::Local(ty) => ty,
                ShadowSlotKind::Field(_, ty) => ty,
            };

            let ptr_val = match self.shadow_ptr_from_value(slot_ty, value) {
                Some(p) => p,
                None => self.context.ptr_type(AddressSpace::default()).const_null(),
            };
            self.store_shadow_slot(slot_idx, ptr_val);
        }

        Ok(())
    }

    fn shadow_ptr_from_value(
        &mut self,
        ty: Ty<'gcx>,
        value: BasicValueEnum<'llvm>,
    ) -> Option<PointerValue<'llvm>> {
        match ty.kind() {
            TyKind::Reference(..) | TyKind::GcPtr => Some(value.into_pointer_value()),
            TyKind::String => {
                let struct_val = value.into_struct_value();
                let ptr_val = self
                    .builder
                    .build_extract_value(struct_val, 0, "gc_str_ptr")
                    .unwrap();
                Some(ptr_val.into_pointer_value())
            }
            _ => None,
        }
    }

    fn emit_shadow_pop(&mut self) {
        let Some(shadow) = &self.shadow else {
            return;
        };
        let ptr_ty = self.context.ptr_type(AddressSpace::default());
        let pop_ty = self.context.void_type().fn_type(&[ptr_ty.into()], false);
        let pop_fn = self
            .module
            .get_function("__rt__gc_pop_frame")
            .unwrap_or_else(|| {
                self.module
                    .add_function("__rt__gc_pop_frame", pop_ty, Some(Linkage::External))
            });
        let _ = self
            .builder
            .build_call(pop_fn, &[shadow.frame_ptr.into()], "gc_pop")
            .unwrap();
    }

    fn lower_statement(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        stmt: &mir::Statement<'gcx>,
    ) -> CompileResult<()> {
        match &stmt.kind {
            mir::StatementKind::Assign(place, rvalue) => {
                let dest_ty = body.locals[place.local].ty;
                if let Some(value) = self.lower_rvalue(body, locals, dest_ty, rvalue)? {
                    self.store_place(place, body, locals, value)?;
                }
            }
            mir::StatementKind::Nop => {}
        }
        Ok(())
    }

    fn lower_rvalue(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        dest_ty: Ty<'gcx>,
        rvalue: &mir::Rvalue<'gcx>,
    ) -> CompileResult<Option<BasicValueEnum<'llvm>>> {
        let value = match rvalue {
            mir::Rvalue::Use(op) => self.eval_operand(body, locals, op)?,
            mir::Rvalue::UnaryOp { operand, op } => {
                let operand = match self.eval_operand(body, locals, operand)? {
                    Some(val) => val,
                    None => return Ok(None),
                };
                Some(self.lower_unary(dest_ty, *op, operand))
            }
            mir::Rvalue::BinaryOp { lhs, rhs, op } => {
                let lhs_ty = self.operand_ty(body, lhs);
                let lhs = match self.eval_operand(body, locals, lhs)? {
                    Some(val) => val,
                    None => return Ok(None),
                };
                let rhs = match self.eval_operand(body, locals, rhs)? {
                    Some(val) => val,
                    None => return Ok(None),
                };
                self.lower_binary(lhs_ty, *op, lhs, rhs)
            }
            mir::Rvalue::Cast { operand, ty } => {
                let from_ty = self.operand_ty(body, operand);
                let val = match self.eval_operand(body, locals, operand)? {
                    Some(val) => val,
                    None => return Ok(None),
                };
                self.lower_cast(from_ty, *ty, val)
            }
            mir::Rvalue::Ref { place, .. } => {
                // Produce the address of the place.
                let ptr = self.project_place(place, body, locals)?;
                Some(ptr.as_basic_value_enum())
            }
            mir::Rvalue::Aggregate { .. } => unreachable!("aggregates should be lowered in MIR"),
            mir::Rvalue::Alloc { ty: alloc_ty } => {
                let llvm_payload_ty =
                    lower_type(self.context, self.gcx, &self.target_data, *alloc_ty)
                        .expect("alloc type");
                let size = self.target_data.get_store_size(&llvm_payload_ty);
                let size_const = self.usize_ty.const_int(size, false);
                let desc_ptr = self.gc_desc_for(*alloc_ty);
                let callee = self.get_gc_alloc();
                let call = self
                    .builder
                    .build_call(
                        callee,
                        &[
                            BasicMetadataValueEnum::from(size_const),
                            BasicMetadataValueEnum::from(desc_ptr),
                        ],
                        "gc_alloc",
                    )
                    .unwrap();
                let ptr_val = call
                    .try_as_basic_value()
                    .basic()
                    .expect("gc_alloc returned void")
                    .into_pointer_value();
                let cast = self
                    .builder
                    .build_bit_cast(
                        ptr_val,
                        self.context
                            .ptr_type(AddressSpace::default())
                            .as_basic_type_enum(),
                        "alloc_cast",
                    )
                    .unwrap();
                Some(cast)
            }
        };
        Ok(value)
    }

    fn lower_unary(
        &mut self,
        dest_ty: Ty<'gcx>,
        op: mir::UnaryOperator,
        operand: BasicValueEnum<'llvm>,
    ) -> BasicValueEnum<'llvm> {
        match op {
            mir::UnaryOperator::LogicalNot => {
                let val = operand.into_int_value();
                self.builder
                    .build_not(val, "bool_not")
                    .unwrap()
                    .as_basic_value_enum()
            }
            mir::UnaryOperator::Negate => match dest_ty.kind() {
                TyKind::Float(_) => {
                    let val = operand.into_float_value();
                    self.builder
                        .build_float_neg(val, "neg")
                        .unwrap()
                        .as_basic_value_enum()
                }
                _ => {
                    let val = operand.into_int_value();
                    self.builder
                        .build_int_neg(val, "neg")
                        .unwrap()
                        .as_basic_value_enum()
                }
            },
            mir::UnaryOperator::BitwiseNot => {
                let val = operand.into_int_value();
                self.builder
                    .build_not(val, "not")
                    .unwrap()
                    .as_basic_value_enum()
            }
        }
    }

    fn lower_binary(
        &mut self,
        operand_ty: Ty<'gcx>,
        op: mir::BinaryOperator,
        lhs: BasicValueEnum<'llvm>,
        rhs: BasicValueEnum<'llvm>,
    ) -> Option<BasicValueEnum<'llvm>> {
        let result = match operand_ty.kind() {
            TyKind::Float(_) => {
                let lhs = lhs.into_float_value();
                let rhs = rhs.into_float_value();
                match op {
                    mir::BinaryOperator::Add => self
                        .builder
                        .build_float_add(lhs, rhs, "add")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Sub => self
                        .builder
                        .build_float_sub(lhs, rhs, "sub")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Mul => self
                        .builder
                        .build_float_mul(lhs, rhs, "mul")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Div => self
                        .builder
                        .build_float_div(lhs, rhs, "div")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Rem => self
                        .builder
                        .build_float_rem(lhs, rhs, "rem")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Eql => self
                        .builder
                        .build_float_compare(FloatPredicate::OEQ, lhs, rhs, "eq")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Neq => self
                        .builder
                        .build_float_compare(FloatPredicate::UNE, lhs, rhs, "neq")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Gt => self
                        .builder
                        .build_float_compare(FloatPredicate::OGT, lhs, rhs, "gt")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Lt => self
                        .builder
                        .build_float_compare(FloatPredicate::OLT, lhs, rhs, "lt")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Geq => self
                        .builder
                        .build_float_compare(FloatPredicate::OGE, lhs, rhs, "ge")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Leq => self
                        .builder
                        .build_float_compare(FloatPredicate::OLE, lhs, rhs, "le")
                        .unwrap()
                        .as_basic_value_enum(),
                    _ => return None,
                }
            }
            TyKind::Bool => {
                let lhs = lhs.into_int_value();
                let rhs = rhs.into_int_value();
                match op {
                    mir::BinaryOperator::BitAnd => self
                        .builder
                        .build_and(lhs, rhs, "and")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::BitOr => self
                        .builder
                        .build_or(lhs, rhs, "or")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::BitXor => self
                        .builder
                        .build_xor(lhs, rhs, "xor")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Eql => self
                        .builder
                        .build_int_compare(IntPredicate::EQ, lhs, rhs, "eq")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Neq => self
                        .builder
                        .build_int_compare(IntPredicate::NE, lhs, rhs, "neq")
                        .unwrap()
                        .as_basic_value_enum(),
                    _ => return None,
                }
            }
            TyKind::Pointer(..) | TyKind::Reference(..) | TyKind::GcPtr => {
                let lhs_ptr = lhs.into_pointer_value();
                let rhs_ptr = rhs.into_pointer_value();
                let ptr_int_ty = self.context.i64_type();
                let lhs = self
                    .builder
                    .build_ptr_to_int(lhs_ptr, ptr_int_ty, "ptr_l")
                    .unwrap();
                let rhs = self
                    .builder
                    .build_ptr_to_int(rhs_ptr, ptr_int_ty, "ptr_r")
                    .unwrap();
                match op {
                    mir::BinaryOperator::Eql => self
                        .builder
                        .build_int_compare(IntPredicate::EQ, lhs, rhs, "ptr_eq")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Neq => self
                        .builder
                        .build_int_compare(IntPredicate::NE, lhs, rhs, "ptr_neq")
                        .unwrap()
                        .as_basic_value_enum(),
                    _ => return None,
                }
            }
            TyKind::Int(_) | TyKind::UInt(_) | TyKind::Rune => {
                let lhs = lhs.into_int_value();
                let rhs = rhs.into_int_value();
                let signed = is_signed(operand_ty);
                match op {
                    mir::BinaryOperator::Add => self
                        .builder
                        .build_int_add(lhs, rhs, "add")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Sub => self
                        .builder
                        .build_int_sub(lhs, rhs, "sub")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Mul => self
                        .builder
                        .build_int_mul(lhs, rhs, "mul")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Div => {
                        if signed {
                            self.builder
                                .build_int_signed_div(lhs, rhs, "div")
                                .unwrap()
                                .as_basic_value_enum()
                        } else {
                            self.builder
                                .build_int_unsigned_div(lhs, rhs, "div")
                                .unwrap()
                                .as_basic_value_enum()
                        }
                    }
                    mir::BinaryOperator::Rem => {
                        if signed {
                            self.builder
                                .build_int_signed_rem(lhs, rhs, "rem")
                                .unwrap()
                                .as_basic_value_enum()
                        } else {
                            self.builder
                                .build_int_unsigned_rem(lhs, rhs, "rem")
                                .unwrap()
                                .as_basic_value_enum()
                        }
                    }
                    mir::BinaryOperator::BitAnd => self
                        .builder
                        .build_and(lhs, rhs, "and")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::BitOr => self
                        .builder
                        .build_or(lhs, rhs, "or")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::BitXor => self
                        .builder
                        .build_xor(lhs, rhs, "xor")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::BitShl => self
                        .builder
                        .build_left_shift(lhs, rhs, "shl")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::BitShr => self
                        .builder
                        .build_right_shift(lhs, rhs, signed, "shr")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Eql => self
                        .builder
                        .build_int_compare(IntPredicate::EQ, lhs, rhs, "eq")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Neq => self
                        .builder
                        .build_int_compare(IntPredicate::NE, lhs, rhs, "neq")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Gt => self
                        .builder
                        .build_int_compare(
                            if signed {
                                IntPredicate::SGT
                            } else {
                                IntPredicate::UGT
                            },
                            lhs,
                            rhs,
                            "gt",
                        )
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Lt => self
                        .builder
                        .build_int_compare(
                            if signed {
                                IntPredicate::SLT
                            } else {
                                IntPredicate::ULT
                            },
                            lhs,
                            rhs,
                            "lt",
                        )
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Geq => self
                        .builder
                        .build_int_compare(
                            if signed {
                                IntPredicate::SGE
                            } else {
                                IntPredicate::UGE
                            },
                            lhs,
                            rhs,
                            "ge",
                        )
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Leq => self
                        .builder
                        .build_int_compare(
                            if signed {
                                IntPredicate::SLE
                            } else {
                                IntPredicate::ULE
                            },
                            lhs,
                            rhs,
                            "le",
                        )
                        .unwrap()
                        .as_basic_value_enum(),
                }
            }
            _ => return None,
        };
        Some(result)
    }

    fn lower_cast(
        &mut self,
        from_ty: Ty<'gcx>,
        to_ty: Ty<'gcx>,
        value: BasicValueEnum<'llvm>,
    ) -> Option<BasicValueEnum<'llvm>> {
        if from_ty == to_ty {
            return Some(value);
        }

        if let (Some((_, _)), Some((to_int, to_signed))) =
            (self.int_type(from_ty), self.int_type(to_ty))
        {
            return Some(
                self.builder
                    .build_int_cast_sign_flag(value.into_int_value(), to_int, to_signed, "int_cast")
                    .unwrap()
                    .as_basic_value_enum(),
            );
        }

        if let (Some(_), Some(to_float)) = (self.int_type(from_ty), self.float_type(to_ty)) {
            let signed = is_signed(from_ty);
            return Some(
                if signed {
                    self.builder
                        .build_signed_int_to_float(value.into_int_value(), to_float, "itof")
                        .unwrap()
                } else {
                    self.builder
                        .build_unsigned_int_to_float(value.into_int_value(), to_float, "itof")
                        .unwrap()
                }
                .as_basic_value_enum(),
            );
        }

        if let (Some(_), Some((to_int, to_signed))) =
            (self.float_type(from_ty), self.int_type(to_ty))
        {
            return Some(
                if to_signed {
                    self.builder
                        .build_float_to_signed_int(value.into_float_value(), to_int, "ftoi")
                        .unwrap()
                } else {
                    self.builder
                        .build_float_to_unsigned_int(value.into_float_value(), to_int, "ftoi")
                        .unwrap()
                }
                .as_basic_value_enum(),
            );
        }

        if let (Some(_), Some(to_float)) = (self.float_type(from_ty), self.float_type(to_ty)) {
            let val = value.into_float_value();
            return Some(
                self.builder
                    .build_float_cast(val, to_float, "fcast")
                    .unwrap()
                    .as_basic_value_enum(),
            );
        }

        if matches!(
            to_ty.kind(),
            TyKind::Pointer(..) | TyKind::Reference(..) | TyKind::GcPtr
        ) {
            return Some(
                self.builder
                    .build_bit_cast(
                        value,
                        self.context
                            .ptr_type(AddressSpace::default())
                            .as_basic_type_enum(),
                        "ptrcast",
                    )
                    .unwrap()
                    .into(),
            );
        }

        None
    }

    fn lower_terminator(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        terminator: &mir::Terminator<'gcx>,
        blocks: &[inkwell::basic_block::BasicBlock<'llvm>],
    ) -> CompileResult<()> {
        match &terminator.kind {
            mir::TerminatorKind::Goto { target } => {
                let _ = self
                    .builder
                    .build_unconditional_branch(blocks[target.index()])
                    .unwrap();
            }
            mir::TerminatorKind::UnresolvedGoto => {
                unreachable!("unresolved terminator should be patched before codegen");
            }
            mir::TerminatorKind::SwitchInt {
                discr,
                targets,
                otherwise,
            } => {
                let Some(value) = self.eval_operand(body, locals, discr)? else {
                    let _ = self.builder.build_unreachable().unwrap();
                    return Ok(());
                };
                let discr_val = value.into_int_value();
                let default_bb = blocks[otherwise.index()];

                let cases: Vec<(inkwell::values::IntValue<'llvm>, _)> = targets
                    .iter()
                    .map(|(const_val, bb)| {
                        (
                            discr_val.get_type().const_int(*const_val as u64, false),
                            blocks[bb.index()],
                        )
                    })
                    .collect();
                let _ = self
                    .builder
                    .build_switch(discr_val, default_bb, &cases)
                    .unwrap();
            }
            mir::TerminatorKind::Return => {
                self.emit_shadow_pop();
                let ret_place = mir::Place {
                    local: body.return_local,
                    projection: vec![],
                };
                match self.load_place(body, locals, &ret_place) {
                    Some(val) => {
                        let _ = self.builder.build_return(Some(&val)).unwrap();
                    }
                    None => {
                        let _ = self.builder.build_return(None).unwrap();
                    }
                }
            }
            mir::TerminatorKind::Unreachable => {
                let _ = self.builder.build_unreachable().unwrap();
            }
            mir::TerminatorKind::Call {
                func,
                args,
                destination,
                target,
            } => {
                let callable = self.lower_callable(func);

                let mut lowered_args = Vec::with_capacity(args.len());
                for arg in args {
                    if let Some(val) = self.eval_operand(body, locals, arg)? {
                        lowered_args.push(BasicMetadataValueEnum::from(val));
                    }
                }

                let call_site = self
                    .builder
                    .build_call(callable, &lowered_args, "call")
                    .unwrap();

                if let Some(ret) = call_site.try_as_basic_value().basic() {
                    self.store_local(destination.local, locals, ret, body);
                }
                let _ = self
                    .builder
                    .build_unconditional_branch(blocks[target.index()])
                    .unwrap();
            }
        }
        Ok(())
    }

    fn lower_callable(&mut self, func: &Operand<'gcx>) -> FunctionValue<'llvm> {
        if let Operand::Constant(c) = func {
            if let mir::ConstantKind::Function(def_id, _) = c.value {
                if let Some(&f) = self.functions.get(&def_id) {
                    return f;
                }

                if self.is_foreign_function(def_id) {
                    let f = self.declare_foreign_function(def_id);
                    self.functions.insert(def_id, f);
                    return f;
                }

                // Not declared yet (likely from another package); declare as external.
                let sig = self.gcx.get_signature(def_id);
                let fn_ty = lower_fn_sig(self.context, self.gcx, &self.target_data, sig);
                let name = mangle(self.gcx, def_id);
                let linkage = Some(Linkage::External);
                let f = self.module.add_function(&name, fn_ty, linkage);
                self.functions.insert(def_id, f);
                return f;
            }
        }

        self.functions
            .values()
            .copied()
            .next()
            .expect("at least one function")
    }

    fn is_foreign_function(&self, id: hir::DefinitionID) -> bool {
        self.gcx.get_signature(id).abi.is_some()
    }

    fn declare_foreign_function(&self, id: hir::DefinitionID) -> FunctionValue<'llvm> {
        let sig = self.gcx.get_signature(id);
        let fn_ty = lower_fn_sig(self.context, self.gcx, &self.target_data, sig);
        let ident = self.gcx.definition_ident(id);
        let name = ident.symbol.as_str();
        self.module.get_function(name).unwrap_or_else(|| {
            self.module
                .add_function(name, fn_ty, Some(Linkage::External))
        })
    }

    fn eval_operand(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &[LocalStorage<'llvm>],
        op: &mir::Operand<'gcx>,
    ) -> CompileResult<Option<BasicValueEnum<'llvm>>> {
        let value = match op {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                self.load_place(body, locals, place)
            }
            mir::Operand::Constant(c) => self.lower_constant(c),
        };
        Ok(value)
    }

    fn load_place(
        &self,
        body: &mir::Body<'gcx>,
        locals: &[LocalStorage<'llvm>],
        place: &mir::Place<'gcx>,
    ) -> Option<BasicValueEnum<'llvm>> {
        let place_ty = self.place_ty(body, place);
        if place.projection.is_empty() {
            return match locals[place.local.index()] {
                LocalStorage::Value(Some(v)) => Some(v),
                LocalStorage::Value(None) => None,
                LocalStorage::Stack(ptr) => {
                    let ty = lower_type(self.context, self.gcx, &self.target_data, place_ty)?;
                    Some(self.builder.build_load(ty, ptr, "load").unwrap())
                }
            };
        }

        let ptr = self.project_place(place, body, locals);
        match ptr {
            Ok(ptr) => {
                let elem_ty = lower_type(self.context, self.gcx, &self.target_data, place_ty)?;
                Some(self.builder.build_load(elem_ty, ptr, "load").unwrap())
            }
            Err(_) => None,
        }
    }

    fn store_local(
        &mut self,
        local: mir::LocalId,
        locals: &mut [LocalStorage<'llvm>],
        value: BasicValueEnum<'llvm>,
        body: &mir::Body<'gcx>,
    ) {
        match locals[local.index()] {
            LocalStorage::Value(_) => {
                locals[local.index()] = LocalStorage::Value(Some(value));
            }
            LocalStorage::Stack(ptr) => {
                if lower_type(
                    self.context,
                    self.gcx,
                    &self.target_data,
                    body.locals[local].ty,
                )
                .is_some()
                {
                    let _ = self.builder.build_store(ptr, value).unwrap();
                }
            }
        }

        let _ = self.update_shadow_for_local(body, locals, local);
    }

    fn store_place(
        &mut self,
        place: &mir::Place<'gcx>,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        value: BasicValueEnum<'llvm>,
    ) -> CompileResult<()> {
        if place.projection.is_empty() {
            self.store_local(place.local, locals, value, body);
            return Ok(());
        }

        let ptr = self.project_place(place, body, locals)?;
        self.builder.build_store(ptr, value).unwrap();
        if !place
            .projection
            .iter()
            .any(|p| matches!(p, mir::PlaceElem::Deref))
        {
            let _ = self.update_shadow_for_local(body, locals, place.local);
        }
        Ok(())
    }

    fn project_place(
        &self,
        place: &mir::Place<'gcx>,
        body: &mir::Body<'gcx>,
        locals: &[LocalStorage<'llvm>],
    ) -> CompileResult<PointerValue<'llvm>> {
        let mut ptr = match locals[place.local.index()] {
            LocalStorage::Stack(p) => p,
            LocalStorage::Value(Some(val)) => match val {
                BasicValueEnum::PointerValue(p) => p,
                _ => panic!("projection on non-pointer local"),
            },
            LocalStorage::Value(None) => {
                panic!("use of uninitialized local");
            }
        };

        // If the pointer comes from a stack slot, we need to load it to follow
        // the deref. Once we have a pointer value, further derefs load from
        // that address if needed.
        let mut ptr_is_storage = matches!(locals[place.local.index()], LocalStorage::Stack(_));
        let mut ty = body.locals[place.local].ty;

        for elem in &place.projection {
            match elem {
                mir::PlaceElem::Deref => {
                    if ptr_is_storage {
                        let ptr_ty = self
                            .context
                            .ptr_type(AddressSpace::default())
                            .as_basic_type_enum();
                        let loaded = self.builder.build_load(ptr_ty, ptr, "deref").unwrap();
                        ptr = loaded.into_pointer_value();
                    }
                    ptr_is_storage = true;
                    if let TyKind::Pointer(inner, _) | TyKind::Reference(inner, _) = ty.kind() {
                        ty = inner;
                    }
                }
                mir::PlaceElem::Field(idx, field_ty) => {
                    // Compute pointer to the requested field.
                    let agg_ty = lower_type(self.context, self.gcx, &self.target_data, ty)
                        .expect("aggregate type lowered");
                    let struct_ty = match agg_ty {
                        BasicTypeEnum::StructType(st) => st,
                        _ => panic!(
                            "field projection on non-struct type {}",
                            ty.format(self.gcx)
                        ),
                    };

                    let gep = self
                        .builder
                        .build_struct_gep(struct_ty, ptr, idx.index() as u32, "field_ptr")
                        .unwrap();
                    ptr = gep;
                    ptr_is_storage = true;
                    ty = *field_ty;
                }
            }
        }

        Ok(ptr)
    }

    fn place_ty<'a>(&self, body: &'a mir::Body<'gcx>, place: &mir::Place<'gcx>) -> Ty<'gcx> {
        let mut ty = body.locals[place.local].ty;
        for elem in &place.projection {
            match elem {
                mir::PlaceElem::Deref => {
                    if let TyKind::Pointer(inner, _) | TyKind::Reference(inner, _) = ty.kind() {
                        ty = inner;
                    }
                }
                mir::PlaceElem::Field(_, field_ty) => {
                    ty = *field_ty;
                }
            }
        }
        ty
    }

    fn lower_constant(&mut self, constant: &mir::Constant<'gcx>) -> Option<BasicValueEnum<'llvm>> {
        match constant.value {
            mir::ConstantKind::Bool(b) => Some(
                self.context
                    .bool_type()
                    .const_int(b as u64, false)
                    .as_basic_value_enum(),
            ),
            mir::ConstantKind::Rune(r) => Some(
                self.context
                    .i32_type()
                    .const_int(r as u64, false)
                    .as_basic_value_enum(),
            ),
            mir::ConstantKind::String(sym) => {
                let ptr = self.lower_string(sym);
                let len = self.usize_ty.const_int(sym.as_str().len() as u64, false);
                let Some(ty) = lower_type(self.context, self.gcx, &self.target_data, constant.ty)
                else {
                    return None;
                };
                let string_ty = ty.into_struct_type();
                let value = string_ty
                    .const_named_struct(&[ptr.as_basic_value_enum(), len.as_basic_value_enum()]);
                Some(value.as_basic_value_enum())
            }
            mir::ConstantKind::Integer(i) => self
                .int_type(constant.ty)
                .map(|(ty, _)| ty.const_int(i, false).as_basic_value_enum()),
            mir::ConstantKind::Float(f) => self
                .float_type(constant.ty)
                .map(|ty| ty.const_float(f).as_basic_value_enum()),
            mir::ConstantKind::Unit => None,
            mir::ConstantKind::Function(def_id, _) => self
                .functions
                .get(&def_id)
                .map(|f| f.as_global_value().as_pointer_value().as_basic_value_enum()),
        }
    }

    fn lower_string(&mut self, sym: Symbol) -> PointerValue<'llvm> {
        if let Some(ptr) = self.strings.get(&sym) {
            return *ptr;
        }
        let gv = self
            .builder
            .build_global_string_ptr(sym.as_str(), "str")
            .unwrap();
        let ptr = gv.as_pointer_value();
        let _ = self.strings.insert(sym, ptr);
        ptr
    }

    fn operand_ty(&self, body: &mir::Body<'gcx>, operand: &mir::Operand<'gcx>) -> Ty<'gcx> {
        match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => body.locals[place.local].ty,
            mir::Operand::Constant(c) => c.ty,
        }
    }

    fn int_type(&self, ty: Ty<'gcx>) -> Option<(IntType<'llvm>, bool)> {
        match ty.kind() {
            TyKind::Bool => Some((self.context.bool_type(), false)),
            TyKind::Rune => Some((self.context.i32_type(), true)),
            TyKind::Int(i) => Some((int_from_kind(self.context, &self.target_data, i), true)),
            TyKind::UInt(u) => Some((uint_from_kind(self.context, &self.target_data, u), false)),
            _ => None,
        }
    }

    fn float_type(&self, ty: Ty<'gcx>) -> Option<FloatType<'llvm>> {
        match ty.kind() {
            TyKind::Float(FloatTy::F32) => Some(self.context.f32_type()),
            TyKind::Float(FloatTy::F64) => Some(self.context.f64_type()),
            _ => None,
        }
    }

    fn get_gc_alloc(&self) -> FunctionValue<'llvm> {
        if let Some(f) = self.module.get_function("gc_alloc") {
            return f;
        }
        let opaque_ptr = self.context.ptr_type(AddressSpace::default());
        let gc_desc_ptr = opaque_ptr;
        let fn_ty = self
            .context
            .ptr_type(AddressSpace::default())
            .fn_type(&[self.usize_ty.into(), gc_desc_ptr.into()], false);
        self.module
            .add_function("gc_alloc", fn_ty, Some(Linkage::External))
    }

    fn gc_desc_for(&mut self, ty: Ty<'gcx>) -> PointerValue<'llvm> {
        if let Some(&gv) = self.gc_descs.get(&ty) {
            return gv;
        }

        let llvm_ty =
            lower_type(self.context, self.gcx, &self.target_data, ty).expect("lower type");
        let size = self.target_data.get_store_size(&llvm_ty);
        let align = self.target_data.get_abi_alignment(&llvm_ty) as u64;

        // Collect pointer field offsets (only direct reference/string/GcPtr fields).
        let mut offsets: Vec<u64> = vec![];
        match ty.kind() {
            TyKind::Adt(def) => {
                let defn = self.gcx.get_struct_definition(def.id);
                for (idx, field) in defn.fields.iter().enumerate() {
                    if is_pointer_ty(field.ty) {
                        let struct_ty = llvm_ty.into_struct_type();
                        if let Some(off) =
                            self.target_data.offset_of_element(&struct_ty, idx as u32)
                        {
                            offsets.push(off);
                        }
                    }
                }
            }
            TyKind::Tuple(items) => {
                let struct_ty = llvm_ty.into_struct_type();
                for (idx, item) in items.iter().enumerate() {
                    if is_pointer_ty(*item) {
                        if let Some(off) =
                            self.target_data.offset_of_element(&struct_ty, idx as u32)
                        {
                            offsets.push(off);
                        }
                    }
                }
            }
            TyKind::String | TyKind::GcPtr | TyKind::Reference(..) => {
                offsets.push(0);
            }
            _ => {}
        }

        let ptr_offsets_ptr = if offsets.is_empty() {
            self.context
                .ptr_type(AddressSpace::default())
                .const_null()
                .as_basic_value_enum()
        } else {
            let arr_ty = self.usize_ty.array_type(offsets.len() as u32);
            let consts: Vec<_> = offsets
                .iter()
                .map(|o| self.usize_ty.const_int(*o, false))
                .collect();
            let arr_const = self.usize_ty.const_array(&consts);
            let global = self.module.add_global(
                arr_ty,
                None,
                &format!("__gc_offsets_{}", self.gc_descs.len()),
            );
            global.set_initializer(&arr_const);
            let ptr = global
                .as_pointer_value()
                .const_cast(self.context.ptr_type(AddressSpace::default()));
            ptr.as_basic_value_enum()
        };

        let desc_const = self.gc_desc_ty.const_named_struct(&[
            self.usize_ty.const_int(size, false).into(),
            self.usize_ty.const_int(align, false).into(),
            ptr_offsets_ptr,
            self.usize_ty.const_int(offsets.len() as u64, false).into(),
        ]);
        let gv = self.module.add_global(
            self.gc_desc_ty,
            None,
            &format!("__gc_desc_{}", self.gc_descs.len()),
        );
        gv.set_initializer(&desc_const);
        gv.set_constant(true);
        gv.set_linkage(Linkage::Internal);
        let ptr = gv.as_pointer_value();
        self.gc_descs.insert(ty, ptr);
        ptr
    }
}

fn is_pointer_ty(ty: Ty) -> bool {
    matches!(
        ty.kind(),
        TyKind::Reference(..) | TyKind::String | TyKind::GcPtr
    )
}

fn lower_fn_sig<'llvm>(
    context: &'llvm Context,
    gcx: Gcx<'_>,
    target_data: &TargetData,
    sig: &crate::sema::models::LabeledFunctionSignature,
) -> FunctionType<'llvm> {
    let params: Vec<BasicMetadataTypeEnum<'llvm>> = sig
        .inputs
        .iter()
        .filter_map(|p| lower_type(context, gcx, target_data, p.ty).map(|t| t.into()))
        .collect();
    match lower_type(context, gcx, target_data, sig.output) {
        Some(ret) => ret.fn_type(&params, sig.is_variadic),
        None => context.void_type().fn_type(&params, sig.is_variadic),
    }
}

fn lower_type<'llvm>(
    context: &'llvm Context,
    gcx: Gcx<'_>,
    target_data: &TargetData,
    ty: Ty,
) -> Option<BasicTypeEnum<'llvm>> {
    match ty.kind() {
        TyKind::Bool => Some(context.bool_type().into()),
        TyKind::Rune => Some(context.i32_type().into()),
        TyKind::String => Some(string_header_ty(context, target_data).into()),
        TyKind::GcPtr => Some(
            context
                .ptr_type(AddressSpace::default())
                .as_basic_type_enum(),
        ),
        TyKind::Int(i) => Some(int_from_kind(context, target_data, i).into()),
        TyKind::UInt(u) => Some(uint_from_kind(context, target_data, u).into()),
        TyKind::Float(f) => Some(match f {
            FloatTy::F32 => context.f32_type().into(),
            FloatTy::F64 => context.f64_type().into(),
        }),
        TyKind::Adt(def) => {
            let defn = gcx.get_struct_definition(def.id);
            let field_tys: Vec<BasicTypeEnum<'llvm>> = defn
                .fields
                .iter()
                .filter_map(|f| lower_type(context, gcx, target_data, f.ty))
                .collect();
            Some(context.struct_type(&field_tys, false).into())
        }
        TyKind::Pointer(..) | TyKind::Reference(..) => Some(
            context
                .ptr_type(AddressSpace::default())
                .as_basic_type_enum(),
        ),
        TyKind::Tuple(items) => {
            if items.is_empty() {
                None
            } else {
                let fields: Vec<BasicTypeEnum<'llvm>> = items
                    .iter()
                    .filter_map(|t| lower_type(context, gcx, target_data, *t))
                    .collect();
                Some(context.struct_type(&fields, false).into())
            }
        }
        TyKind::FnPointer { .. } => Some(
            context
                .ptr_type(AddressSpace::default())
                .as_basic_type_enum(),
        ),
        TyKind::Infer(_) | TyKind::Error => unreachable!(),
    }
}

fn string_header_ty<'llvm>(context: &'llvm Context, target_data: &TargetData) -> StructType<'llvm> {
    if let Some(ty) = context.get_struct_type("_stringHeader") {
        if ty.is_opaque() {
            let ptr_ty = context.ptr_type(AddressSpace::default());
            let len_ty = uint_from_kind(context, target_data, UIntTy::USize);
            ty.set_body(&[ptr_ty.into(), len_ty.into()], false);
        }
        return ty;
    }

    let ty = context.opaque_struct_type("_stringHeader");
    let ptr_ty = context.ptr_type(AddressSpace::default());
    let len_ty = uint_from_kind(context, target_data, UIntTy::USize);
    ty.set_body(&[ptr_ty.into(), len_ty.into()], false);
    ty
}

fn int_from_kind<'llvm>(
    context: &'llvm Context,
    target_data: &TargetData,
    ty: IntTy,
) -> IntType<'llvm> {
    match ty {
        IntTy::I8 => context.i8_type(),
        IntTy::I16 => context.i16_type(),
        IntTy::I32 => context.i32_type(),
        IntTy::I64 => context.i64_type(),
        IntTy::ISize => context.ptr_sized_int_type(target_data, None),
    }
}

fn uint_from_kind<'llvm>(
    context: &'llvm Context,
    target_data: &TargetData,
    ty: UIntTy,
) -> IntType<'llvm> {
    match ty {
        UIntTy::U8 => context.i8_type(),
        UIntTy::U16 => context.i16_type(),
        UIntTy::U32 => context.i32_type(),
        UIntTy::U64 => context.i64_type(),
        UIntTy::USize => context.ptr_sized_int_type(target_data, None),
    }
}

fn is_signed(ty: Ty) -> bool {
    matches!(ty.kind(), TyKind::Int(_) | TyKind::Rune)
}
