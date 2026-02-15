use crate::{
    codegen::mangle::mangle_instance,
    compile::context::{Gcx, GlobalContext},
    error::CompileResult,
    hir,
    mir::{self, Operand, Place},
    sema::{
        models::{
            ConstKind, ConstValue, FloatTy, GenericArgument, GenericArguments, IntTy,
            InterfaceDefinition, InterfaceReference, InterfaceRequirements, Ty, TyKind, UIntTy,
        },
        resolve::models::TypeHead,
        tycheck::resolve_conformance_witness,
        tycheck::utils::{
            instantiate::{instantiate_const_with_args, instantiate_ty_with_args},
            type_head_from_value_ty,
        },
    },
    span::Symbol,
    specialize::{Instance, InstanceKind, resolve_instance},
};
use inkwell::{
    AddressSpace, FloatPredicate, IntPredicate,
    builder::Builder,
    context::Context,
    module::{Linkage, Module},
    passes::PassManager,
    targets::{FileType, TargetData},
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

    // Use the shared target layout from CompilerStore.
    let target_layout = &gcx.store.target_layout;
    module.set_data_layout(&target_layout.data_layout());
    module.set_triple(&target_layout.triple());

    let mut emitter = Emitter::new(&context, module, builder, gcx);
    emitter.declare_instances();
    emitter.lower_instances(package)?;
    emitter.emit_start_shim(package);
    emitter.run_function_passes();

    // Dump LLVM IR if requested
    if gcx.config.debug.dump_llvm {
        eprintln!("\n=== LLVM IR for {} ===", gcx.config.name);
        let ir = emitter.module.print_to_string().to_string();
        eprintln!("{ir}");
        eprintln!("=== End LLVM Dump ===\n");
    }

    let obj = emitter.emit_object_file()?;
    gcx.cache_object_file(obj.clone());
    Ok(obj)
}

struct Emitter<'llvm, 'gcx> {
    context: &'llvm Context,
    module: Module<'llvm>,
    builder: Builder<'llvm>,
    gcx: GlobalContext<'gcx>,
    functions: FxHashMap<Instance<'gcx>, FunctionValue<'llvm>>,
    strings: FxHashMap<Symbol, PointerValue<'llvm>>,
    target_data: inkwell::targets::TargetData,
    gc_descs: FxHashMap<Ty<'gcx>, PointerValue<'llvm>>,
    witness_tables: FxHashMap<(TypeHead, InterfaceReference<'gcx>), PointerValue<'llvm>>,
    /// Cache for witness table thunks: (type_head, interface, impl_method_id) -> thunk_fn_ptr
    witness_thunks:
        FxHashMap<(TypeHead, InterfaceReference<'gcx>, hir::DefinitionID), PointerValue<'llvm>>,
    gc_desc_ty: inkwell::types::StructType<'llvm>,
    usize_ty: inkwell::types::IntType<'llvm>,
    shadow: Option<ShadowStackInfo<'llvm, 'gcx>>,
    /// Current substitution context for monomorphization
    current_subst: GenericArguments<'gcx>,
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
    EnumFieldOffset(u64),
}

impl<'llvm, 'gcx> Emitter<'llvm, 'gcx> {
    fn new(
        context: &'llvm Context,
        module: Module<'llvm>,
        builder: Builder<'llvm>,
        gcx: GlobalContext<'gcx>,
    ) -> Self {
        let target_data = gcx.store.target_layout.target_data();
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
            target_data,
            gc_descs: FxHashMap::default(),
            witness_tables: FxHashMap::default(),
            witness_thunks: FxHashMap::default(),
            gc_desc_ty,
            usize_ty,
            shadow: None,
            current_subst: &[],
        }
    }

    fn resolve_generic_args(&self, args: GenericArguments<'gcx>) -> GenericArguments<'gcx> {
        if self.current_subst.is_empty() || args.is_empty() {
            return args;
        }

        let resolved: Vec<_> = args
            .iter()
            .map(|arg| match arg {
                GenericArgument::Type(ty) => {
                    let instantiated = instantiate_ty_with_args(self.gcx, *ty, self.current_subst);
                    let normalized = crate::sema::tycheck::utils::normalize_post_monomorphization(
                        self.gcx,
                        instantiated,
                    );
                    GenericArgument::Type(normalized)
                }
                GenericArgument::Const(c) => {
                    let substituted = instantiate_const_with_args(self.gcx, *c, self.current_subst);
                    GenericArgument::Const(substituted)
                }
            })
            .collect();
        self.gcx.store.interners.intern_generic_args(resolved)
    }

    fn instance_for_call(
        &self,
        def_id: hir::DefinitionID,
        args: GenericArguments<'gcx>,
    ) -> Instance<'gcx> {
        let args = self.resolve_generic_args(args);
        resolve_instance(self.gcx, def_id, args)
    }

    /// Lower a type with substitution context applied.
    #[track_caller]
    fn lower_ty(&self, ty: Ty<'gcx>) -> Option<BasicTypeEnum<'llvm>> {
        lower_type(
            self.context,
            self.gcx,
            &self.target_data,
            ty,
            self.current_subst,
        )
    }

    /// Lower a function signature with substitution context applied.
    fn lower_fn_sig(
        &self,
        sig: &crate::sema::models::LabeledFunctionSignature<'gcx>,
    ) -> FunctionType<'llvm> {
        let params: Vec<BasicMetadataTypeEnum<'llvm>> = sig
            .inputs
            .iter()
            .filter_map(|p| self.lower_ty(p.ty).map(|t| t.into()))
            .collect();
        match self.lower_ty(sig.output) {
            Some(ret) => ret.fn_type(&params, sig.is_variadic),
            None => self.context.void_type().fn_type(&params, sig.is_variadic),
        }
    }

    fn declare_instances(&mut self) {
        let current_pkg = self.gcx.package_index();
        let instances = self.gcx.specializations_of(current_pkg);
        for instance in instances {
            let def_id = match instance.kind() {
                InstanceKind::Item(def_id) => def_id,
                InstanceKind::Virtual(_) => continue,
            };

            // Skip intrinsic functions - they are handled specially via try_lower_intrinsic_call
            // and don't need to be declared as regular functions.
            if matches!(
                self.gcx.get_signature(def_id).abi,
                Some(hir::Abi::Intrinsic)
            ) {
                continue;
            }

            // Set substitution context for this instance
            self.current_subst = instance.args();

            let sig = self.gcx.get_signature(def_id);
            let fn_ty = self.lower_fn_sig(sig);
            let name = mangle_instance(self.gcx, instance);

            let f = self.module.add_function(&name, fn_ty, None);
            self.functions.insert(instance, f);
        }
    }

    fn lower_instances(&mut self, _package: &mir::MirPackage<'gcx>) -> CompileResult<()> {
        let current_pkg = self.gcx.package_index();
        let instances = self.gcx.specializations_of(current_pkg);
        for instance in instances {
            // Skip if already compiled by another package
            if self.gcx.is_instance_compiled(instance) {
                continue;
            }

            let def_id = match instance.kind() {
                InstanceKind::Item(def_id) => def_id,
                InstanceKind::Virtual(_) => continue,
            };

            // Skip intrinsic functions - they are handled specially via try_lower_intrinsic_call
            // and don't have MIR bodies.
            if matches!(
                self.gcx.get_signature(def_id).abi,
                Some(hir::Abi::Intrinsic | hir::Abi::C)
            ) {
                continue;
            }

            let body = self.gcx.get_mir_body(def_id);
            self.lower_body(instance, body)?;

            // Mark as compiled so other packages don't duplicate work
            self.gcx.mark_instance_compiled(instance);
        }
        Ok(())
    }

    fn emit_start_shim(&mut self, package: &mir::MirPackage<'gcx>) {
        let Some(entry) = package.entry else {
            return;
        };
        // Entry point is always a concrete instance with no generic args
        let entry_instance = Instance::item(entry, &[]);
        let Some(&user_fn) = self.functions.get(&entry_instance) else {
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
            (TyKind::Pointer(..) | TyKind::Reference(..), Some(val)) => {
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
        let tm = self.gcx.store.target_layout.target_machine();
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
        instance: Instance<'gcx>,
        body: &mir::Body<'gcx>,
    ) -> CompileResult<()> {
        // Set substitution context for monomorphization
        self.current_subst = instance.args();

        let function = *self
            .functions
            .get(&instance)
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
            let storage = match self.lower_ty(decl.ty) {
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
                TyKind::Reference(..) | TyKind::String => {
                    local_slots.push(ShadowSlotKind::Local(ty));
                }
                TyKind::Adt(def, adt_args) => match def.kind {
                    crate::sema::models::AdtKind::Struct => {
                        let defn = self.gcx.get_struct_definition(def.id);
                        for (idx, field) in defn.fields.iter().enumerate() {
                            if is_pointer_ty(field.ty) {
                                let field_idx = crate::thir::FieldIndex::new(idx);
                                local_slots.push(ShadowSlotKind::Field(field_idx, field.ty));
                            }
                        }
                    }
                    crate::sema::models::AdtKind::Enum => {
                        let offsets = enum_pointer_offsets(
                            self.context,
                            self.gcx,
                            &self.target_data,
                            def.id,
                            adt_args,
                            self.current_subst,
                        );
                        for offset in offsets {
                            local_slots.push(ShadowSlotKind::EnumFieldOffset(offset));
                        }
                    }
                },
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
            match def.kind.clone() {
                ShadowSlotKind::Local(_) | ShadowSlotKind::Field(_, _) => {
                    let place = match def.kind.clone() {
                        ShadowSlotKind::Local(_) => mir::Place::from_local(def.local),
                        ShadowSlotKind::Field(field_idx, field_ty) => mir::Place {
                            local: def.local,
                            projection: vec![mir::PlaceElem::Field(field_idx, field_ty)],
                        },
                        ShadowSlotKind::EnumFieldOffset(_) => {
                            unreachable!("enum offsets handled separately")
                        }
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
                        ShadowSlotKind::EnumFieldOffset(_) => {
                            unreachable!("enum offsets handled separately")
                        }
                    };

                    let ptr_val = match self.shadow_ptr_from_value(slot_ty, value) {
                        Some(p) => p,
                        None => self.context.ptr_type(AddressSpace::default()).const_null(),
                    };
                    self.store_shadow_slot(slot_idx, ptr_val);
                }
                ShadowSlotKind::EnumFieldOffset(offset) => {
                    let ptr_val = match locals[def.local.index()] {
                        LocalStorage::Stack(ptr) => {
                            let i8_ptr_ty = self.context.ptr_type(AddressSpace::default());
                            let base = self
                                .builder
                                .build_bit_cast(ptr, i8_ptr_ty, "enum_base_i8")
                                .unwrap()
                                .into_pointer_value();
                            let offset_const = self.usize_ty.const_int(offset, false);
                            let field_ptr = unsafe {
                                self.builder
                                    .build_gep(
                                        self.context.i8_type(),
                                        base,
                                        &[offset_const],
                                        "enum_field_ptr",
                                    )
                                    .unwrap()
                            };
                            let ptr_ty = self.context.ptr_type(AddressSpace::default());
                            self.builder
                                .build_load(ptr_ty, field_ptr, "enum_ptr_load")
                                .unwrap()
                                .into_pointer_value()
                        }
                        LocalStorage::Value(_) => {
                            self.context.ptr_type(AddressSpace::default()).const_null()
                        }
                    };
                    self.store_shadow_slot(slot_idx, ptr_val);
                }
            }
        }

        Ok(())
    }

    fn shadow_ptr_from_value(
        &mut self,
        ty: Ty<'gcx>,
        value: BasicValueEnum<'llvm>,
    ) -> Option<PointerValue<'llvm>> {
        match ty.kind() {
            TyKind::Reference(..) => Some(value.into_pointer_value()),
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
            mir::StatementKind::GcSafepoint => {
                let callee = self.get_gc_poll();
                let _ = self.builder.build_call(callee, &[], "gc_poll").unwrap();
            }
            mir::StatementKind::SetDiscriminant {
                place,
                variant_index,
            } => {
                let ptr = self.project_place(place, body, locals)?;
                let place_ty = self.place_ty(body, place);
                let _def = match place_ty.kind() {
                    TyKind::Adt(def, _) if def.kind == crate::sema::models::AdtKind::Enum => def,
                    _ => panic!(
                        "set_discriminant on non-enum type {}",
                        place_ty.format(self.gcx)
                    ),
                };
                let enum_ty = self.lower_ty(place_ty).expect("enum");
                let enum_struct = enum_ty.into_struct_type();
                let discr_ptr = self
                    .builder
                    .build_struct_gep(enum_struct, ptr, 0, "enum_discr_ptr")
                    .unwrap();
                let discr_val = self.usize_ty.const_int(variant_index.index() as u64, false);
                let _ = self.builder.build_store(discr_ptr, discr_val).unwrap();
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
            mir::Rvalue::Cast { operand, ty, kind } => {
                let from_ty = self.operand_ty(body, operand);
                let val = match self.eval_operand(body, locals, operand)? {
                    Some(val) => val,
                    None => return Ok(None),
                };
                match kind {
                    mir::CastKind::Numeric => return Ok(self.lower_cast(from_ty, *ty, val)),
                    mir::CastKind::BoxExistential => {
                        let value = self.lower_boxed_existential(from_ty, *ty, val)?;
                        return Ok(Some(value));
                    }
                    mir::CastKind::ExistentialUpcast => {
                        let value = self.lower_existential_upcast(from_ty, *ty, val)?;
                        return Ok(Some(value));
                    }
                    mir::CastKind::Pointer => return Ok(self.lower_cast(from_ty, *ty, val)),
                    mir::CastKind::ClosureToFnPointer => {
                        let value = self.lower_closure_to_fn_pointer(from_ty, *ty)?;
                        return Ok(Some(value));
                    }
                }
            }
            mir::Rvalue::Ref { place, .. } => {
                // Produce the address of the place.
                let ptr = self.project_place(place, body, locals)?;
                Some(ptr.as_basic_value_enum())
            }
            mir::Rvalue::Discriminant { place } => {
                let ptr = self.project_place(place, body, locals)?;
                let place_ty = self.place_ty(body, place);
                let _def = match place_ty.kind() {
                    TyKind::Adt(def, _) if def.kind == crate::sema::models::AdtKind::Enum => def,
                    _ => panic!(
                        "ICE: discriminant on non-enum type {}",
                        place_ty.format(self.gcx)
                    ),
                };
                let enum_ty = self.lower_ty(place_ty).expect("enum");
                let enum_struct = enum_ty.into_struct_type();
                let discr_ptr = self
                    .builder
                    .build_struct_gep(enum_struct, ptr, 0, "enum_discr_ptr")
                    .unwrap();
                let discr_val = self
                    .builder
                    .build_load(self.usize_ty, discr_ptr, "enum_discr")
                    .unwrap();
                Some(discr_val.as_basic_value_enum())
            }
            mir::Rvalue::Aggregate { kind, fields } => match kind {
                mir::AggregateKind::Array { .. } => {
                    let llvm_ty = self
                        .lower_ty(dest_ty)
                        .expect("array aggregate destination type");
                    let arr_ty = llvm_ty.into_array_type();
                    let mut agg = arr_ty.get_undef();
                    for (idx, field) in fields.iter_enumerated() {
                        let Some(val) = self.eval_operand(body, locals, field)? else {
                            return Ok(None);
                        };
                        let insert_idx =
                            u32::try_from(idx.index()).expect("array element index fits in u32");
                        let insert = self
                            .builder
                            .build_insert_value(agg, val, insert_idx, "array_ins")
                            .unwrap();
                        agg = insert.into_array_value();
                    }
                    Some(agg.as_basic_value_enum())
                }
                _ => unreachable!("non-array aggregates should be lowered in MIR"),
            },
            mir::Rvalue::Repeat { operand, count, .. } => {
                let arr_ty = match self.lower_ty(dest_ty) {
                    Some(ty) => ty.into_array_type(),
                    None => return Ok(None),
                };
                let Some(val) = self.eval_operand(body, locals, operand)? else {
                    return Ok(None);
                };
                // Build the array by inserting the repeated value at each index.
                // For small arrays, LLVM optimizes this well. For very large arrays,
                // a memory-based approach with memset/loop could be more efficient,
                // but would require restructuring the rvalue lowering to store directly.
                let mut agg = arr_ty.get_undef();
                for i in 0..*count {
                    let insert_idx =
                        u32::try_from(i).expect("repeat count should fit in u32 for LLVM array");
                    let insert = self
                        .builder
                        .build_insert_value(agg, val, insert_idx, "repeat_ins")
                        .unwrap();
                    agg = insert.into_array_value();
                }
                Some(agg.as_basic_value_enum())
            }
            mir::Rvalue::Alloc { ty: alloc_ty } => {
                let llvm_payload_ty = self.lower_ty(*alloc_ty).expect("alloc type");
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
            TyKind::Pointer(..) | TyKind::Reference(..) => {
                let ptr_int_ty = self.context.ptr_sized_int_type(&self.target_data, None);
                let lhs = match lhs {
                    BasicValueEnum::PointerValue(ptr) => self
                        .builder
                        .build_ptr_to_int(ptr, ptr_int_ty, "ptr_l")
                        .unwrap(),
                    BasicValueEnum::IntValue(val) => {
                        if val.get_type() == ptr_int_ty {
                            val
                        } else {
                            self.builder
                                .build_int_cast(val, ptr_int_ty, "ptr_l_cast")
                                .unwrap()
                        }
                    }
                    _ => return None,
                };
                let rhs = match rhs {
                    BasicValueEnum::PointerValue(ptr) => self
                        .builder
                        .build_ptr_to_int(ptr, ptr_int_ty, "ptr_r")
                        .unwrap(),
                    BasicValueEnum::IntValue(val) => {
                        if val.get_type() == ptr_int_ty {
                            val
                        } else {
                            self.builder
                                .build_int_cast(val, ptr_int_ty, "ptr_r_cast")
                                .unwrap()
                        }
                    }
                    _ => return None,
                };
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

        if matches!(to_ty.kind(), TyKind::Pointer(..) | TyKind::Reference(..)) {
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

    fn lower_boxed_existential(
        &mut self,
        from_ty: Ty<'gcx>,
        to_ty: Ty<'gcx>,
        value: BasicValueEnum<'llvm>,
    ) -> CompileResult<BasicValueEnum<'llvm>> {
        let TyKind::BoxedExistential { interfaces } = to_ty.kind() else {
            return Ok(value);
        };

        let data_ptr = self.box_value(from_ty, value)?;
        let mut table_ptrs = Vec::with_capacity(interfaces.len());
        for iface in interfaces.iter().copied() {
            let ptr = self.witness_table_ptr(from_ty, iface);
            table_ptrs.push(ptr);
        }

        Ok(self.build_existential_value(to_ty, data_ptr, &table_ptrs))
    }

    fn lower_existential_upcast(
        &mut self,
        from_ty: Ty<'gcx>,
        to_ty: Ty<'gcx>,
        value: BasicValueEnum<'llvm>,
    ) -> CompileResult<BasicValueEnum<'llvm>> {
        let TyKind::BoxedExistential {
            interfaces: from_ifaces,
        } = from_ty.kind()
        else {
            return Ok(value);
        };
        let TyKind::BoxedExistential {
            interfaces: to_ifaces,
        } = to_ty.kind()
        else {
            return Ok(value);
        };

        let src = value.into_struct_value();
        let data_ptr = self
            .builder
            .build_extract_value(src, 0, "exist_data")
            .unwrap()
            .into_pointer_value();

        let mut table_ptrs = Vec::with_capacity(to_ifaces.len());
        for target in to_ifaces.iter().copied() {
            if let Some(index) = self.interface_index(from_ifaces, target.id) {
                let ptr = self
                    .builder
                    .build_extract_value(src, (index + 1) as u32, "exist_table")
                    .unwrap()
                    .into_pointer_value();
                table_ptrs.push(ptr);
                continue;
            }

            if let Some((root_index, chain)) =
                self.superface_chain_from_root(from_ifaces, target.id)
            {
                let mut current_ptr = self
                    .builder
                    .build_extract_value(src, (root_index + 1) as u32, "exist_root_table")
                    .unwrap()
                    .into_pointer_value();
                for (current_iface, super_index) in chain {
                    let table_ty = self.witness_table_struct_ty(current_iface);
                    let table_ptr_ty = self.context.ptr_type(AddressSpace::default());
                    let typed_ptr = self
                        .builder
                        .build_bit_cast(current_ptr, table_ptr_ty, "wt_cast")
                        .unwrap()
                        .into_pointer_value();
                    let field_index = self.interface_method_count(current_iface) + super_index;
                    let field_ptr = self
                        .builder
                        .build_struct_gep(table_ty, typed_ptr, field_index as u32, "wt_super_ptr")
                        .unwrap();
                    current_ptr = self
                        .builder
                        .build_load(
                            self.context.ptr_type(AddressSpace::default()),
                            field_ptr,
                            "wt_super_load",
                        )
                        .unwrap()
                        .into_pointer_value();
                }
                table_ptrs.push(current_ptr);
                continue;
            }

            table_ptrs.push(self.context.ptr_type(AddressSpace::default()).const_null());
        }

        Ok(self.build_existential_value(to_ty, data_ptr, &table_ptrs))
    }

    /// Coerce a non-capturing closure to a function pointer.
    /// This generates a shim function that calls the closure body with a null self pointer.
    fn lower_closure_to_fn_pointer(
        &mut self,
        from_ty: Ty<'gcx>,
        to_ty: Ty<'gcx>,
    ) -> CompileResult<BasicValueEnum<'llvm>> {
        let TyKind::Closure { closure_def_id, .. } = from_ty.kind() else {
            panic!("ICE: closure to fn pointer cast on non-closure type");
        };

        let TyKind::FnPointer { inputs, output } = to_ty.kind() else {
            panic!("ICE: closure to fn pointer cast to non-fn-pointer type");
        };

        // Generate a unique name for the shim
        let shim_name = format!(
            "{}_fn_shim",
            mangle_instance(self.gcx, Instance::item(closure_def_id, &[]))
        );

        // Check if we've already generated this shim
        if let Some(existing) = self.module.get_function(&shim_name) {
            return Ok(existing.as_global_value().as_pointer_value().into());
        }

        // Get the closure body function
        let closure_instance = Instance::item(closure_def_id, &[]);
        let closure_fn = if let Some(&f) = self.functions.get(&closure_instance) {
            f
        } else {
            // Declare the closure body function
            let prev_subst = self.current_subst;
            self.current_subst = &[];
            let sig = self.gcx.get_signature(closure_def_id);
            let fn_ty = self.lower_fn_sig(sig);
            let name = mangle_instance(self.gcx, closure_instance);
            let f = self
                .module
                .add_function(&name, fn_ty, Some(Linkage::External));
            self.functions.insert(closure_instance, f);
            self.current_subst = prev_subst;
            f
        };

        // Build the shim function type (without self parameter)
        let mut param_types: Vec<BasicMetadataTypeEnum> = Vec::new();
        for &input_ty in inputs.iter() {
            if let Some(llvm_ty) = self.lower_ty(input_ty) {
                param_types.push(llvm_ty.into());
            }
        }
        let ret_ty = self.lower_ty(output);
        let shim_fn_ty = match ret_ty {
            Some(ret) => ret.fn_type(&param_types, false),
            None => self.context.void_type().fn_type(&param_types, false),
        };

        // Create the shim function
        let shim_fn = self
            .module
            .add_function(&shim_name, shim_fn_ty, Some(Linkage::Internal));
        let entry_bb = self.context.append_basic_block(shim_fn, "entry");

        // Save current builder position
        let saved_bb = self.builder.get_insert_block();

        // Build the shim body
        self.builder.position_at_end(entry_bb);

        // Create null self pointer (closure has no captures)
        let self_param_ty = closure_fn.get_type().get_param_types().first().copied();
        let null_self = match self_param_ty {
            Some(BasicMetadataTypeEnum::PointerType(ptr_ty)) => ptr_ty.const_null(),
            _ => self.context.ptr_type(AddressSpace::default()).const_null(),
        };

        // Build arguments: null self + forwarded params
        let mut call_args: Vec<BasicMetadataValueEnum> = vec![null_self.into()];
        for (i, _) in inputs.iter().enumerate() {
            call_args.push(shim_fn.get_nth_param(i as u32).unwrap().into());
        }

        // Call the closure body
        let call = self
            .builder
            .build_call(closure_fn, &call_args, "closure_call")
            .unwrap();

        // Return the result
        if ret_ty.is_some() {
            let ret_val = call.try_as_basic_value().basic().unwrap();
            self.builder.build_return(Some(&ret_val)).unwrap();
        } else {
            self.builder.build_return(None).unwrap();
        }

        // Restore builder position
        if let Some(bb) = saved_bb {
            self.builder.position_at_end(bb);
        }

        Ok(shim_fn.as_global_value().as_pointer_value().into())
    }

    fn box_value(
        &mut self,
        ty: Ty<'gcx>,
        value: BasicValueEnum<'llvm>,
    ) -> CompileResult<PointerValue<'llvm>> {
        let Some(llvm_payload_ty) = self.lower_ty(ty) else {
            return Ok(self.context.ptr_type(AddressSpace::default()).const_null());
        };
        let size = self.target_data.get_store_size(&llvm_payload_ty);
        let size_const = self.usize_ty.const_int(size, false);
        let desc_ptr = self.gc_desc_for(ty);
        let callee = self.get_gc_alloc();
        let call = self
            .builder
            .build_call(
                callee,
                &[
                    BasicMetadataValueEnum::from(size_const),
                    BasicMetadataValueEnum::from(desc_ptr),
                ],
                "exist_alloc",
            )
            .unwrap();
        let raw_ptr = call
            .try_as_basic_value()
            .basic()
            .expect("gc_alloc returned void")
            .into_pointer_value();
        let typed_ptr = self
            .builder
            .build_bit_cast(
                raw_ptr,
                self.context.ptr_type(AddressSpace::default()),
                "exist_payload_ptr",
            )
            .unwrap()
            .into_pointer_value();
        let _ = self.builder.build_store(typed_ptr, value).unwrap();
        Ok(raw_ptr)
    }

    fn build_existential_value(
        &self,
        ty: Ty<'gcx>,
        data_ptr: PointerValue<'llvm>,
        tables: &[PointerValue<'llvm>],
    ) -> BasicValueEnum<'llvm> {
        let Some(BasicTypeEnum::StructType(struct_ty)) = self.lower_ty(ty) else {
            return data_ptr.as_basic_value_enum();
        };

        let mut value = struct_ty.get_undef();
        value = self
            .builder
            .build_insert_value(value, data_ptr, 0, "exist_data")
            .unwrap()
            .into_struct_value();
        for (index, table) in tables.iter().enumerate() {
            value = self
                .builder
                .build_insert_value(
                    value,
                    (*table).as_basic_value_enum(),
                    (index + 1) as u32,
                    "exist_table",
                )
                .unwrap()
                .into_struct_value();
        }

        value.as_basic_value_enum()
    }

    fn witness_table_ptr(
        &mut self,
        concrete_ty: Ty<'gcx>,
        iface: InterfaceReference<'gcx>,
    ) -> PointerValue<'llvm> {
        let Some(type_head) = type_head_from_value_ty(concrete_ty) else {
            return self.context.ptr_type(AddressSpace::default()).const_null();
        };

        let iface = self.interface_args_with_self(concrete_ty, iface);

        if let Some(ptr) = self.witness_tables.get(&(type_head, iface)) {
            return *ptr;
        }

        let requirements = match self.interface_requirements(iface.id) {
            Some(req) => req,
            None => return self.context.ptr_type(AddressSpace::default()).const_null(),
        };
        let witness = self.conformance_witness(type_head, iface);

        let method_count = requirements
            .methods
            .iter()
            .filter(|method| method.has_self)
            .count();
        let mut entries: Vec<BasicValueEnum<'llvm>> = Vec::with_capacity(method_count);
        for method in requirements.methods.iter().filter(|method| method.has_self) {
            let (impl_def_id, args) = if let Some(method_witness) = witness
                .as_ref()
                .and_then(|w| w.method_witnesses.get(&method.id))
            {
                // TODO: Handle synthetic implementations (generated code)
                let impl_id = method_witness
                    .implementation
                    .impl_id()
                    .expect("synthetic methods not yet supported in vtable generation");
                let args = self.instantiate_generic_args_with_args(
                    method_witness.args_template,
                    iface.arguments,
                );
                (impl_id, args)
            } else {
                (method.id, iface.arguments)
            };
            // Use a thunk to bridge virtual call signature (ptr self) to concrete impl
            let thunk_ptr = self.witness_method_thunk(type_head, iface, impl_def_id, args);
            entries.push(thunk_ptr.as_basic_value_enum());
        }

        let superfaces = self.interface_superfaces(iface);
        for superface in superfaces {
            let ptr = self.witness_table_ptr(concrete_ty, superface);
            entries.push(ptr.as_basic_value_enum());
        }

        let table_ty = self.witness_table_struct_ty(iface.id);
        let const_struct = table_ty.const_named_struct(&entries);
        let gv = self.module.add_global(
            table_ty,
            None,
            &format!("__wt_{}", self.witness_tables.len()),
        );
        gv.set_initializer(&const_struct);
        gv.set_constant(true);
        gv.set_linkage(Linkage::Internal);
        let ptr = gv.as_pointer_value();
        let opaque_ptr = ptr.const_cast(self.context.ptr_type(AddressSpace::default()));
        self.witness_tables.insert((type_head, iface), opaque_ptr);
        opaque_ptr
    }

    fn function_ptr_for_instance(&mut self, instance: Instance<'gcx>) -> PointerValue<'llvm> {
        let def_id = match instance.kind() {
            InstanceKind::Item(def_id) => def_id,
            InstanceKind::Virtual(_) => {
                return self.context.ptr_type(AddressSpace::default()).const_null();
            }
        };

        if let Some(&f) = self.functions.get(&instance) {
            return f.as_global_value().as_pointer_value();
        }

        if self.is_foreign_function(def_id) {
            let f = self.declare_foreign_function(def_id);
            self.functions.insert(instance, f);
            return f.as_global_value().as_pointer_value();
        }

        let prev_subst = self.current_subst;
        self.current_subst = instance.args();
        let sig = self.gcx.get_signature(def_id);
        let fn_ty = self.lower_fn_sig(sig);
        let name = mangle_instance(self.gcx, instance);
        let f = self
            .module
            .add_function(&name, fn_ty, Some(Linkage::External));
        self.functions.insert(instance, f);
        self.current_subst = prev_subst;
        f.as_global_value().as_pointer_value()
    }

    /// Generate a thunk for witness table entries.
    /// The thunk takes a raw ptr as self (from existential data pointer) and forwards
    /// to the concrete implementation with the correct signature.
    fn witness_method_thunk(
        &mut self,
        type_head: TypeHead,
        iface: InterfaceReference<'gcx>,
        impl_def_id: hir::DefinitionID,
        args: GenericArguments<'gcx>,
    ) -> PointerValue<'llvm> {
        // Check cache first
        let cache_key = (type_head, iface, impl_def_id);
        if let Some(&ptr) = self.witness_thunks.get(&cache_key) {
            return ptr;
        }

        // Get the concrete implementation function
        let impl_instance = Instance::item(impl_def_id, args);
        let impl_fn = self.function_ptr_for_instance(impl_instance);

        // Get the implementation signature
        let prev_subst = self.current_subst;
        self.current_subst = args;
        let sig = self.gcx.get_signature(impl_def_id);

        // Build thunk parameter types: first param is raw ptr (data pointer from existential)
        // Rest are the same as the implementation
        let opaque_ptr = self.context.ptr_type(AddressSpace::default());
        let mut thunk_param_types: Vec<BasicMetadataTypeEnum<'llvm>> = vec![opaque_ptr.into()];
        for param in sig.inputs.iter().skip(1) {
            if let Some(ty) = self.lower_ty(param.ty) {
                thunk_param_types.push(ty.into());
            }
        }

        // Build thunk return type
        let thunk_fn_ty = match self.lower_ty(sig.output) {
            Some(ret) => ret.fn_type(&thunk_param_types, false),
            None => self.context.void_type().fn_type(&thunk_param_types, false),
        };

        // Create thunk function
        let thunk_name = format!(
            "__wt_thunk_{}_{}",
            self.witness_thunks.len(),
            self.gcx.definition_ident(impl_def_id).symbol,
        );
        let thunk_fn = self.module.add_function(&thunk_name, thunk_fn_ty, None);

        // Save current position and build thunk body
        let current_block = self.builder.get_insert_block();
        let entry = self.context.append_basic_block(thunk_fn, "entry");
        self.builder.position_at_end(entry);

        // Gather arguments: first is the data pointer, rest are passed through
        let mut call_args: Vec<BasicMetadataValueEnum<'llvm>> =
            Vec::with_capacity(thunk_param_types.len());

        // First argument is the raw data pointer - pass it directly to impl
        // (the impl expects a reference/pointer to the concrete type, which is what data_ptr points to)
        call_args.push(thunk_fn.get_nth_param(0).unwrap().into());

        // Forward remaining arguments
        for i in 1..thunk_fn.count_params() {
            call_args.push(thunk_fn.get_nth_param(i).unwrap().into());
        }

        // Get the implementation function type for indirect call
        let impl_fn_ty = self.lower_fn_sig(sig);

        // Call the implementation
        let call = self
            .builder
            .build_indirect_call(impl_fn_ty, impl_fn, &call_args, "thunk_call")
            .unwrap();

        // Return the result
        if sig.output == self.gcx.types.void {
            self.builder.build_return(None).unwrap();
        } else if let Some(ret_val) = call.try_as_basic_value().basic() {
            self.builder.build_return(Some(&ret_val)).unwrap();
        } else {
            self.builder.build_return(None).unwrap();
        }

        // Restore builder position
        if let Some(block) = current_block {
            self.builder.position_at_end(block);
        }

        self.current_subst = prev_subst;

        // Cache and return
        let thunk_ptr = thunk_fn.as_global_value().as_pointer_value();
        self.witness_thunks.insert(cache_key, thunk_ptr);
        thunk_ptr
    }

    fn interface_requirements(
        &self,
        interface_id: hir::DefinitionID,
    ) -> Option<&'gcx InterfaceRequirements<'gcx>> {
        self.gcx.with_type_database(interface_id.package(), |db| {
            db.interface_requirements.get(&interface_id).copied()
        })
    }

    fn interface_definition(
        &self,
        interface_id: hir::DefinitionID,
    ) -> Option<&'gcx InterfaceDefinition<'gcx>> {
        self.gcx.with_type_database(interface_id.package(), |db| {
            db.def_to_iface_def.get(&interface_id).copied()
        })
    }

    fn conformance_witness(
        &self,
        type_head: TypeHead,
        interface: InterfaceReference<'gcx>,
    ) -> Option<crate::sema::models::ConformanceWitness<'gcx>> {
        // Check cached witnesses across all packages
        if let Some(cached) = self.gcx.find_in_databases(|db| {
            db.conformance_witnesses
                .get(&(type_head, interface))
                .cloned()
        }) {
            return Some(cached);
        }

        resolve_conformance_witness(self.gcx, type_head, interface)
    }

    fn interface_method_count(&self, interface_id: hir::DefinitionID) -> usize {
        self.interface_requirements(interface_id)
            .map(|req| req.methods.len())
            .unwrap_or(0)
    }

    fn interface_superfaces(
        &self,
        iface: InterfaceReference<'gcx>,
    ) -> Vec<InterfaceReference<'gcx>> {
        let Some(def) = self.interface_definition(iface.id) else {
            return Vec::new();
        };

        let mut out = Vec::with_capacity(def.superfaces.len());
        for superface in &def.superfaces {
            let substituted = self.substitute_interface_ref(superface.value, iface.arguments);
            out.push(substituted);
        }
        out
    }

    fn interface_args_with_self(
        &self,
        self_ty: Ty<'gcx>,
        iface: InterfaceReference<'gcx>,
    ) -> InterfaceReference<'gcx> {
        if iface.arguments.is_empty() {
            return iface;
        }

        let mut args: Vec<_> = iface.arguments.iter().copied().collect();
        if let Some(first) = args.get_mut(0) {
            *first = GenericArgument::Type(self_ty);
        }

        let interned = self.gcx.store.interners.intern_generic_args(args);
        InterfaceReference {
            id: iface.id,
            arguments: interned,
            bindings: &[],
        }
    }

    fn instantiate_generic_args_with_args(
        &self,
        template: GenericArguments<'gcx>,
        args: GenericArguments<'gcx>,
    ) -> GenericArguments<'gcx> {
        if template.is_empty() {
            return template;
        }

        let mut out = Vec::with_capacity(template.len());
        for arg in template.iter() {
            match arg {
                GenericArgument::Type(ty) => {
                    let instantiated = instantiate_ty_with_args(self.gcx, *ty, args);
                    out.push(GenericArgument::Type(instantiated));
                }
                GenericArgument::Const(c) => {
                    let instantiated = instantiate_const_with_args(self.gcx, *c, args);
                    out.push(GenericArgument::Const(instantiated));
                }
            }
        }

        self.gcx.store.interners.intern_generic_args(out)
    }

    fn substitute_interface_ref(
        &self,
        template: InterfaceReference<'gcx>,
        args: GenericArguments<'gcx>,
    ) -> InterfaceReference<'gcx> {
        if args.is_empty() {
            return template;
        }

        let mut new_args = Vec::with_capacity(template.arguments.len());
        for arg in template.arguments.iter() {
            match arg {
                GenericArgument::Type(ty) => {
                    let substituted = instantiate_ty_with_args(self.gcx, *ty, args);
                    new_args.push(GenericArgument::Type(substituted));
                }
                GenericArgument::Const(c) => {
                    let substituted = instantiate_const_with_args(self.gcx, *c, args);
                    new_args.push(GenericArgument::Const(substituted));
                }
            }
        }

        let interned = self.gcx.store.interners.intern_generic_args(new_args);

        // Also substitute bindings
        let mut new_bindings = Vec::with_capacity(template.bindings.len());
        for binding in template.bindings {
            let substituted_ty = instantiate_ty_with_args(self.gcx, binding.ty, args);
            new_bindings.push(crate::sema::models::AssociatedTypeBinding {
                name: binding.name,
                ty: substituted_ty,
            });
        }

        InterfaceReference {
            id: template.id,
            arguments: interned,
            bindings: self.gcx.store.arenas.global.alloc_slice_copy(&new_bindings),
        }
    }

    fn witness_table_struct_ty(&self, interface_id: hir::DefinitionID) -> StructType<'llvm> {
        let method_count = self.interface_method_count(interface_id);
        let super_count = self
            .interface_definition(interface_id)
            .map(|def| def.superfaces.len())
            .unwrap_or(0);
        let total = method_count + super_count;
        let ptr_ty = self.context.ptr_type(AddressSpace::default());
        let fields: Vec<_> = (0..total).map(|_| ptr_ty.into()).collect();
        self.context.struct_type(&fields, false)
    }

    fn interface_index(
        &self,
        interfaces: &[InterfaceReference<'gcx>],
        interface_id: hir::DefinitionID,
    ) -> Option<usize> {
        interfaces.iter().position(|iface| iface.id == interface_id)
    }

    fn superface_chain_from_root(
        &self,
        interfaces: &[InterfaceReference<'gcx>],
        target_id: hir::DefinitionID,
    ) -> Option<(usize, Vec<(hir::DefinitionID, usize)>)> {
        for (index, iface) in interfaces.iter().enumerate() {
            if iface.id == target_id {
                return Some((index, Vec::new()));
            }
            if !self.interface_has_superface(iface.id, target_id) {
                continue;
            }
            let chain = self.superface_chain_indices(iface.id, target_id)?;
            return Some((index, chain));
        }
        None
    }

    fn interface_has_superface(
        &self,
        interface_id: hir::DefinitionID,
        target_id: hir::DefinitionID,
    ) -> bool {
        self.gcx.with_type_database(interface_id.package(), |db| {
            db.interface_to_supers
                .get(&interface_id)
                .map_or(false, |supers| supers.contains(&target_id))
        })
    }

    fn superface_chain_indices(
        &self,
        root_id: hir::DefinitionID,
        target_id: hir::DefinitionID,
    ) -> Option<Vec<(hir::DefinitionID, usize)>> {
        use std::collections::{HashMap, VecDeque};

        let mut queue = VecDeque::new();
        let mut parents: HashMap<hir::DefinitionID, (hir::DefinitionID, usize)> = HashMap::new();
        queue.push_back(root_id);
        parents.insert(root_id, (root_id, 0));

        while let Some(current) = queue.pop_front() {
            if current == target_id {
                break;
            }
            let Some(def) = self.interface_definition(current) else {
                continue;
            };
            for (index, superface) in def.superfaces.iter().enumerate() {
                let next = superface.value.id;
                if parents.contains_key(&next) {
                    continue;
                }
                parents.insert(next, (current, index));
                queue.push_back(next);
            }
        }

        if !parents.contains_key(&target_id) {
            return None;
        }

        let mut chain = Vec::new();
        let mut current = target_id;
        while current != root_id {
            let Some((parent, index)) = parents.get(&current).copied() else {
                return None;
            };
            chain.push((parent, index));
            current = parent;
        }
        chain.reverse();
        Some(chain)
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
                if self.try_lower_intrinsic_call(body, locals, func, args, destination)? {
                    let _ = self
                        .builder
                        .build_unconditional_branch(blocks[target.index()])
                        .unwrap();
                    return Ok(());
                }
                if let Some(instance) = self.virtual_instance_for_call(func) {
                    self.lower_virtual_call(body, locals, &instance, args, destination)?;
                } else if let Some(closure_fn) = self.closure_callable(body, func) {
                    // Calling a closure - call the closure's body function directly
                    let mut lowered_args = Vec::with_capacity(args.len());
                    for arg in args {
                        if let Some(val) = self.eval_operand(body, locals, arg)? {
                            lowered_args.push(BasicMetadataValueEnum::from(val));
                        }
                    }

                    let call_site = self
                        .builder
                        .build_call(closure_fn, &lowered_args, "call")
                        .unwrap();

                    if let Some(ret) = call_site.try_as_basic_value().basic() {
                        self.store_place(&destination, body, locals, ret)?;
                    }
                } else if matches!(self.operand_ty(body, func).kind(), TyKind::FnPointer { .. })
                    && !matches!(func, Operand::Constant(_))
                {
                    let (fn_ty, fn_ptr) = self.lower_fn_pointer_call_target(body, locals, func)?;

                    let mut lowered_args = Vec::with_capacity(args.len());
                    for arg in args {
                        if let Some(val) = self.eval_operand(body, locals, arg)? {
                            lowered_args.push(BasicMetadataValueEnum::from(val));
                        }
                    }

                    let call_site = self
                        .builder
                        .build_indirect_call(fn_ty, fn_ptr, &lowered_args, "call")
                        .unwrap();

                    if let Some(ret) = call_site.try_as_basic_value().basic() {
                        self.store_place(&destination, body, locals, ret)?;
                    }
                } else {
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
                        self.store_place(&destination, body, locals, ret)?;
                    }
                }
                let _ = self
                    .builder
                    .build_unconditional_branch(blocks[target.index()])
                    .unwrap();
            }
        }
        Ok(())
    }

    fn try_lower_intrinsic_call(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        func: &Operand<'gcx>,
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
    ) -> CompileResult<bool> {
        let Operand::Constant(c) = func else {
            return Ok(false);
        };
        let mir::ConstantKind::Function(def_id, call_args, _) = c.value else {
            return Ok(false);
        };

        let Some(hir::Abi::Intrinsic) = self.gcx.get_signature(def_id).abi else {
            return Ok(false);
        };

        let ident = self.gcx.definition_ident(def_id);
        let name = ident.symbol.as_str();
        if self.try_lower_typed_math_intrinsic(name, body, locals, args, destination)? {
            return Ok(true);
        }
        match name {
            "__intrinsic_array_read_unchecked" => {
                self.lower_intrinsic_array_read(body, locals, args, destination)?;
                Ok(true)
            }
            "__intrinsic_array_read_mut_unchecked" => {
                self.lower_intrinsic_array_read(body, locals, args, destination)?;
                Ok(true)
            }
            "__intrinsic_array_write_unchecked" => {
                self.lower_intrinsic_array_write(body, locals, args)?;
                Ok(true)
            }
            "__intrinsic_gc_desc" => {
                self.lower_intrinsic_gc_desc(body, locals, call_args, destination)?;
                Ok(true)
            }
            "__intrinsic_list_write" => {
                self.lower_intrinsic_list_write(body, locals, call_args, args)?;
                Ok(true)
            }
            "__intrinsic_list_read_unchecked" => {
                self.lower_intrinsic_list_read_ref(body, locals, call_args, args, destination)?;
                Ok(true)
            }
            "__intrinsic_list_read_mut_unchecked" => {
                self.lower_intrinsic_list_read_ref(body, locals, call_args, args, destination)?;
                Ok(true)
            }
            "__intrinsic_ref_to_ptr" => {
                self.lower_intrinsic_ref_to_ptr(body, locals, args, destination)?;
                Ok(true)
            }
            "__intrinsic_mut_ref_to_ptr" => {
                self.lower_intrinsic_ref_to_ptr(body, locals, args, destination)?;
                Ok(true)
            }
            "__intrinsic_ptr_to_u8" => {
                self.lower_intrinsic_ptr_to_u8(body, locals, args, destination)?;
                Ok(true)
            }
            "__intrinsic_ptr_to_u8_mut" => {
                self.lower_intrinsic_ptr_to_u8(body, locals, args, destination)?;
                Ok(true)
            }
            "__intrinsic_ptr_add" => {
                self.lower_intrinsic_ptr_add(body, locals, call_args, args, destination)?;
                Ok(true)
            }
            "__intrinsic_ptr_sub" => {
                self.lower_intrinsic_ptr_sub(body, locals, call_args, args, destination)?;
                Ok(true)
            }
            "__intrinsic_ptr_offset" => {
                self.lower_intrinsic_ptr_offset(body, locals, call_args, args, destination)?;
                Ok(true)
            }
            "__intrinsic_ptr_byte_add" => {
                self.lower_intrinsic_ptr_byte_add(body, locals, call_args, args, destination)?;
                Ok(true)
            }
            "__intrinsic_ptr_byte_sub" => {
                self.lower_intrinsic_ptr_byte_sub(body, locals, call_args, args, destination)?;
                Ok(true)
            }
            "__intrinsic_ptr_read" => {
                self.lower_intrinsic_ptr_read(body, locals, call_args, args, destination)?;
                Ok(true)
            }
            "__intrinsic_ptr_write" => {
                self.lower_intrinsic_ptr_write(body, locals, call_args, args, destination)?;
                Ok(true)
            }
            "__intrinsic_memcpy" => {
                self.lower_intrinsic_memcpy(body, locals, call_args, args)?;
                Ok(true)
            }
            "__intrinsic_memmove" => {
                self.lower_intrinsic_memmove(body, locals, call_args, args)?;
                Ok(true)
            }
            "__intrinsic_memset" => {
                self.lower_intrinsic_memset(body, locals, call_args, args)?;
                Ok(true)
            }
            "__intrinsic_size_of" => {
                self.lower_intrinsic_size_of(body, locals, call_args, args, destination)?;
                Ok(true)
            }
            "__intrinsic_align_of" => {
                self.lower_intrinsic_align_of(body, locals, call_args, args, destination)?;
                Ok(true)
            }
            "__intrinsic_sqrt" => {
                self.lower_intrinsic_unary_float(body, locals, args, destination, "sqrt")?;
                Ok(true)
            }
            "__intrinsic_sin" => {
                self.lower_intrinsic_unary_float(body, locals, args, destination, "sin")?;
                Ok(true)
            }
            "__intrinsic_cos" => {
                self.lower_intrinsic_unary_float(body, locals, args, destination, "cos")?;
                Ok(true)
            }
            "__intrinsic_tan" => {
                self.lower_libm_unary_float(
                    body,
                    locals,
                    args,
                    destination,
                    "__intrinsic_tan",
                    "tanf",
                    "tan",
                )?;
                Ok(true)
            }
            "__intrinsic_asin" => {
                self.lower_libm_unary_float(
                    body,
                    locals,
                    args,
                    destination,
                    "__intrinsic_asin",
                    "asinf",
                    "asin",
                )?;
                Ok(true)
            }
            "__intrinsic_acos" => {
                self.lower_libm_unary_float(
                    body,
                    locals,
                    args,
                    destination,
                    "__intrinsic_acos",
                    "acosf",
                    "acos",
                )?;
                Ok(true)
            }
            "__intrinsic_atan" => {
                self.lower_libm_unary_float(
                    body,
                    locals,
                    args,
                    destination,
                    "__intrinsic_atan",
                    "atanf",
                    "atan",
                )?;
                Ok(true)
            }
            "__intrinsic_sinh" => {
                self.lower_libm_unary_float(
                    body,
                    locals,
                    args,
                    destination,
                    "__intrinsic_sinh",
                    "sinhf",
                    "sinh",
                )?;
                Ok(true)
            }
            "__intrinsic_cosh" => {
                self.lower_libm_unary_float(
                    body,
                    locals,
                    args,
                    destination,
                    "__intrinsic_cosh",
                    "coshf",
                    "cosh",
                )?;
                Ok(true)
            }
            "__intrinsic_tanh" => {
                self.lower_libm_unary_float(
                    body,
                    locals,
                    args,
                    destination,
                    "__intrinsic_tanh",
                    "tanhf",
                    "tanh",
                )?;
                Ok(true)
            }
            "__intrinsic_exp" => {
                self.lower_intrinsic_unary_float(body, locals, args, destination, "exp")?;
                Ok(true)
            }
            "__intrinsic_exp2" => {
                self.lower_intrinsic_unary_float(body, locals, args, destination, "exp2")?;
                Ok(true)
            }
            "__intrinsic_log" => {
                self.lower_intrinsic_unary_float(body, locals, args, destination, "log")?;
                Ok(true)
            }
            "__intrinsic_log2" => {
                self.lower_intrinsic_unary_float(body, locals, args, destination, "log2")?;
                Ok(true)
            }
            "__intrinsic_log10" => {
                self.lower_intrinsic_unary_float(body, locals, args, destination, "log10")?;
                Ok(true)
            }
            "__intrinsic_fabs" => {
                self.lower_intrinsic_unary_float(body, locals, args, destination, "fabs")?;
                Ok(true)
            }
            "__intrinsic_floor" => {
                self.lower_intrinsic_unary_float(body, locals, args, destination, "floor")?;
                Ok(true)
            }
            "__intrinsic_ceil" => {
                self.lower_intrinsic_unary_float(body, locals, args, destination, "ceil")?;
                Ok(true)
            }
            "__intrinsic_trunc" => {
                self.lower_intrinsic_unary_float(body, locals, args, destination, "trunc")?;
                Ok(true)
            }
            "__intrinsic_rint" => {
                self.lower_intrinsic_unary_float(body, locals, args, destination, "rint")?;
                Ok(true)
            }
            "__intrinsic_nearbyint" => {
                self.lower_intrinsic_unary_float(body, locals, args, destination, "nearbyint")?;
                Ok(true)
            }
            "__intrinsic_round" => {
                self.lower_intrinsic_unary_float(body, locals, args, destination, "round")?;
                Ok(true)
            }
            "__intrinsic_roundeven" => {
                self.lower_intrinsic_unary_float(body, locals, args, destination, "roundeven")?;
                Ok(true)
            }
            "__intrinsic_pow" => {
                self.lower_intrinsic_binary_float(body, locals, args, destination, "pow")?;
                Ok(true)
            }
            "__intrinsic_powi" => {
                self.lower_intrinsic_powi(body, locals, args, destination)?;
                Ok(true)
            }
            "__intrinsic_copysign" => {
                self.lower_intrinsic_binary_float(body, locals, args, destination, "copysign")?;
                Ok(true)
            }
            "__intrinsic_fma" => {
                self.lower_intrinsic_ternary_float(body, locals, args, destination, "fma")?;
                Ok(true)
            }
            "__intrinsic_minimum" => {
                self.lower_intrinsic_binary_float(body, locals, args, destination, "minimum")?;
                Ok(true)
            }
            "__intrinsic_maximum" => {
                self.lower_intrinsic_binary_float(body, locals, args, destination, "maximum")?;
                Ok(true)
            }
            "__intrinsic_minimumnum" => {
                self.lower_intrinsic_binary_float(body, locals, args, destination, "minnum")?;
                Ok(true)
            }
            "__intrinsic_maximumnum" => {
                self.lower_intrinsic_binary_float(body, locals, args, destination, "maxnum")?;
                Ok(true)
            }
            "__intrinsic_string_from_parts" => {
                self.lower_intrinsic_string_from_parts(body, locals, args, destination)?;
                Ok(true)
            }
            "__intrinsic_string_data" => {
                self.lower_intrinsic_string_data(body, locals, args, destination)?;
                Ok(true)
            }
            "__intrinsic_string_len" => {
                self.lower_intrinsic_string_len(body, locals, args, destination)?;
                Ok(true)
            }
            _ => {
                self.gcx
                    .dcx()
                    .emit_error(format!("unknown intrinsic '{}'", name), None);
                Ok(true)
            }
        }
    }

    fn try_lower_typed_math_intrinsic(
        &mut self,
        name: &str,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
    ) -> CompileResult<bool> {
        let Some(stem) = name.strip_prefix("__intrinsic_") else {
            return Ok(false);
        };

        if matches!(stem, "powi_f32_i32" | "powi_f64_i32") {
            self.lower_intrinsic_powi(body, locals, args, destination)?;
            return Ok(true);
        }

        let Some(op) = stem
            .strip_suffix("_f32")
            .or_else(|| stem.strip_suffix("_f64"))
        else {
            return Ok(false);
        };

        match op {
            "sqrt" | "sin" | "cos" | "exp" | "exp2" | "log" | "log2" | "log10" | "fabs"
            | "floor" | "ceil" | "trunc" | "rint" | "nearbyint" | "round" | "roundeven" => {
                self.lower_intrinsic_unary_float(body, locals, args, destination, op)?;
                Ok(true)
            }
            "tan" => {
                self.lower_libm_unary_float(body, locals, args, destination, name, "tanf", "tan")?;
                Ok(true)
            }
            "asin" => {
                self.lower_libm_unary_float(body, locals, args, destination, name, "asinf", "asin")?;
                Ok(true)
            }
            "acos" => {
                self.lower_libm_unary_float(body, locals, args, destination, name, "acosf", "acos")?;
                Ok(true)
            }
            "atan" => {
                self.lower_libm_unary_float(body, locals, args, destination, name, "atanf", "atan")?;
                Ok(true)
            }
            "sinh" => {
                self.lower_libm_unary_float(body, locals, args, destination, name, "sinhf", "sinh")?;
                Ok(true)
            }
            "cosh" => {
                self.lower_libm_unary_float(body, locals, args, destination, name, "coshf", "cosh")?;
                Ok(true)
            }
            "tanh" => {
                self.lower_libm_unary_float(body, locals, args, destination, name, "tanhf", "tanh")?;
                Ok(true)
            }
            "pow" | "copysign" | "minimum" | "maximum" => {
                self.lower_intrinsic_binary_float(body, locals, args, destination, op)?;
                Ok(true)
            }
            "minimumnum" => {
                self.lower_intrinsic_binary_float(body, locals, args, destination, "minnum")?;
                Ok(true)
            }
            "maximumnum" => {
                self.lower_intrinsic_binary_float(body, locals, args, destination, "maxnum")?;
                Ok(true)
            }
            "fma" => {
                self.lower_intrinsic_ternary_float(body, locals, args, destination, "fma")?;
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    fn lower_intrinsic_array_read(
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

        // Get operand type, substitute generic parameters, then normalize
        let mut arr_ty = self.operand_ty(body, arr);
        arr_ty = instantiate_ty_with_args(self.gcx, arr_ty, self.current_subst);
        arr_ty = crate::sema::tycheck::utils::normalize_post_monomorphization(self.gcx, arr_ty);
        let arr_ty = match arr_ty.kind() {
            TyKind::Reference(inner, _) | TyKind::Pointer(inner, _) => inner,
            _ => arr_ty,
        };
        // Normalize again after unwrapping reference (already substituted so just normalize)
        let arr_ty = crate::sema::tycheck::utils::normalize_post_monomorphization(self.gcx, arr_ty);
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

    fn lower_intrinsic_array_write(
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

        // Get operand type, substitute generic parameters, then normalize
        let mut arr_ty = self.operand_ty(body, arr);
        arr_ty = instantiate_ty_with_args(self.gcx, arr_ty, self.current_subst);
        arr_ty = crate::sema::tycheck::utils::normalize_post_monomorphization(self.gcx, arr_ty);
        let arr_ty = match arr_ty.kind() {
            TyKind::Reference(inner, _) | TyKind::Pointer(inner, _) => inner,
            _ => arr_ty,
        };
        // Normalize again after unwrapping reference (already substituted so just normalize)
        let arr_ty = crate::sema::tycheck::utils::normalize_post_monomorphization(self.gcx, arr_ty);
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
    fn lower_intrinsic_gc_desc(
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

        // Substitute with current generic context and normalize
        let ty = instantiate_ty_with_args(self.gcx, *ty, self.current_subst);
        let ty = crate::sema::tycheck::utils::normalize_post_monomorphization(self.gcx, ty);

        // Get or create the GC descriptor for this type
        let desc_ptr = self.gc_desc_for(ty);

        self.store_place(destination, body, locals, desc_ptr.into())
    }

    /// Intrinsic: __intrinsic_list_write[T](buffer: GcPtr, index: usize, value: T)
    /// Writes a value to the buffer at the given element index.
    fn lower_intrinsic_list_write(
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

        let elem_ty = instantiate_ty_with_args(self.gcx, *elem_ty, self.current_subst);
        let elem_ty =
            crate::sema::tycheck::utils::normalize_post_monomorphization(self.gcx, elem_ty);

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
    fn lower_intrinsic_list_read_ref(
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

        let elem_ty = instantiate_ty_with_args(self.gcx, *elem_ty, self.current_subst);
        let elem_ty =
            crate::sema::tycheck::utils::normalize_post_monomorphization(self.gcx, elem_ty);

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
    fn lower_intrinsic_ref_to_ptr(
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
    fn lower_intrinsic_ptr_add(
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
    fn lower_intrinsic_ptr_sub(
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
    fn lower_intrinsic_ptr_offset(
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
        let elem_ty = instantiate_ty_with_args(self.gcx, *elem_ty, self.current_subst);
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

    fn lower_intrinsic_ptr_byte_add(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        call_args: GenericArguments<'gcx>,
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
    ) -> CompileResult<()> {
        self.lower_intrinsic_ptr_byte_op(body, locals, call_args, args, destination, false)
    }

    fn lower_intrinsic_ptr_byte_sub(
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

    fn lower_intrinsic_ptr_read(
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
        let elem_ty = instantiate_ty_with_args(self.gcx, *elem_ty, self.current_subst);
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

    fn lower_intrinsic_ptr_write(
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

    fn lower_intrinsic_memcpy(
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

    fn lower_intrinsic_memmove(
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

    fn lower_intrinsic_memset(
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

    fn lower_intrinsic_size_of(
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
        let elem_ty = instantiate_ty_with_args(self.gcx, *elem_ty, self.current_subst);
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

    fn lower_intrinsic_align_of(
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
        let elem_ty = instantiate_ty_with_args(self.gcx, *elem_ty, self.current_subst);
        let Some(llvm_elem_ty) = self.lower_ty(elem_ty) else {
            return Ok(());
        };

        let align = self.target_data.get_abi_alignment(&llvm_elem_ty);
        let align = self.usize_ty.const_int(align as u64, false);

        self.store_place(destination, body, locals, align.into())
    }

    fn lower_intrinsic_string_from_parts(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
    ) -> CompileResult<()> {
        let data = args.first().expect("string_from_parts missing data pointer");
        let len = args.get(1).expect("string_from_parts missing length");

        let Some(data_val) = self.eval_operand(body, locals, data)? else {
            let _ = self.builder.build_unreachable().unwrap();
            return Ok(());
        };
        let Some(len_val) = self.eval_operand(body, locals, len)? else {
            let _ = self.builder.build_unreachable().unwrap();
            return Ok(());
        };

        let ptr_ty = self.context.ptr_type(AddressSpace::default());
        let data_ptr = match data_val {
            BasicValueEnum::PointerValue(ptr) => ptr,
            BasicValueEnum::IntValue(int_val) => self
                .builder
                .build_int_to_ptr(int_val, ptr_ty, "string_data_ptr")
                .unwrap(),
            _ => {
                self.gcx
                    .dcx()
                    .emit_error("string_from_parts expects a pointer for data".into(), None);
                return Ok(());
            }
        };

        let mut len_int = match len_val {
            BasicValueEnum::IntValue(int_val) => int_val,
            _ => {
                self.gcx
                    .dcx()
                    .emit_error("string_from_parts expects an integer length".into(), None);
                return Ok(());
            }
        };
        if len_int.get_type() != self.usize_ty {
            len_int = self
                .builder
                .build_int_cast(len_int, self.usize_ty, "string_len_cast")
                .unwrap();
        }

        let string_ty = self
            .lower_ty(self.place_ty(body, destination))
            .expect("string type lowered")
            .into_struct_type();
        let mut value = string_ty.get_undef();
        value = self
            .builder
            .build_insert_value(value, data_ptr, 0, "string_ins_data")
            .unwrap()
            .into_struct_value();
        value = self
            .builder
            .build_insert_value(value, len_int, 1, "string_ins_len")
            .unwrap()
            .into_struct_value();

        self.store_place(destination, body, locals, value.as_basic_value_enum())
    }

    fn lower_intrinsic_string_data(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
    ) -> CompileResult<()> {
        let value = args.first().expect("string_data missing string value");
        let Some(value) = self.eval_operand(body, locals, value)? else {
            let _ = self.builder.build_unreachable().unwrap();
            return Ok(());
        };

        let struct_val = match value {
            BasicValueEnum::StructValue(struct_val) => struct_val,
            _ => {
                self.gcx
                    .dcx()
                    .emit_error("string_data expects a string value".into(), None);
                return Ok(());
            }
        };

        let data = self
            .builder
            .build_extract_value(struct_val, 0, "string_data")
            .unwrap()
            .into_pointer_value();
        self.store_place(destination, body, locals, data.as_basic_value_enum())
    }

    fn lower_intrinsic_string_len(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
    ) -> CompileResult<()> {
        let value = args.first().expect("string_len missing string value");
        let Some(value) = self.eval_operand(body, locals, value)? else {
            let _ = self.builder.build_unreachable().unwrap();
            return Ok(());
        };

        let struct_val = match value {
            BasicValueEnum::StructValue(struct_val) => struct_val,
            _ => {
                self.gcx
                    .dcx()
                    .emit_error("string_len expects a string value".into(), None);
                return Ok(());
            }
        };

        let len = self
            .builder
            .build_extract_value(struct_val, 1, "string_len")
            .unwrap()
            .into_int_value();
        self.store_place(destination, body, locals, len.as_basic_value_enum())
    }

    fn lower_intrinsic_unary_float(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
        intrinsic: &str,
    ) -> CompileResult<()> {
        let operand = args.first().expect("missing unary intrinsic operand");
        let Some(value) = self.eval_operand(body, locals, operand)? else {
            let _ = self.builder.build_unreachable().unwrap();
            return Ok(());
        };

        let float_val = match value {
            BasicValueEnum::FloatValue(float_val) => float_val,
            _ => {
                self.gcx.dcx().emit_error(
                    format!("'{}' expects a float or double argument", intrinsic),
                    None,
                );
                return Ok(());
            }
        };

        let ty = float_val.get_type();
        let Some(suffix) = self.float_intrinsic_suffix(ty) else {
            self.gcx.dcx().emit_error(
                format!("'{}' only supports float and double", intrinsic),
                None,
            );
            return Ok(());
        };

        let name = format!("llvm.{}.{}", intrinsic, suffix);
        let fn_ty = ty.fn_type(&[ty.into()], false);
        let callee = self.get_or_add_intrinsic_function(&name, fn_ty);
        let call = self
            .builder
            .build_call(callee, &[float_val.into()], "intrinsic_call")
            .unwrap();
        let Some(result) = call.try_as_basic_value().basic() else {
            self.gcx
                .dcx()
                .emit_error(format!("intrinsic '{}' returned void", name), None);
            return Ok(());
        };

        self.store_place(destination, body, locals, result)
    }

    fn lower_libm_unary_float(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
        intrinsic_name: &str,
        f32_symbol: &str,
        f64_symbol: &str,
    ) -> CompileResult<()> {
        let operand = args.first().expect("missing unary intrinsic operand");
        let Some(value) = self.eval_operand(body, locals, operand)? else {
            let _ = self.builder.build_unreachable().unwrap();
            return Ok(());
        };

        let float_val = match value {
            BasicValueEnum::FloatValue(float_val) => float_val,
            _ => {
                self.gcx.dcx().emit_error(
                    format!("'{}' expects a float or double argument", intrinsic_name),
                    None,
                );
                return Ok(());
            }
        };

        let ty = float_val.get_type();
        let (symbol, fn_ty) = match ty.get_bit_width() {
            32 => (f32_symbol, ty.fn_type(&[ty.into()], false)),
            64 => (f64_symbol, ty.fn_type(&[ty.into()], false)),
            _ => {
                self.gcx.dcx().emit_error(
                    format!("'{}' only supports float and double", intrinsic_name),
                    None,
                );
                return Ok(());
            }
        };

        let callee = self.get_or_add_external_function(symbol, fn_ty);
        let call = self
            .builder
            .build_call(callee, &[float_val.into()], "libm_call")
            .unwrap();
        let Some(result) = call.try_as_basic_value().basic() else {
            self.gcx
                .dcx()
                .emit_error(format!("libm function '{}' returned void", symbol), None);
            return Ok(());
        };

        self.store_place(destination, body, locals, result)
    }

    fn lower_intrinsic_binary_float(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
        intrinsic: &str,
    ) -> CompileResult<()> {
        let lhs = args.first().expect("missing binary intrinsic lhs");
        let rhs = args.get(1).expect("missing binary intrinsic rhs");

        let Some(lhs_val) = self.eval_operand(body, locals, lhs)? else {
            let _ = self.builder.build_unreachable().unwrap();
            return Ok(());
        };
        let Some(rhs_val) = self.eval_operand(body, locals, rhs)? else {
            let _ = self.builder.build_unreachable().unwrap();
            return Ok(());
        };

        let lhs_float = match lhs_val {
            BasicValueEnum::FloatValue(val) => val,
            _ => {
                self.gcx.dcx().emit_error(
                    format!("'{}' expects float or double arguments", intrinsic),
                    None,
                );
                return Ok(());
            }
        };
        let rhs_float = match rhs_val {
            BasicValueEnum::FloatValue(val) => val,
            _ => {
                self.gcx.dcx().emit_error(
                    format!("'{}' expects float or double arguments", intrinsic),
                    None,
                );
                return Ok(());
            }
        };

        let ty = lhs_float.get_type();
        if ty != rhs_float.get_type() {
            self.gcx
                .dcx()
                .emit_error(format!("'{}' requires matching float types", intrinsic), None);
            return Ok(());
        }
        let Some(suffix) = self.float_intrinsic_suffix(ty) else {
            self.gcx.dcx().emit_error(
                format!("'{}' only supports float and double", intrinsic),
                None,
            );
            return Ok(());
        };

        let name = format!("llvm.{}.{}", intrinsic, suffix);
        let fn_ty = ty.fn_type(&[ty.into(), ty.into()], false);
        let callee = self.get_or_add_intrinsic_function(&name, fn_ty);
        let call = self
            .builder
            .build_call(
                callee,
                &[lhs_float.into(), rhs_float.into()],
                "intrinsic_call",
            )
            .unwrap();
        let Some(result) = call.try_as_basic_value().basic() else {
            self.gcx
                .dcx()
                .emit_error(format!("intrinsic '{}' returned void", name), None);
            return Ok(());
        };

        self.store_place(destination, body, locals, result)
    }

    fn lower_intrinsic_ternary_float(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
        intrinsic: &str,
    ) -> CompileResult<()> {
        let x = args.first().expect("missing ternary intrinsic operand x");
        let y = args.get(1).expect("missing ternary intrinsic operand y");
        let z = args.get(2).expect("missing ternary intrinsic operand z");

        let Some(x_val) = self.eval_operand(body, locals, x)? else {
            let _ = self.builder.build_unreachable().unwrap();
            return Ok(());
        };
        let Some(y_val) = self.eval_operand(body, locals, y)? else {
            let _ = self.builder.build_unreachable().unwrap();
            return Ok(());
        };
        let Some(z_val) = self.eval_operand(body, locals, z)? else {
            let _ = self.builder.build_unreachable().unwrap();
            return Ok(());
        };

        let x_float = match x_val {
            BasicValueEnum::FloatValue(val) => val,
            _ => {
                self.gcx.dcx().emit_error(
                    format!("'{}' expects float or double arguments", intrinsic),
                    None,
                );
                return Ok(());
            }
        };
        let y_float = match y_val {
            BasicValueEnum::FloatValue(val) => val,
            _ => {
                self.gcx.dcx().emit_error(
                    format!("'{}' expects float or double arguments", intrinsic),
                    None,
                );
                return Ok(());
            }
        };
        let z_float = match z_val {
            BasicValueEnum::FloatValue(val) => val,
            _ => {
                self.gcx.dcx().emit_error(
                    format!("'{}' expects float or double arguments", intrinsic),
                    None,
                );
                return Ok(());
            }
        };

        let ty = x_float.get_type();
        if ty != y_float.get_type() || ty != z_float.get_type() {
            self.gcx
                .dcx()
                .emit_error(format!("'{}' requires matching float types", intrinsic), None);
            return Ok(());
        }
        let Some(suffix) = self.float_intrinsic_suffix(ty) else {
            self.gcx.dcx().emit_error(
                format!("'{}' only supports float and double", intrinsic),
                None,
            );
            return Ok(());
        };

        let name = format!("llvm.{}.{}", intrinsic, suffix);
        let fn_ty = ty.fn_type(&[ty.into(), ty.into(), ty.into()], false);
        let callee = self.get_or_add_intrinsic_function(&name, fn_ty);
        let call = self
            .builder
            .build_call(
                callee,
                &[x_float.into(), y_float.into(), z_float.into()],
                "intrinsic_call",
            )
            .unwrap();
        let Some(result) = call.try_as_basic_value().basic() else {
            self.gcx
                .dcx()
                .emit_error(format!("intrinsic '{}' returned void", name), None);
            return Ok(());
        };

        self.store_place(destination, body, locals, result)
    }

    fn lower_intrinsic_powi(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
    ) -> CompileResult<()> {
        let base = args.first().expect("missing powi base");
        let exponent = args.get(1).expect("missing powi exponent");

        let Some(base_val) = self.eval_operand(body, locals, base)? else {
            let _ = self.builder.build_unreachable().unwrap();
            return Ok(());
        };
        let Some(exponent_val) = self.eval_operand(body, locals, exponent)? else {
            let _ = self.builder.build_unreachable().unwrap();
            return Ok(());
        };

        let base_float = match base_val {
            BasicValueEnum::FloatValue(val) => val,
            _ => {
                self.gcx
                    .dcx()
                    .emit_error("'powi' expects a float or double base".into(), None);
                return Ok(());
            }
        };
        let exponent_int = match exponent_val {
            BasicValueEnum::IntValue(val) => val,
            _ => {
                self.gcx
                    .dcx()
                    .emit_error("'powi' expects an int32 exponent".into(), None);
                return Ok(());
            }
        };

        let ty = base_float.get_type();
        let Some(suffix) = self.float_intrinsic_suffix(ty) else {
            self.gcx
                .dcx()
                .emit_error("'powi' only supports float and double".into(), None);
            return Ok(());
        };
        let i32_ty = self.context.i32_type();
        let exponent_i32 = if exponent_int.get_type() == i32_ty {
            exponent_int
        } else {
            self.builder
                .build_int_cast(exponent_int, i32_ty, "powi_exp_cast")
                .unwrap()
        };

        let name = format!("llvm.powi.{}.i32", suffix);
        let fn_ty = ty.fn_type(&[ty.into(), i32_ty.into()], false);
        let callee = self.get_or_add_intrinsic_function(&name, fn_ty);
        let call = self
            .builder
            .build_call(
                callee,
                &[base_float.into(), exponent_i32.into()],
                "intrinsic_call",
            )
            .unwrap();
        let Some(result) = call.try_as_basic_value().basic() else {
            self.gcx
                .dcx()
                .emit_error(format!("intrinsic '{}' returned void", name), None);
            return Ok(());
        };

        self.store_place(destination, body, locals, result)
    }

    fn float_intrinsic_suffix(&self, ty: FloatType<'llvm>) -> Option<&'static str> {
        match ty.get_bit_width() {
            32 => Some("f32"),
            64 => Some("f64"),
            _ => None,
        }
    }

    fn get_or_add_intrinsic_function(
        &self,
        name: &str,
        fn_ty: FunctionType<'llvm>,
    ) -> FunctionValue<'llvm> {
        self.module
            .get_function(name)
            .unwrap_or_else(|| self.module.add_function(name, fn_ty, None))
    }

    fn get_or_add_external_function(
        &self,
        name: &str,
        fn_ty: FunctionType<'llvm>,
    ) -> FunctionValue<'llvm> {
        self.module
            .get_function(name)
            .unwrap_or_else(|| self.module.add_function(name, fn_ty, Some(Linkage::External)))
    }

    /// Intrinsic: __intrinsic_ptr_to_u8[T](*const T) -> *const uint8
    /// Intrinsic: __intrinsic_ptr_to_u8_mut[T](*mut T) -> *mut uint8
    /// Reinterprets a raw pointer as a byte pointer.
    fn lower_intrinsic_ptr_to_u8(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
    ) -> CompileResult<()> {
        let value = args.first().expect("ptr_to_u8 missing value");
        let Some(val) = self.eval_operand(body, locals, value)? else {
            let _ = self.builder.build_unreachable().unwrap();
            return Ok(());
        };

        let ptr_ty = self.context.ptr_type(AddressSpace::default());
        let ptr_val = match val {
            BasicValueEnum::PointerValue(ptr) => ptr,
            BasicValueEnum::IntValue(int_val) => self
                .builder
                .build_int_to_ptr(int_val, ptr_ty, "int_to_ptr")
                .unwrap(),
            _ => {
                self.gcx
                    .dcx()
                    .emit_error("ptr_to_u8 expects a pointer value".into(), None);
                return Ok(());
            }
        };

        let byte_ptr_ty = self.context.ptr_type(AddressSpace::default());
        let cast = self
            .builder
            .build_bit_cast(ptr_val, byte_ptr_ty, "ptr_u8")
            .unwrap();

        self.store_place(destination, body, locals, cast.into())
    }

    fn lower_callable(&mut self, func: &Operand<'gcx>) -> FunctionValue<'llvm> {
        if let Operand::Constant(c) = func {
            if let mir::ConstantKind::Function(def_id, args, _) = c.value {
                let instance = self.instance_for_call(def_id, args);
                if let InstanceKind::Virtual(_) = instance.kind() {
                    todo!("virtual call codegen for boxed existentials");
                }

                if let Some(&f) = self.functions.get(&instance) {
                    return f;
                }

                if self.is_foreign_function(def_id) {
                    let f = self.declare_foreign_function(def_id);
                    self.functions.insert(instance, f);
                    return f;
                }

                // Not declared yet (likely from another package); declare as external.
                // Set substitution context for signature lowering
                let prev_subst = self.current_subst;
                self.current_subst = instance.args();
                let sig = self.gcx.get_signature(def_id);
                let fn_ty = self.lower_fn_sig(sig);
                let name = mangle_instance(self.gcx, instance);
                let linkage = Some(Linkage::External);
                let f = self.module.add_function(&name, fn_ty, linkage);
                self.functions.insert(instance, f);
                self.current_subst = prev_subst;
                return f;
            }
        }

        self.functions
            .values()
            .copied()
            .next()
            .expect("at least one function")
    }

    fn lower_fn_pointer_sig(
        &self,
        inputs: &'gcx [Ty<'gcx>],
        output: Ty<'gcx>,
    ) -> FunctionType<'llvm> {
        let params: Vec<BasicMetadataTypeEnum<'llvm>> = inputs
            .iter()
            .filter_map(|&ty| self.lower_ty(ty).map(|t| t.into()))
            .collect();
        match self.lower_ty(output) {
            Some(ret) => ret.fn_type(&params, false),
            None => self.context.void_type().fn_type(&params, false),
        }
    }

    fn lower_fn_pointer_call_target(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        func: &Operand<'gcx>,
    ) -> CompileResult<(FunctionType<'llvm>, PointerValue<'llvm>)> {
        let TyKind::FnPointer { inputs, output } = self.operand_ty(body, func).kind() else {
            self.gcx
                .dcx()
                .emit_error("expected function pointer operand".into(), None);
            return Err(crate::error::ReportedError);
        };
        let Some(value) = self.eval_operand(body, locals, func)? else {
            self.gcx
                .dcx()
                .emit_error("expected function pointer value".into(), None);
            return Err(crate::error::ReportedError);
        };
        let BasicValueEnum::PointerValue(ptr) = value else {
            self.gcx
                .dcx()
                .emit_error("expected function pointer value".into(), None);
            return Err(crate::error::ReportedError);
        };

        let fn_ty = self.lower_fn_pointer_sig(inputs, output);
        let fn_ptr_ty = self.context.ptr_type(AddressSpace::default());
        let cast_ptr = self
            .builder
            .build_bit_cast(ptr, fn_ptr_ty, "fn_ptr_cast")
            .unwrap()
            .into_pointer_value();
        Ok((fn_ty, cast_ptr))
    }

    /// Check if the func operand is a closure and return the closure body function
    fn closure_callable(
        &mut self,
        body: &mir::Body<'gcx>,
        func: &Operand<'gcx>,
    ) -> Option<FunctionValue<'llvm>> {
        // Get the type of the operand
        let ty = match func {
            Operand::Copy(place) | Operand::Move(place) => {
                // Get the base type from the local
                let mut ty = body.locals[place.local].ty;
                // Apply projections to get the final type
                for elem in &place.projection {
                    ty = match elem {
                        mir::PlaceElem::Deref => ty.dereference().unwrap_or(ty),
                        mir::PlaceElem::Field(_, field_ty) => *field_ty,
                        mir::PlaceElem::VariantDowncast { .. } => ty,
                    };
                }
                ty
            }
            Operand::Constant(_) => return None, // Constants handled by lower_callable
        };

        // Check if it's a closure type
        let TyKind::Closure { closure_def_id, .. } = ty.kind() else {
            return None;
        };

        // Create an instance for the closure body function
        let instance = Instance::item(closure_def_id, &[]);

        // Look up or declare the closure body function
        if let Some(&f) = self.functions.get(&instance) {
            return Some(f);
        }

        // Need to declare it as external
        let prev_subst = self.current_subst;
        self.current_subst = &[];
        let sig = self.gcx.get_signature(closure_def_id);
        let fn_ty = self.lower_fn_sig(sig);
        let name = mangle_instance(self.gcx, instance);
        let linkage = Some(Linkage::External);
        let f = self.module.add_function(&name, fn_ty, linkage);
        self.functions.insert(instance, f);
        self.current_subst = prev_subst;
        Some(f)
    }

    fn virtual_instance_for_call(
        &self,
        func: &Operand<'gcx>,
    ) -> Option<crate::specialize::VirtualInstance> {
        let Operand::Constant(c) = func else {
            return None;
        };
        let mir::ConstantKind::Function(def_id, args, _) = c.value else {
            return None;
        };
        let instance = resolve_instance(self.gcx, def_id, args);
        match instance.kind() {
            InstanceKind::Virtual(instance) => Some(instance),
            InstanceKind::Item(_) => None,
        }
    }

    fn lower_virtual_call(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        instance: &crate::specialize::VirtualInstance,
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
    ) -> CompileResult<()> {
        let receiver = args.first().expect("virtual call missing receiver");
        let receiver_ty = self.operand_ty(body, receiver);
        let Some(receiver_val) = self.eval_operand(body, locals, receiver)? else {
            return Ok(());
        };

        let self_ty = match receiver_ty.kind() {
            TyKind::Reference(inner, _) | TyKind::Pointer(inner, _) => inner,
            _ => receiver_ty,
        };

        let TyKind::BoxedExistential { interfaces } = self_ty.kind() else {
            return Ok(());
        };
        let Some(root_iface) = interfaces.get(instance.table_index).copied() else {
            return Ok(());
        };

        let (data_ptr, root_table_ptr) =
            self.extract_existential_parts(receiver_ty, receiver_val, instance.table_index)?;

        let method_table_ptr = if root_iface.id == instance.method_interface {
            root_table_ptr
        } else if let Some(chain) =
            self.superface_chain_indices(root_iface.id, instance.method_interface)
        {
            let mut current_ptr = root_table_ptr;
            for (current_iface, super_index) in chain {
                let table_ty = self.witness_table_struct_ty(current_iface);
                let table_ptr_ty = self.context.ptr_type(AddressSpace::default());
                let typed_ptr = self
                    .builder
                    .build_bit_cast(current_ptr, table_ptr_ty, "wt_cast")
                    .unwrap()
                    .into_pointer_value();
                let field_index = self.interface_method_count(current_iface) + super_index;
                let field_ptr = self
                    .builder
                    .build_struct_gep(table_ty, typed_ptr, field_index as u32, "wt_super_ptr")
                    .unwrap();
                current_ptr = self
                    .builder
                    .build_load(
                        self.context.ptr_type(AddressSpace::default()),
                        field_ptr,
                        "wt_super_load",
                    )
                    .unwrap()
                    .into_pointer_value();
            }
            current_ptr
        } else {
            root_table_ptr
        };

        let method_table_ty = self.witness_table_struct_ty(instance.method_interface);
        let method_table_ptr_ty = self.context.ptr_type(AddressSpace::default());
        let typed_method_table = self
            .builder
            .build_bit_cast(method_table_ptr, method_table_ptr_ty, "wt_method_cast")
            .unwrap()
            .into_pointer_value();
        let slot_ptr = self
            .builder
            .build_struct_gep(
                method_table_ty,
                typed_method_table,
                instance.slot as u32,
                "wt_method_ptr",
            )
            .unwrap();
        let fn_ptr = self
            .builder
            .build_load(
                self.context.ptr_type(AddressSpace::default()),
                slot_ptr,
                "wt_method_load",
            )
            .unwrap()
            .into_pointer_value();

        let mut lowered_args: Vec<BasicMetadataValueEnum<'llvm>> = Vec::with_capacity(args.len());
        lowered_args.push(BasicMetadataValueEnum::from(data_ptr.as_basic_value_enum()));
        for arg in args.iter().skip(1) {
            if let Some(val) = self.eval_operand(body, locals, arg)? {
                lowered_args.push(BasicMetadataValueEnum::from(val));
            }
        }

        let param_types: Vec<BasicMetadataTypeEnum<'llvm>> = lowered_args
            .iter()
            .map(|arg| match arg {
                BasicMetadataValueEnum::ArrayValue(v) => v.get_type().into(),
                BasicMetadataValueEnum::IntValue(v) => v.get_type().into(),
                BasicMetadataValueEnum::FloatValue(v) => v.get_type().into(),
                BasicMetadataValueEnum::PointerValue(v) => v.get_type().into(),
                BasicMetadataValueEnum::StructValue(v) => v.get_type().into(),
                BasicMetadataValueEnum::VectorValue(v) => v.get_type().into(),
                BasicMetadataValueEnum::ScalableVectorValue(v) => v.get_type().into(),
                BasicMetadataValueEnum::MetadataValue(_) => self.context.metadata_type().into(),
            })
            .collect();
        let ret_ty = self.place_ty(body, destination);
        let fn_ty = match self.lower_ty(ret_ty) {
            Some(ret) => ret.fn_type(&param_types, false),
            None => self.context.void_type().fn_type(&param_types, false),
        };

        let fn_ptr_cast = self
            .builder
            .build_bit_cast(
                fn_ptr,
                self.context.ptr_type(AddressSpace::default()),
                "virt_fn_ptr",
            )
            .unwrap()
            .into_pointer_value();
        let call_site = self
            .builder
            .build_indirect_call(fn_ty, fn_ptr_cast, &lowered_args, "virt_call")
            .unwrap();

        if let Some(ret) = call_site.try_as_basic_value().basic() {
            self.store_place(destination, body, locals, ret)?;
        }

        Ok(())
    }

    fn extract_existential_parts(
        &self,
        receiver_ty: Ty<'gcx>,
        receiver_val: BasicValueEnum<'llvm>,
        table_index: usize,
    ) -> CompileResult<(PointerValue<'llvm>, PointerValue<'llvm>)> {
        let (existential_ty, struct_ptr, struct_val) = match receiver_ty.kind() {
            TyKind::Reference(inner, _) | TyKind::Pointer(inner, _) => {
                (inner, Some(receiver_val.into_pointer_value()), None)
            }
            TyKind::BoxedExistential { .. } => {
                (receiver_ty, None, Some(receiver_val.into_struct_value()))
            }
            _ => (receiver_ty, None, Some(receiver_val.into_struct_value())),
        };

        let TyKind::BoxedExistential { interfaces } = existential_ty.kind() else {
            let null_ptr = self.context.ptr_type(AddressSpace::default()).const_null();
            return Ok((null_ptr, null_ptr));
        };
        if table_index >= interfaces.len() {
            let null_ptr = self.context.ptr_type(AddressSpace::default()).const_null();
            return Ok((null_ptr, null_ptr));
        }

        let table_field = table_index + 1;
        let Some(BasicTypeEnum::StructType(struct_ty)) = self.lower_ty(existential_ty) else {
            let null_ptr = self.context.ptr_type(AddressSpace::default()).const_null();
            return Ok((null_ptr, null_ptr));
        };

        if let Some(struct_val) = struct_val {
            let data_ptr = self
                .builder
                .build_extract_value(struct_val, 0, "exist_data")
                .unwrap()
                .into_pointer_value();
            let table_ptr = self
                .builder
                .build_extract_value(struct_val, table_field as u32, "exist_table")
                .unwrap()
                .into_pointer_value();
            return Ok((data_ptr, table_ptr));
        }

        let struct_ptr = struct_ptr.expect("existential pointer");
        let data_ptr_gep = self
            .builder
            .build_struct_gep(struct_ty, struct_ptr, 0, "exist_data_ptr")
            .unwrap();
        let data_ptr = self
            .builder
            .build_load(
                self.context.ptr_type(AddressSpace::default()),
                data_ptr_gep,
                "exist_data_load",
            )
            .unwrap()
            .into_pointer_value();
        let table_ptr_gep = self
            .builder
            .build_struct_gep(struct_ty, struct_ptr, table_field as u32, "exist_table_ptr")
            .unwrap();
        let table_ptr = self
            .builder
            .build_load(
                self.context.ptr_type(AddressSpace::default()),
                table_ptr_gep,
                "exist_table_load",
            )
            .unwrap()
            .into_pointer_value();

        Ok((data_ptr, table_ptr))
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
                    let ty = self.lower_ty(place_ty)?;
                    Some(self.builder.build_load(ty, ptr, "load").unwrap())
                }
            };
        }

        let ptr = self.project_place(place, body, locals);
        match ptr {
            Ok(ptr) => {
                let elem_ty = self.lower_ty(place_ty)?;
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
                if self.lower_ty(body.locals[local].ty).is_some() {
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
                    let agg_ty = self.lower_ty(ty).expect("aggregate type lowered");
                    match agg_ty {
                        BasicTypeEnum::StructType(st) => {
                            let gep = self
                                .builder
                                .build_struct_gep(st, ptr, idx.index() as u32, "field_ptr")
                                .unwrap();
                            ptr = gep;
                        }
                        BasicTypeEnum::ArrayType(arr_ty) => {
                            let zero = self.usize_ty.const_zero();
                            let idx_val = self.usize_ty.const_int(idx.index() as u64, false);
                            let gep = unsafe {
                                self.builder
                                    .build_gep(arr_ty, ptr, &[zero, idx_val], "array_elem_ptr")
                                    .unwrap()
                            };
                            ptr = gep;
                        }
                        _ => {
                            panic!(
                                "field projection on non-aggregate type {}",
                                ty.format(self.gcx)
                            )
                        }
                    }

                    ptr_is_storage = true;
                    ty = *field_ty;
                }
                mir::PlaceElem::VariantDowncast { name: _, index } => {
                    let (def, adt_args) = match ty.kind() {
                        TyKind::Adt(def, args)
                            if def.kind == crate::sema::models::AdtKind::Enum =>
                        {
                            (def, args)
                        }
                        _ => panic!("variant downcast on non-enum type {}", ty.format(self.gcx)),
                    };
                    let layout = enum_layout(
                        self.context,
                        self.gcx,
                        &self.target_data,
                        def.id,
                        adt_args,
                        self.current_subst,
                    );
                    let payload_index = layout
                        .payload_field_index
                        .expect("enum payload field index");

                    let enum_ty = self.lower_ty(ty).expect("enum");
                    let enum_struct = enum_ty.into_struct_type();
                    let payload_ptr = self
                        .builder
                        .build_struct_gep(enum_struct, ptr, payload_index, "enum_payload_ptr")
                        .unwrap();

                    let variant_ty = enum_variant_tuple_ty(self.gcx, def.id, *index, adt_args);
                    let _variant_struct = match self.lower_ty(variant_ty) {
                        Some(BasicTypeEnum::StructType(st)) => st,
                        None => self.context.struct_type(&[], false),
                        Some(other) => {
                            panic!("variant tuple lowered to non-struct {:?}", other);
                        }
                    };
                    let variant_ptr = self
                        .builder
                        .build_bit_cast(
                            payload_ptr,
                            self.context.ptr_type(AddressSpace::default()),
                            "enum_variant_ptr",
                        )
                        .unwrap()
                        .into_pointer_value();

                    ptr = variant_ptr;
                    ptr_is_storage = true;
                    ty = variant_ty;
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
                mir::PlaceElem::VariantDowncast { name: _, index } => {
                    let (def, adt_args) = match ty.kind() {
                        TyKind::Adt(def, args)
                            if def.kind == crate::sema::models::AdtKind::Enum =>
                        {
                            (def, args)
                        }
                        _ => panic!("variant downcast on non-enum type {}", ty.format(self.gcx)),
                    };
                    ty = enum_variant_tuple_ty(self.gcx, def.id, *index, adt_args);
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
                let Some(ty) = self.lower_ty(constant.ty) else {
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
            mir::ConstantKind::ConstParam(param) => {
                let konst = crate::sema::models::Const {
                    ty: constant.ty,
                    kind: ConstKind::Param(param),
                };
                let instantiated = instantiate_const_with_args(self.gcx, konst, self.current_subst);
                let ConstKind::Value(value) = instantiated.kind else {
                    self.gcx
                        .dcx()
                        .emit_error("const parameter could not be resolved".into(), None);
                    return None;
                };
                match value {
                    ConstValue::Bool(b) => Some(
                        self.context
                            .bool_type()
                            .const_int(b as u64, false)
                            .as_basic_value_enum(),
                    ),
                    ConstValue::Rune(r) => Some(
                        self.context
                            .i32_type()
                            .const_int(r as u64, false)
                            .as_basic_value_enum(),
                    ),
                    ConstValue::String(sym) => {
                        let ptr = self.lower_string(sym);
                        let len = self.usize_ty.const_int(sym.as_str().len() as u64, false);
                        let Some(ty) = self.lower_ty(constant.ty) else {
                            return None;
                        };
                        let string_ty = ty.into_struct_type();
                        let value = string_ty.const_named_struct(&[
                            ptr.as_basic_value_enum(),
                            len.as_basic_value_enum(),
                        ]);
                        Some(value.as_basic_value_enum())
                    }
                    ConstValue::Integer(i) => self
                        .int_type(constant.ty)
                        .map(|(ty, _)| ty.const_int(i as u64, false).as_basic_value_enum()),
                    ConstValue::Float(f) => self
                        .float_type(constant.ty)
                        .map(|ty| ty.const_float(f).as_basic_value_enum()),
                    ConstValue::Unit => None,
                }
            }
            mir::ConstantKind::Function(def_id, args, _) => {
                let instance = self.instance_for_call(def_id, args);
                if let InstanceKind::Virtual(_) = instance.kind() {
                    todo!("function pointers to virtual interface methods are not supported");
                }
                self.functions
                    .get(&instance)
                    .map(|f| f.as_global_value().as_pointer_value().as_basic_value_enum())
            }
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
        if let Some(f) = self.module.get_function("__gc__alloc") {
            return f;
        }
        let opaque_ptr = self.context.ptr_type(AddressSpace::default());
        let gc_desc_ptr = opaque_ptr;
        let fn_ty = self
            .context
            .ptr_type(AddressSpace::default())
            .fn_type(&[self.usize_ty.into(), gc_desc_ptr.into()], false);
        self.module
            .add_function("__gc__alloc", fn_ty, Some(Linkage::External))
    }

    fn get_gc_poll(&self) -> FunctionValue<'llvm> {
        if let Some(f) = self.module.get_function("__gc__poll") {
            return f;
        }
        let fn_ty = self.context.void_type().fn_type(&[], false);
        self.module
            .add_function("__gc__poll", fn_ty, Some(Linkage::External))
    }

    fn gc_desc_for(&mut self, ty: Ty<'gcx>) -> PointerValue<'llvm> {
        if let Some(&gv) = self.gc_descs.get(&ty) {
            return gv;
        }

        let llvm_ty = self.lower_ty(ty).expect("lower type");
        let size = self.target_data.get_store_size(&llvm_ty);
        let align = self.target_data.get_abi_alignment(&llvm_ty) as u64;

        // Collect pointer field offsets (only direct reference/string/GcPtr fields).
        let mut offsets: Vec<u64> = vec![];
        match ty.kind() {
            TyKind::Adt(def, adt_args) => match def.kind {
                crate::sema::models::AdtKind::Struct => {
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
                crate::sema::models::AdtKind::Enum => {
                    offsets = enum_pointer_offsets(
                        self.context,
                        self.gcx,
                        &self.target_data,
                        def.id,
                        adt_args,
                        self.current_subst,
                    );
                }
            },
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
            TyKind::Array { element, len } => {
                if !is_pointer_ty(element) {
                    // Only track direct pointer-like elements for now.
                } else if let ConstKind::Value(ConstValue::Integer(n)) = len.kind {
                    if n > 0 {
                        let elem_ty = self.lower_ty(element).expect("array element type");
                        let elem_size = self.target_data.get_store_size(&elem_ty);
                        for i in 0..(n as u64) {
                            offsets.push(i * elem_size);
                        }
                    }
                }
            }
            TyKind::String | TyKind::Reference(..) | TyKind::BoxedExistential { .. } => {
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

#[derive(Clone, Copy)]
struct EnumLayout<'llvm> {
    discr_ty: IntType<'llvm>,
    discr_size: u64,
    payload_size: u64,
    payload_offset: u64,
    payload_field_index: Option<u32>,
}

fn align_up(value: u64, align: u64) -> u64 {
    if align == 0 {
        return value;
    }
    let rem = value % align;
    if rem == 0 {
        value
    } else {
        value + (align - rem)
    }
}

fn enum_layout<'llvm, 'gcx>(
    context: &'llvm Context,
    gcx: Gcx<'gcx>,
    target_data: &TargetData,
    def_id: hir::DefinitionID,
    adt_args: GenericArguments<'gcx>,
    subst: GenericArguments<'gcx>,
) -> EnumLayout<'llvm> {
    let def = gcx.get_enum_definition(def_id);
    let discr_ty = context.ptr_sized_int_type(target_data, None);
    let discr_size = target_data.get_store_size(&discr_ty);
    let mut payload_size = 0u64;
    let mut payload_align = 1u64;

    for variant in def.variants.iter() {
        let (size, align) = match variant.kind {
            crate::sema::models::EnumVariantKind::Unit => (0u64, 1u64),
            crate::sema::models::EnumVariantKind::Tuple(fields) => {
                if fields.is_empty() {
                    (0u64, 1u64)
                } else {
                    let struct_ty =
                        enum_variant_struct_ty(context, gcx, target_data, fields, adt_args, subst);
                    let size = target_data.get_store_size(&struct_ty);
                    let align = target_data.get_abi_alignment(&struct_ty) as u64;
                    (size, align)
                }
            }
        };
        payload_size = payload_size.max(size);
        payload_align = payload_align.max(align);
    }

    let payload_offset = align_up(discr_size, payload_align);
    let pad = payload_offset.saturating_sub(discr_size);
    let payload_field_index = if payload_size == 0 {
        None
    } else if pad > 0 {
        Some(2)
    } else {
        Some(1)
    };

    EnumLayout {
        discr_ty,
        discr_size,
        payload_size,
        payload_offset,
        payload_field_index,
    }
}

fn enum_variant_struct_ty<'llvm, 'gcx>(
    context: &'llvm Context,
    gcx: GlobalContext<'gcx>,
    target_data: &TargetData,
    fields: &[crate::sema::models::EnumVariantField<'gcx>],
    adt_args: GenericArguments<'gcx>,
    subst: GenericArguments<'gcx>,
) -> StructType<'llvm> {
    let field_tys: Vec<BasicTypeEnum<'llvm>> = fields
        .iter()
        .filter_map(|field| {
            // Substitute field type with ADT's generic args
            let resolved = instantiate_ty_with_args(gcx, field.ty, adt_args);
            lower_type(context, gcx, target_data, resolved, subst)
        })
        .collect();
    context.struct_type(&field_tys, false)
}

fn enum_variant_tuple_ty<'gcx>(
    gcx: Gcx<'gcx>,
    def_id: hir::DefinitionID,
    variant_index: crate::thir::VariantIndex,
    adt_args: GenericArguments<'gcx>,
) -> Ty<'gcx> {
    let def = gcx.get_enum_definition(def_id);
    let variant = def
        .variants
        .get(variant_index.index())
        .expect("enum variant index");
    match variant.kind {
        crate::sema::models::EnumVariantKind::Unit => gcx.types.void,
        crate::sema::models::EnumVariantKind::Tuple(fields) => {
            let mut tys = Vec::with_capacity(fields.len());
            for field in fields.iter() {
                let resolved = instantiate_ty_with_args(gcx, field.ty, adt_args);
                tys.push(resolved);
            }
            let list = gcx.store.interners.intern_ty_list(tys);
            Ty::new(TyKind::Tuple(list), gcx)
        }
    }
}

fn enum_pointer_offsets<'llvm, 'gcx>(
    context: &'llvm Context,
    gcx: Gcx<'gcx>,
    target_data: &TargetData,
    def_id: hir::DefinitionID,
    adt_args: GenericArguments<'gcx>,
    subst: GenericArguments<'gcx>,
) -> Vec<u64> {
    let def = gcx.get_enum_definition(def_id);
    let layout = enum_layout(context, gcx, target_data, def_id, adt_args, subst);
    let mut offsets = Vec::new();

    for variant in def.variants.iter() {
        let crate::sema::models::EnumVariantKind::Tuple(fields) = variant.kind else {
            continue;
        };
        if fields.is_empty() {
            continue;
        }
        let struct_ty = enum_variant_struct_ty(context, gcx, target_data, fields, adt_args, subst);
        for (idx, field) in fields.iter().enumerate() {
            let resolved = instantiate_ty_with_args(gcx, field.ty, adt_args);
            if !is_pointer_ty(resolved) {
                continue;
            }
            if let Some(off) = target_data.offset_of_element(&struct_ty, idx as u32) {
                offsets.push(layout.payload_offset + off);
            }
        }
    }

    offsets.sort_unstable();
    offsets.dedup();
    offsets
}

fn is_pointer_ty(ty: Ty) -> bool {
    matches!(
        ty.kind(),
        TyKind::Reference(..) | TyKind::String | TyKind::BoxedExistential { .. }
    )
}

fn lower_fn_sig<'llvm, 'gcx>(
    context: &'llvm Context,
    gcx: GlobalContext<'gcx>,
    target_data: &TargetData,
    sig: &crate::sema::models::LabeledFunctionSignature<'gcx>,
) -> FunctionType<'llvm> {
    let params: Vec<BasicMetadataTypeEnum<'llvm>> = sig
        .inputs
        .iter()
        .filter_map(|p| lower_type(context, gcx, target_data, p.ty, &[]).map(|t| t.into()))
        .collect();
    match lower_type(context, gcx, target_data, sig.output, &[]) {
        Some(ret) => ret.fn_type(&params, sig.is_variadic),
        None => context.void_type().fn_type(&params, sig.is_variadic),
    }
}

fn lower_type<'llvm, 'gcx>(
    context: &'llvm Context,
    gcx: GlobalContext<'gcx>,
    target_data: &TargetData,
    ty: Ty<'gcx>,
    subst: GenericArguments<'gcx>,
) -> Option<BasicTypeEnum<'llvm>> {
    // Resolve type parameters first
    let ty = if subst.is_empty() {
        ty
    } else {
        instantiate_ty_with_args(gcx, ty, subst)
    };
    // Normalize all aliases including projections
    let ty = crate::sema::tycheck::utils::normalize_post_monomorphization(gcx, ty);

    match ty.kind() {
        TyKind::Never => None,
        TyKind::Bool => Some(context.bool_type().into()),
        TyKind::Rune => Some(context.i32_type().into()),
        TyKind::String => Some(string_header_ty(context, target_data).into()),
        TyKind::Array { element, len } => {
            let Some(elem_ty) = lower_type(context, gcx, target_data, element, subst) else {
                return None;
            };
            let count = match len.kind {
                ConstKind::Value(ConstValue::Integer(i)) if i >= 0 => usize::try_from(i).ok()?,
                _ => return None,
            };
            Some(elem_ty.array_type(count as u32).into())
        }
        TyKind::Int(i) => Some(int_from_kind(context, target_data, i).into()),
        TyKind::UInt(u) => Some(uint_from_kind(context, target_data, u).into()),
        TyKind::Float(f) => Some(match f {
            FloatTy::F32 => context.f32_type().into(),
            FloatTy::F64 => context.f64_type().into(),
        }),
        TyKind::Adt(def, adt_args) => match def.kind {
            crate::sema::models::AdtKind::Struct => {
                let defn = gcx.get_struct_definition(def.id);
                let field_tys: Vec<BasicTypeEnum<'llvm>> = defn
                    .fields
                    .iter()
                    .filter_map(|f| {
                        // Substitute field type with ADT's generic args
                        let resolved = instantiate_ty_with_args(gcx, f.ty, adt_args);
                        lower_type(context, gcx, target_data, resolved, subst)
                    })
                    .collect();
                Some(context.struct_type(&field_tys, false).into())
            }
            crate::sema::models::AdtKind::Enum => {
                let layout = enum_layout(context, gcx, target_data, def.id, adt_args, subst);
                let mut fields: Vec<BasicTypeEnum<'llvm>> = vec![layout.discr_ty.into()];

                if layout.payload_size == 0 {
                    return Some(context.struct_type(&fields, false).into());
                }

                let pad = layout.payload_offset.saturating_sub(layout.discr_size);
                if pad > 0 {
                    let pad_len = u32::try_from(pad).expect("enum padding fits u32");
                    fields.push(context.i8_type().array_type(pad_len).into());
                }

                let payload_len =
                    u32::try_from(layout.payload_size).expect("enum payload fits u32");
                fields.push(context.i8_type().array_type(payload_len).into());
                Some(context.struct_type(&fields, false).into())
            }
        },
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
                    .filter_map(|t| lower_type(context, gcx, target_data, *t, subst))
                    .collect();
                Some(context.struct_type(&fields, false).into())
            }
        }
        TyKind::FnPointer { .. } => Some(
            context
                .ptr_type(AddressSpace::default())
                .as_basic_type_enum(),
        ),
        TyKind::BoxedExistential { interfaces } => {
            let ptr_ty = context.ptr_type(AddressSpace::default());
            let mut fields: Vec<BasicTypeEnum<'llvm>> = Vec::with_capacity(1 + interfaces.len());
            fields.push(ptr_ty.into());
            for _ in interfaces.iter() {
                fields.push(ptr_ty.into());
            }
            Some(context.struct_type(&fields, false).into())
        }
        TyKind::Parameter(_) => {
            // Should have been resolved by instantiate_ty_with_args above
            unreachable!(
                "ICE: unresolved type parameter in lower_type: {}",
                ty.format(gcx)
            )
        }
        TyKind::Alias { kind, def_id, args } => {
            let formatted = ty.format(gcx);
            let kind_str = match kind {
                crate::sema::models::AliasKind::Weak => "weak alias",
                crate::sema::models::AliasKind::Inherent => "inherent alias",
                crate::sema::models::AliasKind::Projection => "projection",
            };
            unreachable!(
                "ICE: unnormalized {} in codegen: {}\n\
                 This should have been normalized by normalize_post_monomorphization.\n\
                 def_id: {:?}, args: {:?}",
                kind_str, formatted, def_id, args
            )
        }
        TyKind::Closure { closure_def_id, .. } => {
            // Closure is represented as its environment struct
            // Get the captures and build a struct type for them
            if let Some(captures) = gcx.get_closure_captures(closure_def_id) {
                if captures.captures.is_empty() {
                    // Empty closure - zero-sized struct (empty struct in LLVM)
                    Some(context.struct_type(&[], false).into())
                } else {
                    // Build struct from capture field types
                    let fields: Vec<BasicTypeEnum<'llvm>> = captures
                        .captures
                        .iter()
                        .filter_map(|cap| {
                            let field_ty = match cap.capture_kind {
                                crate::sema::models::CaptureKind::ByCopy
                                | crate::sema::models::CaptureKind::ByMove => cap.ty,
                                crate::sema::models::CaptureKind::ByRef { mutable } => {
                                    let mutability = if mutable {
                                        crate::hir::Mutability::Mutable
                                    } else {
                                        crate::hir::Mutability::Immutable
                                    };
                                    Ty::new(TyKind::Reference(cap.ty, mutability), gcx)
                                }
                            };
                            lower_type(context, gcx, target_data, field_ty, subst)
                        })
                        .collect();
                    Some(context.struct_type(&fields, false).into())
                }
            } else {
                // No capture info - use empty struct as fallback
                Some(context.struct_type(&[], false).into())
            }
        }
        TyKind::Infer(_) | TyKind::Error => unreachable!(),
        TyKind::Opaque(_) => {
            // Opaque types have no known layout - they can only appear behind pointers
            unreachable!(
                "ICE: opaque type used directly in codegen: {}",
                ty.format(gcx)
            )
        }
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
