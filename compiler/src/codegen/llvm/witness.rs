use super::{CallTarget, Emitter, LocalStorage, StackMapSiteKind};
use crate::{
    codegen::{
        abi,
        mangle::{interface_ref_key, stable_hash_u64, ty_key},
    },
    error::CompileResult,
    hir,
    mir::{self, Operand, Place},
    sema::{
        models::{
            AssociatedTypeBinding, GenericArgument, GenericArguments, InterfaceDefinition,
            InterfaceReference, InterfaceRequirements, SelectionMode, Ty, TyKind,
        },
        resolve::models::TypeHead,
        tycheck::{
            resolve_conformance_witness_with_mode,
            utils::{type_head_from_value_ty, unresolved::contains_unresolved_generics},
        },
    },
    specialize::{InstanceKind, resolve_instance},
};
use inkwell::{
    AddressSpace,
    basic_block::BasicBlock,
    module::Linkage,
    types::{BasicMetadataTypeEnum, BasicType, BasicTypeEnum, StructType},
    values::{BasicMetadataValueEnum, BasicValue, BasicValueEnum, PointerValue},
};
use rustc_hash::FxHashSet;

impl<'llvm, 'gcx> Emitter<'llvm, 'gcx> {
    fn witness_instance(
        &self,
        id: hir::DefinitionID,
        args: GenericArguments<'gcx>,
    ) -> crate::specialize::Instance<'gcx> {
        resolve_instance(self.gcx, id, args)
    }

    fn debug_witness_subst_enabled(&self) -> bool {
        std::env::var_os("TARO_DEBUG_WITNESS_SUBST").is_some()
    }

    fn debug_format_generic_args(&self, args: GenericArguments<'gcx>) -> String {
        let mut parts = Vec::with_capacity(args.len());
        for arg in args {
            let piece = match arg {
                GenericArgument::Type(ty) => format!("type {}", ty.format(self.gcx)),
                GenericArgument::Const(c) => format!("const {}", c.ty.format(self.gcx)),
            };
            parts.push(piece);
        }
        format!("[{}]", parts.join(", "))
    }

    fn debug_witness_subst(&self, msg: impl AsRef<str>) {
        if self.debug_witness_subst_enabled() {
            eprintln!("[witness-subst] {}", msg.as_ref());
        }
    }

    fn debug_virtual_dispatch_enabled(&self) -> bool {
        std::env::var_os("TARO_DEBUG_VIRTUAL_CALL").is_some()
    }

    fn debug_virtual_dispatch(&self, msg: impl AsRef<str>) {
        if self.debug_virtual_dispatch_enabled() {
            eprintln!("[virtual-call] {}", msg.as_ref());
        }
    }

    pub(super) fn interface_descriptor_ptr(
        &mut self,
        iface: InterfaceReference<'gcx>,
    ) -> PointerValue<'llvm> {
        let canonical =
            crate::sema::impl_engine::ref_ops::descriptor_key_interface_ref(self.gcx, iface);
        if let Some(ptr) = self.interface_descriptors.get(&canonical) {
            return *ptr;
        }

        let key = stable_hash_u64(&interface_ref_key(self.gcx, canonical));
        let symbol = format!("__rt_iface_desc_{key:016x}");

        let gv = if let Some(existing) = self.module.get_global(&symbol) {
            existing
        } else {
            let gv = self.module.add_global(self.usize_ty, None, &symbol);
            gv.set_initializer(&self.usize_ty.const_int(key, false));
            gv.set_constant(true);
            gv.set_linkage(Linkage::LinkOnceODR);
            gv
        };

        let ptr = gv
            .as_pointer_value()
            .const_cast(self.context.ptr_type(AddressSpace::default()));
        self.interface_descriptors.insert(canonical, ptr);
        ptr
    }

    fn collect_interface_and_superfaces_for_metadata(
        &self,
        iface: InterfaceReference<'gcx>,
        seen: &mut FxHashSet<InterfaceReference<'gcx>>,
        out: &mut Vec<InterfaceReference<'gcx>>,
    ) {
        if !seen.insert(iface) {
            return;
        }
        out.push(iface);
        for superface in self.interface_superfaces(iface) {
            self.collect_interface_and_superfaces_for_metadata(superface, seen, out);
        }
    }

    fn collect_conformance_interfaces_for_metadata(
        &self,
        concrete_ty: Ty<'gcx>,
        type_head: Option<TypeHead>,
    ) -> Vec<InterfaceReference<'gcx>> {
        let records = type_head.map_or_else(Vec::new, |type_head| {
            self.gcx.collect_from_databases(|db| {
                db.conformance_by_head
                    .get(&type_head)
                    .map_or_else(Vec::new, |ids| {
                        ids.iter()
                            .filter_map(|id| db.conformance_records.get(id).copied())
                            .collect()
                    })
            })
        });
        let mut seen = FxHashSet::default();
        let mut out = Vec::new();
        // Closures conform through builtin selection rather than impl records.
        // Their runtime metadata must expose the same callable interfaces so
        // erased values support is/as? just like explicitly implemented types.
        if let Some(interface) = crate::sema::models::callable_interface_ref(self.gcx, concrete_ty)
        {
            self.collect_interface_and_superfaces_for_metadata(interface, &mut seen, &mut out);
        }
        // Runtime interface tests/casts must see primitive conformances too,
        // rather than only source-declared implementation records.
        for &item in crate::mir::primitive_operators::ITEMS {
            if let Some(interface) =
                crate::mir::primitive_operators::interface_for_type(self.gcx, concrete_ty, item)
            {
                self.collect_interface_and_superfaces_for_metadata(interface, &mut seen, &mut out);
            }
        }
        for record in records {
            let Some(iface) = self.materialized_interface_for_record(
                record.extension,
                concrete_ty,
                record.interface,
            ) else {
                continue;
            };
            self.collect_interface_and_superfaces_for_metadata(iface, &mut seen, &mut out);
        }
        out
    }

    fn materialized_interface_for_record(
        &self,
        extension_id: hir::DefinitionID,
        concrete_ty: Ty<'gcx>,
        iface: InterfaceReference<'gcx>,
    ) -> Option<InterfaceReference<'gcx>> {
        let extension_args =
            crate::sema::impl_engine::deduce_impl_subst(self.gcx, extension_id, concrete_ty, &[])?;

        let instantiated = if extension_args.is_empty() {
            iface
        } else {
            crate::sema::tycheck::utils::instantiate::instantiate_interface_ref_with_args(
                self.gcx,
                iface,
                extension_args,
            )
        };
        let instantiated = self.interface_args_with_self(concrete_ty, instantiated);
        let instantiated = self.normalize_interface_ref_for_metadata(instantiated);

        if self.conformance_witness(instantiated).is_none() {
            return None;
        }

        Some(instantiated)
    }

    fn normalize_interface_ref_for_metadata(
        &self,
        iface: InterfaceReference<'gcx>,
    ) -> InterfaceReference<'gcx> {
        let args = iface
            .arguments
            .iter()
            .map(|arg| match arg {
                GenericArgument::Type(ty) => {
                    GenericArgument::Type(self.normalize_post_mono_ty(*ty))
                }
                GenericArgument::Const(c) => GenericArgument::Const(*c),
            })
            .collect();
        let args = self.gcx.store.interners.intern_generic_args(args);

        let bindings = iface
            .bindings
            .iter()
            .map(|binding| AssociatedTypeBinding {
                name: binding.name,
                ty: self.normalize_post_mono_ty(binding.ty),
            })
            .collect::<Vec<_>>();
        let bindings = self.gcx.store.arenas.global.alloc_slice_clone(&bindings);

        InterfaceReference {
            id: iface.id,
            arguments: args,
            bindings,
        }
    }

    pub(super) fn type_metadata_ptr(&mut self, concrete_ty: Ty<'gcx>) -> PointerValue<'llvm> {
        let concrete_ty = self.mono_ty(concrete_ty);
        self.gcx
            .store
            .erased_opening_types
            .borrow_mut()
            .entry(self.gcx.package_index())
            .or_default()
            .insert(concrete_ty);
        if let Some(ptr) = self.type_metadata.get(&concrete_ty) {
            return *ptr;
        }

        let opaque_ptr = self.context.ptr_type(AddressSpace::default());
        let type_key: String = ty_key(self.gcx, concrete_ty)
            .bytes()
            .map(|byte| format!("{byte:02x}"))
            .collect();
        let interfaces = self.collect_conformance_interfaces_for_metadata(
            concrete_ty,
            type_head_from_value_ty(concrete_ty),
        );
        // ODR merging must not substitute release-library arithmetic tables
        // into a checked consumer. Keep identity canonical, dispatch contextual.
        let overflow_mode = if self.gcx.config.overflow_checks {
            "checked"
        } else {
            "unchecked"
        };
        let mode = format!("{overflow_mode}_gc");
        let identity = self.erased_type_identity(concrete_ty);
        // Declare metadata before emitting witnesses: recursive Self-result
        // thunks reuse its immutable value-copy descriptor.
        let (metadata_global, metadata_pointer) = {
            let symbol = format!("__gc_type_meta_{type_key}_{mode}");
            let global = self.module.get_global(&symbol).unwrap_or_else(|| {
                self.module
                    .add_global(self.gc_type_metadata_ty(), None, &symbol)
            });
            let pointer = global.as_pointer_value().const_cast(opaque_ptr);
            self.type_metadata.insert(concrete_ty, pointer);
            (global, pointer)
        };

        let mut entry_values = Vec::new();
        let mut descriptor_keys = FxHashSet::default();
        for iface in interfaces {
            if contains_unresolved_generics(iface) {
                continue;
            }
            let Some(_) = self.conformance_witness(iface) else {
                continue;
            };
            let witness_ptr = self.witness_table_ptr(concrete_ty, iface);
            let relative = crate::sema::tycheck::utils::erased_self::abstract_concrete(
                self.gcx,
                iface,
                concrete_ty,
            );
            for descriptor in [iface, relative] {
                let key = crate::sema::impl_engine::ref_ops::descriptor_key_interface_ref(
                    self.gcx, descriptor,
                );
                if !descriptor_keys.insert(key) {
                    continue;
                }
                let iface_desc_ptr = self.interface_descriptor_ptr(descriptor);
                let entry = self.rt_conformance_entry_ty.const_named_struct(&[
                    iface_desc_ptr.as_basic_value_enum(),
                    witness_ptr.as_basic_value_enum(),
                ]);
                entry_values.push(entry);
            }
        }

        let entries_ptr = if entry_values.is_empty() {
            opaque_ptr.const_null()
        } else {
            let entries_ty = self
                .rt_conformance_entry_ty
                .array_type(entry_values.len() as u32);
            let entries_const = self.rt_conformance_entry_ty.const_array(&entry_values);
            let entries_symbol = format!("__rt_type_meta_entries_{type_key}_{mode}");
            let entries_gv = if let Some(existing) = self.module.get_global(&entries_symbol) {
                existing
            } else {
                let gv = self.module.add_global(entries_ty, None, &entries_symbol);
                gv.set_initializer(&entries_const);
                gv.set_constant(true);
                gv.set_linkage(Linkage::LinkOnceODR);
                gv
            };
            entries_gv.as_pointer_value().const_cast(opaque_ptr)
        };

        if metadata_global.get_initializer().is_none() {
            let value = self.gc_value_descriptor_for(concrete_ty);
            metadata_global.set_initializer(
                &self.gc_type_metadata_ty().const_named_struct(&[
                    entries_ptr.as_basic_value_enum(),
                    self.usize_ty
                        .const_int(entry_values.len() as u64, false)
                        .as_basic_value_enum(),
                    identity.as_basic_value_enum(),
                    value.as_basic_value_enum(),
                ]),
            );
            metadata_global.set_constant(true);
            metadata_global.set_linkage(Linkage::LinkOnceODR);
        }
        metadata_pointer
    }

    pub(super) fn witness_table_ptr(
        &mut self,
        concrete_ty: Ty<'gcx>,
        iface: InterfaceReference<'gcx>,
    ) -> PointerValue<'llvm> {
        let iface = self.interface_args_with_self(concrete_ty, iface);

        if let Some(ptr) = self.witness_tables.get(&(concrete_ty, iface)) {
            return *ptr;
        }

        let requirements = match self.interface_requirements(iface.id) {
            Some(req) => req,
            None => return self.context.ptr_type(AddressSpace::default()).const_null(),
        };
        let witness = self.conformance_witness(iface);
        if witness.is_none() {
            return self.context.ptr_type(AddressSpace::default()).const_null();
        }

        // Method pointers followed by direct superface pointers. All entries
        // use the same GC value ABI.
        // The filter below MUST match `ref_ops::method_is_dispatchable` — the
        // same predicate drives slot numbering in sema and the field offsets
        // used by every reader, so any divergence here silently shifts slots.
        // Non-dispatchable methods (static or generic) get no slot at all:
        // sema and monomorphization guarantee no virtual call to them exists.
        let mut entries: Vec<BasicValueEnum<'llvm>> = Vec::new();
        let gcx = self.gcx;
        for method in requirements
            .methods
            .iter()
            .filter(|method| crate::sema::impl_engine::ref_ops::method_is_dispatchable(gcx, method))
        {
            let method_target = if witness
                .as_ref()
                .and_then(|w| w.method_witnesses.get(&method.id))
                .is_some()
            {
                // Build thunk targets in terms of the requirement method and interface call args
                // (`[Self, ...iface generics]`). `resolve_instance` then computes the concrete
                // impl/synthetic/default target with the correct impl substitutions.
                let args = self.complete_interface_call_args(method.id, iface.arguments);
                if self.debug_witness_subst_enabled() {
                    let iface_name = self
                        .gcx
                        .symbol_text(self.gcx.definition_ident(iface.id).symbol);
                    let method_name = self.gcx.symbol_text(method.name);
                    self.debug_witness_subst(format!(
                        "iface {} method {}: call_args={}",
                        iface_name,
                        method_name,
                        self.debug_format_generic_args(args),
                    ));
                }
                if contains_unresolved_generics(args)
                    || !crate::sema::impl_engine::ref_ops::concrete_method_constraints_hold(
                        gcx, method.id, args,
                    )
                {
                    None
                } else {
                    Some((method.id, args))
                }
            } else {
                None
            };

            // Use a thunk to bridge virtual call signature (ptr self) to concrete impl.
            let thunk_ptr = if let Some((impl_def_id, args)) = method_target {
                self.witness_method_thunk(concrete_ty, iface, impl_def_id, args)
            } else {
                self.context.ptr_type(AddressSpace::default()).const_null()
            };
            entries.push(thunk_ptr.as_basic_value_enum());
        }

        let superfaces = self.interface_superfaces(iface);
        for superface in superfaces {
            let ptr = self.witness_table_ptr(concrete_ty, superface);
            entries.push(ptr.as_basic_value_enum());
        }

        let table_ty = self.witness_table_struct_ty(iface.id);
        // `const_named_struct` does not validate arity and LLVM's module
        // verifier does not catch the mismatch either: an undersized
        // initializer is accepted silently and reads of the missing fields
        // return garbage at runtime. This assert turns any future drift
        // between the writer above and `witness_table_struct_ty` into an
        // immediate compiler panic instead of a miscompiled program.
        assert_eq!(
            entries.len() as u32,
            table_ty.count_fields(),
            "witness table entry count must match its struct type (interface {:?})",
            iface.id
        );
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
        self.witness_tables.insert((concrete_ty, iface), opaque_ptr);
        opaque_ptr
    }

    /// Only a direct owned Self result has the approved re-erasure contract.
    /// Associated/defaulted and nested Self results need separate rules.
    fn method_returns_owned_self(&self, method: hir::DefinitionID) -> bool {
        !self.gcx.definition_is_async(method)
            && crate::sema::tycheck::utils::erased_self::returns_owned_self(self.gcx, method)
    }

    /// Adapt an erased payload address to the implementation's receiver ABI.
    fn witness_method_thunk(
        &mut self,
        concrete_ty: Ty<'gcx>,
        iface: InterfaceReference<'gcx>,
        impl_def_id: hir::DefinitionID,
        args: GenericArguments<'gcx>,
    ) -> PointerValue<'llvm> {
        if contains_unresolved_generics(args) {
            return self.context.ptr_type(AddressSpace::default()).const_null();
        }
        // Check cache first
        let cache_key = (concrete_ty, iface, impl_def_id);
        if let Some(&ptr) = self.witness_thunks.get(&cache_key) {
            return ptr;
        }

        // Get the concrete implementation function
        let impl_instance = self.witness_instance(impl_def_id, args);
        let impl_target_def_id = impl_instance.def_id();
        // Codegen cannot create bodies. A witness that still names a
        // requirement without a default body means sema never demanded the
        // implementation; report it here rather than emitting a trap reached
        // by the first dynamic call.
        let bodyless_requirement = self.interface_requirements(iface.id).is_some_and(|req| {
            req.methods
                .iter()
                .any(|method| method.id == impl_target_def_id && method.is_required)
        });
        if bodyless_requirement && !self.instance_has_mir_body(impl_instance) {
            let method = self.gcx.definition_ident(impl_def_id).symbol;
            self.gcx.dcx().emit_error(
                format!(
                    "internal error: `{}: {}` has no implementation of `{}` for dynamic dispatch",
                    concrete_ty.format(self.gcx),
                    iface.format(self.gcx),
                    self.gcx.symbol_text(method),
                ),
                self.current_span,
            );
            return self.context.ptr_type(AddressSpace::default()).const_null();
        }
        let (impl_fn, impl_fn_abi) = self.instance_function_with_abi(impl_instance);

        // Get the implementation signature
        let prev_subst = self.current_subst;
        self.current_subst = impl_instance.args();
        let sig = self.gcx.get_signature(impl_target_def_id);
        let erase_self_result = self.method_returns_owned_self(impl_def_id);

        let self_input_ty = sig.inputs.first().map(|p| self.mono_ty(p.ty));
        let concrete_self = self.mono_ty(iface.self_ty().expect("witness Self"));
        // Computed accessors still receive &Self until G39. A declaration on
        // &T instead receives Self = &T by value: its pointer header must load.
        let receiver_is_address = self_input_ty
            .is_some_and(|ty| matches!(ty.kind(), TyKind::Reference(_)) && ty != concrete_self);
        let opaque_ptr = self.context.ptr_type(AddressSpace::default());
        let mut thunk_param_types: Vec<BasicMetadataTypeEnum<'llvm>> =
            Vec::with_capacity(sig.inputs.len() + 1);
        if !erase_self_result && matches!(impl_fn_abi.ret.mode, abi::PassMode::Indirect { .. }) {
            thunk_param_types.push(opaque_ptr.into());
        }
        thunk_param_types.push(opaque_ptr.into());
        for arg_abi in impl_fn_abi.args.iter().skip(1) {
            match arg_abi.mode {
                abi::PassMode::Ignore => {}
                abi::PassMode::Direct => {
                    if let Some(ty) = self.lower_ty(arg_abi.ty) {
                        thunk_param_types.push(ty.into());
                    }
                }
                abi::PassMode::Indirect { .. } => {
                    thunk_param_types.push(opaque_ptr.into());
                }
            }
        }

        // Build thunk return type
        let thunk_fn_ty = if erase_self_result {
            opaque_ptr.fn_type(&thunk_param_types, false)
        } else {
            match impl_fn_abi.ret.mode {
                abi::PassMode::Ignore | abi::PassMode::Indirect { .. } => {
                    self.context.void_type().fn_type(&thunk_param_types, false)
                }
                abi::PassMode::Direct => match self.lower_ty(impl_fn_abi.ret.ty) {
                    Some(ret) => ret.fn_type(&thunk_param_types, false),
                    None => self.context.void_type().fn_type(&thunk_param_types, false),
                },
            }
        };

        // Create thunk function
        let thunk_name = format!(
            "__wt_thunk_{}_{}",
            self.witness_thunks.len(),
            self.gcx.definition_ident(impl_target_def_id).symbol,
        );
        // Thunk names use a module-local numeric index, just like their
        // internal witness tables. Keep the functions internal as well so a
        // downstream package can materialize its own thunks without colliding
        // with thunks already emitted into a dependency object.
        let thunk_fn = self
            .module
            .add_function(&thunk_name, thunk_fn_ty, Some(Linkage::Internal));

        // This bridge can call a collecting implementation even when LLVM
        // proves the result constant. Without unwind metadata, a non-leaf
        // optimized thunk can hide the caller's roots from the native walker.
        self.preserve_diagnostic_frame(thunk_fn);

        // Save current position and build thunk body
        let current_block = self.builder.get_insert_block();
        let previous_span = self.current_span;
        self.current_span = Some(self.gcx.definition_ident(impl_target_def_id).span);
        let entry = self.context.append_basic_block(thunk_fn, "entry");
        self.builder.position_at_end(entry);

        // Gather arguments: first is the data pointer, rest are passed through
        let mut call_args: Vec<BasicMetadataValueEnum<'llvm>> =
            Vec::with_capacity(thunk_param_types.len());

        let mut param_index = 0u32;
        let concrete_output = self.mono_ty(impl_fn_abi.ret.ty);
        let result_storage = if erase_self_result
            && matches!(impl_fn_abi.ret.mode, abi::PassMode::Indirect { .. })
        {
            let ty = self
                .lower_ty(concrete_output)
                .expect("owned Self result layout");
            Some(self.build_entry_alloca(ty, "self_result"))
        } else {
            None
        };
        if matches!(impl_fn_abi.ret.mode, abi::PassMode::Indirect { .. }) {
            if let Some(storage) = result_storage {
                call_args.push(storage.into());
            } else {
                call_args.push(thunk_fn.get_nth_param(param_index).unwrap().into());
                param_index += 1;
            }
        }

        // The thunk receives the address of the stored Self value.
        let receiver_param = thunk_fn.get_nth_param(param_index).unwrap();
        // Metadata contains stable table/type-token pointers, without payload roots.
        let result_metadata = if erase_self_result {
            Some(self.type_metadata_ptr(concrete_output))
        } else {
            None
        };

        // The receiver arrives as a pointer to the callee's own value; loading
        // from it is the copy.
        let self_ptr = receiver_param.into_pointer_value();
        if let Some(self_abi) = impl_fn_abi.args.first() {
            match self_abi.mode {
                abi::PassMode::Ignore => {}
                abi::PassMode::Direct => {
                    if receiver_is_address {
                        call_args.push(self_ptr.into());
                    } else if let Some(load_ty) = self.lower_ty(self_abi.ty) {
                        let loaded = self
                            .builder
                            .build_load(load_ty, self_ptr, "thunk_self_load")
                            .unwrap();
                        call_args.push(loaded.into());
                    } else {
                        call_args.push(self_ptr.into());
                    }
                }
                abi::PassMode::Indirect { .. } => {
                    call_args.push(self_ptr.into());
                }
            }
        }
        param_index += 1;

        // Forward remaining arguments according to implementation ABI.
        for arg_abi in impl_fn_abi.args.iter().skip(1) {
            if matches!(arg_abi.mode, abi::PassMode::Ignore) {
                continue;
            }
            call_args.push(thunk_fn.get_nth_param(param_index).unwrap().into());
            param_index += 1;
        }

        // A concrete stored Base handle can still identify a Derived object.
        // Keep the exact receiver ABI, then use ordinary class
        // dispatch so direct, generic and erased calls reach the same override.
        let class = self_input_ty
            .map(|ty| match ty.kind() {
                TyKind::Reference(class) => class,
                _ => ty,
            })
            .filter(|ty| self.gcx.is_class_type(*ty));
        let virtual_target = if let Some(class) = class {
            let handle = self
                .builder
                .build_load(
                    self.lower_ty(class).unwrap(),
                    self_ptr,
                    "witness_class_handle",
                )
                .unwrap();
            self.class_handle_call_target(impl_instance, handle)
                .unwrap_or_else(|_| panic!("class witness dispatch requires a native target"))
        } else {
            None
        };
        let call = match virtual_target {
            Some((CallTarget::Indirect(signature, target), _)) => self
                .builder
                .build_indirect_call(signature, target, &call_args, "thunk_virtual_call")
                .unwrap(),
            Some((CallTarget::Direct(target), _)) => self
                .builder
                .build_call(target, &call_args, "thunk_call")
                .unwrap(),
            None => self
                .builder
                .build_call(impl_fn, &call_args, "thunk_call")
                .unwrap(),
        };

        // Return traced payload storage regardless of the concrete size or
        // the caller's interface intersection.
        if erase_self_result {
            let value = if let Some(storage) = result_storage {
                self.builder
                    .build_load(
                        self.lower_ty(concrete_output).unwrap(),
                        storage,
                        "self_result_load",
                    )
                    .unwrap()
            } else if let Some(value) = call.try_as_basic_value().basic() {
                value
            } else {
                self.context.struct_type(&[], false).get_undef().into()
            };
            let data = self.box_gc_value(concrete_output, value, result_metadata.unwrap(), false);
            self.builder.build_return(Some(&data)).unwrap();
        } else {
            match impl_fn_abi.ret.mode {
                abi::PassMode::Ignore | abi::PassMode::Indirect { .. } => {
                    self.builder.build_return(None).unwrap();
                }
                abi::PassMode::Direct => {
                    if let Some(ret_val) = call.try_as_basic_value().basic() {
                        self.builder.build_return(Some(&ret_val)).unwrap();
                    } else {
                        self.builder.build_return(None).unwrap();
                    }
                }
            }
        }

        // Restore builder position
        if let Some(block) = current_block {
            self.builder.position_at_end(block);
        }

        self.current_subst = prev_subst;
        self.current_span = previous_span;

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
            db.interface_requirements.get(&interface_id).cloned()
        })
    }

    fn interface_definition(
        &self,
        interface_id: hir::DefinitionID,
    ) -> Option<&'gcx InterfaceDefinition<'gcx>> {
        self.gcx.with_type_database(interface_id.package(), |db| {
            db.def_to_iface_def.get(&interface_id).cloned()
        })
    }

    pub(super) fn conformance_witness(
        &self,
        interface: InterfaceReference<'gcx>,
    ) -> Option<crate::sema::models::ConformanceWitness<'gcx>> {
        resolve_conformance_witness_with_mode(self.gcx, interface, SelectionMode::Codegen)
    }

    /// Number of method slots in an interface's witness table. Superface
    /// table pointers live directly after the method slots, so this is also
    /// the base offset for superface fields. Delegates to sema so that table
    /// layout and sema's slot numbering cannot drift apart (the previous
    /// unfiltered `methods.len()` here disagreed with the filtered table
    /// writer and corrupted every superface lookup).
    pub(super) fn witness_method_slot_count(&self, interface_id: hir::DefinitionID) -> usize {
        crate::sema::impl_engine::ref_ops::dispatchable_method_count(self.gcx, interface_id)
    }

    pub(super) fn interface_superfaces(
        &self,
        iface: InterfaceReference<'gcx>,
    ) -> Vec<InterfaceReference<'gcx>> {
        crate::sema::impl_engine::ref_ops::direct_superfaces(self.gcx, iface)
    }

    pub(super) fn interface_args_with_self(
        &self,
        self_ty: Ty<'gcx>,
        iface: InterfaceReference<'gcx>,
    ) -> InterfaceReference<'gcx> {
        crate::sema::impl_engine::ref_ops::interface_ref_with_self(self.gcx, self_ty, iface)
    }

    fn complete_interface_call_args(
        &self,
        method_id: hir::DefinitionID,
        args: GenericArguments<'gcx>,
    ) -> GenericArguments<'gcx> {
        let Some(parent) = self.gcx.definition_parent(method_id) else {
            return args;
        };
        if self.gcx.definition_kind(parent)
            != crate::sema::resolve::models::DefinitionKind::Interface
        {
            return args;
        }

        crate::sema::impl_engine::ref_ops::complete_interface_arguments(self.gcx, parent, args)
            .unwrap_or(args)
    }

    /// LLVM struct type for an interface's witness table:
    /// `{ <method ptrs...>, <superface ptrs...> }`.
    /// Must mirror the entry list built in `witness_table_ptr` exactly — the
    /// arity assert there enforces it.
    pub(super) fn witness_table_struct_ty(
        &self,
        interface_id: hir::DefinitionID,
    ) -> StructType<'llvm> {
        let method_count = self.witness_method_slot_count(interface_id);
        let super_count = self
            .interface_definition(interface_id)
            .map(|def| def.superfaces.len())
            .unwrap_or(0);
        let total = method_count + super_count;
        let ptr_ty = self.context.ptr_type(AddressSpace::default());
        let fields: Vec<BasicTypeEnum<'llvm>> = (0..total).map(|_| ptr_ty.into()).collect();
        self.context.struct_type(&fields, false)
    }

    pub(super) fn virtual_instance_for_call(
        &self,
        func: &Operand<'gcx>,
    ) -> Option<crate::specialize::VirtualInstance<'gcx>> {
        let Operand::Constant(c) = func else {
            return None;
        };
        let mir::ConstantKind::Function(def_id, args, _) = c.value else {
            return None;
        };
        // Resolve generic args with the current monomorphization substitution
        // context so that `Self = T` becomes `Self = any Interface` (or the
        // concrete type) before we ask resolve_instance to decide between
        // direct and virtual dispatch.
        let args = self.resolve_generic_args(args);
        let instance = resolve_instance(self.gcx, def_id, args);
        match instance.kind() {
            InstanceKind::Virtual(instance) => Some(instance),
            InstanceKind::Item(_) => None,
        }
    }

    pub(super) fn lower_virtual_call(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        instance: &crate::specialize::VirtualInstance<'gcx>,
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
        unwind_target: Option<BasicBlock<'llvm>>,
        stack_map: Option<crate::span::Span>,
    ) -> CompileResult<()> {
        let receiver = args.first().expect("virtual call missing receiver");
        let receiver_ty = self.operand_ty(body, receiver);
        let method_name = self.gcx.definition_symbol_or_fallback(instance.method_id);
        let iface_name = self
            .gcx
            .definition_symbol_or_fallback(instance.method_interface.id);
        self.debug_virtual_dispatch(format!(
            "method={:?} ({}) iface={:?} ({}) slot={} table_index={} receiver_ty={}",
            instance.method_id,
            self.gcx.symbol_text(method_name),
            instance.method_interface.id,
            self.gcx.symbol_text(iface_name),
            instance.slot,
            instance.table_index,
            receiver_ty.format(self.gcx)
        ));
        let Some(receiver_val) = self.eval_operand(body, locals, receiver)? else {
            return Ok(());
        };

        let self_ty = match receiver_ty.kind() {
            TyKind::Reference(inner) | TyKind::Pointer(inner, _) => inner,
            _ => receiver_ty,
        };

        let TyKind::BoxedExistential { interfaces } = self_ty.kind() else {
            return Ok(());
        };
        let Some(root_iface) = interfaces.get(instance.table_index).cloned() else {
            return Ok(());
        };

        let (data_ptr, root_table_ptr) =
            self.extract_existential_parts(receiver_ty, receiver_val, instance.table_index)?;
        let erase_self_result = self.method_returns_owned_self(instance.method_id);
        let receiver_metadata = if erase_self_result {
            let (_, header) =
                self.normalize_cast_source_existential_ref(receiver_ty, receiver_val)?;
            Some(
                self.builder
                    .build_extract_value(header.into_struct_value(), 1, "self_metadata")
                    .unwrap()
                    .into_pointer_value(),
            )
        } else {
            None
        };
        let receiver_ptr = { data_ptr };

        let method_table_ptr = if crate::sema::impl_engine::ref_ops::interface_ref_matches(
            instance.method_interface,
            root_iface,
            crate::sema::impl_engine::ref_ops::InterfaceRefMatch::Logical,
        ) {
            root_table_ptr
        } else if let Some(chain) =
            crate::sema::impl_engine::ref_ops::superface_chain_to_interface_ref(
                self.gcx,
                root_iface,
                instance.method_interface,
            )
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
                // Superface table pointers are stored after the method slots,
                // so the field offset is the dispatchable-method count (NOT
                // the raw requirement count) plus the superface's position.
                let field_index = self.witness_method_slot_count(current_iface) + super_index;
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

        let method_table_ty = self.witness_table_struct_ty(instance.method_interface.id);
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

        // Classify the non-receiver arguments and the return with the same ABI
        // rules the witness thunk uses for its parameters (witness_method_thunk),
        // so large aggregates are passed indirectly on both sides of the
        // virtual-call boundary instead of the caller handing a value where the
        // thunk expects a pointer.
        let arg_input_tys: Vec<_> = args
            .iter()
            .skip(1)
            .map(|arg| self.mono_ty_if_resolved(self.operand_ty(body, arg)))
            .collect();
        let output = self.mono_ty_if_resolved(self.place_ty(body, destination));
        let virt_fn_abi = abi::compute_fn_abi_from_tys(
            &arg_input_tys,
            if erase_self_result {
                Ty::new(
                    TyKind::Pointer(self.gcx.types.uint8, hir::Mutability::Mutable),
                    self.gcx,
                )
            } else {
                output
            },
            false,
            |ty| self.type_layout(ty),
            abi::AbiPolicy {
                enable_indirect_returns: true,
                indirect_return_threshold_bytes: self.indirect_return_threshold_bytes,
                enable_indirect_args: true,
                indirect_arg_threshold_bytes: self.indirect_arg_threshold_bytes,
            },
        );
        let ret_mode = virt_fn_abi.ret.mode;
        let mut lowered_args =
            self.lower_call_args_with_fn_abi(body, locals, &args[1..], destination, &virt_fn_abi)?;
        // The existential data pointer takes the receiver slot, right after the
        // sret parameter when the return is indirect.
        let receiver_index = usize::from(matches!(ret_mode, abi::PassMode::Indirect { .. }));
        let receiver_argument = { receiver_ptr.as_basic_value_enum() };
        lowered_args.insert(receiver_index, receiver_argument);

        let param_types: Vec<BasicMetadataTypeEnum<'llvm>> = lowered_args
            .iter()
            .map(|arg| arg.get_type().into())
            .collect();
        let fn_ty = match ret_mode {
            abi::PassMode::Indirect { .. } | abi::PassMode::Ignore => {
                self.context.void_type().fn_type(&param_types, false)
            }
            abi::PassMode::Direct => {
                let ret_ty = virt_fn_abi.ret.ty;
                match self.lower_ty(ret_ty) {
                    Some(ret) => ret.fn_type(&param_types, false),
                    None => self.context.void_type().fn_type(&param_types, false),
                }
            }
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
        if let Some(span) = stack_map {
            self.emit_source_typed_gc_stack_map(span, StackMapSiteKind::Call);
        }
        let call_site = self.emit_call_maybe_unwind(
            CallTarget::Indirect(fn_ty, fn_ptr_cast),
            &lowered_args,
            unwind_target,
            "virt_call",
        )?;

        if erase_self_result {
            let owner = call_site
                .try_as_basic_value()
                .basic()
                .expect("owned Self witness result")
                .into_pointer_value();
            let value = self.existential_from_gc_payload(
                output,
                owner,
                receiver_metadata.expect("Self result metadata"),
            );
            self.store_place(destination, body, locals, value)?;
        } else {
            self.store_call_result(body, locals, destination, &virt_fn_abi, call_site)?;
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
            TyKind::Reference(inner) | TyKind::Pointer(inner, _) => {
                (inner, Some(self.reference_data(receiver_val)), None)
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

        let table_field = table_index + 2;
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
}

#[cfg(test)]
mod borrow_guard_tests {
    use super::*;
    use inkwell::{context::Context, values::AnyValue};

    #[test]
    fn conditional_methods_keep_slots_without_materializing_unavailable_bodies() {
        crate::test_support::analyze_script(
            r#"
interface Ordered { func greater() -> bool; }
interface View {
    type Element
    func size() -> int32;
    func maximum() -> int32 where Self::Element: Ordered { 0 }
}
struct Label {}
conform Label to View {
    type Element = Label
    func size() -> int32 { 1 }
}
struct Number {}
conform Number to Ordered {
    func greater() -> bool { true }
}
conform Number to View {
    type Element = Number
    func size() -> int32 { 1 }
}
func main() {}
"#,
            |package, gcx| {
                let find = |name: &str| {
                    package
                        .root
                        .declarations
                        .iter()
                        .find(|d| d.identifier.symbol.as_str() == name)
                        .unwrap()
                        .id
                };
                let interface = find("View");
                let context = Context::create();
                let mut emitter = Emitter::new(
                    &context,
                    context.create_module("conditional-witness"),
                    context.create_builder(),
                    gcx,
                )
                .unwrap_or_else(|_| panic!("conditional witness emitter"));
                for (name, available) in [("Label", false), ("Number", true)] {
                    let ty = gcx.get_type(find(name));
                    let iface = InterfaceReference {
                        id: interface,
                        arguments: gcx
                            .store
                            .interners
                            .intern_generic_args(vec![GenericArgument::Type(ty)]),
                        bindings: &[],
                    };
                    let ptr = emitter.witness_table_ptr(ty, iface);
                    assert!(!ptr.is_null());
                    let table = emitter
                        .module
                        .get_global(ptr.get_name().to_str().unwrap())
                        .unwrap();
                    let ir = table.print_to_string().to_string();
                    assert_eq!(ir.contains("ptr null"), !available, "{name}: {ir}");
                    assert_eq!(
                        emitter.witness_table_struct_ty(interface).count_fields(),
                        2,
                        "conditional availability must not alter method slot offsets"
                    );
                }
                emitter.module.verify().unwrap();
            },
        );
    }

    #[test]
    fn inherited_accessor_witness_passes_the_class_handle_value() {
        crate::test_support::analyze_script(
            "interface Read { var value: int32 { get }; }\nclass Base { data: int32 }\nextend Base { init(_ data: int32) { self.data = data }; }\nconform Base to Read { var value: int32 { get { self.data } }; }\nclass Derived: Base {}\nfunc main() {}",
            |package, gcx| {
                let find = |name: &str| {
                    package
                        .root
                        .declarations
                        .iter()
                        .find(|declaration| declaration.identifier.symbol.as_str() == name)
                        .unwrap()
                        .id
                };
                let concrete = gcx.get_type(find("Derived"));
                let interface = InterfaceReference {
                    id: find("Read"),
                    arguments: gcx.store.interners.intern_generic_args(vec![
                        crate::sema::models::GenericArgument::Type(concrete),
                    ]),
                    bindings: &[],
                };
                let context = Context::create();
                let module = context.create_module("inherited-accessor-receiver");
                let mut emitter = Emitter::new(&context, module, context.create_builder(), gcx)
                    .unwrap_or_else(|_| panic!("inherited accessor emitter"));
                emitter.witness_table_ptr(concrete, interface);
                let thunk = emitter
                    .module
                    .get_functions()
                    .find(|function| {
                        function
                            .get_name()
                            .to_str()
                            .unwrap()
                            .starts_with("__wt_thunk_")
                    })
                    .unwrap();
                let ir = thunk.print_to_string().to_string();
                assert!(
                    ir.contains("thunk_self_load") && ir.contains("thunk_virtual_call"),
                    "an inherited implicit getter receives the shared class handle value: {ir}"
                );
                emitter.module.verify().unwrap();
            },
        );
    }

    #[test]
    fn witness_receivers_pass_plain_gc_addresses_without_protocol_tags() {
        for referenced in [false, true] {
            let target = if referenced { "&Counter" } else { "Counter" };
            let source = format!(
                "interface Probe {{\n    func read() -> int32\n}}\n\
                 struct Counter {{\n    value: int32\n}}\n\
                 conform {target} to Probe {{\n    func read() -> int32 {{ self.value; }}\n}}\n\
                 func main() {{}}\n"
            );
            crate::test_support::analyze_script(&source, |package, gcx| {
                let interface = package
                    .root
                    .declarations
                    .iter()
                    .find(|d| d.identifier.symbol.as_str() == "Probe")
                    .unwrap()
                    .id;
                let structure = package
                    .root
                    .declarations
                    .iter()
                    .find(|d| d.identifier.symbol.as_str() == "Counter")
                    .unwrap()
                    .id;
                let definition = gcx.get_struct_definition(structure);
                let concrete = Ty::new(
                    TyKind::Adt(definition.adt_def, GenericArguments::empty()),
                    gcx,
                );
                let concrete = if referenced {
                    Ty::new(TyKind::Reference(concrete), gcx)
                } else {
                    concrete
                };
                let iface = InterfaceReference {
                    id: interface,
                    arguments: gcx
                        .store
                        .interners
                        .intern_generic_args(vec![GenericArgument::Type(concrete)]),
                    bindings: &[],
                };
                let context = Context::create();
                let module = context.create_module("witness-borrow-guard");
                let mut emitter = Emitter::new(&context, module, context.create_builder(), gcx)
                    .unwrap_or_else(|_| panic!("witness emitter"));
                let table = emitter.witness_table_ptr(concrete, iface);
                assert!(
                    !table.is_null(),
                    "test conformance must generate a real table"
                );
                assert_eq!(emitter.witness_table_struct_ty(interface).count_fields(), 1);
                let thunk = emitter
                    .module
                    .get_functions()
                    .find(|f| f.get_name().to_str().unwrap().starts_with("__wt_thunk_"))
                    .unwrap();
                assert_eq!(
                    thunk.get_type().get_param_types()[0],
                    context.ptr_type(AddressSpace::default()).into(),
                    "GC reference receivers carry one address"
                );
                let ir = thunk.print_to_string().to_string();
                assert!(ir.contains("thunk_call"));
                assert!(
                    ir.contains("thunk_self_load"),
                    "value receivers, including reference headers, must load the erased payload: {ir}"
                );
                assert!(!ir.contains("__rt__borrow_"));
                assert!(!ir.contains("__rt__arc_"));
                emitter.module.verify().unwrap();
            });
        }
    }
}
