use super::{Emitter, LocalStorage};
use crate::{
    codegen::{abi, mangle::mangle_instance},
    error::CompileResult,
    hir,
    mir::{self, Operand, Place},
    sema::{
        models::{
            AssociatedTypeBinding, ConstKind, GenericArgument, GenericArguments,
            InterfaceDefinition, InterfaceReference, InterfaceRequirements, SelectionMode, Ty,
            TyKind,
        },
        resolve::models::TypeHead,
        tycheck::{
            resolve_conformance_witness_with_mode,
            utils::{instantiate::instantiate_ty_with_args, type_head_from_value_ty},
        },
    },
    specialize::{Instance, InstanceKind, resolve_instance},
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

        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        std::hash::Hash::hash(&canonical, &mut hasher);
        let key = std::hash::Hasher::finish(&hasher);
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

    fn ty_contains_unresolved_generics(&self, ty: Ty<'gcx>) -> bool {
        match ty.kind() {
            TyKind::Parameter(_) | TyKind::Infer(_) | TyKind::Alias { .. } => true,
            TyKind::Adt(_, args) => args.iter().any(|arg| match arg {
                GenericArgument::Type(ty) => self.ty_contains_unresolved_generics(*ty),
                GenericArgument::Const(c) => self.const_contains_unresolved_generics(*c),
            }),
            TyKind::Pointer(inner, _) | TyKind::Reference(inner, _) => {
                self.ty_contains_unresolved_generics(inner)
            }
            TyKind::Array { element, len } => {
                self.ty_contains_unresolved_generics(element)
                    || self.const_contains_unresolved_generics(len)
            }
            TyKind::Tuple(items) => items
                .iter()
                .any(|item| self.ty_contains_unresolved_generics(*item)),
            TyKind::FnPointer { inputs, output } => {
                inputs
                    .iter()
                    .any(|input| self.ty_contains_unresolved_generics(*input))
                    || self.ty_contains_unresolved_generics(output)
            }
            TyKind::BoxedExistential { interfaces } => interfaces
                .iter()
                .any(|iface| !self.interface_ref_is_runtime_materializable(*iface)),
            _ => false,
        }
    }

    fn const_contains_unresolved_generics(&self, c: crate::sema::models::Const<'gcx>) -> bool {
        matches!(c.kind, ConstKind::Param(_) | ConstKind::Infer(_))
            || self.ty_contains_unresolved_generics(c.ty)
    }

    fn interface_ref_is_runtime_materializable(&self, iface: InterfaceReference<'gcx>) -> bool {
        iface.arguments.iter().all(|arg| match arg {
            GenericArgument::Type(ty) => !self.ty_contains_unresolved_generics(*ty),
            GenericArgument::Const(c) => !self.const_contains_unresolved_generics(*c),
        }) && iface
            .bindings
            .iter()
            .all(|binding| !self.ty_contains_unresolved_generics(binding.ty))
    }

    fn generic_args_are_runtime_materializable(&self, args: GenericArguments<'gcx>) -> bool {
        args.iter().all(|arg| match arg {
            GenericArgument::Type(ty) => !self.ty_contains_unresolved_generics(*ty),
            GenericArgument::Const(c) => !self.const_contains_unresolved_generics(*c),
        })
    }

    fn collect_conformance_interfaces_for_metadata(
        &self,
        concrete_ty: Ty<'gcx>,
        type_head: TypeHead,
    ) -> Vec<InterfaceReference<'gcx>> {
        let records = self.gcx.collect_from_databases(|db| {
            db.conformance_by_head
                .get(&type_head)
                .map_or_else(Vec::new, |ids| {
                    ids.iter()
                        .filter_map(|id| db.conformance_records.get(id).copied())
                        .collect()
                })
        });
        let mut seen = FxHashSet::default();
        let mut out = Vec::new();
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
            crate::sema::impl_engine::ref_ops::substitute_interface_ref(
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
        if let Some(ptr) = self.type_metadata.get(&concrete_ty) {
            return *ptr;
        }

        let opaque_ptr = self.context.ptr_type(AddressSpace::default());
        let Some(type_head) = type_head_from_value_ty(concrete_ty) else {
            let null_ptr = opaque_ptr.const_null();
            self.type_metadata.insert(concrete_ty, null_ptr);
            return null_ptr;
        };

        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        std::hash::Hash::hash(&concrete_ty, &mut hasher);
        let type_key = std::hash::Hasher::finish(&hasher);
        let interfaces = self.collect_conformance_interfaces_for_metadata(concrete_ty, type_head);

        let mut entry_values = Vec::new();
        for iface in interfaces {
            if !self.interface_ref_is_runtime_materializable(iface) {
                continue;
            }
            let Some(_) = self.conformance_witness(iface) else {
                continue;
            };
            let iface_desc_ptr = self.interface_descriptor_ptr(iface);
            let witness_ptr = self.witness_table_ptr(concrete_ty, iface);
            let entry = self.rt_conformance_entry_ty.const_named_struct(&[
                iface_desc_ptr.as_basic_value_enum(),
                witness_ptr.as_basic_value_enum(),
            ]);
            entry_values.push(entry);
        }

        let entries_ptr = if entry_values.is_empty() {
            opaque_ptr.const_null()
        } else {
            let entries_ty = self
                .rt_conformance_entry_ty
                .array_type(entry_values.len() as u32);
            let entries_const = self.rt_conformance_entry_ty.const_array(&entry_values);
            let entries_symbol = format!("__rt_type_meta_entries_{type_key:016x}");
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

        let metadata_const = self.rt_type_metadata_ty.const_named_struct(&[
            entries_ptr.as_basic_value_enum(),
            self.usize_ty
                .const_int(entry_values.len() as u64, false)
                .as_basic_value_enum(),
        ]);
        let metadata_symbol = format!("__rt_type_meta_{type_key:016x}");
        let metadata_gv = if let Some(existing) = self.module.get_global(&metadata_symbol) {
            existing
        } else {
            let gv = self
                .module
                .add_global(self.rt_type_metadata_ty, None, &metadata_symbol);
            gv.set_initializer(&metadata_const);
            gv.set_constant(true);
            gv.set_linkage(Linkage::LinkOnceODR);
            gv
        };
        let metadata_ptr = metadata_gv.as_pointer_value().const_cast(opaque_ptr);
        self.type_metadata.insert(concrete_ty, metadata_ptr);
        metadata_ptr
    }

    pub(super) fn witness_table_ptr(
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
        let witness = self.conformance_witness(iface);
        if witness.is_none() {
            return self.context.ptr_type(AddressSpace::default()).const_null();
        }

        // Table layout: one pointer slot per dispatchable method (in
        // requirements order), then one pointer per direct superface table.
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
                if !self.generic_args_are_runtime_materializable(args) {
                    None
                } else {
                    Some((method.id, args))
                }
            } else {
                None
            };

            // Use a thunk to bridge virtual call signature (ptr self) to concrete impl.
            let thunk_ptr = if let Some((impl_def_id, args)) = method_target {
                self.witness_method_thunk(type_head, iface, impl_def_id, args)
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

        let sig = self.gcx.get_signature(def_id);
        let prev_subst = self.current_subst;
        self.current_subst = instance.args();
        let fn_abi = self.compute_fn_abi(sig);
        self.current_subst = prev_subst;

        if self.is_foreign_function(def_id) {
            let f = self.declare_foreign_function(def_id);
            self.functions.insert(instance, f);
            self.fn_abis.insert(instance, fn_abi);
            return f.as_global_value().as_pointer_value();
        }

        let prev_subst = self.current_subst;
        self.current_subst = instance.args();
        let fn_ty = self.lower_fn_abi(&fn_abi);
        let name = mangle_instance(self.gcx, instance);
        let f = self
            .module
            .add_function(&name, fn_ty, Some(Linkage::External));
        self.functions.insert(instance, f);
        self.fn_abis.insert(instance, fn_abi);
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
        if !self.generic_args_are_runtime_materializable(args) {
            return self.context.ptr_type(AddressSpace::default()).const_null();
        }
        // Check cache first
        let cache_key = (type_head, iface, impl_def_id);
        if let Some(&ptr) = self.witness_thunks.get(&cache_key) {
            return ptr;
        }

        // Get the concrete implementation function
        let impl_instance = resolve_instance(self.gcx, impl_def_id, args);
        let impl_target_def_id = impl_instance.def_id();
        let impl_fn = self.function_ptr_for_instance(impl_instance);

        // Get the implementation signature
        let prev_subst = self.current_subst;
        self.current_subst = impl_instance.args();
        let sig = self.gcx.get_signature(impl_target_def_id);
        let impl_fn_abi = self.compute_fn_abi(sig);

        // Build thunk parameter types: first param is raw ptr (data pointer from existential),
        // then map remaining implementation arguments according to ABI mode.
        let opaque_ptr = self.context.ptr_type(AddressSpace::default());
        let mut thunk_param_types: Vec<BasicMetadataTypeEnum<'llvm>> =
            Vec::with_capacity(sig.inputs.len() + 1);
        if matches!(impl_fn_abi.ret.mode, abi::PassMode::Indirect { .. }) {
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
        let thunk_fn_ty = match impl_fn_abi.ret.mode {
            abi::PassMode::Ignore | abi::PassMode::Indirect { .. } => {
                self.context.void_type().fn_type(&thunk_param_types, false)
            }
            abi::PassMode::Direct => match self.lower_ty(sig.output) {
                Some(ret) => ret.fn_type(&thunk_param_types, false),
                None => self.context.void_type().fn_type(&thunk_param_types, false),
            },
        };

        // Create thunk function
        let thunk_name = format!(
            "__wt_thunk_{}_{}",
            self.witness_thunks.len(),
            self.gcx.definition_ident(impl_target_def_id).symbol,
        );
        let thunk_fn = self.module.add_function(&thunk_name, thunk_fn_ty, None);

        // Save current position and build thunk body
        let current_block = self.builder.get_insert_block();
        let entry = self.context.append_basic_block(thunk_fn, "entry");
        self.builder.position_at_end(entry);

        // Gather arguments: first is the data pointer, rest are passed through
        let mut call_args: Vec<BasicMetadataValueEnum<'llvm>> =
            Vec::with_capacity(thunk_param_types.len());

        let mut param_index = 0u32;
        if matches!(impl_fn_abi.ret.mode, abi::PassMode::Indirect { .. }) {
            call_args.push(thunk_fn.get_nth_param(param_index).unwrap().into());
            param_index += 1;
        }

        // Next argument is the raw data pointer. Bridge it to the concrete self ABI:
        // - by-ref/ptr self: pass the pointer directly
        // - by-value self: load the concrete value from data pointer and pass it directly
        // - indirect self: pass the pointer directly
        let self_param = thunk_fn.get_nth_param(param_index).unwrap();
        let self_ptr = self_param.into_pointer_value();
        if let Some(self_abi) = impl_fn_abi.args.first() {
            match self_abi.mode {
                abi::PassMode::Ignore => {}
                abi::PassMode::Direct => {
                    let self_input_ty = sig.inputs.first().map(|p| p.ty);
                    let self_is_ref_like = self_input_ty.is_some_and(|ty| {
                        matches!(ty.kind(), TyKind::Reference(..) | TyKind::Pointer(..))
                    });
                    if self_is_ref_like {
                        call_args.push(self_param.into());
                    } else if let Some(load_ty) = self.lower_ty(self_abi.ty) {
                        let loaded = self
                            .builder
                            .build_load(load_ty, self_ptr, "thunk_self_load")
                            .unwrap();
                        call_args.push(loaded.into());
                    } else {
                        call_args.push(self_param.into());
                    }
                }
                abi::PassMode::Indirect { .. } => {
                    call_args.push(self_param.into());
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

        // Get the implementation function type for indirect call
        let impl_fn_ty = self.lower_fn_abi(&impl_fn_abi);

        // Call the implementation
        let call = self
            .builder
            .build_indirect_call(impl_fn_ty, impl_fn, &call_args, "thunk_call")
            .unwrap();

        // Return the result
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
    /// `{ <dispatchable method slots...>, <direct superface table ptrs...> }`.
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
        let fields: Vec<_> = (0..total).map(|_| ptr_ty.into()).collect();
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

    pub(super) fn try_lower_devirtualized_call(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        hint: &mir::DevirtHint<'gcx>,
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
        normal_bb: BasicBlock<'llvm>,
        unwind_target: Option<BasicBlock<'llvm>>,
    ) -> CompileResult<bool> {
        macro_rules! fallback {
            () => {{
                crate::mir::optimize::devirtualize::bump_codegen_fallback();
                return Ok(false);
            }};
        }

        let receiver = match args.first() {
            Some(receiver) => receiver,
            None => fallback!(),
        };

        let impl_instance = self.instance_for_call(hint.impl_def_id, hint.impl_args);
        let impl_def_id = match impl_instance.kind() {
            InstanceKind::Item(def_id) => def_id,
            InstanceKind::Virtual(_) => fallback!(),
        };

        let synthetic_func = Operand::Constant(mir::Constant {
            ty: hint.concrete_self_ty,
            value: mir::ConstantKind::Function(
                hint.impl_def_id,
                hint.impl_args,
                hint.concrete_self_ty,
            ),
        });
        let (callable, fn_abi) = self.lower_callable_with_abi(&synthetic_func);

        let receiver_ty = self.operand_ty(body, receiver);
        let Some(receiver_val) = self.eval_operand(body, locals, receiver)? else {
            fallback!();
        };
        let Some(data_ptr) = self.extract_existential_data_ptr(receiver_ty, receiver_val) else {
            fallback!();
        };

        let sig = self.gcx.get_signature(impl_def_id);
        if sig.inputs.is_empty() || args.len() != sig.inputs.len() || fn_abi.args.is_empty() {
            fallback!();
        }

        let resolved_input_tys: Vec<_> = sig
            .inputs
            .iter()
            .map(|param| {
                let ty = if impl_instance.args().is_empty() {
                    param.ty
                } else {
                    instantiate_ty_with_args(self.gcx, param.ty, impl_instance.args())
                };
                self.normalize_post_mono_ty(ty)
            })
            .collect();
        let self_input_ty = resolved_input_tys[0];
        let self_abi = fn_abi.args[0];

        let self_value = match self_abi.mode {
            abi::PassMode::Ignore => fallback!(),
            abi::PassMode::Direct => {
                let self_is_ref_like = matches!(
                    self_input_ty.kind(),
                    TyKind::Reference(..) | TyKind::Pointer(..)
                );
                if self_is_ref_like {
                    data_ptr.as_basic_value_enum()
                } else {
                    let Some(load_ty) = self
                        .lower_ty(self_input_ty)
                        .or_else(|| self.lower_ty(self_abi.ty))
                    else {
                        fallback!();
                    };
                    let loaded =
                        match self
                            .builder
                            .build_load(load_ty, data_ptr, "devirt_self_load")
                        {
                            Ok(v) => v,
                            Err(_) => fallback!(),
                        };
                    loaded
                }
            }
            abi::PassMode::Indirect { .. } => data_ptr.as_basic_value_enum(),
        };

        let mut lowered_args =
            self.lower_call_args_with_fn_abi(body, locals, args, destination, &fn_abi)?;
        let self_slot = if matches!(fn_abi.ret.mode, abi::PassMode::Indirect { .. }) {
            1
        } else {
            0
        };
        let Some(slot) = lowered_args.get_mut(self_slot) else {
            fallback!();
        };
        *slot = self_value;

        let call_site = self.emit_direct_call_maybe_unwind(
            callable,
            &lowered_args,
            normal_bb,
            unwind_target,
            "devirt_call",
        )?;
        self.store_direct_call_result(body, locals, destination, &fn_abi, call_site)?;
        crate::mir::optimize::devirtualize::bump_codegen_used();
        Ok(true)
    }

    pub(super) fn lower_virtual_call(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        instance: &crate::specialize::VirtualInstance<'gcx>,
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
        normal_bb: BasicBlock<'llvm>,
        unwind_target: Option<BasicBlock<'llvm>>,
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
            TyKind::Reference(inner, _) | TyKind::Pointer(inner, _) => inner,
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

        let mut lowered_args: Vec<BasicValueEnum<'llvm>> = Vec::with_capacity(args.len() + 1);
        let ret_mode = self
            .compute_fn_pointer_abi(&[], self.place_ty(body, destination))
            .ret
            .mode;
        if matches!(ret_mode, abi::PassMode::Indirect { .. }) {
            let Some(sret_dest) = self.place_address(body, locals, destination)? else {
                self.gcx.dcx().emit_error(
                    "virtual call with indirect return requires an addressable destination".into(),
                    None,
                );
                return Err(crate::error::ReportedError);
            };
            lowered_args.push(sret_dest.as_basic_value_enum());
        }
        lowered_args.push(data_ptr.as_basic_value_enum());
        for arg in args.iter().skip(1) {
            if let Some(val) = self.eval_operand(body, locals, arg)? {
                lowered_args.push(val);
            }
        }

        let param_types: Vec<BasicMetadataTypeEnum<'llvm>> = lowered_args
            .iter()
            .map(|arg| match arg {
                BasicValueEnum::ArrayValue(v) => v.get_type().into(),
                BasicValueEnum::IntValue(v) => v.get_type().into(),
                BasicValueEnum::FloatValue(v) => v.get_type().into(),
                BasicValueEnum::PointerValue(v) => v.get_type().into(),
                BasicValueEnum::StructValue(v) => v.get_type().into(),
                BasicValueEnum::VectorValue(v) => v.get_type().into(),
                BasicValueEnum::ScalableVectorValue(v) => v.get_type().into(),
            })
            .collect();
        let fn_ty = match ret_mode {
            abi::PassMode::Indirect { .. } | abi::PassMode::Ignore => {
                self.context.void_type().fn_type(&param_types, false)
            }
            abi::PassMode::Direct => {
                let ret_ty = self.place_ty(body, destination);
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
        let call_site = self.emit_indirect_call_maybe_unwind(
            fn_ty,
            fn_ptr_cast,
            &lowered_args,
            normal_bb,
            unwind_target,
            "virt_call",
        )?;

        if !matches!(ret_mode, abi::PassMode::Indirect { .. }) {
            if let Some(ret) = call_site.try_as_basic_value().basic() {
                self.store_place(destination, body, locals, ret)?;
            }
        }
        // Branch to normal_bb is emitted by the caller (lower_terminator) so that
        // Rc release of old destination can be inserted before the branch.

        Ok(())
    }

    fn extract_existential_data_ptr(
        &self,
        receiver_ty: Ty<'gcx>,
        receiver_val: BasicValueEnum<'llvm>,
    ) -> Option<PointerValue<'llvm>> {
        let ptr_ty = self.context.ptr_type(AddressSpace::default());
        match receiver_ty.kind() {
            TyKind::Reference(inner, _) | TyKind::Pointer(inner, _) => {
                if !matches!(inner.kind(), TyKind::BoxedExistential { .. }) {
                    return None;
                }
                let BasicValueEnum::PointerValue(struct_ptr) = receiver_val else {
                    return None;
                };
                let Some(BasicTypeEnum::StructType(struct_ty)) = self.lower_ty(inner) else {
                    return None;
                };
                let data_ptr_gep = self
                    .builder
                    .build_struct_gep(struct_ty, struct_ptr, 0, "devirt_exist_data_ptr")
                    .ok()?;
                let data_ptr = self
                    .builder
                    .build_load(ptr_ty, data_ptr_gep, "devirt_exist_data_load")
                    .ok()?
                    .into_pointer_value();
                Some(data_ptr)
            }
            TyKind::BoxedExistential { .. } => {
                let BasicValueEnum::StructValue(struct_val) = receiver_val else {
                    return None;
                };
                let data_ptr = self
                    .builder
                    .build_extract_value(struct_val, 0, "devirt_exist_data")
                    .ok()?
                    .into_pointer_value();
                Some(data_ptr)
            }
            _ => None,
        }
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
