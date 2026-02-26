use super::{Emitter, LocalStorage};
use crate::{
    codegen::{abi, mangle::mangle_instance},
    error::CompileResult,
    hir,
    mir::{self, Operand, Place},
    sema::{
        models::{
            ConstKind, GenericArgument, GenericArguments, InterfaceDefinition, InterfaceReference,
            InterfaceRequirements, SelectionMode, Ty, TyKind,
        },
        resolve::models::TypeHead,
        tycheck::{
            resolve_conformance_witness_with_mode,
            utils::{
                instantiate::{instantiate_const_with_args, instantiate_ty_with_args},
                type_head_from_value_ty,
            },
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

    fn canonical_interface_ref_for_assert(
        &self,
        iface: InterfaceReference<'gcx>,
    ) -> InterfaceReference<'gcx> {
        let args = if !iface.arguments.is_empty() {
            iface.arguments[1..].iter().copied().collect::<Vec<_>>()
        } else {
            iface.arguments.iter().copied().collect::<Vec<_>>()
        };
        let canonical_args = self.gcx.store.interners.intern_generic_args(args);
        InterfaceReference {
            id: iface.id,
            arguments: canonical_args,
            bindings: iface.bindings,
        }
    }

    pub(super) fn interface_descriptor_ptr(
        &mut self,
        iface: InterfaceReference<'gcx>,
    ) -> PointerValue<'llvm> {
        let canonical = self.canonical_interface_ref_for_assert(iface);
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
            let Some(iface) = self.materialized_interface_for_record(record.extension, concrete_ty, record.interface) else {
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
            self.substitute_interface_ref(iface, extension_args)
        };
        let instantiated = self.interface_args_with_self(concrete_ty, instantiated);

        if self.conformance_witness(instantiated).is_none() {
            return None;
        }

        Some(instantiated)
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

        let method_count = requirements
            .methods
            .iter()
            .filter(|method| method.has_self)
            .count();
        let mut entries: Vec<BasicValueEnum<'llvm>> = Vec::with_capacity(method_count);
        for method in requirements.methods.iter().filter(|method| method.has_self) {
            // Generic interface methods are not materializable in runtime witness
            // tables because method-level type/const arguments are unknown at
            // metadata construction time.
            if self.gcx.generics_of(method.id).total_count() > 0 {
                self.debug_witness_subst(format!(
                    "iface method {} has method-level generics; emitting null witness slot",
                    self.gcx.symbol_text(method.name)
                ));
                entries.push(self.context.ptr_type(AddressSpace::default()).const_null().into());
                continue;
            }

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
                    let iface_name = self.gcx.symbol_text(self.gcx.definition_ident(iface.id).symbol);
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

    pub(super) fn interface_method_count(&self, interface_id: hir::DefinitionID) -> usize {
        self.interface_requirements(interface_id)
            .map(|req| req.methods.len())
            .unwrap_or(0)
    }

    pub(super) fn interface_superfaces(
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

    pub(super) fn interface_args_with_self(
        &self,
        self_ty: Ty<'gcx>,
        iface: InterfaceReference<'gcx>,
    ) -> InterfaceReference<'gcx> {
        if iface.arguments.is_empty() {
            return iface;
        }

        let mut args: Vec<_> = iface.arguments.iter().cloned().collect();
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

    fn complete_interface_call_args(
        &self,
        method_id: hir::DefinitionID,
        args: GenericArguments<'gcx>,
    ) -> GenericArguments<'gcx> {
        let Some(parent) = self.gcx.definition_parent(method_id) else {
            return args;
        };
        if self.gcx.definition_kind(parent) != crate::sema::resolve::models::DefinitionKind::Interface
        {
            return args;
        }

        let expected = self.gcx.generics_of(parent).total_count();
        if args.len() >= expected {
            return args;
        }

        // PartialEq has default `Rhs = Self`; callers often materialize only `Self`.
        if let Some(partial_eq_id) = self.gcx.std_item_def(hir::StdItem::PartialEq) {
            if parent == partial_eq_id && args.len() == 1 && expected == 2 {
                if let Some(GenericArgument::Type(self_ty)) = args.get(0).copied() {
                    return self.gcx.store.interners.intern_generic_args(vec![
                        GenericArgument::Type(self_ty),
                        GenericArgument::Type(self_ty),
                    ]);
                }
            }
        }

        args
    }

    fn substitute_interface_ref(
        &self,
        template: InterfaceReference<'gcx>,
        args: GenericArguments<'gcx>,
    ) -> InterfaceReference<'gcx> {
        let mut new_args = Vec::with_capacity(template.arguments.len());
        for arg in template.arguments.iter() {
            match arg {
                GenericArgument::Type(ty) => {
                    let substituted = if args.is_empty() {
                        *ty
                    } else {
                        instantiate_ty_with_args(self.gcx, *ty, args)
                    };
                    let normalized = self.normalize_post_mono_ty(substituted);
                    new_args.push(GenericArgument::Type(normalized));
                }
                GenericArgument::Const(c) => {
                    let substituted = if args.is_empty() {
                        *c
                    } else {
                        instantiate_const_with_args(self.gcx, *c, args)
                    };
                    new_args.push(GenericArgument::Const(substituted));
                }
            }
        }

        let interned = self.gcx.store.interners.intern_generic_args(new_args);

        // Also substitute bindings
        let mut new_bindings = Vec::with_capacity(template.bindings.len());
        for binding in template.bindings {
            let substituted_ty = if args.is_empty() {
                binding.ty
            } else {
                instantiate_ty_with_args(self.gcx, binding.ty, args)
            };
            let substituted_ty = self.normalize_post_mono_ty(substituted_ty);
            new_bindings.push(crate::sema::models::AssociatedTypeBinding {
                name: binding.name,
                ty: substituted_ty,
            });
        }

        InterfaceReference {
            id: template.id,
            arguments: interned,
            bindings: self
                .gcx
                .store
                .arenas
                .global
                .alloc_slice_clone(&new_bindings),
        }
    }

    pub(super) fn witness_table_struct_ty(
        &self,
        interface_id: hir::DefinitionID,
    ) -> StructType<'llvm> {
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

    pub(super) fn interface_index(
        &self,
        interfaces: &[InterfaceReference<'gcx>],
        interface_id: hir::DefinitionID,
    ) -> Option<usize> {
        interfaces.iter().position(|iface| iface.id == interface_id)
    }

    pub(super) fn superface_chain_from_root(
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

    pub(super) fn interface_has_superface(
        &self,
        interface_id: hir::DefinitionID,
        target_id: hir::DefinitionID,
    ) -> bool {
        self.gcx.with_type_database(interface_id.package(), |db| {
            db.interface_to_supers
                .get(&interface_id)
                .is_some_and(|supers| supers.contains(&target_id))
        })
    }

    pub(super) fn superface_chain_indices(
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
            let Some((parent, index)) = parents.get(&current).cloned() else {
                return None;
            };
            chain.push((parent, index));
            current = parent;
        }
        chain.reverse();
        Some(chain)
    }

    pub(super) fn virtual_instance_for_call(
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

    pub(super) fn lower_virtual_call(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        instance: &crate::specialize::VirtualInstance,
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
            .definition_symbol_or_fallback(instance.method_interface);
        self.debug_virtual_dispatch(format!(
            "method={:?} ({}) iface={:?} ({}) slot={} table_index={} receiver_ty={}",
            instance.method_id,
            self.gcx.symbol_text(method_name),
            instance.method_interface,
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
        let _ = self.builder.build_unconditional_branch(normal_bb).unwrap();

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
