//! Monomorphized generic bodies behind a call-scoped erased bridge.
//! No generic body is compiled with the owning existential as its hidden T.
use super::*;
use crate::sema::lowering::erased_opening::OpeningPlan;
use crate::sema::models::GenericArgument;

impl<'llvm, 'gcx> Emitter<'llvm, 'gcx> {
    fn opening_key(&self, domain: &str, value: &str) -> PointerValue<'llvm> {
        let encoded: String = value.bytes().map(|byte| format!("{byte:02x}")).collect();
        let name = format!("__taro_erased_{domain}_{encoded}");
        self.module
            .get_global(&name)
            .unwrap_or_else(|| {
                let global = self.module.add_global(self.context.i8_type(), None, &name);
                global.set_initializer(&self.context.i8_type().const_zero());
                global.set_constant(true);
                global.set_linkage(Linkage::LinkOnceODR);
                global
            })
            .as_pointer_value()
    }

    /// A linker identity uses the complete structural key, not a hash as proof
    /// that two concrete payloads have the same storage layout or destruction.
    pub(super) fn erased_type_identity(&self, ty: Ty<'gcx>) -> PointerValue<'llvm> {
        self.opening_key("type", &crate::codegen::mangle::ty_key(self.gcx, ty))
    }

    fn opening_family(&self, call: Instance<'gcx>) -> PointerValue<'llvm> {
        self.opening_key(
            "family",
            &crate::codegen::mangle::definition_key(call.def_id()),
        )
    }

    fn opening_arguments(&self, call: Instance<'gcx>) -> PointerValue<'llvm> {
        // Includes the bridge's static interface shape and every other generic
        // argument. The dynamic concrete identity is a separate registry key.
        self.opening_key(
            "arguments",
            &crate::codegen::mangle::mangle_instance(self.gcx, call),
        )
    }

    fn opening_parameters(
        &self,
        function: FunctionValue<'llvm>,
        abi: &abi::FnAbi<'gcx>,
    ) -> (
        Option<BasicValueEnum<'llvm>>,
        Vec<Option<BasicValueEnum<'llvm>>>,
    ) {
        let mut next = 0;
        let sret = matches!(abi.ret.mode, abi::PassMode::Indirect { .. }).then(|| {
            next += 1;
            function.get_nth_param(0).unwrap()
        });
        let arguments = abi
            .args
            .iter()
            .map(|arg| {
                if matches!(arg.mode, abi::PassMode::Ignore) {
                    return None;
                }
                let value = function.get_nth_param(next).unwrap();
                next += 1;
                Some(value)
            })
            .collect();
        (sret, arguments)
    }

    fn opening_container(
        &self,
        builder: &Builder<'llvm>,
        input: BasicValueEnum<'llvm>,
        abi: &abi::ArgAbi<'gcx>,
        plan: OpeningPlan<'gcx>,
    ) -> BasicValueEnum<'llvm> {
        if plan.borrow.is_some() {
            let address = input.into_pointer_value();
            return builder
                .build_load(
                    self.lower_ty(plan.erased).unwrap(),
                    address,
                    "erased_container",
                )
                .unwrap();
        }
        if matches!(abi.mode, abi::PassMode::Indirect { .. }) {
            builder
                .build_load(
                    self.lower_ty(plan.erased).unwrap(),
                    input.into_pointer_value(),
                    "owned_container",
                )
                .unwrap()
        } else {
            input
        }
    }

    pub(super) fn emit_erased_opening(
        &mut self,
        instance: Instance<'gcx>,
        plan: OpeningPlan<'gcx>,
    ) -> CompileResult<()> {
        self.gcx
            .store
            .erased_opening_calls
            .borrow_mut()
            .entry(self.gcx.package_index())
            .or_default()
            .insert(instance);
        let (function, abi) = self.instance_function_with_abi(instance);
        self.preserve_diagnostic_frame(function);
        let builder = self.context.create_builder();
        builder.position_at_end(self.context.append_basic_block(function, "open_concrete"));
        let (_, inputs) = self.opening_parameters(function, &abi);
        let container = self
            .opening_container(
                &builder,
                inputs[plan.input].unwrap(),
                &abi.args[plan.input],
                plan,
            )
            .into_struct_value();
        let metadata = builder
            .build_extract_value(container, 1, "stored_metadata")
            .unwrap()
            .into_pointer_value();
        let identity_address = builder
            .build_struct_gep(
                self.rt_type_metadata_ty,
                metadata,
                2,
                "stored_identity_address",
            )
            .unwrap();
        let ptr = self.context.ptr_type(AddressSpace::default());
        let identity = builder
            .build_load(ptr, identity_address, "stored_type")
            .unwrap();
        let resolve = self.get_or_add_external_function(
            "__rt__erased_resolve_opening",
            ptr.fn_type(&[ptr.into(), ptr.into(), ptr.into()], false),
        );
        let target = builder
            .build_call(
                resolve,
                &[
                    identity.into(),
                    self.opening_family(instance).into(),
                    self.opening_arguments(instance).into(),
                ],
                "concrete_bridge",
            )
            .unwrap()
            .try_as_basic_value()
            .basic()
            .unwrap()
            .into_pointer_value();
        let arguments: Vec<_> = function.get_param_iter().map(Into::into).collect();
        let call = builder
            .build_indirect_call(function.get_type(), target, &arguments, "opened_result")
            .unwrap();
        call.set_call_convention(function.get_call_conventions());
        if let Some(result) = call.try_as_basic_value().basic() {
            builder.build_return(Some(&result)).unwrap();
        } else {
            builder.build_return(None).unwrap();
        }
        Ok(())
    }

    /// Adapt just the opened input. All remaining ABI words and the known
    /// result pass unchanged. This forwarding-only stub has no user callbacks
    /// before concrete callee entry, including during owned-shell extraction.
    fn concrete_opening_bridge(
        &mut self,
        call: Instance<'gcx>,
        concrete: Ty<'gcx>,
        plan: OpeningPlan<'gcx>,
    ) -> CompileResult<PointerValue<'llvm>> {
        let mut arguments = call.args().to_vec();
        arguments[plan.parameter] = GenericArgument::Type(concrete);
        let arguments = self.gcx.store.interners.intern_generic_args(arguments);
        let target = Instance::item(call.def_id(), arguments);
        let (callee, concrete_abi) = self.instance_function_with_abi(target);
        let (entry, erased_abi) = self.instance_function_with_abi(call);
        let name = format!(
            "__taro_open_bridge_{}_{}",
            crate::codegen::mangle::mangle_instance(self.gcx, call),
            crate::codegen::mangle::ty_key(self.gcx, concrete)
                .bytes()
                .map(|byte| format!("{byte:02x}"))
                .collect::<String>()
        );
        let function =
            self.module
                .add_function(&name, entry.get_type(), Some(Linkage::LinkOnceODR));
        self.preserve_diagnostic_frame(function);
        let previous_block = self.builder.get_insert_block();
        let previous_subst = self.current_subst;
        self.current_subst = arguments;
        self.builder
            .position_at_end(self.context.append_basic_block(function, "concrete_input"));
        let (sret, inputs) = self.opening_parameters(function, &erased_abi);
        let input = inputs[plan.input].unwrap();
        let container = self
            .opening_container(&self.builder, input, &erased_abi.args[plan.input], plan)
            .into_struct_value();
        let actual_input = {
            // The traced payload is the opened value's storage. A borrowed
            // opening passes its address; an owned header was passed to this
            // call, so its payload is already the callee's own value.
            let data = self
                .builder
                .build_extract_value(container, 0, "concrete_data")
                .unwrap()
                .into_pointer_value();
            if plan.borrow.is_some() {
                Some(data.into())
            } else {
                match concrete_abi.args[plan.input].mode {
                    abi::PassMode::Ignore => None,
                    abi::PassMode::Indirect { .. } => Some(data.into()),
                    abi::PassMode::Direct => self
                        .lower_ty(concrete)
                        .map(|ty| self.builder.build_load(ty, data, "owned_concrete").unwrap()),
                }
            }
        };
        let mut forwarded: Vec<BasicMetadataValueEnum<'llvm>> = Vec::new();
        if let Some(sret) = sret {
            forwarded.push(sret.into());
        }
        for (index, argument) in inputs.into_iter().enumerate() {
            if let Some(argument) = if index == plan.input {
                actual_input
            } else {
                argument
            } {
                forwarded.push(argument.into());
            }
        }
        let result = self
            .builder
            .build_call(callee, &forwarded, "concrete_result")
            .unwrap();
        result.set_call_convention(callee.get_call_conventions());
        if let Some(result) = result.try_as_basic_value().basic() {
            self.builder.build_return(Some(&result)).unwrap();
        } else {
            self.builder.build_return(None).unwrap();
        }
        if let Some(block) = previous_block {
            self.builder.position_at_end(block);
        }
        self.current_subst = previous_subst;
        Ok(function.as_global_value().as_pointer_value())
    }

    pub(super) fn close_erased_openings(&mut self) -> CompileResult<()> {
        let types: Vec<_> = self
            .gcx
            .store
            .erased_opening_types
            .borrow()
            .values()
            .flat_map(|types| types.iter().copied())
            .collect();
        let calls: Vec<_> = self
            .gcx
            .store
            .erased_opening_calls
            .borrow()
            .values()
            .flat_map(|calls| calls.iter().copied())
            .collect();
        for call in calls {
            let plan = match crate::sema::lowering::erased_opening::plan(
                self.gcx,
                call.def_id(),
                call.args(),
            ) {
                Ok(Some(plan)) => plan,
                _ => {
                    self.gcx
                        .dcx()
                        .emit_error("invalid imported existential opening fact".into(), None);
                    return self.gcx.dcx().ok();
                }
            };
            for concrete in &types {
                if self
                    .erased_opening_registrations
                    .contains_key(&(*concrete, call))
                {
                    continue;
                }
                let mut arguments = call.args().to_vec();
                arguments[plan.parameter] = GenericArgument::Type(*concrete);
                let arguments = self.gcx.store.interners.intern_generic_args(arguments);
                if !crate::sema::lowering::classes::method_available(
                    self.gcx,
                    call.def_id(),
                    arguments,
                ) {
                    self.erased_opening_registrations
                        .insert((*concrete, call), None);
                    continue;
                }
                let target = self.concrete_opening_bridge(call, *concrete, plan)?;
                self.erased_opening_registrations
                    .insert((*concrete, call), Some(target));
            }
        }
        Ok(())
    }

    pub(super) fn emit_erased_opening_ctor(&mut self) {
        let registrations: Vec<_> = self
            .erased_opening_registrations
            .iter()
            .filter_map(|((concrete, call), target)| {
                target.map(|target| (*concrete, *call, target))
            })
            .collect();
        if registrations.is_empty() {
            return;
        }
        let ptr = self.context.ptr_type(AddressSpace::default());
        let entry_ty = self
            .context
            .struct_type(&[ptr.into(), ptr.into(), ptr.into(), ptr.into()], false);
        let entries: Vec<_> = registrations
            .into_iter()
            .map(|(concrete, call, target)| {
                entry_ty.const_named_struct(&[
                    self.erased_type_identity(concrete).into(),
                    self.opening_family(call).into(),
                    self.opening_arguments(call).into(),
                    target.into(),
                ])
            })
            .collect();
        let table = self.module.add_global(
            entry_ty.array_type(entries.len() as u32),
            None,
            "__taro_erased_openings",
        );
        table.set_constant(true);
        table.set_linkage(Linkage::Internal);
        table.set_initializer(&entry_ty.const_array(&entries));
        let ctor = self.module.add_function(
            "__taro_register_erased_openings",
            self.context.void_type().fn_type(&[], false),
            Some(Linkage::Internal),
        );
        let builder = self.context.create_builder();
        builder.position_at_end(self.context.append_basic_block(ctor, "register"));
        let register = self.get_or_add_external_function(
            "__rt__erased_register_openings",
            self.context
                .void_type()
                .fn_type(&[ptr.into(), self.usize_ty.into()], false),
        );
        builder
            .build_call(
                register,
                &[
                    table.as_pointer_value().into(),
                    self.usize_ty.const_int(entries.len() as u64, false).into(),
                ],
                "",
            )
            .unwrap();
        builder.build_return(None).unwrap();
    }
}
