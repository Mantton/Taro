//! Native class dispatch. Generic calls retain their monomorphized ABI; the
//! final module closes imported call/publication facts to a fixed point.
use super::*;
use crate::codegen::mangle::{definition_key, generic_arg_key, ty_key};

impl<'llvm, 'gcx> Emitter<'llvm, 'gcx> {
    /// Addresses are identities. Encode the complete structural key in the
    /// symbol rather than treating a digest collision as type equality.
    fn class_identity_key(&self, domain: &str, key: &str) -> PointerValue<'llvm> {
        let encoded: String = key.bytes().map(|byte| format!("{byte:02x}")).collect();
        let name = format!("__taro_class_{domain}_{encoded}");
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

    pub(super) fn class_identity(&self, class: Ty<'gcx>) -> PointerValue<'llvm> {
        self.class_identity_key("type", &ty_key(self.gcx, class))
    }

    fn class_family(&self, family: hir::DefinitionID) -> PointerValue<'llvm> {
        self.class_identity_key("family", &definition_key(family))
    }

    fn class_arguments(&self, arguments: GenericArguments<'gcx>) -> PointerValue<'llvm> {
        // Length-prefix every argument, so tuple boundaries are unambiguous.
        let key: String = arguments
            .iter()
            .map(|argument| {
                let key = generic_arg_key(self.gcx, *argument);
                format!("{}:{key}", key.len())
            })
            .collect();
        self.class_identity_key("arguments", &key)
    }

    fn class_dispatch_target(
        &mut self,
        instance: Instance<'gcx>,
    ) -> CompileResult<PointerValue<'llvm>> {
        let (function, _) = self.instance_function_with_abi(instance);
        {
            return Ok(function.as_global_value().as_pointer_value());
        }
    }

    pub(super) fn class_descriptor(
        &mut self,
        class: Ty<'gcx>,
    ) -> CompileResult<PointerValue<'llvm>> {
        if let Some(descriptor) = self.class_descriptors.get(&class) {
            return Ok(*descriptor);
        }
        let info = self
            .gcx
            .class_info(class)
            .expect("class descriptor requires a class");
        self.gcx
            .store
            .class_dispatch_types
            .borrow_mut()
            .entry(self.gcx.package_index())
            .or_default()
            .insert(class);
        let ptr = self.context.ptr_type(AddressSpace::default());
        let descriptor_ty = self.context.struct_type(
            &[ptr.into(), ptr.into(), ptr.into(), self.usize_ty.into()],
            false,
        );
        let name = format!(
            "__taro_class_descriptor_{}{}",
            "gc_",
            ty_key(self.gcx, class)
                .bytes()
                .map(|b| format!("{b:02x}"))
                .collect::<String>()
        );
        let global = self.module.add_global(descriptor_ty, None, &name);
        global.set_linkage(Linkage::LinkOnceODR);
        global.set_constant(true);
        self.class_descriptors
            .insert(class, global.as_pointer_value());
        let base = match self.gcx.class_base(class) {
            Some(base) => self.class_descriptor(base)?,
            None => ptr.const_null(),
        };
        let TyKind::Adt(_, class_args) = class.kind() else {
            unreachable!()
        };
        let method_ty = self.context.struct_type(&[ptr.into(), ptr.into()], false);
        let mut methods = vec![];
        for method in info.methods {
            if self.gcx.class_family_is_registered(method.family) {
                continue;
            }
            if !self
                .gcx
                .generics_of(method.implementation)
                .parameters
                .is_empty()
            {
                continue;
            }
            let owner = instantiate_ty_with_args(self.gcx, method.owner, class_args);
            let empty = self.gcx.store.interners.intern_generic_args(vec![]);
            let Some(arguments) =
                self.gcx
                    .class_method_arguments(owner, method.implementation, empty)
            else {
                continue;
            };
            if !crate::sema::lowering::classes::method_available(
                self.gcx,
                method.implementation,
                arguments,
            ) {
                continue;
            }
            let target =
                self.class_dispatch_target(Instance::item(method.implementation, arguments))?;
            methods.push(
                method_ty
                    .const_named_struct(&[self.class_family(method.family).into(), target.into()]),
            );
        }
        // Constructor families share canonical dispatch identities with virtual
        // methods, but runtime construction lookup uses this concrete table
        // only: a missing derived entry must never allocate a base object.
        for initializer in info.initializers {
            if !self
                .gcx
                .generics_of(initializer.implementation)
                .parameters
                .is_empty()
            {
                continue;
            }
            let Some(arguments) = self.gcx.class_method_arguments(
                class,
                initializer.implementation,
                GenericArguments::empty(),
            ) else {
                continue;
            };
            if !crate::sema::lowering::classes::method_available(
                self.gcx,
                initializer.implementation,
                arguments,
            ) {
                continue;
            }
            let target =
                self.class_dispatch_target(Instance::item(initializer.implementation, arguments))?;
            methods.push(method_ty.const_named_struct(&[
                self.class_family(initializer.family).into(),
                target.into(),
            ]));
        }
        let table = if methods.is_empty() {
            ptr.const_null()
        } else {
            let table = self.module.add_global(
                method_ty.array_type(methods.len() as u32),
                None,
                &format!("{name}_methods"),
            );
            table.set_linkage(Linkage::LinkOnceODR);
            table.set_constant(true);
            table.set_initializer(&method_ty.const_array(&methods));
            table.as_pointer_value()
        };
        global.set_initializer(&descriptor_ty.const_named_struct(&[
            self.class_identity(class).into(),
            base.into(),
            table.into(),
            self.usize_ty.const_int(methods.len() as u64, false).into(),
        ]));
        Ok(global.as_pointer_value())
    }

    pub(super) fn lower_class_call_target(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        function: &Operand<'gcx>,
        arguments: &[Operand<'gcx>],
    ) -> CompileResult<Option<(CallTarget<'llvm>, abi::FnAbi<'gcx>)>> {
        if self.current_span.is_some_and(|span| {
            self.gcx
                .store
                .class_super_calls
                .borrow()
                .values()
                .any(|calls| calls.contains(&span))
        }) {
            return Ok(None);
        }
        let Operand::Constant(constant) = function else {
            return Ok(None);
        };
        let mir::ConstantKind::Function(method, generics, _) = constant.value else {
            return Ok(None);
        };
        let Some(declared_type) = self.gcx.try_get_type(method) else {
            // Instance-generated drop/borrow glue has no source callable type.
            return Ok(None);
        };
        let initializer = matches!(declared_type.kind(), TyKind::FnPointer { output, .. }
            if self.gcx.class_initializer(output, method).is_some());
        let class_member = self
            .gcx
            .definition_parent(method)
            .and_then(|parent| self.gcx.get_impl_target_ty(parent))
            .is_some_and(|ty| self.gcx.is_class_type(ty))
            || self
                .gcx
                .store
                .synthetic_definitions
                .borrow()
                .get(&method)
                .is_some_and(|definition| {
                    matches!(
                        definition.kind,
                        crate::sema::models::SyntheticDefinitionKind::AdoptedClassDefault { .. }
                            | crate::sema::models::SyntheticDefinitionKind::ClassEncoder { .. }
                    )
                });
        let interface_member = self.gcx.definition_parent(method).is_some_and(|parent| {
            self.gcx.try_definition_kind(parent) == Some(hir::DefinitionKind::Interface)
        });
        if !initializer && !class_member && !interface_member {
            // Unrelated generated witness instances may use a different generic
            // coordinate system from their source declaration. Class discovery
            // must not instantiate those source types as a side effect.
            return Ok(None);
        }
        let instance = self.instance_for_call(method, generics);
        let method = instance.def_id();
        let Some(declared_type) = self.gcx.try_get_type(method) else {
            return Ok(None);
        };
        let signature = instantiate_ty_with_args(self.gcx, declared_type, instance.args());
        if initializer {
            // Direct calls still use their normal statically selected target.
            // Export generic argument facts so contextual construction of a
            // published subclass can close the matching native specialization.
            let own = &instance.args()[self.gcx.generics_of(method).parent_count..];
            if !own.is_empty() {
                self.gcx
                    .store
                    .class_dispatch_calls
                    .borrow_mut()
                    .entry(self.gcx.package_index())
                    .or_default()
                    .insert(instance);
            }
            return Ok(None);
        }
        let TyKind::FnPointer { inputs, .. } = signature.kind() else {
            return Ok(None);
        };
        let Some(receiver) = inputs.first().copied() else {
            return Ok(None);
        };
        let class = match receiver.kind() {
            TyKind::Reference(class) => class,
            _ => receiver,
        };
        if !self.gcx.is_class_type(class) {
            return Ok(None);
        }
        let Some(slot) = self.gcx.class_method(class, method) else {
            return Ok(None);
        };
        if slot.is_final {
            return Ok(None);
        }
        let Some(value) = self.eval_operand(body, locals, &arguments[0])? else {
            return Err(crate::error::ReportedError);
        };
        let handle = if matches!(receiver.kind(), TyKind::Reference(..)) {
            self.builder
                .build_load(
                    self.lower_ty(class).unwrap(),
                    value.into_pointer_value(),
                    "virtual_handle",
                )
                .unwrap()
        } else {
            value
        };
        self.class_handle_call_target(instance, handle)
    }

    /// Erased witnesses and ordinary source calls must select the same
    /// override family on the object's actual descriptor. A witness's concrete
    /// stored type determines the call ABI, not the dynamic implementation.
    pub(super) fn class_handle_call_target(
        &mut self,
        instance: Instance<'gcx>,
        handle: BasicValueEnum<'llvm>,
    ) -> CompileResult<Option<(CallTarget<'llvm>, abi::FnAbi<'gcx>)>> {
        let method = instance.def_id();
        let signature =
            instantiate_ty_with_args(self.gcx, self.gcx.get_type(method), instance.args());
        let TyKind::FnPointer { inputs, .. } = signature.kind() else {
            return Ok(None);
        };
        let Some(receiver) = inputs.first().copied() else {
            return Ok(None);
        };
        let class = match receiver.kind() {
            TyKind::Reference(class) => class,
            _ => receiver,
        };
        if !self.gcx.is_class_type(class) {
            return Ok(None);
        }
        let Some(slot) = self.gcx.class_method(class, method) else {
            return Ok(None);
        };
        if slot.is_final {
            return Ok(None);
        }
        let (declared, fn_abi) = self.instance_function_with_abi(instance);
        let owner = self
            .builder
            .build_extract_value(handle.into_struct_value(), 0, "virtual_owner")
            .unwrap();
        let own = self.gcx.store.interners.intern_generic_args_slice(
            &instance.args()[self.gcx.generics_of(method).parent_count..],
        );
        let key = if own.is_empty() && !self.gcx.class_family_is_registered(slot.family) {
            self.context.ptr_type(AddressSpace::default()).const_null()
        } else {
            self.gcx
                .store
                .class_dispatch_calls
                .borrow_mut()
                .entry(self.gcx.package_index())
                .or_default()
                .insert(instance);
            self.class_arguments(own)
        };
        let ptr = self.context.ptr_type(AddressSpace::default());
        let lookup = self.get_or_add_external_function(
            "__gc__class_resolve_method",
            ptr.fn_type(&[ptr.into(), ptr.into(), ptr.into()], false),
        );
        let target = self
            .builder
            .build_call(
                lookup,
                &[
                    owner.into(),
                    self.class_family(slot.family).into(),
                    key.into(),
                ],
                "virtual_target",
            )
            .unwrap()
            .try_as_basic_value()
            .basic()
            .unwrap()
            .into_pointer_value();
        Ok(Some((
            CallTarget::Indirect(declared.get_type(), target),
            fn_abi,
        )))
    }

    pub(super) fn close_class_dispatch(&mut self) -> CompileResult<()> {
        let classes: Vec<_> = self
            .gcx
            .store
            .class_dispatch_types
            .borrow()
            .values()
            .flat_map(|set| set.iter().copied())
            .collect();
        let calls: Vec<_> = self
            .gcx
            .store
            .class_dispatch_calls
            .borrow()
            .values()
            .flat_map(|set| set.iter().copied())
            .collect();
        for class in classes {
            for call in &calls {
                if self.class_registrations.contains_key(&(class, *call)) {
                    continue;
                }
                let signature = instantiate_ty_with_args(
                    self.gcx,
                    self.gcx.get_type(call.def_id()),
                    call.args(),
                );
                if let TyKind::FnPointer { output, .. } = signature.kind()
                    && let Some(source) = self.gcx.class_initializer(output, call.def_id())
                {
                    if !self
                        .gcx
                        .is_class_subtype(class, self.gcx.constructor_value(output))
                    {
                        continue;
                    }
                    let Some(entry) = self.gcx.class_initializer(class, source.family) else {
                        continue;
                    };
                    let own = self.gcx.store.interners.intern_generic_args_slice(
                        &call.args()[self.gcx.generics_of(call.def_id()).parent_count..],
                    );
                    let Some(arguments) =
                        self.gcx
                            .class_method_arguments(class, entry.implementation, own)
                    else {
                        continue;
                    };
                    if !crate::sema::lowering::classes::method_available(
                        self.gcx,
                        entry.implementation,
                        arguments,
                    ) {
                        continue;
                    }
                    let target = Instance::item(entry.implementation, arguments);
                    self.class_dispatch_target(target)?;
                    self.class_registrations
                        .insert((class, *call), (source.family, own, target));
                    continue;
                }
                let TyKind::FnPointer { inputs, .. } = signature.kind() else {
                    continue;
                };
                let Some(receiver) = inputs.first().copied() else {
                    continue;
                };
                let static_class = match receiver.kind() {
                    TyKind::Reference(class) => class,
                    _ => receiver,
                };
                if !self.gcx.is_class_subtype(class, static_class) {
                    continue;
                }
                let Some(base_slot) = self.gcx.class_method(static_class, call.def_id()) else {
                    continue;
                };
                let Some(slot) = self.gcx.class_method(class, base_slot.family) else {
                    continue;
                };
                let own = self.gcx.store.interners.intern_generic_args_slice(
                    &call.args()[self.gcx.generics_of(call.def_id()).parent_count..],
                );
                let arguments = self
                    .gcx
                    .class_method_arguments(slot.owner, slot.implementation, own)
                    .expect("validated class method substitution");
                let target = Instance::item(slot.implementation, arguments);
                if !crate::sema::lowering::classes::method_available(
                    self.gcx,
                    slot.implementation,
                    arguments,
                ) {
                    self.gcx.dcx().emit_error(
                        "generic virtual target does not satisfy its declared conditions".into(),
                        Some(self.gcx.definition_ident(slot.implementation).span),
                    );
                    return Err(crate::error::ReportedError);
                }
                self.class_dispatch_target(target)?;
                self.class_registrations
                    .insert((class, *call), (base_slot.family, own, target));
            }
        }
        Ok(())
    }

    /// Dynamic construction metadata outlives its object. Consume the copied
    /// handle supplied by the caller, balancing its retain before returning.
    /// Unlike an ordinary borrowed parameter, no access-control debt crosses
    /// this compiler-private stub.
    pub(super) fn emit_class_object_descriptor(
        &mut self,
        instance: Instance<'gcx>,
    ) -> CompileResult<()> {
        let (function, abi) = self.instance_function_with_abi(instance);
        if function.count_params() != 1
            || !matches!(abi.args[0].mode, abi::PassMode::Direct)
            || !matches!(abi.ret.mode, abi::PassMode::Direct)
        {
            self.gcx.dcx().emit_error(
                "dynamic class descriptor has an incompatible native ABI".into(),
                Some(self.gcx.definition_ident(instance.def_id()).span),
            );
            return Err(crate::error::ReportedError);
        }
        let ptr = self.context.ptr_type(AddressSpace::default());
        let lookup = self.get_or_add_external_function(
            "__gc__class_descriptor",
            ptr.fn_type(&[ptr.into()], false),
        );
        let builder = self.context.create_builder();
        builder.position_at_end(self.context.append_basic_block(function, "object_context"));
        let owner = builder
            .build_extract_value(
                function.get_nth_param(0).unwrap().into_struct_value(),
                0,
                "object_owner",
            )
            .unwrap();
        let descriptor = builder
            .build_call(lookup, &[owner.into()], "actual_class")
            .unwrap()
            .try_as_basic_value()
            .basic()
            .unwrap();
        builder.build_return(Some(&descriptor)).unwrap();
        Ok(())
    }

    /// Emit a forwarding-only frame. All ownership obligations pass directly
    /// to the selected constructor, so a panic unwinds through this frame with
    /// no duplicate local cleanup. The descriptor is immutable process metadata.
    pub(super) fn emit_class_initializer_dispatch(
        &mut self,
        instance: Instance<'gcx>,
        source: hir::DefinitionID,
    ) -> CompileResult<()> {
        let source_instance = Instance::item(source, instance.args());
        self.class_dispatch_target(source_instance)?;
        let source_signature =
            instantiate_ty_with_args(self.gcx, self.gcx.get_type(source), instance.args());
        let TyKind::FnPointer { output, .. } = source_signature.kind() else {
            unreachable!()
        };
        let entry = self
            .gcx
            .class_initializer(output, source)
            .expect("validated constructor family");
        let (function, abi) = self.instance_function_with_abi(instance);
        let (declared, source_abi) = self.instance_function_with_abi(source_instance);
        if abi.ret.mode != source_abi.ret.mode
            || function.count_params() != declared.count_params() + 1
            || function.get_type().get_return_type() != declared.get_type().get_return_type()
        {
            self.gcx.dcx().emit_error(
                "contextual constructor has an incompatible native ABI".into(),
                Some(self.gcx.definition_ident(source).span),
            );
            return Err(crate::error::ReportedError);
        }
        let own = self.gcx.store.interners.intern_generic_args_slice(
            &instance.args()[self.gcx.generics_of(source).parent_count..],
        );
        let ptr = self.context.ptr_type(AddressSpace::default());
        let key = if own.is_empty() {
            ptr.const_null()
        } else {
            self.gcx
                .store
                .class_dispatch_calls
                .borrow_mut()
                .entry(self.gcx.package_index())
                .or_default()
                .insert(source_instance);
            self.class_arguments(own)
        };
        let lookup = self.get_or_add_external_function(
            "__rt__class_resolve_initializer",
            ptr.fn_type(&[ptr.into(), ptr.into(), ptr.into()], false),
        );
        let builder = self.context.create_builder();
        builder.position_at_end(
            self.context
                .append_basic_block(function, "constructor_dispatch"),
        );
        // Indirect results precede ordinary inputs in the native ABI. Forward
        // their caller-owned storage unchanged, removing only class context.
        let context_index = usize::from(matches!(abi.ret.mode, abi::PassMode::Indirect { .. }));
        let target = builder
            .build_call(
                lookup,
                &[
                    function.get_nth_param(context_index as u32).unwrap().into(),
                    self.class_family(entry.family).into(),
                    key.into(),
                ],
                "constructor_target",
            )
            .unwrap()
            .try_as_basic_value()
            .basic()
            .unwrap()
            .into_pointer_value();
        let arguments: Vec<BasicMetadataValueEnum<'llvm>> = function
            .get_param_iter()
            .enumerate()
            .filter_map(|(index, value)| (index != context_index).then_some(value.into()))
            .collect();
        let call = builder
            .build_indirect_call(declared.get_type(), target, &arguments, "constructed")
            .unwrap();
        call.set_call_convention(declared.get_call_conventions());
        let result = call.try_as_basic_value().basic();
        builder
            .build_return(result.as_ref().map(|value| value as &dyn BasicValue))
            .unwrap();
        Ok(())
    }

    pub(super) fn emit_class_registration_ctor(&mut self) -> CompileResult<()> {
        if self.class_registrations.is_empty() {
            return Ok(());
        }
        let ptr = self.context.ptr_type(AddressSpace::default());
        let entry_ty = self
            .context
            .struct_type(&[ptr.into(), ptr.into(), ptr.into(), ptr.into()], false);
        let registrations: Vec<_> = self
            .class_registrations
            .iter()
            .map(|(key, value)| (*key, *value))
            .collect();
        let mut entries = vec![];
        for ((class, _), (family, arguments, target)) in registrations {
            let target = self.class_dispatch_target(target)?;
            entries.push(entry_ty.const_named_struct(&[
                self.class_identity(class).into(),
                self.class_family(family).into(),
                self.class_arguments(arguments).into(),
                target.into(),
            ]));
        }
        let table = self.module.add_global(
            entry_ty.array_type(entries.len() as u32),
            None,
            "__taro_generic_class_methods",
        );
        table.set_linkage(Linkage::Internal);
        table.set_constant(true);
        table.set_initializer(&entry_ty.const_array(&entries));
        let ctor = self.module.add_function(
            "__taro_register_class_methods",
            self.context.void_type().fn_type(&[], false),
            Some(Linkage::Internal),
        );
        let builder = self.context.create_builder();
        builder.position_at_end(self.context.append_basic_block(ctor, "entry"));
        let register = self.get_or_add_external_function(
            "__rt__class_register_generic_methods",
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
        Ok(())
    }
}

#[cfg(test)]
mod discovery_tests {
    use super::*;

    #[test]
    fn function_operands_do_not_apply_callee_arguments_to_a_caller_snapshot() {
        crate::test_support::analyze_script(
            "func target[T, U, const N: usize](_ first: T, _ second: U, _ values: [U; N]) {}\nfunc caller[X, Y, Z, const N: usize]() {}\nfunc main() {}",
            |package, gcx| {
                let target = package.root.declarations[0].id;
                let caller = package.root.declarations[1].id;
                let caller_args =
                    crate::sema::tycheck::utils::generics::GenericsBuilder::identity_for_item(
                        gcx, caller,
                    );
                let args = gcx
                    .store
                    .interners
                    .intern_generic_args_slice(&caller_args[1..]);
                let snapshot = instantiate_ty_with_args(gcx, gcx.get_type(target), args);
                let function = Operand::Constant(mir::Constant {
                    ty: snapshot,
                    value: mir::ConstantKind::Function(target, args, snapshot),
                });
                let context = Context::create();
                let emitter = Emitter::new(
                    &context,
                    context.create_module("function-template"),
                    context.create_builder(),
                    gcx,
                )
                .unwrap_or_else(|_| panic!("function template emitter"));
                let body = crate::mir::test_support::minimal_body(gcx);
                assert_eq!(emitter.operand_ty(&body, &function), snapshot);
            },
        );
    }

    #[test]
    fn unrelated_call_discovery_does_not_instantiate_source_generic_coordinates() {
        crate::test_support::analyze_script(
            "func unrelated[T, const N: usize]() -> [T; N] { loop {} }\nfunc main() {}",
            |package, gcx| {
                let id = package.root.declarations[0].id;
                // A generated callable may have remapped coordinates that are
                // not its source function's [type, const] coordinates. Class
                // discovery must leave that callable to its actual generator.
                let args = gcx.store.interners.intern_generic_args(vec![
                    crate::sema::models::GenericArgument::Type(gcx.types.bool),
                    crate::sema::models::GenericArgument::Type(gcx.types.bool),
                ]);
                let function = Operand::Constant(mir::Constant {
                    ty: gcx.get_type(id),
                    value: mir::ConstantKind::Function(id, args, gcx.get_type(id)),
                });
                let context = Context::create();
                let mut emitter = Emitter::new(
                    &context,
                    context.create_module("class-discovery"),
                    context.create_builder(),
                    gcx,
                )
                .unwrap_or_else(|_| panic!("class discovery emitter"));
                let body = crate::mir::test_support::minimal_body(gcx);
                assert!(
                    emitter
                        .lower_class_call_target(&body, &mut [], &function, &[])
                        .unwrap_or_else(|_| panic!("class call discovery"))
                        .is_none()
                );
            },
        );
    }
}
