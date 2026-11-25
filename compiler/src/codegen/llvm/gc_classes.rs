//! Candidate object payloads keep an immutable, non-traced metadata word first,
//! followed by the current model's flattened base-to-derived logical fields.
//! Tuple order preserves every inherited field offset in subclasses. Class
//! values themselves remain one pointer and are traced as handles.
use super::*;

impl<'llvm, 'gcx> Emitter<'llvm, 'gcx> {
    /// Replace the compiler-private publication helper as one unit. Constructor
    /// field/default evaluation still produces its checked nested payload;
    /// publication stores those fields in the flattened GC object layout. The
    /// following class-handle conversion installs the actual dynamic metadata.
    pub(super) fn try_emit_gc_class_factory(
        &mut self,
        instance: Instance<'gcx>,
    ) -> CompileResult<bool> {
        if !self.gcx.is_class_payload_factory(instance.def_id()) {
            return Ok(false);
        }
        let signature = instantiate_ty_with_args(
            self.gcx,
            self.gcx.get_type(instance.def_id()),
            instance.args(),
        );
        let TyKind::FnPointer { inputs, output, .. } = signature.kind() else {
            return Ok(false);
        };
        let [source_ty] = inputs.as_slice() else {
            return Ok(false);
        };
        let Some(class) = self.gcx.class_for_payload(*source_ty) else {
            return Ok(false);
        };
        if !self.gcx.uses_native_class_handle(output) {
            return Ok(false);
        }
        let (function, abi) = self.instance_function_with_abi(instance);
        assert!(
            matches!(abi.ret.mode, abi::PassMode::Direct),
            "class handle result ABI"
        );
        let saved = self.builder.get_insert_block();
        self.builder.position_at_end(
            self.context
                .append_basic_block(function, "gc_class_publish"),
        );
        let source_layout = self
            .lower_ty(*source_ty)
            .expect("class constructor payload layout");
        // Indirect payloads live in caller storage; the walker reaches them
        // through a spilled frame slot, like indirect MIR parameters.
        let mut root = None;
        let source = match abi.args[0].mode {
            abi::PassMode::Indirect { .. } => {
                let payload = function.get_nth_param(0).unwrap().into_pointer_value();
                let pointer = self.context.ptr_type(AddressSpace::default());
                let slot = self.build_entry_alloca(pointer, "class_fields_base");
                self.builder.build_store(slot, payload).unwrap();
                root = Some((slot, 1));
                payload
            }
            abi::PassMode::Direct => {
                let storage = self.build_entry_alloca(source_layout, "initialized_class_fields");
                self.builder
                    .build_store(storage, function.get_nth_param(0).unwrap())
                    .unwrap();
                storage
            }
            abi::PassMode::Ignore => self.build_entry_alloca(source_layout, "empty_class_fields"),
        };
        let selector = self.build_entry_alloca(self.context.i64_type(), "class_gc_selector");
        let ident = self.gcx.definition_ident(instance.def_id());
        let record = self.emit_gc_stack_map(
            function,
            selector,
            0,
            crate::codegen::gc_stack_maps::StackMapSiteKind::Allocation,
            &[super::gc_sites::GcRootOperand {
                location: root.map_or(source, |(slot, _)| slot),
                ty: *source_ty,
                storage_deref_depth: root.map_or(0, |(_, depth)| depth),
            }],
            vec![crate::codegen::gc_stack_maps::PendingLogicalFrame {
                function: self.gcx.symbol_text(ident.symbol).as_str().into(),
                file: self
                    .gcx
                    .dcx()
                    .file_path(ident.span.file)
                    .map(|path| path.to_string_lossy().into_owned())
                    .unwrap_or_else(|| "<unknown>".into()),
                line: ident
                    .span
                    .start
                    .line
                    .saturating_add(1)
                    .try_into()
                    .unwrap_or(u32::MAX),
                column: ident
                    .span
                    .start
                    .offset
                    .saturating_add(1)
                    .try_into()
                    .unwrap_or(u32::MAX),
            }],
        );
        self.pending_gc_stack_maps.push(record);
        let payload = self.gc_class_payload_ty(class).unwrap();
        let object = self.call_gc_alloc(payload);
        let layout = self.lower_ty(payload).unwrap().into_struct_type();
        let TyKind::Adt(class_def, _) = class.kind() else {
            unreachable!()
        };
        for field in 0..self.gcx.get_struct_definition(class_def.id).fields.len() {
            let path = self
                .gcx
                .class_field_payload_path(class, field)
                .expect("inherited constructor field path");
            let mut address = source;
            let mut ty = *source_ty;
            for field in path {
                let TyKind::Adt(definition, arguments) = ty.kind() else {
                    panic!("constructor field path crosses non-payload storage")
                };
                let definition = self.gcx.get_struct_definition(definition.id);
                let field_ty = instantiate_ty_with_args(
                    self.gcx,
                    definition.fields[field as usize].ty,
                    arguments,
                );
                let physical = struct_field_layout(
                    self.context,
                    self.gcx,
                    &self.target_data,
                    definition.adt_def.id,
                    arguments,
                    GenericArguments::empty(),
                    definition.repr,
                )
                .logical_to_physical[field as usize];
                address = self
                    .builder
                    .build_struct_gep(
                        self.lower_ty(ty).unwrap().into_struct_type(),
                        address,
                        physical,
                        "constructor_field",
                    )
                    .unwrap();
                ty = field_ty;
            }
            if let Some(field_layout) = self.lower_ty(ty) {
                let value = self
                    .builder
                    .build_load(field_layout, address, "initialized_field")
                    .unwrap();
                let slot = self
                    .builder
                    .build_struct_gep(layout, object, (field + 1) as u32, "gc_class_field")
                    .unwrap();
                self.builder.build_store(slot, value).unwrap();
            }
        }
        let handle = self
            .lower_ty(output)
            .unwrap()
            .into_struct_type()
            .const_zero();
        let handle = self
            .builder
            .build_insert_value(handle, object, 0, "gc_class_handle")
            .unwrap()
            .as_basic_value_enum();
        self.builder.build_return(Some(&handle)).unwrap();
        if let Some(saved) = saved {
            self.builder.position_at_end(saved);
        }
        Ok(true)
    }

    pub(super) fn gc_class_payload_ty(&self, class: Ty<'gcx>) -> Option<Ty<'gcx>> {
        crate::sema::tycheck::class_layout::gc_class_payload_ty(self.gcx, self.mono_ty(class))
    }
}

#[cfg(test)]
mod tests {

    #[test]
    fn published_gc_handles_preserve_dynamic_dispatch_and_construction_metadata() {
        unsafe extern "C" {
            fn __gc__class_initialize(object: *mut u8, descriptor: *const u8);
            fn __gc__class_descriptor(object: *const u8) -> *const u8;
            fn __gc__class_resolve_method(
                object: *const u8,
                family: *const u8,
                arguments: *const u8,
            ) -> *const u8;
            fn __gc__class_is_a(object: *const u8, identity: *const u8) -> bool;
        }
        crate::test_support::analyze_native_class_fixture(
            "class Base {}\nclass Child: Base {}\nextend Base { func read() -> int32 { return 11; }; }\nextend Child { override func read() -> int32 { return 22; }; }\nfunc main() {}",
            &[],
            &[],
            |package, bodies, gcx| {
                let base = gcx.get_type(package.root.declarations[0].id);
                let child = gcx.get_type(package.root.declarations[1].id);
                let functions = bodies
                    .into_iter()
                    .map(|body| (body.owner, &*gcx.store.arenas.mir_bodies.alloc(body)))
                    .collect();
                let mir = gcx.store.alloc_mir_package(mir::MirPackage {
                    functions,
                    entry: None,
                });
                gcx.store
                    .mir_packages
                    .borrow_mut()
                    .insert(gcx.package_index(), mir);
                let context = Context::create();
                let mut emitter = Emitter::new(
                    &context,
                    context.create_module("gc-class-dispatch"),
                    context.create_builder(),
                    gcx,
                )
                .unwrap_or_else(|_| panic!("class dispatch emitter"));

                let pointer = context.ptr_type(AddressSpace::default());
                let declared = gcx.class_methods(base)[0];
                let base_instance =
                    Instance::item(declared.implementation, GenericArguments::empty());
                for (class, result) in [(base, 11), (child, 22)] {
                    let method = gcx.class_methods(class)[0];
                    let instance = Instance::item(method.implementation, GenericArguments::empty());
                    let (function, _) = emitter.instance_function_with_abi(instance);
                    emitter
                        .builder
                        .position_at_end(context.append_basic_block(function, "implementation"));
                    emitter
                        .builder
                        .build_return(Some(&context.i32_type().const_int(result, false)))
                        .unwrap();
                }
                let publish = emitter.module.add_function(
                    "publish_child",
                    context
                        .void_type()
                        .fn_type(&[pointer.into(), pointer.into()], false),
                    None,
                );
                emitter
                    .builder
                    .position_at_end(context.append_basic_block(publish, "entry"));
                let mut body = mir::test_support::minimal_body(gcx);
                body.locals[body.return_local].ty = child;
                let raw = mir::test_support::push_temp(
                    &mut body,
                    Ty::new(
                        TyKind::Pointer(gcx.types.uint8, hir::Mutability::Mutable),
                        gcx,
                    ),
                );
                let mut locals = vec![
                    LocalStorage::Stack(publish.get_nth_param(1).unwrap().into_pointer_value()),
                    LocalStorage::Value(Some(publish.get_nth_param(0).unwrap())),
                ];
                let value = emitter
                    .lower_rvalue(
                        &body,
                        &mut locals,
                        child,
                        &mir::Rvalue::Cast {
                            operand: Operand::Copy(Place::from_local(raw)),
                            ty: child,
                            kind: mir::CastKind::NativeClassHandle,
                        },
                    )
                    .unwrap_or_else(|_| panic!("GC handle publication"))
                    .unwrap();
                emitter
                    .builder
                    .build_store(
                        publish.get_nth_param(1).unwrap().into_pointer_value(),
                        value,
                    )
                    .unwrap();
                emitter.builder.build_return(None).unwrap();
                let run = emitter.module.add_function(
                    "read_as_base",
                    context.i32_type().fn_type(&[pointer.into()], false),
                    None,
                );
                emitter
                    .builder
                    .position_at_end(context.append_basic_block(run, "entry"));
                let handle = emitter
                    .builder
                    .build_load(
                        emitter.lower_ty(base).unwrap(),
                        run.get_nth_param(0).unwrap().into_pointer_value(),
                        "base_handle",
                    )
                    .unwrap();
                let (target, _) = emitter
                    .class_handle_call_target(base_instance, handle)
                    .unwrap_or_else(|_| panic!("virtual GC receiver"))
                    .unwrap();
                let CallTarget::Indirect(signature, target) = target else {
                    panic!("non-final method requires dynamic dispatch")
                };
                let result = emitter
                    .builder
                    .build_indirect_call(signature, target, &[handle.into()], "read")
                    .unwrap()
                    .try_as_basic_value()
                    .basic()
                    .unwrap();
                emitter.builder.build_return(Some(&result)).unwrap();
                let synthetic = gcx.class_object_descriptor(base).unwrap();
                let synthetic_instance = Instance::item(synthetic, GenericArguments::empty());
                emitter
                    .emit_class_object_descriptor(synthetic_instance)
                    .unwrap_or_else(|_| panic!("dynamic constructor metadata"));
                let (descriptor_fn, _) = emitter.instance_function_with_abi(synthetic_instance);
                let descriptor = emitter.module.add_function(
                    "actual_descriptor",
                    pointer.fn_type(&[pointer.into()], false),
                    None,
                );
                emitter
                    .builder
                    .position_at_end(context.append_basic_block(descriptor, "entry"));
                let handle = emitter
                    .builder
                    .build_load(
                        emitter.lower_ty(base).unwrap(),
                        descriptor.get_nth_param(0).unwrap().into_pointer_value(),
                        "handle",
                    )
                    .unwrap();
                let value = emitter
                    .builder
                    .build_call(descriptor_fn, &[handle.into()], "descriptor")
                    .unwrap()
                    .try_as_basic_value()
                    .basic()
                    .unwrap();
                emitter.builder.build_return(Some(&value)).unwrap();
                let is_child = emitter.module.add_function(
                    "is_child",
                    context.bool_type().fn_type(&[pointer.into()], false),
                    None,
                );
                emitter
                    .builder
                    .position_at_end(context.append_basic_block(is_child, "entry"));
                let handle = emitter
                    .builder
                    .build_load(
                        emitter.lower_ty(base).unwrap(),
                        is_child.get_nth_param(0).unwrap().into_pointer_value(),
                        "handle",
                    )
                    .unwrap();
                let value = emitter
                    .lower_existential_type_is(base, child, handle)
                    .unwrap_or_else(|_| panic!("GC dynamic subtype"));
                emitter.builder.build_return(Some(&value)).unwrap();
                emitter.module.verify().unwrap();
                let ir = emitter.module.print_to_string().to_string();
                assert!(!ir.contains("__rt__arc_"));
                assert!(!ir.contains("__rt__borrow_"));
                emitter
                    .module
                    .run_passes(
                        "default<O3>",
                        &emitter.target_machine,
                        PassBuilderOptions::create(),
                    )
                    .unwrap();
                let symbols = [
                    (
                        "__gc__class_initialize",
                        __gc__class_initialize as *const () as usize,
                    ),
                    (
                        "__gc__class_descriptor",
                        __gc__class_descriptor as *const () as usize,
                    ),
                    (
                        "__gc__class_resolve_method",
                        __gc__class_resolve_method as *const () as usize,
                    ),
                    ("__gc__class_is_a", __gc__class_is_a as *const () as usize),
                ];
                let symbols: Vec<_> = symbols
                    .into_iter()
                    .map(|(name, address)| (emitter.module.get_function(name).unwrap(), address))
                    .collect();
                let engine = emitter
                    .module
                    .create_jit_execution_engine(inkwell::OptimizationLevel::Aggressive)
                    .unwrap();
                for (function, address) in symbols {
                    engine.add_global_mapping(&function, address);
                }
                unsafe {
                    let mut header = 0_usize;
                    let object = (&mut header as *mut usize).cast();
                    let mut slot = std::ptr::null_mut::<u8>();
                    engine
                        .get_function::<unsafe extern "C" fn(*mut u8, *mut *mut u8)>(
                            "publish_child",
                        )
                        .unwrap()
                        .call(object, &mut slot);
                    assert_eq!(slot, object);
                    assert_ne!(header, 0);
                    let receiver = (&mut slot as *mut *mut u8).cast();
                    assert_eq!(
                        engine
                            .get_function::<unsafe extern "C" fn(*mut u8) -> i32>("read_as_base")
                            .unwrap()
                            .call(receiver),
                        22
                    );
                    assert!(
                        engine
                            .get_function::<unsafe extern "C" fn(*mut u8) -> bool>("is_child")
                            .unwrap()
                            .call(receiver)
                    );
                    assert_eq!(
                        engine
                            .get_function::<unsafe extern "C" fn(*mut u8) -> *const u8>(
                                "actual_descriptor"
                            )
                            .unwrap()
                            .call(receiver) as usize,
                        header
                    );
                }
                std::mem::forget(engine);
            },
        );
    }

    #[test]
    fn constructor_publication_flattens_inherited_fields_for_direct_and_indirect_arguments() {
        unsafe extern "C" {
            fn __gc__alloc(size: usize, descriptor: *const u8) -> *mut u8;
            fn __gc__thread_detach();
        }
        crate::test_support::analyze_native_class_fixture(
            "struct ClassHandle { owner: *const uint8 }\nfunc __classAllocatePayload[P](_ value: P) -> ClassHandle { loop {} }\nclass Base[T] { value: T }\nclass Child[T]: Base[T] { extra: int64 }\nstruct Cases { small: Child[int32]; large: Child[[int64; 4]]; referenced: Child[*const int32] }\nfunc main() {}",
            &[],
            &[(hir::StdItem::ClassHandle, "ClassHandle")],
            |package, bodies, gcx| {
                let helper = package.root.declarations[1].id;
                let functions = bodies
                    .into_iter()
                    .map(|body| (body.owner, &*gcx.store.arenas.mir_bodies.alloc(body)))
                    .collect();
                let mir = gcx.store.alloc_mir_package(mir::MirPackage {
                    functions,
                    entry: None,
                });
                gcx.store
                    .mir_packages
                    .borrow_mut()
                    .insert(gcx.package_index(), mir);
                let cases = gcx.get_struct_definition(package.root.declarations[4].id);
                let context = Context::create();
                let mut emitter = Emitter::new(
                    &context,
                    context.create_module("gc-class-publication"),
                    context.create_builder(),
                    gcx,
                )
                .unwrap_or_else(|_| panic!("class publication emitter"));

                let pointer = context.ptr_type(AddressSpace::default());
                let mut layouts = vec![];
                for (index, field) in cases.fields.iter().enumerate() {
                    // Native admission still rejects persistent safe-reference
                    // fields. Instantiate the target reference case after
                    // checking its equivalent raw-pointer declaration.
                    let class = if index == 2 {
                        let TyKind::Adt(definition, _) = field.ty.kind() else {
                            unreachable!()
                        };
                        let reference = Ty::new(TyKind::Reference(gcx.types.int32), gcx);
                        Ty::new(
                            TyKind::Adt(
                                definition,
                                gcx.store.interners.intern_generic_args(vec![
                                    crate::sema::models::GenericArgument::Type(reference),
                                ]),
                            ),
                            gcx,
                        )
                    } else {
                        field.ty
                    };
                    let source_ty = gcx.ensure_class_payload(class).unwrap();
                    let arguments = gcx.store.interners.intern_generic_args(vec![
                        crate::sema::models::GenericArgument::Type(source_ty),
                    ]);
                    let instance = Instance::item(helper, arguments);
                    assert!(
                        emitter
                            .try_emit_gc_class_factory(instance)
                            .unwrap_or_else(|_| panic!("GC factory"))
                    );
                    let (factory, abi) = emitter.instance_function_with_abi(instance);
                    let source_layout = emitter.lower_ty(source_ty).unwrap().into_struct_type();
                    let extra_path = gcx.class_field_payload_path(class, 1).unwrap();
                    assert_eq!(extra_path.len(), 1);
                    let TyKind::Adt(source_def, source_args) = source_ty.kind() else {
                        unreachable!()
                    };
                    let definition = gcx.get_struct_definition(source_def.id);
                    let physical = struct_field_layout(
                        &context,
                        gcx,
                        &emitter.target_data,
                        source_def.id,
                        source_args,
                        GenericArguments::empty(),
                        definition.repr,
                    )
                    .logical_to_physical[extra_path[0] as usize];
                    let source_extra_offset = emitter
                        .target_data
                        .offset_of_element(&source_layout, physical)
                        .unwrap() as usize;
                    let target_ty = emitter.gc_class_payload_ty(class).unwrap();
                    let target_layout = emitter.lower_ty(target_ty).unwrap().into_struct_type();
                    layouts.push((
                        source_extra_offset,
                        emitter
                            .target_data
                            .offset_of_element(&target_layout, 1)
                            .unwrap() as usize,
                        emitter
                            .target_data
                            .offset_of_element(&target_layout, 2)
                            .unwrap() as usize,
                    ));
                    assert_eq!(
                        matches!(abi.args[0].mode, abi::PassMode::Indirect { .. }),
                        index == 1
                    );
                    let wrapper = emitter.module.add_function(
                        &format!("publish_{index}"),
                        context
                            .void_type()
                            .fn_type(&[pointer.into(), pointer.into()], false),
                        None,
                    );
                    emitter
                        .builder
                        .position_at_end(context.append_basic_block(wrapper, "entry"));
                    let source = wrapper.get_nth_param(0).unwrap().into_pointer_value();
                    let arguments = match abi.args[0].mode {
                        abi::PassMode::Direct => vec![
                            emitter
                                .builder
                                .build_load(source_layout, source, "source_payload")
                                .unwrap()
                                .into(),
                        ],
                        abi::PassMode::Indirect { .. } => vec![source.into()],
                        abi::PassMode::Ignore => vec![],
                    };
                    let value = emitter
                        .builder
                        .build_call(factory, &arguments, "publish")
                        .unwrap()
                        .try_as_basic_value()
                        .basic()
                        .unwrap();
                    emitter
                        .builder
                        .build_store(
                            wrapper.get_nth_param(1).unwrap().into_pointer_value(),
                            value,
                        )
                        .unwrap();
                    emitter.builder.build_return(None).unwrap();
                }
                assert_eq!(
                    emitter.pending_gc_stack_maps.len(),
                    3,
                    "every publication has a collecting-site record"
                );
                assert_eq!(emitter.pending_gc_stack_maps[2].roots.len(), 1);
                assert!(emitter.pending_gc_stack_maps[2].roots[0].nodes.iter().any(
                    |node| node.kind == crate::codegen::gc_stack_maps::GcLayoutKind::Reference
                ));
                let ir = emitter.module.print_to_string().to_string();
                assert!(!ir.contains("__rt__owned_buffer_"));
                assert!(!ir.contains("__rt__arc_"));
                emitter.module.verify().unwrap();
                emitter
                    .module
                    .run_passes(
                        "default<O3>",
                        &emitter.target_machine,
                        PassBuilderOptions::create(),
                    )
                    .unwrap();
                let allocation = emitter.module.get_function("__gc__alloc").unwrap();
                let engine = emitter
                    .module
                    .create_jit_execution_engine(inkwell::OptimizationLevel::Aggressive)
                    .unwrap();
                engine.add_global_mapping(&allocation, __gc__alloc as *const () as usize);
                let reference_target = Box::new(123_i32);
                for (index, (source_extra, value_offset, extra_offset)) in
                    layouts.into_iter().enumerate()
                {
                    let mut source = [10_i64, 20, 30, 40, 50, 60, 70, 80];
                    if index == 2 {
                        source[0] = (&*reference_target as *const i32) as i64;
                    }
                    unsafe {
                        source
                            .as_mut_ptr()
                            .cast::<u8>()
                            .add(source_extra)
                            .cast::<i64>()
                            .write(77);
                        let mut object = std::ptr::null_mut::<u8>();
                        let publish = engine
                            .get_function::<unsafe extern "C" fn(*const u8, *mut *mut u8)>(
                                &format!("publish_{index}"),
                            )
                            .unwrap();
                        publish.call(source.as_ptr().cast(), &mut object);
                        assert!(!object.is_null());
                        assert_eq!(
                            *object.cast::<usize>(),
                            0,
                            "dynamic metadata is published by the following checked handle conversion"
                        );
                        assert_eq!(*object.add(extra_offset).cast::<i64>(), 77);
                        if index == 0 {
                            assert_eq!(*object.add(value_offset).cast::<i32>(), 10);
                        } else if index == 1 {
                            assert_eq!(
                                *object.add(value_offset).cast::<[i64; 4]>(),
                                [10, 20, 30, 40]
                            );
                        } else {
                            let reference = *object.add(value_offset).cast::<*const i32>();
                            assert_eq!(reference, &*reference_target as *const i32);
                            assert_eq!(*reference, 123);
                        }
                    }
                }
                unsafe {
                    __gc__thread_detach();
                }
                std::mem::forget(engine);
            },
        );
    }

    #[test]
    fn inherited_gc_fields_use_direct_addresses_without_access_controllers() {
        for optimized in [false, true] {
            crate::test_support::analyze_native_class_fixture(
                "struct Pair { left: int32; right: int32 }\nclass Base { prefix: uint8; pair: Pair }\nclass Child: Base { extra: int64 }\nfunc main() {}",
                &[],
                &[],
                |package, _, gcx| {
                    let base = gcx.get_type(package.root.declarations[1].id);
                    let child = gcx.get_type(package.root.declarations[2].id);
                    let context = Context::create();
                    let mut emitter = Emitter::new(
                        &context,
                        context.create_module("gc-class-fields"),
                        context.create_builder(),
                        gcx,
                    )
                    .unwrap_or_else(|_| panic!("GC field emitter"));

                    let pointer = context.ptr_type(AddressSpace::default());
                    let payload = emitter.gc_class_payload_ty(child).unwrap();
                    let payload_layout = emitter.lower_ty(payload).unwrap().into_struct_type();
                    let pair_offset = emitter
                        .target_data
                        .offset_of_element(&payload_layout, 2)
                        .unwrap() as usize;
                    for (name, class, intrinsic, path) in [
                        (
                            "base_left",
                            base,
                            "__intrinsic_class_field_reference",
                            "1.0",
                        ),
                        (
                            "child_right",
                            child,
                            "__intrinsic_class_field_reference",
                            "1.1",
                        ),
                        ("read_left", base, "__intrinsic_class_field_read", "1.0"),
                        ("write_left", child, "__intrinsic_class_field_write", "1.0"),
                        ("add_left", base, "__intrinsic_class_field_modify", "1.0"),
                    ] {
                        let function = emitter.module.add_function(
                            name,
                            context
                                .void_type()
                                .fn_type(&[pointer.into(), pointer.into()], false),
                            None,
                        );
                        emitter
                            .builder
                            .position_at_end(context.append_basic_block(function, "entry"));
                        emitter.current_fn = Some(function);
                        let mut body = mir::test_support::minimal_body(gcx);
                        body.owner = package.root.declarations[3].id;
                        body.locals[body.return_local].ty = match intrinsic {
                            "__intrinsic_class_field_read" => gcx.types.int32,
                            "__intrinsic_class_field_write" | "__intrinsic_class_field_modify" => {
                                gcx.types.void
                            }
                            _ => Ty::new(TyKind::Reference(gcx.types.int32), gcx),
                        };
                        let input = mir::test_support::push_temp(
                            &mut body,
                            Ty::new(TyKind::Reference(class), gcx),
                        );
                        let mut locals = vec![
                            LocalStorage::Stack(
                                function.get_nth_param(1).unwrap().into_pointer_value(),
                            ),
                            LocalStorage::Value(Some(function.get_nth_param(0).unwrap())),
                        ];
                        let mut args = vec![
                            Operand::Copy(Place::from_local(input)),
                            Operand::Constant(mir::Constant {
                                ty: gcx.types.string,
                                value: mir::ConstantKind::String(gcx.intern_symbol(path)),
                            }),
                        ];
                        if intrinsic == "__intrinsic_class_field_modify" {
                            args.push(Operand::Constant(mir::Constant {
                                ty: gcx.types.string,
                                value: mir::ConstantKind::String(gcx.intern_symbol(
                                    mir::BinaryOperator::Add.compound_name().unwrap(),
                                )),
                            }));
                        }
                        if matches!(
                            intrinsic,
                            "__intrinsic_class_field_write" | "__intrinsic_class_field_modify"
                        ) {
                            args.push(Operand::Constant(mir::Constant {
                                ty: gcx.types.int32,
                                value: mir::ConstantKind::Integer(10),
                            }));
                        }
                        emitter
                            .lower_intrinsic_class_field(
                                &body,
                                &mut locals,
                                &args,
                                &Place::return_place(),
                                intrinsic,
                                None,
                            )
                            .unwrap_or_else(|_| {
                                panic!(
                                    "GC class field lowering: {:#?}",
                                    gcx.dcx().take_recorded_diagnostics()
                                )
                            });
                        emitter.builder.build_return(None).unwrap();
                    }
                    emitter.module.verify().unwrap();
                    let ir = emitter.module.print_to_string().to_string();
                    assert!(!ir.contains("__rt__arc_"));
                    assert!(!ir.contains("__rt__borrow_"));
                    if optimized {
                        emitter
                            .module
                            .run_passes(
                                "default<O3>",
                                &emitter.target_machine,
                                PassBuilderOptions::create(),
                            )
                            .unwrap();
                    }
                    let engine = emitter
                        .module
                        .create_jit_execution_engine(inkwell::OptimizationLevel::None)
                        .unwrap();
                    type Access = unsafe extern "C" fn(*mut u8, *mut u8);
                    let mut storage = [0_u64; 8];
                    let mut handle = storage.as_mut_ptr().cast::<u8>();
                    unsafe {
                        let left = handle.add(pair_offset).cast::<i32>();
                        let right = left.add(1);
                        left.write(21);
                        right.write(22);
                        for name in ["base_left", "child_right"] {
                            let mut projected = std::ptr::null_mut::<i32>();
                            engine.get_function::<Access>(name).unwrap().call(
                                (&mut handle as *mut *mut u8).cast(),
                                (&mut projected as *mut *mut i32).cast(),
                            );
                            assert_eq!(projected, if name == "child_right" { right } else { left });
                        }
                        let mut result = 0_i32;
                        engine.get_function::<Access>("read_left").unwrap().call(
                            (&mut handle as *mut *mut u8).cast(),
                            (&mut result as *mut i32).cast(),
                        );
                        assert_eq!(result, 21);
                        for (name, expected) in [("write_left", 10), ("add_left", 20)] {
                            engine
                                .get_function::<Access>(name)
                                .unwrap()
                                .call((&mut handle as *mut *mut u8).cast(), std::ptr::null_mut());
                            assert_eq!(*left, expected);
                        }
                    }
                },
            );
        }
    }
    use super::*;
    use crate::codegen::gc_stack_maps::GcLayoutKind;

    #[test]
    fn inherited_generic_fields_keep_offsets_and_metadata_is_not_traced() {
        crate::test_support::analyze_native_class_fixture(
            "class Base[T] { value: T; peer: *const int32 }\nclass Child[T]: Base[T] { label: string }\nstruct Holder { child: Child[int32] }\nfunc main() {}",
            &[],
            &[],
            |package, _, gcx| {
                let holder = package
                    .root
                    .declarations
                    .iter()
                    .find(|declaration| {
                        gcx.symbol_text(gcx.definition_ident(declaration.id).symbol).as_str() == "Holder"
                    })
                    .unwrap()
                    .id;
                let child = gcx.get_struct_definition(holder).fields[0].ty;
                let base = gcx.class_base(child).unwrap();
                // Native admission still rejects stored safe references until
                // G10/G26. Construct the selected persistent-reference field
                // in the model after checking the equivalent raw-pointer fixture.
                for class in [base, child] {
                    let TyKind::Adt(definition, _) = class.kind() else {
                        unreachable!()
                    };
                    let mut definition = gcx.get_struct_definition(definition.id).clone();
                    let mut fields = definition.fields.to_vec();
                    fields[1].ty = Ty::new(TyKind::Reference(gcx.types.int32), gcx);
                    definition.fields = gcx.store.arenas.global.alloc_slice_copy(&fields);
                    gcx.cache_struct_definition(definition.adt_def.id, definition);
                }
                let context = Context::create();
                let mut emitter = Emitter::new(
                    &context,
                    context.create_module("gc-class-layout"),
                    context.create_builder(),
                    gcx,
                )
                .unwrap_or_else(|_| panic!("class layout emitter"));

                let base_payload = emitter.gc_class_payload_ty(base).unwrap();
                let child_payload = emitter.gc_class_payload_ty(child).unwrap();
                let base_llvm = emitter.lower_ty(base_payload).unwrap().into_struct_type();
                let child_llvm = emitter.lower_ty(child_payload).unwrap().into_struct_type();
                assert_eq!(base_llvm.count_fields(), 3);
                assert_eq!(child_llvm.count_fields(), 4);
                for field in 0..base_llvm.count_fields() {
                    assert_eq!(
                        emitter.target_data.offset_of_element(&base_llvm, field),
                        emitter.target_data.offset_of_element(&child_llvm, field)
                    );
                }
                let nodes = emitter.gc_layout_nodes_for_ty(child_payload);
                assert_eq!(
                    crate::codegen::gc_stack_maps::gc_pointer_offsets(&nodes),
                    vec![
                        emitter
                            .target_data
                            .offset_of_element(&child_llvm, 2)
                            .unwrap(),
                        emitter
                            .target_data
                            .offset_of_element(&child_llvm, 3)
                            .unwrap(),
                    ],
                    "only peer and label are edges; metadata and scalar fields are omitted"
                );
                assert!(
                    nodes
                        .iter()
                        .any(|node| node.kind == GcLayoutKind::Reference)
                );
                assert!(nodes.iter().any(|node| node.kind == GcLayoutKind::Pointer));
                let descriptor = emitter.gc_descriptor_for(child_payload);
                assert_eq!(emitter.gc_descriptor_for(child_payload), descriptor);
                emitter
                    .module
                    .verify()
                    .expect("valid immutable class descriptor globals");
            },
        );
    }

    #[test]
    fn a_reference_to_a_class_traces_the_handle_slot_before_the_object() {
        crate::test_support::analyze_native_class_fixture(
            "final class Object { value: int32 }
func main() {}",
            &[],
            &[],
            |package, _, gcx| {
                let object = package
                    .root
                    .declarations
                    .iter()
                    .find(|declaration| {
                        gcx.symbol_text(gcx.definition_ident(declaration.id).symbol).as_str() == "Object"
                    })
                    .unwrap()
                    .id;
                let class = gcx.get_type(object);
                let reference = Ty::new(TyKind::Reference(class), gcx);
                let context = Context::create();
                let mut emitter = Emitter::new(
                    &context,
                    context.create_module("class-handle-slot"),
                    context.create_builder(),
                    gcx,
                )
                .unwrap_or_else(|_| panic!("class slot emitter"));

                let nodes = emitter.gc_layout_nodes_for_ty(reference);
                assert_eq!(nodes[0].kind, GcLayoutKind::Reference);
                assert_eq!(nodes[0].child_count, 1);
                assert_eq!(
                    nodes[nodes[0].first_child as usize].kind,
                    GcLayoutKind::Pointer
                );
                let word = emitter.target_data.get_pointer_byte_size(None) as u64;
                assert_eq!(
                    emitter
                        .target_data
                        .get_store_size(&emitter.lower_ty(class).unwrap()),
                    word
                );
                assert_eq!(
                    emitter
                        .target_data
                        .get_store_size(&emitter.lower_ty(reference).unwrap()),
                    word
                );
            },
        );
    }

    #[test]
    fn optional_classes_use_a_pointer_niche_but_nested_options_keep_their_tag() {
        crate::test_support::analyze_native_class_fixture(
            "final class Object { value: int32 }
enum MaybeObject { case none; case some(Object) }
enum Nested { case none; case some(MaybeObject) }
func main() {}",
            &[],
            &[],
            |package, _, gcx| {
                let find = |name: &str| {
                    package
                        .root
                        .declarations
                        .iter()
                        .find(|declaration| {
                            gcx.symbol_text(gcx.definition_ident(declaration.id).symbol).as_str() == name
                        })
                        .unwrap()
                        .id
                };
                let optional = find("MaybeObject");
                let nested = find("Nested");
                {
                    let context = Context::create();
                    let mut emitter = Emitter::new(
                        &context,
                        context.create_module("class-option-niches"),
                        context.create_builder(),
                        gcx,
                    )
                    .unwrap_or_else(|_| panic!("class option emitter"));

                    let word = emitter.target_data.get_pointer_byte_size(None) as u64;
                    let size = emitter
                        .target_data
                        .get_store_size(&emitter.lower_ty(gcx.get_type(optional)).unwrap());
                    assert_eq!(size, word);
                    let TyKind::Adt(_, args) = gcx.get_type(optional).kind() else {
                        unreachable!()
                    };
                    assert!(emitter.enum_layout_for(optional, args).npo.is_some());
                    let TyKind::Adt(_, args) = gcx.get_type(nested).kind() else {
                        unreachable!()
                    };
                    assert!(
                        emitter.enum_layout_for(nested, args).npo.is_none(),
                        "some(none) must remain distinct from none"
                    );
                    {
                        let nodes = emitter.gc_layout_nodes_for_ty(gcx.get_type(nested));
                        assert_eq!(nodes[0].kind, GcLayoutKind::Tagged);
                    }
                }
            },
        );
    }

    #[test]
    fn recursive_class_fields_trace_handles_instead_of_expanding_objects() {
        crate::test_support::analyze_native_class_fixture(
            "enum Link { case none; case some(Node) }\nfinal class Node { next: Link }\nfunc main() {}",
            &[],
            &[],
            |package, _, gcx| {
                let node = package
                    .root
                    .declarations
                    .iter()
                    .find(|declaration| {
                        gcx.symbol_text(gcx.definition_ident(declaration.id).symbol).as_str() == "Node"
                    })
                    .unwrap()
                    .id;
                let context = Context::create();
                let mut emitter = Emitter::new(
                    &context,
                    context.create_module("gc-class-recursive"),
                    context.create_builder(),
                    gcx,
                )
                .unwrap_or_else(|_| panic!("class layout emitter"));
                let payload = emitter.gc_class_payload_ty(gcx.get_type(node)).unwrap();
                let nodes = emitter.gc_layout_nodes_for_ty(payload);
                assert!(
                    nodes.len() < 10,
                    "recursive class handle terminates the layout graph"
                );
                assert!(nodes.iter().any(|node| node.kind == GcLayoutKind::Pointer));
                emitter.gc_descriptor_for(payload);
                emitter
                    .module
                    .verify()
                    .expect("valid recursive class descriptor");
            },
        );
    }
}
