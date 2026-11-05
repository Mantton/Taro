//! Concrete copy metadata for GC-erased values. Only erased payload shells
//! require work; references, strings and class objects retain shared identity.
//! These physical recipes contain no source Clone/drop or borrow callbacks.
use super::*;

impl<'llvm, 'gcx> Emitter<'llvm, 'gcx> {
    pub(super) fn gc_value_descriptor_for(&mut self, ty: Ty<'gcx>) -> PointerValue<'llvm> {
        let ty = crate::sema::tycheck::utils::normalize_post_monomorphization(
            self.gcx,
            self.mono_ty(ty),
        );
        if let Some(descriptor) = self.gc_value_descriptors.get(&ty) {
            return *descriptor;
        }
        let layout = self.gc_descriptor_for(ty);
        let nodes = self.gc_copy_layout_nodes_for_ty(ty);
        let copies = self.gc_nodes_constant(
            &nodes,
            &format!("__gc_copy_layout_{}", self.gc_value_descriptors.len()),
        );
        let pointer = self.context.ptr_type(AddressSpace::default());
        let descriptor_ty = self.context.struct_type(
            &[pointer.into(), pointer.into(), self.usize_ty.into()],
            false,
        );
        let initializer = descriptor_ty.const_named_struct(&[
            layout.into(),
            copies.into(),
            self.usize_ty.const_int(nodes.len() as u64, false).into(),
        ]);
        let global = self.module.add_global(
            descriptor_ty,
            None,
            &format!("__gc_value_descriptor_{}", self.gc_value_descriptors.len()),
        );
        global.set_initializer(&initializer);
        global.set_constant(true);
        global.set_linkage(Linkage::Internal);
        let descriptor = global.as_pointer_value();
        self.gc_value_descriptors.insert(ty, descriptor);
        descriptor
    }

    /// Runtime roots cover the temporary snapshot while nested erased payload
    /// allocations collect. The caller publishes the surrounding MIR frame.
    pub(super) fn copy_gc_value_storage(&mut self, ty: Ty<'gcx>, storage: PointerValue<'llvm>) {
        let descriptor = self.gc_value_descriptor_for(ty);
        let pointer = self.context.ptr_type(AddressSpace::default());
        let copy = self.get_or_add_external_function(
            "__gc__value_copy",
            self.context
                .void_type()
                .fn_type(&[pointer.into(), pointer.into(), pointer.into()], false),
        );
        self.builder
            .build_call(
                copy,
                &[storage.into(), storage.into(), descriptor.into()],
                "",
            )
            .unwrap();
    }

    /// `GcTypeMetadata`: the native dispatch prefix plus a value descriptor.
    pub(super) fn gc_type_metadata_ty(&self) -> inkwell::types::StructType<'llvm> {
        let pointer = self.context.ptr_type(AddressSpace::default());
        self.context.struct_type(
            &[
                pointer.into(),
                self.usize_ty.into(),
                pointer.into(),
                pointer.into(),
            ],
            false,
        )
    }

    /// Erase one concrete value into fresh traced payload storage. The runtime
    /// roots the staged source and duplicates nested erased payloads, so boxing
    /// is an ordinary value copy. Witness thunks have no MIR frame to publish;
    /// their caller's call-site map roots everything they forward.
    pub(super) fn box_gc_value(
        &mut self,
        ty: Ty<'gcx>,
        value: BasicValueEnum<'llvm>,
        metadata: PointerValue<'llvm>,
        publish_frame: bool,
    ) -> PointerValue<'llvm> {
        let pointer = self.context.ptr_type(AddressSpace::default());
        let source = match self.lower_ty(ty) {
            Some(llvm_ty) => {
                let source = self.build_entry_alloca(llvm_ty, "gc_exist_source");
                self.builder.build_store(source, value).unwrap();
                source
            }
            None => pointer.const_null(),
        };
        if publish_frame {
            self.emit_source_typed_gc_stack_map(
                self.current_span.expect("boxing source span"),
                crate::codegen::gc_stack_maps::StackMapSiteKind::Allocation,
            );
        }
        let boxing = self.get_or_add_external_function(
            "__gc__existential_box",
            pointer.fn_type(&[pointer.into(), pointer.into()], false),
        );
        self.builder
            .build_call(boxing, &[source.into(), metadata.into()], "gc_exist_data")
            .unwrap()
            .try_as_basic_value()
            .basic()
            .unwrap()
            .into_pointer_value()
    }

    pub(super) fn copy_gc_value(
        &mut self,
        ty: Ty<'gcx>,
        value: BasicValueEnum<'llvm>,
    ) -> BasicValueEnum<'llvm> {
        if self.gc_copy_layout_nodes_for_ty(ty).is_empty() {
            return value;
        }
        let snapshot = self.build_entry_alloca(value.get_type(), "gc_value_copy");
        self.builder.build_store(snapshot, value).unwrap();
        self.emit_source_typed_gc_stack_map(
            self.current_span.expect("copy source span"),
            crate::codegen::gc_stack_maps::StackMapSiteKind::Allocation,
        );
        self.copy_gc_value_storage(ty, snapshot);
        self.builder
            .build_load(value.get_type(), snapshot, "gc_copied_value")
            .unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::codegen::gc_stack_maps::GcLayoutKind;

    #[test]
    fn copy_layouts_visit_inline_erased_headers_but_preserve_references_and_classes() {
        crate::test_support::analyze_native_class_fixture(
            "class Item { value: int32 }\nfunc main() {}",
            &[],
            &[],
            |package, _, gcx| {
                let class = gcx.get_type(package.root.declarations[0].id);
                let erased = Ty::new(TyKind::BoxedExistential { interfaces: &[] }, gcx);
                let reference = Ty::new(TyKind::Reference(erased), gcx);
                let tuple = Ty::new(
                    TyKind::Tuple(gcx.store.interners.intern_ty_list(vec![
                        erased,
                        reference,
                        class,
                        gcx.types.int32,
                    ])),
                    gcx,
                );
                let context = Context::create();
                let mut emitter = Emitter::new(
                    &context,
                    context.create_module("gc-copy-layout"),
                    context.create_builder(),
                    gcx,
                )
                .unwrap_or_else(|_| panic!("copy layout emitter"));

                for ty in [reference, class, gcx.types.int32, gcx.types.string] {
                    assert!(
                        emitter.gc_copy_layout_nodes_for_ty(ty).is_empty(),
                        "shared/trivial values require no copy fixups"
                    );
                }
                let nodes = emitter.gc_copy_layout_nodes_for_ty(tuple);
                assert_eq!(nodes.len(), 1, "only the inline erased slot needs a fixup");
                assert_eq!(nodes[0].kind, GcLayoutKind::Pointer);
                assert_eq!(nodes[0].offset, 0);
                assert_eq!(
                    nodes
                        .iter()
                        .filter(|node| node.kind == GcLayoutKind::Pointer)
                        .count(),
                    1
                );
                assert!(
                    !nodes
                        .iter()
                        .any(|node| node.kind == GcLayoutKind::Reference)
                );
                let descriptor = emitter.gc_value_descriptor_for(tuple);
                assert_eq!(emitter.gc_value_descriptor_for(tuple), descriptor);
                emitter.module.verify().unwrap();
            },
        );
    }

    #[test]
    fn generated_value_copy_recipes_execute_against_the_real_collector() {
        unsafe extern "C" {
            fn __gc__value_copy(destination: *mut u8, source: *const u8, descriptor: *const u8);
            fn __gc__existential_box(source: *const u8, metadata: *const u8) -> *mut u8;
            fn __gc__thread_detach();
        }
        #[repr(C)]
        struct Metadata {
            entries: *const u8,
            len: usize,
            identity: *const u8,
            value: *const u8,
        }
        #[repr(C)]
        struct Header {
            data: *mut u8,
            metadata: *const Metadata,
        }
        #[repr(C)]
        struct Record {
            scalar: i64,
            shared: *mut i64,
        }
        crate::test_support::analyze_script("func main() {}", |_, gcx| {
            let context = Context::create();
            let mut emitter = Emitter::new(
                &context,
                context.create_module("gc-copy-execute"),
                context.create_builder(),
                gcx,
            )
            .unwrap_or_else(|_| panic!("copy execution emitter"));

            let erased = Ty::new(TyKind::BoxedExistential { interfaces: &[] }, gcx);
            let reference = Ty::new(TyKind::Reference(gcx.types.int64), gcx);
            let record = Ty::new(
                TyKind::Tuple(
                    gcx.store
                        .interners
                        .intern_ty_list(vec![gcx.types.int64, reference]),
                ),
                gcx,
            );
            let descriptor = emitter.gc_value_descriptor_for(record);
            let pointer = context.ptr_type(AddressSpace::default());
            let getter =
                emitter
                    .module
                    .add_function("record_descriptor", pointer.fn_type(&[], false), None);
            emitter
                .builder
                .position_at_end(context.append_basic_block(getter, "entry"));
            emitter.builder.build_return(Some(&descriptor)).unwrap();
            let function = emitter.module.add_function(
                "copy_header",
                context.void_type().fn_type(&[pointer.into()], false),
                None,
            );
            emitter
                .builder
                .position_at_end(context.append_basic_block(function, "entry"));
            emitter.copy_gc_value_storage(
                erased,
                function.get_nth_param(0).unwrap().into_pointer_value(),
            );
            emitter.builder.build_return(None).unwrap();
            emitter.module.verify().unwrap();
            emitter
                .module
                .run_passes(
                    "default<O3>",
                    &emitter.target_machine,
                    PassBuilderOptions::create(),
                )
                .unwrap();
            let copy_runtime = emitter.module.get_function("__gc__value_copy").unwrap();
            let engine = emitter
                .module
                .create_jit_execution_engine(inkwell::OptimizationLevel::Aggressive)
                .unwrap();
            engine.add_global_mapping(&copy_runtime, __gc__value_copy as *const () as usize);
            unsafe {
                let getter = engine
                    .get_function::<unsafe extern "C" fn() -> *const u8>("record_descriptor")
                    .unwrap();
                let copy = engine
                    .get_function::<unsafe extern "C" fn(*mut u8)>("copy_header")
                    .unwrap();
                let metadata = Box::leak(Box::new(Metadata {
                    entries: std::ptr::null(),
                    len: 0,
                    identity: Box::leak(Box::new(1_u8)),
                    value: getter.call(),
                }));
                let mut shared = Box::new(7_i64);
                let source = Record {
                    scalar: 11,
                    shared: &mut *shared,
                };
                let data = __gc__existential_box(
                    (&source as *const Record).cast(),
                    (metadata as *const Metadata).cast(),
                );
                let original = Header { data, metadata };
                let mut copied = Header { ..original };
                copy.call((&mut copied as *mut Header).cast());
                assert_ne!(
                    copied.data, original.data,
                    "erased value copies must duplicate their payload storage"
                );
                (*copied.data.cast::<Record>()).scalar = 42;
                assert_eq!((*original.data.cast::<Record>()).scalar, 11);
                assert_eq!((*copied.data.cast::<Record>()).shared, source.shared);
                *(*copied.data.cast::<Record>()).shared = 99;
                assert_eq!(*shared, 99);
                __gc__thread_detach();
            }
            // Heap spans retain immutable descriptor pointers. Keep generated
            // metadata/code process-long, just like a linked Taro image.
            std::mem::forget(engine);
        });
    }
}
