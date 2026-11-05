//! G06c typed root-layout construction, adapted from main at 264cbe0e.
//! Layout follows the actual target ABI, including field reordering and active
//! enum payloads. Managed class values are pointer edges; allocation descriptors
//! for their payloads are built separately during G09.
use super::*;
use crate::codegen::gc_stack_maps::{GcLayoutKind, GcLayoutNode};

impl<'llvm, 'gcx> Emitter<'llvm, 'gcx> {
    pub(super) fn lower_gc_alloc(&mut self, ty: Ty<'gcx>) -> CompileResult<BasicValueEnum<'llvm>> {
        self.emit_source_typed_gc_stack_map(
            self.current_span.expect("allocation has no source span"),
            crate::codegen::gc_stack_maps::StackMapSiteKind::Allocation,
        );
        let pointer = self.call_gc_alloc(ty);
        Ok(self.lexical_reference(pointer))
    }

    /// The caller publishes its MIR or synthetic-frame root map first.
    pub(super) fn call_gc_alloc(&mut self, ty: Ty<'gcx>) -> PointerValue<'llvm> {
        let descriptor = self.gc_descriptor_for(ty);
        let size = self
            .lower_ty(ty)
            .map_or(0, |ty| self.target_data.get_abi_size(&ty))
            .max(1);
        let pointer = self.context.ptr_type(AddressSpace::default());
        let function = self.module.get_function("__gc__alloc").unwrap_or_else(|| {
            self.module.add_function(
                "__gc__alloc",
                pointer.fn_type(&[self.usize_ty.into(), pointer.into()], false),
                None,
            )
        });
        let call = self
            .builder
            .build_call(
                function,
                &[
                    self.usize_ty.const_int(size, false).into(),
                    descriptor.into(),
                ],
                "gc_alloc",
            )
            .unwrap();
        // Managed references use the returned storage address directly.
        let pointer = call
            .try_as_basic_value()
            .basic()
            .expect("GC allocation returns a pointer")
            .into_pointer_value();
        pointer
    }

    pub(super) fn gc_descriptor_for(&mut self, ty: Ty<'gcx>) -> PointerValue<'llvm> {
        let ty = crate::sema::tycheck::utils::normalize_aliases(self.gcx, self.mono_ty(ty));
        if let Some(descriptor) = self.gc_descriptors.get(&ty) {
            return *descriptor;
        }
        let (size, align) = self.lower_ty(ty).map_or((0, 1), |lowered| {
            (
                self.target_data.get_abi_size(&lowered),
                u64::from(self.target_data.get_abi_alignment(&lowered)),
            )
        });
        let nodes = self.gc_layout_nodes_for_ty(ty);
        let pointer = self.context.ptr_type(AddressSpace::default());
        let node_pointer = self.gc_nodes_constant(
            &nodes,
            &format!("__gc_layout_{}", self.gc_descriptors.len()),
        );
        let descriptor_ty = self.context.struct_type(
            &[
                self.usize_ty.into(),
                self.usize_ty.into(),
                pointer.into(),
                self.usize_ty.into(),
            ],
            false,
        );
        let value = descriptor_ty.const_named_struct(&[
            self.usize_ty.const_int(size, false).into(),
            self.usize_ty.const_int(align, false).into(),
            node_pointer.into(),
            self.usize_ty.const_int(nodes.len() as u64, false).into(),
        ]);
        let global = self.module.add_global(
            descriptor_ty,
            None,
            &format!("__gc_descriptor_{}", self.gc_descriptors.len()),
        );
        global.set_initializer(&value);
        global.set_constant(true);
        global.set_linkage(Linkage::Internal);
        let descriptor = global.as_pointer_value();
        self.gc_descriptors.insert(ty, descriptor);
        descriptor
    }

    pub(super) fn gc_nodes_constant(
        &self,
        nodes: &[GcLayoutNode],
        name: &str,
    ) -> PointerValue<'llvm> {
        let pointer = self.context.ptr_type(AddressSpace::default());
        let i8 = self.context.i8_type();
        let i32 = self.context.i32_type();
        let i64 = self.context.i64_type();
        let reserved = i8.array_type(6);
        let node_ty = self.context.struct_type(
            &[
                i64.into(),
                i64.into(),
                i32.into(),
                i32.into(),
                i8.into(),
                i8.into(),
                reserved.into(),
            ],
            false,
        );
        let node_values: Vec<_> = nodes
            .iter()
            .map(|node| {
                node_ty.const_named_struct(&[
                    i64.const_int(node.offset, false).into(),
                    i64.const_int(node.stride, false).into(),
                    i32.const_int(u64::from(node.first_child), false).into(),
                    i32.const_int(u64::from(node.child_count), false).into(),
                    i8.const_int(node.kind as u64, false).into(),
                    i8.const_int(u64::from(node.width), false).into(),
                    reserved.const_zero().into(),
                ])
            })
            .collect();
        if nodes.is_empty() {
            pointer.const_null()
        } else {
            let value = node_ty.const_array(&node_values);
            let global = self.module.add_global(value.get_type(), None, name);
            global.set_initializer(&value);
            global.set_constant(true);
            global.set_linkage(Linkage::Internal);
            global.as_pointer_value()
        }
    }

    pub(super) fn gc_layout_nodes_for_ty(&mut self, ty: Ty<'gcx>) -> Vec<GcLayoutNode> {
        self.gc_value_layout_nodes(ty, false)
    }

    /// Copy plans share physical offsets/tags with tracing, but visit only
    /// inline erased headers; references and class objects remain shared.
    pub(super) fn gc_copy_layout_nodes_for_ty(&mut self, ty: Ty<'gcx>) -> Vec<GcLayoutNode> {
        self.gc_value_layout_nodes(ty, true)
    }

    fn gc_value_layout_nodes(&mut self, ty: Ty<'gcx>, for_copy: bool) -> Vec<GcLayoutNode> {
        let ty = crate::sema::tycheck::utils::normalize_aliases(self.gcx, self.mono_ty(ty));
        let mut nodes = vec![Self::empty_gc_layout_node()];
        let mut canonical_nodes = FxHashMap::default();
        canonical_nodes.insert(ty, 0);
        if self.fill_gc_layout_node(0, ty, 0, &mut nodes, &mut canonical_nodes, for_copy) {
            crate::codegen::gc_stack_maps::compact_gc_layout(&mut nodes);
            nodes
        } else {
            Vec::new()
        }
    }

    fn empty_gc_layout_node() -> GcLayoutNode {
        GcLayoutNode {
            offset: 0,
            stride: 0,
            first_child: 0,
            child_count: 0,
            kind: GcLayoutKind::Aggregate,
            width: 0,
        }
    }

    fn reserve_gc_layout_nodes(nodes: &mut Vec<GcLayoutNode>, count: usize) -> usize {
        let first = nodes.len();
        nodes.extend((0..count).map(|_| Self::empty_gc_layout_node()));
        first
    }

    fn canonical_gc_layout_node(
        &mut self,
        ty: Ty<'gcx>,
        nodes: &mut Vec<GcLayoutNode>,
        canonical_nodes: &mut FxHashMap<Ty<'gcx>, usize>,
        for_copy: bool,
    ) -> (usize, bool) {
        let ty = crate::sema::tycheck::utils::normalize_aliases(self.gcx, self.mono_ty(ty));
        if let Some(index) = canonical_nodes.get(&ty).copied() {
            // Existing entries may still be under construction. Linking them
            // is intentional: Reference edges are what make the layout an
            // indexed graph rather than an infinitely expanded tree.
            return (index, true);
        }
        let index = Self::reserve_gc_layout_nodes(nodes, 1);
        canonical_nodes.insert(ty, index);
        let scans = self.fill_gc_layout_node(index, ty, 0, nodes, canonical_nodes, for_copy);
        (index, scans)
    }

    fn fill_gc_layout_node(
        &mut self,
        index: usize,
        ty: Ty<'gcx>,
        offset: u64,
        nodes: &mut Vec<GcLayoutNode>,
        canonical_nodes: &mut FxHashMap<Ty<'gcx>, usize>,
        for_copy: bool,
    ) -> bool {
        let ty = crate::sema::tycheck::utils::normalize_aliases(self.gcx, self.mono_ty(ty));
        // Current classes are nominal structs with class_info. Their value
        // storage holds an object handle, never inline copies of their fields.
        if self.gcx.is_class_type(ty) {
            if for_copy {
                return false;
            }
            nodes[index] = GcLayoutNode {
                offset,
                stride: 0,
                first_child: 0,
                child_count: 0,
                kind: GcLayoutKind::Pointer,
                width: 0,
            };
            return true;
        }
        match ty.kind() {
            TyKind::Pointer(..) | TyKind::String if for_copy => false,
            TyKind::Reference(..) if for_copy => false,
            TyKind::Pointer(..) | TyKind::String | TyKind::BoxedExistential { .. } => {
                nodes[index] = GcLayoutNode {
                    offset,
                    stride: 0,
                    first_child: 0,
                    child_count: 0,
                    kind: if matches!(ty.kind(), TyKind::Pointer(..)) {
                        GcLayoutKind::RawPointer
                    } else {
                        GcLayoutKind::Pointer
                    },
                    width: 0,
                };
                true
            }
            TyKind::Reference(inner) => {
                let (child, child_scans) =
                    self.canonical_gc_layout_node(inner, nodes, canonical_nodes, for_copy);
                nodes[index] = GcLayoutNode {
                    offset,
                    stride: 0,
                    first_child: u32::try_from(child).expect("GC layout node index fits u32"),
                    child_count: u32::from(child_scans),
                    kind: GcLayoutKind::Reference,
                    width: 0,
                };
                true
            }
            TyKind::Adt(def, adt_args) => match def.kind {
                crate::sema::models::AdtKind::Struct => {
                    let definition = self.gcx.get_struct_definition(def.id);
                    let layout = struct_field_layout(
                        self.context,
                        self.gcx,
                        &self.target_data,
                        def.id,
                        adt_args,
                        self.current_subst,
                        definition.repr,
                    );
                    let Some(lowered) = self.lower_ty(ty).map(|ty| ty.into_struct_type()) else {
                        return false;
                    };
                    let first = Self::reserve_gc_layout_nodes(nodes, definition.fields.len());
                    let mut scans = false;
                    for (field_index, field) in definition.fields.iter().enumerate() {
                        let Some(field_offset) = self
                            .target_data
                            .offset_of_element(&lowered, layout.logical_to_physical[field_index])
                        else {
                            continue;
                        };
                        let field_ty = instantiate_ty_with_args(self.gcx, field.ty, adt_args);
                        scans |= self.fill_gc_layout_node(
                            first + field_index,
                            field_ty,
                            field_offset,
                            nodes,
                            canonical_nodes,
                            for_copy,
                        );
                    }
                    nodes[index] = GcLayoutNode {
                        offset,
                        stride: 0,
                        first_child: u32::try_from(first).expect("GC layout node index fits u32"),
                        child_count: u32::try_from(definition.fields.len())
                            .expect("GC child count fits u32"),
                        kind: GcLayoutKind::Aggregate,
                        width: 0,
                    };
                    scans
                }
                crate::sema::models::AdtKind::Enum => {
                    let definition = self.gcx.get_enum_definition(def.id);
                    let layout = self.enum_layout_for(def.id, adt_args);
                    if let Some(npo) = layout.npo {
                        let variant = &definition.variants[npo.payload_variant];
                        let (crate::sema::models::EnumVariantKind::Tuple(fields)
                        | crate::sema::models::EnumVariantKind::Struct(fields)) = variant.kind
                        else {
                            return false;
                        };
                        let Some(field) = fields.first() else {
                            return false;
                        };
                        let field_ty = instantiate_ty_with_args(self.gcx, field.ty, adt_args);
                        return self.fill_gc_layout_node(
                            index,
                            field_ty,
                            offset,
                            nodes,
                            canonical_nodes,
                            for_copy,
                        );
                    }

                    let first = Self::reserve_gc_layout_nodes(nodes, definition.variants.len());
                    let mut scans = false;
                    for (variant_index, variant) in definition.variants.iter().enumerate() {
                        let fields = match variant.kind {
                            crate::sema::models::EnumVariantKind::Unit => &[][..],
                            crate::sema::models::EnumVariantKind::Tuple(fields)
                            | crate::sema::models::EnumVariantKind::Struct(fields) => fields,
                        };
                        let variant_first = Self::reserve_gc_layout_nodes(nodes, fields.len());
                        let variant_ty = enum_variant_struct_ty(
                            self.context,
                            self.gcx,
                            &self.target_data,
                            fields,
                            adt_args,
                            self.current_subst,
                        );
                        let mut variant_scans = false;
                        for (field_index, field) in fields.iter().enumerate() {
                            let Some(field_offset) = self
                                .target_data
                                .offset_of_element(&variant_ty, field_index as u32)
                            else {
                                continue;
                            };
                            let field_ty = instantiate_ty_with_args(self.gcx, field.ty, adt_args);
                            variant_scans |= self.fill_gc_layout_node(
                                variant_first + field_index,
                                field_ty,
                                field_offset,
                                nodes,
                                canonical_nodes,
                                for_copy,
                            );
                        }
                        nodes[first + variant_index] = GcLayoutNode {
                            offset: layout.payload_offset,
                            stride: 0,
                            first_child: u32::try_from(variant_first)
                                .expect("GC layout node index fits u32"),
                            child_count: u32::try_from(fields.len())
                                .expect("GC child count fits u32"),
                            kind: GcLayoutKind::Aggregate,
                            width: 0,
                        };
                        scans |= variant_scans;
                    }
                    nodes[index] = GcLayoutNode {
                        offset,
                        stride: 0,
                        first_child: u32::try_from(first).expect("GC layout node index fits u32"),
                        child_count: u32::try_from(definition.variants.len())
                            .expect("GC variant count fits u32"),
                        kind: GcLayoutKind::Tagged,
                        width: u8::try_from(layout.discr_size)
                            .expect("enum discriminator width fits u8"),
                    };
                    scans
                }
            },
            TyKind::Tuple(items) => {
                let Some(lowered) = self.lower_ty(ty).map(|ty| ty.into_struct_type()) else {
                    return false;
                };
                let first = Self::reserve_gc_layout_nodes(nodes, items.len());
                let mut scans = false;
                for (item_index, item) in items.iter().enumerate() {
                    let Some(field_offset) = self
                        .target_data
                        .offset_of_element(&lowered, item_index as u32)
                    else {
                        continue;
                    };
                    scans |= self.fill_gc_layout_node(
                        first + item_index,
                        *item,
                        field_offset,
                        nodes,
                        canonical_nodes,
                        for_copy,
                    );
                }
                nodes[index] = GcLayoutNode {
                    offset,
                    stride: 0,
                    first_child: u32::try_from(first).expect("GC layout node index fits u32"),
                    child_count: u32::try_from(items.len()).expect("GC child count fits u32"),
                    kind: GcLayoutKind::Aggregate,
                    width: 0,
                };
                scans
            }
            TyKind::Array { element, len } => {
                let count = concrete_array_len_for_gc_offsets(len.kind);
                let first = Self::reserve_gc_layout_nodes(nodes, 1);
                let scans =
                    self.fill_gc_layout_node(first, element, 0, nodes, canonical_nodes, for_copy);
                // In a mixed aggregate, sibling pointer fields keep the whole
                // graph alive. Leave pointer-free arrays empty rather than
                // making every collection interpret one no-op per element.
                if !scans || count == 0 {
                    return false;
                }
                let Some(element_ty) = self.lower_ty(element) else {
                    return false;
                };
                nodes[index] = GcLayoutNode {
                    offset,
                    stride: self.target_data.get_store_size(&element_ty),
                    first_child: u32::try_from(first).expect("GC layout node index fits u32"),
                    child_count: u32::try_from(count).expect("array length fits u32"),
                    kind: GcLayoutKind::Repeat,
                    width: 0,
                };
                true
            }
            TyKind::Closure {
                closure_def_id,
                captured_generics,
                ..
            } => {
                let Some(captures) = self.gcx.get_closure_captures(closure_def_id) else {
                    return false;
                };
                let Some(lowered) = self.lower_ty(ty).map(|ty| ty.into_struct_type()) else {
                    return false;
                };
                let first = Self::reserve_gc_layout_nodes(nodes, captures.captures.len());
                let mut scans = false;
                for (capture_index, capture) in captures.captures.iter().enumerate() {
                    let base_ty = instantiate_ty_with_args(
                        self.gcx,
                        instantiate_ty_with_args(self.gcx, capture.ty, captured_generics),
                        self.current_subst,
                    );
                    let capture_ty =
                        if let crate::sema::models::CaptureKind::ByRef = capture.capture_kind {
                            Ty::new(TyKind::Reference(base_ty), self.gcx)
                        } else {
                            base_ty
                        };
                    let Some(field_offset) = self
                        .target_data
                        .offset_of_element(&lowered, capture_index as u32)
                    else {
                        continue;
                    };
                    scans |= self.fill_gc_layout_node(
                        first + capture_index,
                        capture_ty,
                        field_offset,
                        nodes,
                        canonical_nodes,
                        for_copy,
                    );
                }
                nodes[index] = GcLayoutNode {
                    offset,
                    stride: 0,
                    first_child: u32::try_from(first).expect("GC layout node index fits u32"),
                    child_count: u32::try_from(captures.captures.len())
                        .expect("GC child count fits u32"),
                    kind: GcLayoutKind::Aggregate,
                    width: 0,
                };
                scans
            }
            TyKind::Parameter(_) | TyKind::Alias { .. } | TyKind::Infer(_) | TyKind::Error => {
                panic!(
                    "ICE: unresolved type while constructing GC layout: {}",
                    ty.format(self.gcx)
                )
            }
            _ => false,
        }
    }
}

fn concrete_array_len_for_gc_offsets(len: ConstKind) -> u64 {
    match len {
        ConstKind::Value(ConstValue::Integer(n)) => u64::try_from(n).unwrap_or_else(|_| {
            panic!("ICE: invalid array length while computing GC root offsets: {n}")
        }),
        ConstKind::Value(value) => {
            panic!("ICE: non-integer array length while computing GC root offsets: {value:?}")
        }
        ConstKind::Param(param) => {
            panic!("ICE: unresolved const parameter while computing GC root offsets: {param:?}")
        }
        ConstKind::Infer(var) => {
            panic!("ICE: unresolved inferred const while computing GC root offsets: {var:?}")
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn managed_references_use_one_word_in_arrays_and_optional_payloads() {
        crate::test_support::analyze_script(
            "struct Refs { values: [&int32; 4] }
enum MaybeRef { case none; case some(&int32) }
func main() {}",
            |package, gcx| {
                let context = Context::create();
                let mut emitter = Emitter::new(
                    &context,
                    context.create_module("reference-abi"),
                    context.create_builder(),
                    gcx,
                )
                .unwrap_or_else(|_| panic!("reference ABI emitter"));

                let pointer_size = emitter.target_data.get_pointer_byte_size(None) as u64;
                let expected = pointer_size;
                {
                    let reference = Ty::new(TyKind::Reference(gcx.types.int32), gcx);
                    let physical = emitter.lower_ty(reference).unwrap();
                    assert_eq!(emitter.target_data.get_store_size(&physical), expected);
                    assert!(physical.is_pointer_type());
                    let inputs = gcx.store.interners.intern_ty_list(vec![reference]);
                    let abi = emitter.compute_fn_pointer_abi(inputs.as_slice(), reference);
                    let function = emitter.lower_fn_abi(&abi);
                    assert!(function.get_param_types()[0].is_pointer_type());
                    assert!(function.get_return_type().unwrap().is_pointer_type());
                }
                let references = gcx.get_type(package.root.declarations[0].id);
                let physical = emitter.lower_ty(references).unwrap();
                assert_eq!(emitter.target_data.get_store_size(&physical), 4 * expected);
                let nodes = emitter.gc_layout_nodes_for_ty(references);
                let repeat = nodes
                    .iter()
                    .find(|node| node.kind == GcLayoutKind::Repeat)
                    .unwrap();
                assert_eq!(
                    repeat.stride, expected,
                    "tracing must match the selected physical ABI"
                );
                let optional = gcx.get_type(package.root.declarations[1].id);
                assert_eq!(
                    emitter
                        .target_data
                        .get_store_size(&emitter.lower_ty(optional).unwrap()),
                    expected
                );
            },
        );
    }

    #[test]
    fn a_zero_sized_managed_place_keeps_its_existing_storage_address() {
        crate::test_support::analyze_script("func main() {}", |_, gcx| {
            let context = Context::create();
            let mut emitter = Emitter::new(
                &context,
                context.create_module("zero-sized-reference"),
                context.create_builder(),
                gcx,
            )
            .unwrap_or_else(|_| panic!("zero-sized reference emitter"));

            let reference = Ty::new(TyKind::Reference(gcx.types.void), gcx);
            let mut body = mir::test_support::minimal_body(gcx);
            let storage = mir::test_support::push_temp(&mut body, reference);
            let pointer = context.ptr_type(AddressSpace::default());
            let function = emitter.module.add_function(
                "forward_zero_sized",
                pointer.fn_type(&[pointer.into()], false),
                None,
            );
            emitter
                .builder
                .position_at_end(context.append_basic_block(function, "entry"));
            let slot = emitter
                .builder
                .build_alloca(pointer, "managed_storage")
                .unwrap();
            emitter
                .builder
                .build_store(slot, function.get_first_param().unwrap())
                .unwrap();
            let mut locals = [LocalStorage::Value(None), LocalStorage::Stack(slot)];
            let mut place = Place::from_local(storage);
            place.projection.push(mir::PlaceElem::Deref);
            let value = emitter
                .lower_rvalue(&body, &mut locals, reference, &mir::Rvalue::Ref { place })
                .unwrap_or_else(|_| panic!("zero-sized reference lowering"))
                .unwrap();
            emitter.builder.build_return(Some(&value)).unwrap();
            emitter.module.verify().unwrap();
            emitter
                .module
                .run_passes(
                    "default<O3>",
                    &emitter.target_machine,
                    PassBuilderOptions::create(),
                )
                .unwrap();
            let engine = emitter
                .module
                .create_jit_execution_engine(inkwell::OptimizationLevel::Aggressive)
                .unwrap();
            type Forward = unsafe extern "C" fn(*mut u8) -> *mut u8;
            let forward = unsafe {
                engine
                    .get_function::<Forward>("forward_zero_sized")
                    .unwrap()
            };
            let mut byte = Box::new(0_u8);
            let address = &mut *byte as *mut u8;
            assert_eq!(
                unsafe { forward.call(address) },
                address,
                "a reference must retain the selected storage address even when its value has size zero"
            );
        });
    }

    #[test]
    fn scalar_storage_is_rootless_but_references_have_typed_edges() {
        crate::test_support::analyze_script("func main() {}", |_, gcx| {
            let context = Context::create();
            let mut emitter = Emitter::new(
                &context,
                context.create_module("gc-scalars"),
                context.create_builder(),
                gcx,
            )
            .unwrap_or_else(|_| panic!("GC layout emitter"));
            assert!(emitter.gc_layout_nodes_for_ty(gcx.types.int32).is_empty());
            let reference = Ty::new(TyKind::Reference(gcx.types.int32), gcx);
            let nodes = emitter.gc_layout_nodes_for_ty(reference);
            assert_eq!(nodes[0].kind, GcLayoutKind::Reference);
            assert_eq!(nodes[0].child_count, 0);
        });
    }

    #[test]
    fn recursive_reference_layouts_form_finite_graphs() {
        crate::test_support::analyze_script(
            "struct Node { next: &Node }\nfunc main() {}",
            |package, gcx| {
                let context = Context::create();
                let mut emitter = Emitter::new(
                    &context,
                    context.create_module("gc-recursive"),
                    context.create_builder(),
                    gcx,
                )
                .unwrap_or_else(|_| panic!("GC layout emitter"));
                let nodes =
                    emitter.gc_layout_nodes_for_ty(gcx.get_type(package.root.declarations[0].id));
                assert_eq!(nodes.len(), 1);
                assert_eq!(nodes[0].kind, GcLayoutKind::Reference);
                assert_eq!(nodes[0].first_child, 0);
                assert_eq!(nodes[0].child_count, 1);
            },
        );
    }

    #[test]
    fn array_and_active_enum_layouts_keep_their_physical_shape() {
        crate::test_support::analyze_script(
            "struct Batch { values: [string; 3] }\nenum Choice { case scalar(int32); case text(string) }\nfunc main() {}",
            |package, gcx| {
                let context = Context::create();
                let mut emitter = Emitter::new(
                    &context,
                    context.create_module("gc-aggregates"),
                    context.create_builder(),
                    gcx,
                )
                .unwrap_or_else(|_| panic!("GC layout emitter"));
                let batch =
                    emitter.gc_layout_nodes_for_ty(gcx.get_type(package.root.declarations[0].id));
                let repeat = batch
                    .iter()
                    .find(|node| node.kind == GcLayoutKind::Repeat)
                    .expect("array repeat layout");
                assert_eq!(repeat.child_count, 3);
                assert!(repeat.stride > 0);
                let choice =
                    emitter.gc_layout_nodes_for_ty(gcx.get_type(package.root.declarations[1].id));
                assert_eq!(choice[0].kind, GcLayoutKind::Tagged);
                assert_eq!(choice[0].child_count, 2);
                assert!(choice.iter().any(|node| node.kind == GcLayoutKind::Pointer));
            },
        );
    }

    #[test]
    fn pointer_free_arrays_do_not_add_repeated_gc_work_to_mixed_values() {
        crate::test_support::analyze_script(
            "struct Mixed { scratch: [[uint8; 256]; 32], owner: string }\nfunc main() {}",
            |package, gcx| {
                let context = Context::create();
                let mut emitter = Emitter::new(
                    &context,
                    context.create_module("noscan-arrays"),
                    context.create_builder(),
                    gcx,
                )
                .unwrap_or_else(|_| panic!("GC layout emitter"));
                let ty = gcx.get_type(package.root.declarations[0].id);
                let nodes = emitter.gc_layout_nodes_for_ty(ty);
                assert_eq!(nodes.len(), 1, "only the owner's pointer needs tracing");
                assert_eq!(nodes[0].kind, GcLayoutKind::Pointer);
                let TyKind::Adt(def, args) = ty.kind() else {
                    panic!("mixed struct type")
                };
                let definition = gcx.get_struct_definition(def.id);
                let layout = struct_field_layout(
                    &context,
                    gcx,
                    &emitter.target_data,
                    def.id,
                    args,
                    emitter.current_subst,
                    definition.repr,
                );
                let lowered = emitter.lower_ty(ty).unwrap().into_struct_type();
                let owner = emitter
                    .target_data
                    .offset_of_element(&lowered, layout.logical_to_physical[1])
                    .unwrap();
                assert_eq!(
                    nodes[0].offset, owner,
                    "compaction preserves physical offsets"
                );
            },
        );
    }

    #[test]
    fn single_field_pointer_wrappers_emit_a_direct_edge() {
        crate::test_support::analyze_script(
            "struct Wrapper { value: string }\nfunc main() {}",
            |package, gcx| {
                let context = Context::create();
                let mut emitter = Emitter::new(
                    &context,
                    context.create_module("compact-layout"),
                    context.create_builder(),
                    gcx,
                )
                .unwrap_or_else(|_| panic!("compact layout emitter"));
                let ty = gcx.get_type(package.root.declarations[0].id);
                let nodes = emitter.gc_layout_nodes_for_ty(ty);
                assert_eq!(nodes.len(), 1, "wrapper adds no heap-walk interpreter step");
                assert_eq!(nodes[0].kind, GcLayoutKind::Pointer);
                assert_eq!(nodes[0].offset, 0);
            },
        );
    }

    #[test]
    fn class_values_trace_the_handle_instead_of_inline_fields() {
        crate::test_support::analyze_script(
            "struct Object { value: string }\nfunc main() {}",
            |package, gcx| {
                let id = package.root.declarations[0].id;
                let mut definition = gcx.get_struct_definition(id).clone();
                definition.class_info = Some(crate::sema::models::ClassInfo {
                    initializers: &[],
                    base: None,
                    methods: &[],
                    payload: None,
                    is_final: false,
                });
                gcx.cache_struct_definition(id, definition);
                let context = Context::create();
                let mut emitter = Emitter::new(
                    &context,
                    context.create_module("gc-class"),
                    context.create_builder(),
                    gcx,
                )
                .unwrap_or_else(|_| panic!("GC layout emitter"));
                let nodes = emitter.gc_layout_nodes_for_ty(gcx.get_type(id));
                assert_eq!(nodes.len(), 1);
                assert_eq!(nodes[0].kind, GcLayoutKind::Pointer);
                assert_eq!(nodes[0].offset, 0);
            },
        );
    }
}
