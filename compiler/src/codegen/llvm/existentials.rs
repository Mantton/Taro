use super::{Emitter, enum_layout, enum_variant_tuple_ty};
use crate::{
    error::CompileResult,
    hir,
    sema::{
        models::{GenericArguments, InterfaceReference, Ty, TyKind},
    },
};
use inkwell::{
    AddressSpace, IntPredicate,
    types::BasicTypeEnum,
    values::{BasicMetadataValueEnum, BasicValue, BasicValueEnum, PointerValue, StructValue},
};

impl<'llvm, 'gcx> Emitter<'llvm, 'gcx> {
    pub(super) fn lower_boxed_existential(
        &mut self,
        from_ty: Ty<'gcx>,
        to_ty: Ty<'gcx>,
        value: BasicValueEnum<'llvm>,
    ) -> CompileResult<BasicValueEnum<'llvm>> {
        let TyKind::BoxedExistential { interfaces } = to_ty.kind() else {
            return Ok(value);
        };

        if from_ty == to_ty {
            return Ok(value);
        }

        if matches!(from_ty.kind(), TyKind::BoxedExistential { .. }) {
            return self.lower_existential_upcast(from_ty, to_ty, value);
        }

        let data_ptr = self.box_value(from_ty, value)?;
        let metadata_ptr = self.type_metadata_ptr(from_ty);
        let mut table_ptrs = Vec::with_capacity(interfaces.len());
        for iface in interfaces.iter().cloned() {
            let ptr = self.witness_table_ptr(from_ty, iface);
            table_ptrs.push(ptr);
        }

        Ok(self.build_existential_value(to_ty, data_ptr, metadata_ptr, &table_ptrs))
    }

    pub(super) fn lower_existential_upcast(
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
        let metadata_ptr = self
            .builder
            .build_extract_value(src, 1, "exist_meta")
            .unwrap()
            .into_pointer_value();

        let mut table_ptrs = Vec::with_capacity(to_ifaces.len());
        for target in to_ifaces.iter().cloned() {
            if let Some(index) = self.interface_index(from_ifaces, target.id) {
                let ptr = self
                    .builder
                    .build_extract_value(src, (index + 2) as u32, "exist_table")
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
                    .build_extract_value(src, (root_index + 2) as u32, "exist_root_table")
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

        Ok(self.build_existential_value(to_ty, data_ptr, metadata_ptr, &table_ptrs))
    }

    fn interface_ref_matches_for_assert(
        &self,
        expected: InterfaceReference<'gcx>,
        actual: InterfaceReference<'gcx>,
    ) -> bool {
        if expected.id != actual.id {
            return false;
        }

        let expected_args = if !expected.arguments.is_empty() {
            &expected.arguments[1..]
        } else {
            &expected.arguments
        };
        let actual_args = if !actual.arguments.is_empty() {
            &actual.arguments[1..]
        } else {
            &actual.arguments
        };

        expected_args == actual_args && expected.bindings == actual.bindings
    }

    fn find_existential_projection_route(
        &self,
        from_ifaces: &'gcx [InterfaceReference<'gcx>],
        target: InterfaceReference<'gcx>,
    ) -> Option<(usize, Vec<(hir::DefinitionID, usize)>)> {
        for (index, source) in from_ifaces.iter().enumerate() {
            if self.interface_ref_matches_for_assert(target, *source) {
                return Some((index, Vec::new()));
            }

            if !self.interface_has_superface(source.id, target.id) {
                continue;
            }

            let Some(chain) = self.superface_chain_indices(source.id, target.id) else {
                continue;
            };

            let mut current = *source;
            let mut valid = true;
            for (iface_id, super_index) in chain.iter().copied() {
                if current.id != iface_id {
                    valid = false;
                    break;
                }

                let supers = self.interface_superfaces(current);
                let Some(next) = supers.get(super_index).copied() else {
                    valid = false;
                    break;
                };
                current = next;
            }

            if valid && self.interface_ref_matches_for_assert(target, current) {
                return Some((index, chain));
            }
        }

        None
    }

    fn follow_existential_superface_chain(
        &self,
        mut current_ptr: PointerValue<'llvm>,
        chain: &[(hir::DefinitionID, usize)],
    ) -> PointerValue<'llvm> {
        for (current_iface, super_index) in chain.iter().copied() {
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
    }

    fn pointer_is_non_null(
        &self,
        ptr: PointerValue<'llvm>,
        name: &str,
    ) -> inkwell::values::IntValue<'llvm> {
        let raw = self
            .builder
            .build_ptr_to_int(ptr, self.usize_ty, &format!("{name}_int"))
            .unwrap();
        self.builder
            .build_int_compare(IntPredicate::NE, raw, self.usize_ty.const_zero(), name)
            .unwrap()
    }

    fn pointer_eq(
        &self,
        lhs: PointerValue<'llvm>,
        rhs: PointerValue<'llvm>,
        name: &str,
    ) -> inkwell::values::IntValue<'llvm> {
        let lhs_raw = self
            .builder
            .build_ptr_to_int(lhs, self.usize_ty, &format!("{name}_lhs"))
            .unwrap();
        let rhs_raw = self
            .builder
            .build_ptr_to_int(rhs, self.usize_ty, &format!("{name}_rhs"))
            .unwrap();
        self.builder
            .build_int_compare(IntPredicate::EQ, lhs_raw, rhs_raw, name)
            .unwrap()
    }

    fn lookup_witness_table_from_metadata(
        &mut self,
        metadata_ptr: PointerValue<'llvm>,
        target: InterfaceReference<'gcx>,
    ) -> PointerValue<'llvm> {
        let callee = self.get_rt_existential_lookup_conformance();
        let iface_desc = self.interface_descriptor_ptr(target);
        let call = self
            .builder
            .build_call(
                callee,
                &[
                    BasicMetadataValueEnum::from(metadata_ptr),
                    BasicMetadataValueEnum::from(iface_desc),
                ],
                "exist_lookup",
            )
            .unwrap();
        call.try_as_basic_value()
            .basic()
            .expect("existential conformance lookup returned void")
            .into_pointer_value()
    }

    fn project_existential_value_to_target(
        &mut self,
        from_ifaces: &'gcx [InterfaceReference<'gcx>],
        target_ty: Ty<'gcx>,
        target_ifaces: &'gcx [InterfaceReference<'gcx>],
        src: StructValue<'llvm>,
    ) -> CompileResult<(BasicValueEnum<'llvm>, inkwell::values::IntValue<'llvm>)> {
        let data_ptr = self
            .builder
            .build_extract_value(src, 0, "exist_data")
            .unwrap()
            .into_pointer_value();
        let metadata_ptr = self
            .builder
            .build_extract_value(src, 1, "exist_meta")
            .unwrap()
            .into_pointer_value();

        let mut table_ptrs = Vec::with_capacity(target_ifaces.len());
        let mut success = self.context.bool_type().const_all_ones();
        for target in target_ifaces.iter().cloned() {
            let projected_ptr = if let Some((root_index, chain)) =
                self.find_existential_projection_route(from_ifaces, target)
            {
                let root_ptr = self
                    .builder
                    .build_extract_value(src, (root_index + 2) as u32, "exist_root_table")
                    .unwrap()
                    .into_pointer_value();
                self.follow_existential_superface_chain(root_ptr, &chain)
            } else {
                let from_meta = self.lookup_witness_table_from_metadata(metadata_ptr, target);
                let found = self.pointer_is_non_null(from_meta, "exist_lookup_found");
                success = self
                    .builder
                    .build_and(success, found, "exist_cast_success")
                    .unwrap();
                from_meta
            };
            table_ptrs.push(projected_ptr);
        }

        Ok((
            self.build_existential_value(target_ty, data_ptr, metadata_ptr, &table_ptrs),
            success,
        ))
    }

    pub(super) fn lower_existential_type_is(
        &mut self,
        from_ty: Ty<'gcx>,
        target_ty: Ty<'gcx>,
        value: BasicValueEnum<'llvm>,
    ) -> CompileResult<BasicValueEnum<'llvm>> {
        let (from_ty, value) = self.normalize_cast_source_existential_ref(from_ty, value)?;
        let success = match (from_ty.kind(), target_ty.kind()) {
            (
                TyKind::BoxedExistential {
                    interfaces: from_ifaces,
                },
                TyKind::BoxedExistential {
                    interfaces: target_ifaces,
                },
            ) => {
                let src = value.into_struct_value();
                let (_, success) = self.project_existential_value_to_target(
                    from_ifaces,
                    target_ty,
                    target_ifaces,
                    src,
                )?;
                success
            }
            (TyKind::BoxedExistential { .. }, _) => {
                let src = value.into_struct_value();
                let from_meta = self
                    .builder
                    .build_extract_value(src, 1, "exist_meta")
                    .unwrap()
                    .into_pointer_value();
                let to_meta = self.type_metadata_ptr(target_ty);
                self.pointer_eq(from_meta, to_meta, "exist_type_is_concrete")
            }
            (
                _,
                TyKind::BoxedExistential {
                    interfaces: target_ifaces,
                },
            ) => {
                let mut all = true;
                for target in target_ifaces.iter().cloned() {
                    let iface = self.interface_args_with_self(from_ty, target);
                    if self.conformance_witness(iface).is_none() {
                        all = false;
                        break;
                    }
                }
                self.context
                    .bool_type()
                    .const_int(if all { 1 } else { 0 }, false)
            }
            _ => self
                .context
                .bool_type()
                .const_int(if from_ty == target_ty { 1 } else { 0 }, false),
        };
        Ok(success.as_basic_value_enum())
    }

    fn normalize_cast_source_existential_ref(
        &mut self,
        from_ty: Ty<'gcx>,
        value: BasicValueEnum<'llvm>,
    ) -> CompileResult<(Ty<'gcx>, BasicValueEnum<'llvm>)> {
        let TyKind::Reference(inner, _) = from_ty.kind() else {
            return Ok((from_ty, value));
        };
        let TyKind::BoxedExistential { .. } = inner.kind() else {
            return Ok((from_ty, value));
        };

        let BasicValueEnum::PointerValue(ptr) = value else {
            // Some MIR paths already evaluate the operand to the underlying existential
            // value even though the static source type here is `&any ...`.
            return Ok((inner, value));
        };
        let Some(inner_llvm_ty) = self.lower_ty(inner) else {
            return Ok((from_ty, value));
        };
        let loaded = self
            .builder
            .build_load(inner_llvm_ty, ptr, "exist_cast_ref_load")
            .unwrap();
        Ok((inner, loaded))
    }

    fn optional_variant_indices(
        &self,
        optional_ty: Ty<'gcx>,
    ) -> Option<(
        usize,
        usize,
        crate::sema::models::AdtDef,
        GenericArguments<'gcx>,
    )> {
        let TyKind::Adt(def, args) = optional_ty.kind() else {
            return None;
        };
        if def.kind != crate::sema::models::AdtKind::Enum {
            return None;
        }

        let optional_id = self.gcx.std_item_def(hir::StdItem::Optional)?;
        if def.id != optional_id {
            return None;
        }

        let enum_def = self.gcx.get_enum_definition(def.id);
        let some_index = enum_def
            .variants
            .iter()
            .position(|variant| self.gcx.symbol_eq(variant.name, "some"))?;
        let none_index = enum_def
            .variants
            .iter()
            .position(|variant| self.gcx.symbol_eq(variant.name, "none"))?;

        Some((some_index, none_index, def, args))
    }

    fn build_optional_variant_value(
        &mut self,
        optional_ty: Ty<'gcx>,
        variant_index: usize,
        payload: Option<BasicValueEnum<'llvm>>,
    ) -> CompileResult<BasicValueEnum<'llvm>> {
        let Some(BasicTypeEnum::StructType(enum_struct_ty)) = self.lower_ty(optional_ty) else {
            panic!(
                "ICE: existential try cast result must lower to Optional enum, found '{}'",
                optional_ty.format(self.gcx)
            );
        };

        let Some((_, _, def, adt_args)) = self.optional_variant_indices(optional_ty) else {
            panic!(
                "ICE: existential try cast result must be Optional[T], found '{}'",
                optional_ty.format(self.gcx)
            );
        };

        let enum_ptr = self
            .builder
            .build_alloca(enum_struct_ty, "opt_tmp")
            .unwrap();
        let _ = self
            .builder
            .build_store(enum_ptr, enum_struct_ty.const_zero())
            .unwrap();

        let discr_ptr = self
            .builder
            .build_struct_gep(enum_struct_ty, enum_ptr, 0, "opt_discr_ptr")
            .unwrap();
        let discr_val = self.usize_ty.const_int(variant_index as u64, false);
        let _ = self.builder.build_store(discr_ptr, discr_val).unwrap();

        if let Some(payload_value) = payload {
            let layout = enum_layout(
                self.context,
                self.gcx,
                &self.target_data,
                def.id,
                adt_args,
                self.current_subst,
            );
            if let Some(payload_field_index) = layout.payload_field_index {
                let payload_storage_ptr = self
                    .builder
                    .build_struct_gep(
                        enum_struct_ty,
                        enum_ptr,
                        payload_field_index,
                        "opt_payload_storage",
                    )
                    .unwrap();

                let variant_tuple_ty = enum_variant_tuple_ty(
                    self.gcx,
                    def.id,
                    crate::thir::VariantIndex::from_usize(variant_index),
                    adt_args,
                );
                if let Some(BasicTypeEnum::StructType(variant_struct_ty)) =
                    self.lower_ty(variant_tuple_ty)
                {
                    let variant_ptr = self
                        .builder
                        .build_bit_cast(
                            payload_storage_ptr,
                            self.context.ptr_type(AddressSpace::default()),
                            "opt_variant_ptr",
                        )
                        .unwrap()
                        .into_pointer_value();

                    if variant_struct_ty.count_fields() > 0 {
                        let field_ptr = self
                            .builder
                            .build_struct_gep(
                                variant_struct_ty,
                                variant_ptr,
                                0,
                                "opt_payload_field_ptr",
                            )
                            .unwrap();
                        let _ = self.builder.build_store(field_ptr, payload_value).unwrap();
                    }
                }
            }
        }

        let loaded = self
            .builder
            .build_load(enum_struct_ty, enum_ptr, "opt_load")
            .unwrap();
        Ok(loaded.as_basic_value_enum())
    }

    pub(super) fn lower_existential_try_cast(
        &mut self,
        from_ty: Ty<'gcx>,
        target_ty: Ty<'gcx>,
        result_ty: Ty<'gcx>,
        value: BasicValueEnum<'llvm>,
    ) -> CompileResult<BasicValueEnum<'llvm>> {
        let (from_ty, value) = self.normalize_cast_source_existential_ref(from_ty, value)?;
        let Some((some_index, none_index, _, _)) = self.optional_variant_indices(result_ty) else {
            panic!(
                "ICE: existential try cast result must be Optional[T], found '{}'",
                result_ty.format(self.gcx)
            );
        };

        match (from_ty.kind(), target_ty.kind()) {
            (
                TyKind::BoxedExistential {
                    interfaces: from_ifaces,
                },
                TyKind::BoxedExistential {
                    interfaces: target_ifaces,
                },
            ) => {
                let src = value.into_struct_value();
                let (projected, success) = self.project_existential_value_to_target(
                    from_ifaces,
                    target_ty,
                    target_ifaces,
                    src,
                )?;
                let some_value =
                    self.build_optional_variant_value(result_ty, some_index, Some(projected))?;
                let none_value = self.build_optional_variant_value(result_ty, none_index, None)?;
                let selected = self
                    .builder
                    .build_select(success, some_value, none_value, "exist_try_cast_select")
                    .unwrap();
                Ok(selected)
            }
            (
                _,
                TyKind::BoxedExistential {
                    interfaces: target_ifaces,
                },
            ) => {
                let mut table_ptrs = Vec::with_capacity(target_ifaces.len());
                for target in target_ifaces.iter().cloned() {
                    let iface = self.interface_args_with_self(from_ty, target);
                    if self.conformance_witness(iface).is_none() {
                        return self.build_optional_variant_value(result_ty, none_index, None);
                    }
                    let ptr = self.witness_table_ptr(from_ty, target);
                    table_ptrs.push(ptr);
                }

                let data_ptr = self.box_value(from_ty, value)?;
                let metadata_ptr = self.type_metadata_ptr(from_ty);
                let projected =
                    self.build_existential_value(target_ty, data_ptr, metadata_ptr, &table_ptrs);
                self.build_optional_variant_value(result_ty, some_index, Some(projected))
            }
            (TyKind::BoxedExistential { .. }, _) => {
                let src = value.into_struct_value();
                let from_meta = self
                    .builder
                    .build_extract_value(src, 1, "exist_meta")
                    .unwrap()
                    .into_pointer_value();
                let to_meta = self.type_metadata_ptr(target_ty);
                let success = self.pointer_eq(from_meta, to_meta, "exist_try_cast_concrete_eq");

                let Some(BasicTypeEnum::StructType(result_struct_ty)) = self.lower_ty(result_ty)
                else {
                    panic!(
                        "ICE: existential try cast result must lower to Optional enum, found '{}'",
                        result_ty.format(self.gcx)
                    );
                };
                let tmp_ptr = self
                    .builder
                    .build_alloca(result_struct_ty, "exist_try_cast_tmp")
                    .unwrap();
                let parent = self
                    .current_fn
                    .expect("active function for existential try cast");
                let then_bb = self
                    .context
                    .append_basic_block(parent, "exist_try_cast_some");
                let else_bb = self
                    .context
                    .append_basic_block(parent, "exist_try_cast_none");
                let merge_bb = self
                    .context
                    .append_basic_block(parent, "exist_try_cast_merge");

                let _ = self
                    .builder
                    .build_conditional_branch(success, then_bb, else_bb)
                    .unwrap();

                self.builder.position_at_end(then_bb);
                let data_ptr = self
                    .builder
                    .build_extract_value(src, 0, "exist_data")
                    .unwrap()
                    .into_pointer_value();
                let payload_ty = self.lower_ty(target_ty).expect("downcast target type");
                let payload = self
                    .builder
                    .build_load(payload_ty, data_ptr, "exist_downcast_load")
                    .unwrap();
                let some_value =
                    self.build_optional_variant_value(result_ty, some_index, Some(payload))?;
                let _ = self.builder.build_store(tmp_ptr, some_value).unwrap();
                let _ = self.builder.build_unconditional_branch(merge_bb).unwrap();

                self.builder.position_at_end(else_bb);
                let none_value = self.build_optional_variant_value(result_ty, none_index, None)?;
                let _ = self.builder.build_store(tmp_ptr, none_value).unwrap();
                let _ = self.builder.build_unconditional_branch(merge_bb).unwrap();

                self.builder.position_at_end(merge_bb);
                let loaded = self
                    .builder
                    .build_load(result_struct_ty, tmp_ptr, "exist_try_cast_result")
                    .unwrap();
                Ok(loaded.as_basic_value_enum())
            }
            _ => {
                if from_ty == target_ty {
                    self.build_optional_variant_value(result_ty, some_index, Some(value))
                } else {
                    self.build_optional_variant_value(result_ty, none_index, None)
                }
            }
        }
    }
}
