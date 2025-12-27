//! Layout computation for types.
//!
//! This module provides the `Shape` type which captures runtime layout information
//! (size, alignment, pointer offsets) for use in:
//! - Shape-based generic specialization (types with same shape share code)
//! - GC descriptor generation at codegen time
//!
//! The `LayoutComputer` uses the shared `TargetLayout` from `CompilerStore` for
//! accurate, target-specific layout computation.

use crate::{
    compile::context::Gcx,
    hir::DefinitionID,
    sema::models::{AdtKind, FloatTy, IntTy, Ty, TyKind, UIntTy},
};
use inkwell::{
    AddressSpace,
    context::Context,
    targets::TargetData,
    types::{BasicType, BasicTypeEnum},
};

/// A compile-time representation of a type's runtime layout.
///
/// Two types with identical `Shape` values can share monomorphized code
/// (in shape-based generic specialization), with the actual type-specific
/// operations provided via a runtime dictionary.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Shape {
    /// Size in bytes.
    pub size: u64,
    /// Alignment in bytes.
    pub align: u64,
    /// Byte offsets of pointer fields for GC tracing.
    /// Empty for types with no GC-traced pointers.
    pub pointer_offsets: Vec<u64>,
}

impl Shape {
    /// Returns true if this shape contains any GC-traced pointers.
    pub fn has_pointers(&self) -> bool {
        !self.pointer_offsets.is_empty()
    }

    /// Create a shape for a primitive type with no pointers.
    pub fn primitive(size: u64, align: u64) -> Self {
        Shape {
            size,
            align,
            pointer_offsets: Vec::new(),
        }
    }

    /// Create a shape for a pointer type.
    pub fn pointer(pointer_size: u64) -> Self {
        Shape {
            size: pointer_size,
            align: pointer_size,
            pointer_offsets: vec![0],
        }
    }
}

/// Computes layout for types using the shared target information.
///
/// This struct holds references to the compiler context and an LLVM context
/// for precise layout computation that matches the target ABI.
pub struct LayoutComputer<'a, 'gcx> {
    gcx: Gcx<'gcx>,
    context: &'a Context,
}

impl<'a, 'gcx> LayoutComputer<'a, 'gcx> {
    /// Create a new layout computer.
    pub fn new(gcx: Gcx<'gcx>, context: &'a Context) -> Self {
        LayoutComputer { gcx, context }
    }

    /// Compute the shape for a type.
    pub fn compute_shape(&self, ty: Ty<'gcx>) -> Shape {
        let target_layout = &self.gcx.store.target_layout;
        let target_data = target_layout.target_data();

        match ty.kind() {
            // Primitives with no pointers
            TyKind::Bool => Shape::primitive(1, 1),
            TyKind::Rune => Shape::primitive(4, 4), // i32
            TyKind::Int(i) => self.int_shape(i, &target_data),
            TyKind::UInt(u) => self.uint_shape(u, &target_data),
            TyKind::Float(f) => self.float_shape(f),

            // Pointer types - all same shape
            TyKind::Pointer(..) | TyKind::Reference(..) => {
                Shape::pointer(target_layout.pointer_size)
            }
            TyKind::GcPtr => Shape::pointer(target_layout.pointer_size),

            // String is a struct { ptr, len } - pointer at offset 0
            TyKind::String => {
                let ptr_size = target_layout.pointer_size;
                Shape {
                    size: ptr_size * 2,
                    align: ptr_size,
                    pointer_offsets: vec![0],
                }
            }

            // Function pointers
            TyKind::FnPointer { .. } => {
                let ptr_size = target_layout.pointer_size;
                Shape::primitive(ptr_size, ptr_size)
            }

            // Tuples
            TyKind::Tuple(items) => self.compute_tuple_shape(items, &target_data),

            // ADTs (structs and enums)
            TyKind::Adt(def) => match def.kind {
                AdtKind::Struct => self.compute_struct_shape(def.id, &target_data),
                AdtKind::Enum => self.compute_enum_shape(def.id, &target_data),
            },

            // These should not appear during layout computation
            TyKind::Parameter(_) | TyKind::Infer(_) | TyKind::Error => {
                // Return a placeholder shape for error cases
                Shape::primitive(0, 1)
            }
        }
    }

    fn int_shape(&self, ty: IntTy, target_data: &TargetData) -> Shape {
        let (size, align) = match ty {
            IntTy::I8 => (1, 1),
            IntTy::I16 => (2, 2),
            IntTy::I32 => (4, 4),
            IntTy::I64 => (8, 8),
            IntTy::ISize => {
                let size = target_data.get_pointer_byte_size(None) as u64;
                (size, size)
            }
        };
        Shape::primitive(size, align)
    }

    fn uint_shape(&self, ty: UIntTy, target_data: &TargetData) -> Shape {
        let (size, align) = match ty {
            UIntTy::U8 => (1, 1),
            UIntTy::U16 => (2, 2),
            UIntTy::U32 => (4, 4),
            UIntTy::U64 => (8, 8),
            UIntTy::USize => {
                let size = target_data.get_pointer_byte_size(None) as u64;
                (size, size)
            }
        };
        Shape::primitive(size, align)
    }

    fn float_shape(&self, ty: FloatTy) -> Shape {
        match ty {
            FloatTy::F32 => Shape::primitive(4, 4),
            FloatTy::F64 => Shape::primitive(8, 8),
        }
    }

    fn compute_tuple_shape(&self, items: &[Ty<'gcx>], target_data: &TargetData) -> Shape {
        if items.is_empty() {
            return Shape::primitive(0, 1); // Unit type
        }

        // Lower to LLVM struct type to get accurate layout
        let field_tys: Vec<BasicTypeEnum> =
            items.iter().filter_map(|t| self.lower_type(*t)).collect();

        if field_tys.is_empty() {
            return Shape::primitive(0, 1);
        }

        let struct_ty = self.context.struct_type(&field_tys, false);
        let size = target_data.get_store_size(&struct_ty);
        let align = target_data.get_abi_alignment(&struct_ty) as u64;

        // Collect pointer offsets
        let mut pointer_offsets = Vec::new();
        for (idx, item) in items.iter().enumerate() {
            if self.is_pointer_ty(*item) {
                if let Some(off) = target_data.offset_of_element(&struct_ty, idx as u32) {
                    pointer_offsets.push(off);
                }
            }
        }

        Shape {
            size,
            align,
            pointer_offsets,
        }
    }

    fn compute_struct_shape(&self, def_id: DefinitionID, target_data: &TargetData) -> Shape {
        let defn = self.gcx.get_struct_definition(def_id);
        let field_tys: Vec<BasicTypeEnum> = defn
            .fields
            .iter()
            .filter_map(|f| self.lower_type(f.ty))
            .collect();

        if field_tys.is_empty() {
            return Shape::primitive(0, 1);
        }

        let struct_ty = self.context.struct_type(&field_tys, false);
        let size = target_data.get_store_size(&struct_ty);
        let align = target_data.get_abi_alignment(&struct_ty) as u64;

        // Collect pointer offsets
        let mut pointer_offsets = Vec::new();
        for (idx, field) in defn.fields.iter().enumerate() {
            if self.is_pointer_ty(field.ty) {
                if let Some(off) = target_data.offset_of_element(&struct_ty, idx as u32) {
                    pointer_offsets.push(off);
                }
            }
        }

        Shape {
            size,
            align,
            pointer_offsets,
        }
    }

    fn compute_enum_shape(&self, def_id: DefinitionID, target_data: &TargetData) -> Shape {
        let def = self.gcx.get_enum_definition(def_id);
        let discr_ty = self.context.ptr_sized_int_type(target_data, None);
        let discr_size = target_data.get_store_size(&discr_ty);

        // Compute max payload size and alignment across all variants
        let mut payload_size = 0u64;
        let mut payload_align = 1u64;

        for variant in def.variants.iter() {
            let (size, align) = match variant.kind {
                crate::sema::models::EnumVariantKind::Unit => (0u64, 1u64),
                crate::sema::models::EnumVariantKind::Tuple(fields) => {
                    if fields.is_empty() {
                        (0u64, 1u64)
                    } else {
                        let field_tys: Vec<BasicTypeEnum> = fields
                            .iter()
                            .filter_map(|f| self.lower_type(f.ty))
                            .collect();
                        if field_tys.is_empty() {
                            (0u64, 1u64)
                        } else {
                            let struct_ty = self.context.struct_type(&field_tys, false);
                            let size = target_data.get_store_size(&struct_ty);
                            let align = target_data.get_abi_alignment(&struct_ty) as u64;
                            (size, align)
                        }
                    }
                }
            };
            payload_size = payload_size.max(size);
            payload_align = payload_align.max(align);
        }

        // Compute overall layout
        let payload_offset = align_up(discr_size, payload_align);
        let total_size = if payload_size == 0 {
            discr_size
        } else {
            align_up(payload_offset + payload_size, payload_align.max(discr_size))
        };
        let total_align = discr_size.max(payload_align);

        // Collect all unique pointer offsets across all variants
        let mut pointer_offsets = Vec::new();
        for variant in def.variants.iter() {
            if let crate::sema::models::EnumVariantKind::Tuple(fields) = variant.kind {
                if !fields.is_empty() {
                    let field_tys: Vec<BasicTypeEnum> = fields
                        .iter()
                        .filter_map(|f| self.lower_type(f.ty))
                        .collect();
                    if !field_tys.is_empty() {
                        let struct_ty = self.context.struct_type(&field_tys, false);
                        for (idx, field) in fields.iter().enumerate() {
                            if self.is_pointer_ty(field.ty) {
                                if let Some(off) =
                                    target_data.offset_of_element(&struct_ty, idx as u32)
                                {
                                    pointer_offsets.push(payload_offset + off);
                                }
                            }
                        }
                    }
                }
            }
        }
        pointer_offsets.sort_unstable();
        pointer_offsets.dedup();

        Shape {
            size: total_size,
            align: total_align,
            pointer_offsets,
        }
    }

    /// Check if a type contains GC-traced pointers.
    fn is_pointer_ty(&self, ty: Ty<'gcx>) -> bool {
        matches!(
            ty.kind(),
            TyKind::Reference(..) | TyKind::String | TyKind::GcPtr
        )
    }

    /// Lower a type to its LLVM representation.
    fn lower_type(&self, ty: Ty<'gcx>) -> Option<BasicTypeEnum<'a>> {
        let target_layout = &self.gcx.store.target_layout;
        let target_data = target_layout.target_data();

        match ty.kind() {
            TyKind::Bool => Some(self.context.bool_type().into()),
            TyKind::Rune => Some(self.context.i32_type().into()),
            TyKind::String => {
                let ptr_ty = self.context.ptr_type(AddressSpace::default());
                let len_ty = self.context.ptr_sized_int_type(&target_data, None);
                Some(
                    self.context
                        .struct_type(&[ptr_ty.into(), len_ty.into()], false)
                        .into(),
                )
            }
            TyKind::GcPtr => Some(
                self.context
                    .ptr_type(AddressSpace::default())
                    .as_basic_type_enum(),
            ),
            TyKind::Int(i) => Some(self.lower_int(i, &target_data).into()),
            TyKind::UInt(u) => Some(self.lower_uint(u, &target_data).into()),
            TyKind::Float(f) => Some(match f {
                FloatTy::F32 => self.context.f32_type().into(),
                FloatTy::F64 => self.context.f64_type().into(),
            }),
            TyKind::Adt(def) => match def.kind {
                AdtKind::Struct => {
                    let defn = self.gcx.get_struct_definition(def.id);
                    let field_tys: Vec<BasicTypeEnum> = defn
                        .fields
                        .iter()
                        .filter_map(|f| self.lower_type(f.ty))
                        .collect();
                    Some(self.context.struct_type(&field_tys, false).into())
                }
                AdtKind::Enum => {
                    // Simplified enum layout - just use discriminant + payload bytes
                    let discr_ty = self.context.ptr_sized_int_type(&target_data, None);
                    // For now, return just the discriminant for simplicity
                    // Full enum layout is computed separately
                    Some(discr_ty.into())
                }
            },
            TyKind::Pointer(..) | TyKind::Reference(..) => Some(
                self.context
                    .ptr_type(AddressSpace::default())
                    .as_basic_type_enum(),
            ),
            TyKind::Tuple(items) => {
                if items.is_empty() {
                    None
                } else {
                    let fields: Vec<BasicTypeEnum> =
                        items.iter().filter_map(|t| self.lower_type(*t)).collect();
                    Some(self.context.struct_type(&fields, false).into())
                }
            }
            TyKind::FnPointer { .. } => Some(
                self.context
                    .ptr_type(AddressSpace::default())
                    .as_basic_type_enum(),
            ),
            TyKind::Parameter(_) | TyKind::Infer(_) | TyKind::Error => None,
        }
    }

    fn lower_int(&self, ty: IntTy, target_data: &TargetData) -> inkwell::types::IntType<'a> {
        match ty {
            IntTy::I8 => self.context.i8_type(),
            IntTy::I16 => self.context.i16_type(),
            IntTy::I32 => self.context.i32_type(),
            IntTy::I64 => self.context.i64_type(),
            IntTy::ISize => self.context.ptr_sized_int_type(target_data, None),
        }
    }

    fn lower_uint(&self, ty: UIntTy, target_data: &TargetData) -> inkwell::types::IntType<'a> {
        match ty {
            UIntTy::U8 => self.context.i8_type(),
            UIntTy::U16 => self.context.i16_type(),
            UIntTy::U32 => self.context.i32_type(),
            UIntTy::U64 => self.context.i64_type(),
            UIntTy::USize => self.context.ptr_sized_int_type(target_data, None),
        }
    }
}

/// Align a value up to the given alignment.
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
