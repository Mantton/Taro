//! Runtime-facing, versioned PC metadata emitted as a native sidecar object.
//!
//! LLVM's experimental stack-map encoding stops at [`super::stack_maps`].
//! This module owns the stable Taro ABI registered by a global constructor.

use std::{collections::BTreeMap, path::Path};

use inkwell::{
    AddressSpace,
    context::Context,
    module::{Linkage, Module},
    targets::{FileType, TargetMachine},
    types::StructType,
    values::{BasicValue, GlobalValue, IntValue, PointerValue, StructValue},
};

use super::stack_maps::{PC_METADATA_SCHEMA_VERSION, StackMapSiteKind};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub(crate) enum PcArchitecture {
    X86_64 = 1,
    AArch64 = 2,
}

impl PcArchitecture {
    pub(crate) fn from_target_triple(triple: &str) -> Result<Self, String> {
        let architecture = triple.split('-').next().unwrap_or(triple);
        match architecture {
            "x86_64" => Ok(Self::X86_64),
            "aarch64" | "arm64" => Ok(Self::AArch64),
            other => Err(format!(
                "compiler PC metadata does not support target architecture '{other}'"
            )),
        }
    }

    pub(crate) const fn pointer_bytes(self) -> u8 {
        match self {
            Self::X86_64 | Self::AArch64 => 8,
        }
    }

    pub(crate) fn matches_llvm_name(self, name: &str) -> bool {
        match self {
            Self::X86_64 => name == "x86_64",
            Self::AArch64 => matches!(name, "aarch64" | "arm64"),
        }
    }

    pub(crate) const fn supports_dwarf_base_register(self, register: u16) -> bool {
        match self {
            // DWARF RBP/RSP.
            Self::X86_64 => matches!(register, 6 | 7),
            // DWARF FP/SP.
            Self::AArch64 => matches!(register, 29 | 31),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct PcRootRecipe {
    pub offset: u64,
    pub deref_depth: u8,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct PcRootLocation {
    pub dwarf_register: u16,
    pub frame_offset: i32,
    pub storage_deref_depth: u8,
    pub recipes: Vec<PcRootRecipe>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct PcLogicalFrame {
    pub function: String,
    pub file: String,
    pub line: u32,
    pub column: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PcRecord {
    pub pc_offset: u32,
    pub kind: StackMapSiteKind,
    pub roots: Vec<PcRootLocation>,
    pub logical_frames: Vec<PcLogicalFrame>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PcFunction {
    pub symbol: String,
    pub stack_size: u64,
    pub records: Vec<PcRecord>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PcMetadata {
    pub version: u32,
    pub architecture: PcArchitecture,
    pub pointer_bytes: u8,
    pub functions: Vec<PcFunction>,
}

#[derive(Clone, Copy)]
struct AbiTypes<'ctx> {
    recipe: StructType<'ctx>,
    root: StructType<'ctx>,
    string: StructType<'ctx>,
    frame: StructType<'ctx>,
    record: StructType<'ctx>,
    function: StructType<'ctx>,
    module: StructType<'ctx>,
}

struct ObjectBuilder<'ctx> {
    context: &'ctx Context,
    module: Module<'ctx>,
    module_global: GlobalValue<'ctx>,
    types: AbiTypes<'ctx>,
    strings: BTreeMap<String, PointerValue<'ctx>>,
    recipes: BTreeMap<Vec<PcRootRecipe>, PointerValue<'ctx>>,
    roots: BTreeMap<Vec<PcRootLocation>, PointerValue<'ctx>>,
    frames: BTreeMap<Vec<PcLogicalFrame>, PointerValue<'ctx>>,
    next_global: usize,
}

impl<'ctx> ObjectBuilder<'ctx> {
    fn new(context: &'ctx Context, module: Module<'ctx>) -> Self {
        let i8 = context.i8_type();
        let i16 = context.i16_type();
        let i32 = context.i32_type();
        let i64 = context.i64_type();
        let recipe = context.struct_type(&[i64.into(), i8.into(), i8.array_type(7).into()], false);
        let root = context.struct_type(
            &[
                i64.into(),
                i32.into(),
                i32.into(),
                i16.into(),
                i8.into(),
                i8.into(),
            ],
            false,
        );
        let string = context.struct_type(&[i64.into(), i32.into(), i32.into()], false);
        let frame = context.struct_type(
            &[string.into(), string.into(), i32.into(), i32.into()],
            false,
        );
        let record = context.struct_type(
            &[
                i64.into(),
                i64.into(),
                i32.into(),
                i32.into(),
                i32.into(),
                i8.into(),
                i8.array_type(3).into(),
            ],
            false,
        );
        let function = context.struct_type(
            &[
                i64.into(),
                i64.into(),
                string.into(),
                i64.into(),
                i32.into(),
                i32.into(),
            ],
            false,
        );
        let module_ty = context.struct_type(
            &[
                i64.into(),
                i32.into(),
                i32.into(),
                i8.into(),
                i8.into(),
                i8.array_type(6).into(),
            ],
            false,
        );
        let types = AbiTypes {
            recipe,
            root,
            string,
            frame,
            record,
            function,
            module: module_ty,
        };
        let module_global = module.add_global(types.module, None, "__taro_pc_metadata_module");
        module_global.set_linkage(Linkage::Internal);
        Self {
            context,
            module,
            module_global,
            types,
            strings: BTreeMap::new(),
            recipes: BTreeMap::new(),
            roots: BTreeMap::new(),
            frames: BTreeMap::new(),
            next_global: 0,
        }
    }

    fn name(&mut self, kind: &str) -> String {
        let index = self.next_global;
        self.next_global += 1;
        format!("__taro_pc_{kind}_{index}")
    }

    /// Encode a reference as a signed byte offset from the module header.
    /// Linkers resolve these subtractor expressions statically, leaving the
    /// dynamic loader only the constructor's single module pointer to rebase.
    fn relative(&self, pointer: PointerValue<'ctx>) -> IntValue<'ctx> {
        let i64 = self.context.i64_type();
        if pointer.is_null() {
            i64.const_zero()
        } else {
            pointer
                .const_to_int(i64)
                .const_sub(self.module_global.as_pointer_value().const_to_int(i64))
        }
    }

    fn private_global(
        &mut self,
        ty: impl inkwell::types::BasicType<'ctx>,
        initializer: &impl BasicValue<'ctx>,
        kind: &str,
    ) -> PointerValue<'ctx> {
        let name = self.name(kind);
        let global = self.module.add_global(ty, None, &name);
        global.set_initializer(initializer);
        global.set_constant(true);
        global.set_linkage(Linkage::Private);
        global.set_unnamed_addr(true);
        global.as_pointer_value()
    }

    fn bytes(&mut self, value: &str) -> PointerValue<'ctx> {
        if value.is_empty() {
            return self.context.ptr_type(AddressSpace::default()).const_null();
        }
        if let Some(pointer) = self.strings.get(value) {
            return *pointer;
        }
        let constant = self.context.const_string(value.as_bytes(), false);
        let pointer = self.private_global(constant.get_type(), &constant, "string_bytes");
        self.strings.insert(value.to_owned(), pointer);
        pointer
    }

    fn string(&mut self, value: &str) -> StructValue<'ctx> {
        let pointer = self.bytes(value);
        self.types.string.const_named_struct(&[
            self.relative(pointer).into(),
            self.context
                .i32_type()
                .const_int(value.len() as u64, false)
                .into(),
            self.context.i32_type().const_zero().into(),
        ])
    }

    fn struct_array(
        &mut self,
        ty: StructType<'ctx>,
        values: &[StructValue<'ctx>],
        kind: &str,
    ) -> PointerValue<'ctx> {
        if values.is_empty() {
            return self.context.ptr_type(AddressSpace::default()).const_null();
        }
        let constant = ty.const_array(values);
        self.private_global(constant.get_type(), &constant, kind)
    }

    fn recipes(&mut self, recipes: &[PcRootRecipe]) -> PointerValue<'ctx> {
        if recipes.is_empty() {
            return self.context.ptr_type(AddressSpace::default()).const_null();
        }
        if let Some(pointer) = self.recipes.get(recipes) {
            return *pointer;
        }
        let zero7 = self.context.i8_type().const_zero().get_type().array_type(7);
        let reserved = zero7.const_zero();
        let values: Vec<_> = recipes
            .iter()
            .map(|recipe| {
                self.types.recipe.const_named_struct(&[
                    self.context
                        .i64_type()
                        .const_int(recipe.offset, false)
                        .into(),
                    self.context
                        .i8_type()
                        .const_int(u64::from(recipe.deref_depth), false)
                        .into(),
                    reserved.into(),
                ])
            })
            .collect();
        let pointer = self.struct_array(self.types.recipe, &values, "recipes");
        self.recipes.insert(recipes.to_vec(), pointer);
        pointer
    }

    fn roots(&mut self, roots: &[PcRootLocation]) -> PointerValue<'ctx> {
        if roots.is_empty() {
            return self.context.ptr_type(AddressSpace::default()).const_null();
        }
        if let Some(pointer) = self.roots.get(roots) {
            return *pointer;
        }
        let values: Vec<_> = roots
            .iter()
            .map(|root| {
                let recipes = self.recipes(&root.recipes);
                self.types.root.const_named_struct(&[
                    self.relative(recipes).into(),
                    self.context
                        .i32_type()
                        .const_int(root.frame_offset as u32 as u64, false)
                        .into(),
                    self.context
                        .i32_type()
                        .const_int(root.recipes.len() as u64, false)
                        .into(),
                    self.context
                        .i16_type()
                        .const_int(u64::from(root.dwarf_register), false)
                        .into(),
                    self.context
                        .i8_type()
                        .const_int(u64::from(root.storage_deref_depth), false)
                        .into(),
                    self.context.i8_type().const_zero().into(),
                ])
            })
            .collect();
        let pointer = self.struct_array(self.types.root, &values, "roots");
        self.roots.insert(roots.to_vec(), pointer);
        pointer
    }

    fn frames(&mut self, frames: &[PcLogicalFrame]) -> PointerValue<'ctx> {
        if frames.is_empty() {
            return self.context.ptr_type(AddressSpace::default()).const_null();
        }
        if let Some(pointer) = self.frames.get(frames) {
            return *pointer;
        }
        let values: Vec<_> = frames
            .iter()
            .map(|frame| {
                let function = self.string(&frame.function);
                let file = self.string(&frame.file);
                self.types.frame.const_named_struct(&[
                    function.into(),
                    file.into(),
                    self.context
                        .i32_type()
                        .const_int(u64::from(frame.line), false)
                        .into(),
                    self.context
                        .i32_type()
                        .const_int(u64::from(frame.column), false)
                        .into(),
                ])
            })
            .collect();
        let pointer = self.struct_array(self.types.frame, &values, "frames");
        self.frames.insert(frames.to_vec(), pointer);
        pointer
    }

    fn records(&mut self, records: &[PcRecord]) -> PointerValue<'ctx> {
        let reserved = self.context.i8_type().array_type(3).const_zero();
        let values: Vec<_> = records
            .iter()
            .map(|record| {
                let roots = self.roots(&record.roots);
                let frames = self.frames(&record.logical_frames);
                self.types.record.const_named_struct(&[
                    self.relative(roots).into(),
                    self.relative(frames).into(),
                    self.context
                        .i32_type()
                        .const_int(u64::from(record.pc_offset), false)
                        .into(),
                    self.context
                        .i32_type()
                        .const_int(record.roots.len() as u64, false)
                        .into(),
                    self.context
                        .i32_type()
                        .const_int(record.logical_frames.len() as u64, false)
                        .into(),
                    self.context
                        .i8_type()
                        .const_int(record.kind as u64, false)
                        .into(),
                    reserved.into(),
                ])
            })
            .collect();
        self.struct_array(self.types.record, &values, "records")
    }

    fn functions(&mut self, functions: &[PcFunction]) -> PointerValue<'ctx> {
        let values: Vec<_> = functions
            .iter()
            .map(|function| {
                let declaration = self.module.add_function(
                    &function.symbol,
                    self.context.void_type().fn_type(&[], false),
                    Some(Linkage::External),
                );
                let records = self.records(&function.records);
                let symbol = self.string(&function.symbol);
                self.types.function.const_named_struct(&[
                    self.relative(declaration.as_global_value().as_pointer_value())
                        .into(),
                    self.relative(records).into(),
                    symbol.into(),
                    self.context
                        .i64_type()
                        .const_int(function.stack_size, false)
                        .into(),
                    self.context
                        .i32_type()
                        .const_int(function.records.len() as u64, false)
                        .into(),
                    self.context.i32_type().const_zero().into(),
                ])
            })
            .collect();
        self.struct_array(self.types.function, &values, "functions")
    }

    fn finish(mut self, metadata: &PcMetadata) -> Module<'ctx> {
        let functions = self.functions(&metadata.functions);
        let reserved = self.context.i8_type().array_type(6).const_zero();
        let initializer = self.types.module.const_named_struct(&[
            self.relative(functions).into(),
            self.context
                .i32_type()
                .const_int(metadata.functions.len() as u64, false)
                .into(),
            self.context
                .i32_type()
                .const_int(u64::from(metadata.version), false)
                .into(),
            self.context
                .i8_type()
                .const_int(u64::from(metadata.pointer_bytes), false)
                .into(),
            self.context
                .i8_type()
                .const_int(metadata.architecture as u64, false)
                .into(),
            reserved.into(),
        ]);
        self.module_global.set_initializer(&initializer);
        self.module_global.set_constant(true);

        let ptr = self.context.ptr_type(AddressSpace::default());
        let register = self.module.add_function(
            "__rt__pc_metadata_register",
            self.context.void_type().fn_type(&[ptr.into()], false),
            Some(Linkage::External),
        );
        let ctor = self.module.add_function(
            "__taro_register_pc_metadata",
            self.context.void_type().fn_type(&[], false),
            Some(Linkage::Internal),
        );
        let entry = self.context.append_basic_block(ctor, "entry");
        let builder = self.context.create_builder();
        builder.position_at_end(entry);
        builder
            .build_call(
                register,
                &[self.module_global.as_pointer_value().into()],
                "",
            )
            .unwrap();
        builder.build_return(None).unwrap();

        let i32 = self.context.i32_type();
        let ctor_entry_ty = self
            .context
            .struct_type(&[i32.into(), ptr.into(), ptr.into()], false);
        let ctor_entry = ctor_entry_ty.const_named_struct(&[
            i32.const_int(65535, false).into(),
            ctor.as_global_value().as_pointer_value().into(),
            ptr.const_null().into(),
        ]);
        let ctors = self
            .module
            .add_global(ctor_entry_ty.array_type(1), None, "llvm.global_ctors");
        ctors.set_linkage(Linkage::Appending);
        ctors.set_initializer(&ctor_entry_ty.const_array(&[ctor_entry]));
        self.module
    }
}

pub(crate) fn emit_object(
    metadata: &PcMetadata,
    target_machine: &TargetMachine,
    output: &Path,
) -> Result<(), String> {
    if metadata.version != PC_METADATA_SCHEMA_VERSION {
        return Err(format!(
            "cannot emit PC metadata schema version {} (compiler supports {})",
            metadata.version, PC_METADATA_SCHEMA_VERSION
        ));
    }
    let context = Context::create();
    let module = context.create_module("taro-pc-metadata");
    module.set_triple(&target_machine.get_triple());
    module.set_data_layout(&target_machine.get_target_data().get_data_layout());
    let module = ObjectBuilder::new(&context, module).finish(metadata);
    module
        .verify()
        .map_err(|error| format!("invalid PC metadata module: {error}"))?;
    target_machine
        .write_to_file(&module, FileType::Object, output)
        .map_err(|error| {
            format!(
                "failed to write PC metadata object '{}': {error}",
                output.display()
            )
        })
}

#[cfg(test)]
mod tests {
    use super::{AbiTypes, PcArchitecture};
    use inkwell::{context::Context, targets::TargetData, types::AnyType};

    #[test]
    fn runtime_abi_layout_is_stable_on_64_bit_targets() {
        let context = Context::create();
        let module = context.create_module("layout");
        let builder = super::ObjectBuilder::new(&context, module);
        let AbiTypes {
            recipe,
            root,
            string,
            frame,
            record,
            function,
            module,
        } = builder.types;
        let data = TargetData::create("e-p:64:64-i64:64-n8:16:32:64-S128");
        assert_eq!(data.get_store_size(&recipe.as_any_type_enum()), 16);
        assert_eq!(data.get_store_size(&root.as_any_type_enum()), 24);
        assert_eq!(data.get_store_size(&string.as_any_type_enum()), 16);
        assert_eq!(data.get_store_size(&frame.as_any_type_enum()), 40);
        assert_eq!(data.get_store_size(&record.as_any_type_enum()), 32);
        assert_eq!(data.get_store_size(&function.as_any_type_enum()), 48);
        assert_eq!(data.get_store_size(&module.as_any_type_enum()), 24);
        assert_eq!(data.get_pointer_byte_size(None), 8);
    }

    #[test]
    fn supported_architectures_are_explicit() {
        assert_eq!(
            PcArchitecture::from_target_triple("x86_64-unknown-linux-gnu").unwrap(),
            PcArchitecture::X86_64
        );
        assert_eq!(
            PcArchitecture::from_target_triple("aarch64-apple-darwin").unwrap(),
            PcArchitecture::AArch64
        );
        assert!(PcArchitecture::from_target_triple("wasm32-unknown-unknown").is_err());
    }
}
