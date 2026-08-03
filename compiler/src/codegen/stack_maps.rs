//! Parsing and normalization inputs for LLVM's machine stack-map section.
//!
//! LLVM's raw section is deliberately confined to the compiler. The runtime
//! consumes only Taro's versioned PC metadata, which is built from these owned
//! records after machine-code emission.

use std::{
    borrow::Cow,
    path::Path,
    ptr::NonNull,
    slice,
};

#[repr(C)]
struct NativeParsedStackMap {
    _private: [u8; 0],
}

unsafe extern "C" {
    fn taro_stack_map_parse_object(path: *const u8, path_length: usize)
    -> *mut NativeParsedStackMap;
    fn taro_stack_map_dispose(stack_map: *mut NativeParsedStackMap);
    fn taro_stack_map_is_valid(stack_map: *const NativeParsedStackMap) -> bool;
    fn taro_stack_map_error(
        stack_map: *const NativeParsedStackMap,
        length: *mut usize,
    ) -> *const u8;
    fn taro_stack_map_architecture(
        stack_map: *const NativeParsedStackMap,
        length: *mut usize,
    ) -> *const u8;
    fn taro_stack_map_pointer_bytes(stack_map: *const NativeParsedStackMap) -> u8;
    fn taro_stack_map_function_count(stack_map: *const NativeParsedStackMap) -> usize;
    fn taro_stack_map_function_symbol(
        stack_map: *const NativeParsedStackMap,
        index: usize,
        length: *mut usize,
    ) -> *const u8;
    fn taro_stack_map_function_stack_size(
        stack_map: *const NativeParsedStackMap,
        index: usize,
    ) -> u64;
    fn taro_stack_map_function_record_start(
        stack_map: *const NativeParsedStackMap,
        index: usize,
    ) -> usize;
    fn taro_stack_map_function_record_count(
        stack_map: *const NativeParsedStackMap,
        index: usize,
    ) -> usize;
    fn taro_stack_map_record_count(stack_map: *const NativeParsedStackMap) -> usize;
    fn taro_stack_map_record_id(stack_map: *const NativeParsedStackMap, index: usize) -> u64;
    fn taro_stack_map_record_instruction_offset(
        stack_map: *const NativeParsedStackMap,
        index: usize,
    ) -> u32;
    fn taro_stack_map_record_function_index(
        stack_map: *const NativeParsedStackMap,
        index: usize,
    ) -> usize;
    fn taro_stack_map_location_count(
        stack_map: *const NativeParsedStackMap,
        record_index: usize,
    ) -> usize;
    fn taro_stack_map_location_kind(
        stack_map: *const NativeParsedStackMap,
        record_index: usize,
        location_index: usize,
    ) -> u8;
    fn taro_stack_map_location_size(
        stack_map: *const NativeParsedStackMap,
        record_index: usize,
        location_index: usize,
    ) -> u16;
    fn taro_stack_map_location_dwarf_register(
        stack_map: *const NativeParsedStackMap,
        record_index: usize,
        location_index: usize,
    ) -> u16;
    fn taro_stack_map_location_value(
        stack_map: *const NativeParsedStackMap,
        record_index: usize,
        location_index: usize,
    ) -> i64;
}

struct NativeStackMap(NonNull<NativeParsedStackMap>);

impl NativeStackMap {
    fn parse(path: &Path) -> Result<Self, String> {
        let bytes = path_bytes(path)?;
        let parsed = NonNull::new(unsafe {
            taro_stack_map_parse_object(bytes.as_ptr(), bytes.len())
        })
        .ok_or_else(|| "LLVM failed to allocate a parsed stack map".to_owned())?;
        let parsed = Self(parsed);
        if !unsafe { taro_stack_map_is_valid(parsed.0.as_ptr()) } {
            return Err(parsed.error());
        }
        Ok(parsed)
    }

    fn error(&self) -> String {
        read_native_string(|length| unsafe { taro_stack_map_error(self.0.as_ptr(), length) })
            .unwrap_or_else(|error| format!("invalid LLVM stack map ({error})"))
    }
}

impl Drop for NativeStackMap {
    fn drop(&mut self) {
        unsafe { taro_stack_map_dispose(self.0.as_ptr()) };
    }
}

/// One machine function represented in an LLVM stack-map section.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RawStackMapFunction {
    pub symbol: String,
    pub stack_size: u64,
    pub record_start: usize,
    pub record_count: usize,
}

/// LLVM's location encoding for one intrinsic operand.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum RawStackMapLocationKind {
    Register,
    Direct,
    Indirect,
    Constant,
    ConstantIndex,
}

impl TryFrom<u8> for RawStackMapLocationKind {
    type Error = String;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            1 => Ok(Self::Register),
            2 => Ok(Self::Direct),
            3 => Ok(Self::Indirect),
            4 => Ok(Self::Constant),
            5 => Ok(Self::ConstantIndex),
            _ => Err(format!("LLVM emitted unknown stack-map location kind {value}")),
        }
    }
}

/// Owned machine location for one stack-map operand.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RawStackMapLocation {
    pub kind: RawStackMapLocationKind,
    pub size: u16,
    pub dwarf_register: u16,
    /// Frame offset for direct/indirect locations or value for constants.
    pub value: i64,
}

/// One PC-indexed LLVM stack-map record.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RawStackMapRecord {
    pub id: u64,
    pub instruction_offset: u32,
    pub function_index: usize,
    pub locations: Vec<RawStackMapLocation>,
}

/// Fully owned contents of a raw LLVM stack-map section.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RawStackMap {
    pub architecture: String,
    pub pointer_bytes: u8,
    pub functions: Vec<RawStackMapFunction>,
    pub records: Vec<RawStackMapRecord>,
}

/// Parse the raw LLVM stack-map section in a relocatable object.
///
/// The native shim uses the same pinned LLVM installation as code generation,
/// normalizes Mach-O symbol prefixes, and validates all variable-length ranges
/// before constructing LLVM's accessor parser.
pub(crate) fn parse_object(path: &Path) -> Result<RawStackMap, String> {
    let native = NativeStackMap::parse(path)?;
    let pointer = native.0.as_ptr();
    let architecture = read_native_string(|length| unsafe {
        taro_stack_map_architecture(pointer, length)
    })?;
    let pointer_bytes = unsafe { taro_stack_map_pointer_bytes(pointer) };
    if pointer_bytes == 0 {
        return Err("LLVM stack-map object reported a zero-byte pointer".into());
    }

    let function_count = unsafe { taro_stack_map_function_count(pointer) };
    let mut functions = Vec::with_capacity(function_count);
    for index in 0..function_count {
        let symbol = read_native_string(|length| unsafe {
            taro_stack_map_function_symbol(pointer, index, length)
        })?;
        if symbol.is_empty() {
            return Err(format!("LLVM stack-map function {index} has an empty symbol"));
        }
        functions.push(RawStackMapFunction {
            symbol,
            stack_size: unsafe { taro_stack_map_function_stack_size(pointer, index) },
            record_start: unsafe { taro_stack_map_function_record_start(pointer, index) },
            record_count: unsafe { taro_stack_map_function_record_count(pointer, index) },
        });
    }

    let record_count = unsafe { taro_stack_map_record_count(pointer) };
    let mut records = Vec::with_capacity(record_count);
    for record_index in 0..record_count {
        let function_index = unsafe {
            taro_stack_map_record_function_index(pointer, record_index)
        };
        if function_index >= functions.len() {
            return Err(format!(
                "LLVM stack-map record {record_index} references missing function {function_index}"
            ));
        }
        let location_count = unsafe { taro_stack_map_location_count(pointer, record_index) };
        let mut locations = Vec::with_capacity(location_count);
        for location_index in 0..location_count {
            locations.push(RawStackMapLocation {
                kind: unsafe {
                    taro_stack_map_location_kind(pointer, record_index, location_index)
                }
                .try_into()?,
                size: unsafe {
                    taro_stack_map_location_size(pointer, record_index, location_index)
                },
                dwarf_register: unsafe {
                    taro_stack_map_location_dwarf_register(
                        pointer,
                        record_index,
                        location_index,
                    )
                },
                value: unsafe {
                    taro_stack_map_location_value(pointer, record_index, location_index)
                },
            });
        }
        records.push(RawStackMapRecord {
            id: unsafe { taro_stack_map_record_id(pointer, record_index) },
            instruction_offset: unsafe {
                taro_stack_map_record_instruction_offset(pointer, record_index)
            },
            function_index,
            locations,
        });
    }

    for (function_index, function) in functions.iter().enumerate() {
        let end = function
            .record_start
            .checked_add(function.record_count)
            .ok_or_else(|| format!("LLVM stack-map function {function_index} range overflows"))?;
        if end > records.len()
            || records[function.record_start..end]
                .iter()
                .any(|record| record.function_index != function_index)
        {
            return Err(format!(
                "LLVM stack-map function {function_index} has an invalid record range"
            ));
        }
    }

    Ok(RawStackMap {
        architecture,
        pointer_bytes,
        functions,
        records,
    })
}

fn read_native_string(read: impl FnOnce(*mut usize) -> *const u8) -> Result<String, String> {
    let mut length = 0;
    let pointer = read(&mut length);
    if length == 0 {
        return Ok(String::new());
    }
    if pointer.is_null() {
        return Err("LLVM returned a null stack-map string".into());
    }
    let bytes = unsafe { slice::from_raw_parts(pointer, length) };
    String::from_utf8(bytes.to_vec())
        .map_err(|_| "LLVM returned a non-UTF-8 stack-map string".into())
}

#[cfg(unix)]
fn path_bytes(path: &Path) -> Result<Cow<'_, [u8]>, String> {
    use std::os::unix::ffi::OsStrExt;
    Ok(Cow::Borrowed(path.as_os_str().as_bytes()))
}

#[cfg(not(unix))]
fn path_bytes(path: &Path) -> Result<Cow<'_, [u8]>, String> {
    path.to_str()
        .map(|path| Cow::Borrowed(path.as_bytes()))
        .ok_or_else(|| format!("stack-map path '{}' is not valid UTF-8", path.display()))
}

#[cfg(test)]
mod tests {
    use super::{RawStackMapLocationKind, parse_object};
    use inkwell::{
        OptimizationLevel,
        context::Context,
        memory_buffer::MemoryBuffer,
        passes::PassBuilderOptions,
        targets::{
            CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetTriple,
        },
    };
    use std::{
        fs,
        path::PathBuf,
        sync::atomic::{AtomicU64, Ordering},
        time::SystemTime,
    };

    const STACK_MAP_ID: u64 = 0x0102_0304_0506_0708;
    static NEXT_TEST_DIRECTORY: AtomicU64 = AtomicU64::new(0);

    struct TestDirectory(PathBuf);

    impl TestDirectory {
        fn new() -> Self {
            let nonce = SystemTime::now()
                .duration_since(SystemTime::UNIX_EPOCH)
                .expect("time should follow epoch")
                .as_nanos();
            let path = std::env::temp_dir().join(format!(
                "taro-stack-map-test-{}-{nonce}-{}",
                std::process::id(),
                NEXT_TEST_DIRECTORY.fetch_add(1, Ordering::Relaxed)
            ));
            fs::create_dir_all(&path).expect("create stack-map test directory");
            Self(path)
        }
    }

    impl Drop for TestDirectory {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    fn emit_probe_object(
        triple: &str,
        optimization: OptimizationLevel,
        directory: &TestDirectory,
        name: &str,
    ) -> PathBuf {
        Target::initialize_all(&InitializationConfig::default());
        let triple = TargetTriple::create(triple);
        let target = Target::from_triple(&triple).expect("probe target should be available");
        let machine = target
            .create_target_machine(
                &triple,
                "generic",
                "",
                optimization,
                RelocMode::PIC,
                CodeModel::Default,
            )
            .expect("create probe target machine");
        let context = Context::create();
        let mut ir = format!(
            r#"
                declare void @llvm.experimental.stackmap(i64, i32, ...)

                define void @probe_stackmap() noinline {{
                entry:
                    %root = alloca ptr, align 8
                    call void (i64, i32, ...) @llvm.experimental.stackmap(
                        i64 {STACK_MAP_ID}, i32 0, ptr %root)
                    ret void
                }}
            "#
        );
        ir.push('\0');
        let buffer = MemoryBuffer::create_from_memory_range_copy(ir.as_bytes(), "probe.ll");
        let module = context
            .create_module_from_ir(buffer)
            .expect("parse stack-map probe IR");
        module.set_triple(&triple);
        module.set_data_layout(&machine.get_target_data().get_data_layout());
        if optimization != OptimizationLevel::None {
            module
                .run_passes(
                    "default<O2>",
                    &machine,
                    PassBuilderOptions::create(),
                )
                .expect("optimize stack-map probe");
        }
        module.verify().expect("verify stack-map probe");
        let path = directory.0.join(format!("{name}.o"));
        machine
            .write_to_file(&module, FileType::Object, &path)
            .expect("emit stack-map probe object");
        path
    }

    fn assert_probe(path: &std::path::Path, architecture: &str) {
        let parsed = parse_object(path).expect("parse emitted stack-map object");
        assert_eq!(parsed.architecture, architecture);
        assert_eq!(parsed.pointer_bytes, 8);
        assert_eq!(parsed.functions.len(), 1);
        assert_eq!(parsed.functions[0].symbol, "probe_stackmap");
        assert_eq!(parsed.functions[0].record_start, 0);
        assert_eq!(parsed.functions[0].record_count, 1);
        assert_eq!(parsed.records.len(), 1);
        assert_eq!(parsed.records[0].id, STACK_MAP_ID);
        assert_eq!(parsed.records[0].function_index, 0);
        assert_eq!(parsed.records[0].locations.len(), 1);
        assert_eq!(
            parsed.records[0].locations[0].kind,
            RawStackMapLocationKind::Direct
        );
        assert_eq!(parsed.records[0].locations[0].size, 8);
    }

    #[test]
    fn parses_direct_locations_at_o0_and_o2() {
        let directory = TestDirectory::new();
        let o0 = emit_probe_object(
            "aarch64-apple-darwin",
            OptimizationLevel::None,
            &directory,
            "aarch64-o0",
        );
        let o2 = emit_probe_object(
            "aarch64-apple-darwin",
            OptimizationLevel::Default,
            &directory,
            "aarch64-o2",
        );
        assert_probe(&o0, "aarch64");
        assert_probe(&o2, "aarch64");
    }

    #[test]
    fn parses_elf_and_macho_function_relocations() {
        let directory = TestDirectory::new();
        let elf = emit_probe_object(
            "x86_64-unknown-linux-gnu",
            OptimizationLevel::Default,
            &directory,
            "x86-elf",
        );
        let macho = emit_probe_object(
            "aarch64-apple-darwin",
            OptimizationLevel::Default,
            &directory,
            "arm-macho",
        );
        assert_probe(&elf, "x86_64");
        assert_probe(&macho, "aarch64");
    }

    #[test]
    fn rejects_objects_without_a_stack_map_section() {
        let directory = TestDirectory::new();
        let context = Context::create();
        Target::initialize_all(&InitializationConfig::default());
        let triple = TargetTriple::create("aarch64-apple-darwin");
        let target = Target::from_triple(&triple).expect("AArch64 target");
        let machine = target
            .create_target_machine(
                &triple,
                "generic",
                "",
                OptimizationLevel::None,
                RelocMode::PIC,
                CodeModel::Default,
            )
            .expect("AArch64 target machine");
        let module = context.create_module("empty");
        module.set_triple(&triple);
        module.set_data_layout(&machine.get_target_data().get_data_layout());
        let path = directory.0.join("empty.o");
        machine
            .write_to_file(&module, FileType::Object, &path)
            .expect("emit empty object");
        let error = parse_object(&path).expect_err("missing section must fail");
        assert!(error.contains("does not contain an LLVM stack map section"));
    }
}
