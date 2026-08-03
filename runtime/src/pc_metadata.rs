//! Registered compiler PC metadata.
//!
//! Generated sidecar objects expose this fixed C ABI only to their global
//! constructors. Registration validates the fixed-size module header and
//! retains its address. The first stack walk indexes only function headers;
//! individual PC records and their root/frame data are decoded on demand.
//! Short-lived programs therefore do not pay to copy standard-library metadata
//! they never inspect.

use std::sync::{OnceLock, RwLock};

pub(crate) const PC_METADATA_SCHEMA_VERSION: u32 = 2;
#[cfg(target_arch = "x86_64")]
const ARCH_X86_64: u8 = 1;
#[cfg(target_arch = "aarch64")]
const ARCH_AARCH64: u8 = 2;
const MAX_FUNCTIONS_PER_MODULE: usize = 1 << 20;
const MAX_RECORDS_PER_FUNCTION: usize = 1 << 20;
const MAX_ROOTS_PER_RECORD: usize = 1 << 16;
const MAX_RECIPES_PER_ROOT: usize = 1 << 16;
const MAX_FRAMES_PER_RECORD: usize = 1 << 12;
const MAX_STRING_BYTES: usize = 1 << 20;
const MAX_DEREF_DEPTH: u8 = 32;

#[repr(C)]
struct AbiRootRecipe {
    offset: u64,
    deref_depth: u8,
    reserved: [u8; 7],
}

#[repr(C)]
struct AbiRootLocation {
    recipes_offset: i64,
    frame_offset: i32,
    recipe_count: u32,
    dwarf_register: u16,
    storage_deref_depth: u8,
    reserved: u8,
}

#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct AbiString {
    data_offset: i64,
    len: u32,
    reserved: u32,
}

#[repr(C)]
struct AbiLogicalFrame {
    function: AbiString,
    file: AbiString,
    line: u32,
    column: u32,
}

#[repr(C)]
struct AbiRecord {
    roots_offset: i64,
    logical_frames_offset: i64,
    pc_offset: u32,
    root_count: u32,
    logical_frame_count: u32,
    kind: u8,
    reserved: [u8; 3],
}

#[repr(C)]
struct AbiFunction {
    entry_offset: i64,
    records_offset: i64,
    symbol: AbiString,
    stack_size: u64,
    record_count: u32,
    reserved: u32,
}

#[repr(C)]
pub struct AbiMetadataModule {
    functions_offset: i64,
    function_count: u32,
    version: u32,
    pointer_bytes: u8,
    architecture: u8,
    reserved: [u8; 6],
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RootRecipe {
    pub(crate) offset: u64,
    pub(crate) deref_depth: u8,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RootLocation {
    pub(crate) dwarf_register: u16,
    pub(crate) frame_offset: i32,
    pub(crate) storage_deref_depth: u8,
    pub(crate) recipes: Vec<RootRecipe>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LogicalFrame {
    pub(crate) function: String,
    pub(crate) file: String,
    pub(crate) line: u32,
    pub(crate) column: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PcRecord {
    pub(crate) pc_offset: u32,
    pub(crate) kind: u8,
    pub(crate) roots: Vec<RootLocation>,
    pub(crate) logical_frames: Vec<LogicalFrame>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PcFunction {
    pub(crate) entry: usize,
    pub(crate) stack_size: u64,
    module_base: usize,
    records_offset: i64,
    record_count: usize,
    symbol: AbiString,
}

#[derive(Default)]
struct Registry {
    functions: Vec<PcFunction>,
    pending_modules: Vec<usize>,
}

static REGISTRY: OnceLock<RwLock<Registry>> = OnceLock::new();

fn registry() -> &'static RwLock<Registry> {
    REGISTRY.get_or_init(|| RwLock::new(Registry::default()))
}

const fn host_architecture() -> Option<u8> {
    #[cfg(target_arch = "x86_64")]
    {
        return Some(ARCH_X86_64);
    }
    #[cfg(target_arch = "aarch64")]
    {
        return Some(ARCH_AARCH64);
    }
    #[allow(unreachable_code)]
    None
}

fn relative_address(base: usize, offset: i64, what: &str) -> Result<usize, String> {
    if offset == 0 {
        return Err(format!("PC metadata {what} offset is zero"));
    }
    let magnitude = usize::try_from(offset.unsigned_abs())
        .map_err(|_| format!("PC metadata {what} offset exceeds the address width"))?;
    if offset > 0 {
        base.checked_add(magnitude)
    } else {
        base.checked_sub(magnitude)
    }
    .ok_or_else(|| format!("PC metadata {what} offset overflows the module address"))
}

unsafe fn abi_slice<'a, T>(
    base: usize,
    offset: i64,
    count: usize,
    what: &str,
) -> Result<&'a [T], String> {
    if count == 0 {
        return Ok(&[]);
    }
    let address = relative_address(base, offset, what)?;
    if address % std::mem::align_of::<T>() != 0 {
        return Err(format!("PC metadata {what} is not properly aligned"));
    }
    Ok(unsafe { std::slice::from_raw_parts(address as *const T, count) })
}

unsafe fn copy_string(base: usize, value: AbiString, what: &str) -> Result<String, String> {
    let len = value.len as usize;
    if len > MAX_STRING_BYTES {
        return Err(format!("PC metadata {what} exceeds the string limit"));
    }
    let bytes = unsafe { abi_slice(base, value.data_offset, len, what)? };
    String::from_utf8(bytes.to_vec()).map_err(|_| format!("PC metadata {what} is not UTF-8"))
}

unsafe fn copy_recipes(
    base: usize,
    offset: i64,
    count: usize,
    function_entry: usize,
) -> Result<Vec<RootRecipe>, String> {
    let source: &[AbiRootRecipe] = unsafe { abi_slice(base, offset, count, "root recipes")? };
    let mut copied = Vec::with_capacity(count);
    for recipe in source {
        if recipe.deref_depth > MAX_DEREF_DEPTH {
            return Err(format!(
                "PC metadata root dereference depth for function {function_entry:#x} is too large"
            ));
        }
        copied.push(RootRecipe {
            offset: recipe.offset,
            deref_depth: recipe.deref_depth,
        });
    }
    Ok(copied)
}

unsafe fn copy_roots(
    base: usize,
    offset: i64,
    count: usize,
    function_entry: usize,
) -> Result<Vec<RootLocation>, String> {
    let source: &[AbiRootLocation] = unsafe { abi_slice(base, offset, count, "root table")? };
    let mut copied = Vec::with_capacity(count);
    for root in source {
        if root.storage_deref_depth > MAX_DEREF_DEPTH {
            return Err(format!(
                "PC metadata storage dereference depth for function {function_entry:#x} is too large"
            ));
        }
        let recipe_count = root.recipe_count as usize;
        if recipe_count > MAX_RECIPES_PER_ROOT {
            return Err(format!(
                "PC metadata recipes for function {function_entry:#x} exceed the limit"
            ));
        }
        copied.push(RootLocation {
            dwarf_register: root.dwarf_register,
            frame_offset: root.frame_offset,
            storage_deref_depth: root.storage_deref_depth,
            recipes: unsafe {
                copy_recipes(base, root.recipes_offset, recipe_count, function_entry)?
            },
        });
    }
    Ok(copied)
}

unsafe fn copy_frames(base: usize, offset: i64, count: usize) -> Result<Vec<LogicalFrame>, String> {
    let source: &[AbiLogicalFrame] =
        unsafe { abi_slice(base, offset, count, "logical frame table")? };
    let mut copied = Vec::with_capacity(count);
    for frame in source {
        copied.push(LogicalFrame {
            function: unsafe { copy_string(base, frame.function, "logical function")? },
            file: unsafe { copy_string(base, frame.file, "logical source file")? },
            line: frame.line,
            column: frame.column,
        });
    }
    Ok(copied)
}

unsafe fn index_module(module: &AbiMetadataModule) -> Result<Vec<PcFunction>, String> {
    validate_module_header(module)?;
    let base = module as *const AbiMetadataModule as usize;
    let function_count = module.function_count as usize;
    let functions: &[AbiFunction] = unsafe {
        abi_slice(
            base,
            module.functions_offset,
            function_count,
            "function table",
        )?
    };
    let mut indexed = Vec::with_capacity(function_count);
    for function in functions {
        let entry = relative_address(base, function.entry_offset, "function entry")?;
        if function.symbol.len == 0 {
            return Err("PC metadata function symbol is empty".into());
        }
        if function.symbol.len as usize > MAX_STRING_BYTES {
            return Err(format!(
                "PC metadata function symbol for {entry:#x} exceeds the string limit"
            ));
        }
        relative_address(base, function.symbol.data_offset, "function symbol")?;
        let record_count = function.record_count as usize;
        if record_count > MAX_RECORDS_PER_FUNCTION {
            return Err(format!(
                "PC metadata record count for function {entry:#x} is too large"
            ));
        }
        // Validate the relative range without reading or copying every record.
        let _: &[AbiRecord] =
            unsafe { abi_slice(base, function.records_offset, record_count, "record table")? };
        indexed.push(PcFunction {
            entry,
            stack_size: function.stack_size,
            module_base: base,
            records_offset: function.records_offset,
            record_count,
            symbol: function.symbol,
        });
    }
    Ok(indexed)
}

unsafe fn copy_record(
    function: &PcFunction,
    record: &AbiRecord,
    include_roots: bool,
    include_frames: bool,
) -> Result<PcRecord, String> {
    if !(1..=5).contains(&record.kind) {
        return Err(format!(
            "PC metadata record for function {:#x} has invalid kind",
            function.entry
        ));
    }
    let root_count = record.root_count as usize;
    if root_count > MAX_ROOTS_PER_RECORD {
        return Err(format!(
            "PC metadata roots for function {:#x} exceed the limit",
            function.entry
        ));
    }
    let frame_count = record.logical_frame_count as usize;
    if frame_count > MAX_FRAMES_PER_RECORD {
        return Err(format!(
            "PC metadata frames for function {:#x} exceed the limit",
            function.entry
        ));
    }
    Ok(PcRecord {
        pc_offset: record.pc_offset,
        kind: record.kind,
        roots: if include_roots {
            unsafe {
                copy_roots(
                    function.module_base,
                    record.roots_offset,
                    root_count,
                    function.entry,
                )?
            }
        } else {
            Vec::new()
        },
        logical_frames: if include_frames {
            unsafe {
                copy_frames(
                    function.module_base,
                    record.logical_frames_offset,
                    frame_count,
                )?
            }
        } else {
            Vec::new()
        },
    })
}

fn validate_module_header(module: &AbiMetadataModule) -> Result<(), String> {
    if module.version != PC_METADATA_SCHEMA_VERSION {
        return Err(format!(
            "PC metadata schema mismatch: runtime {}, module {}",
            PC_METADATA_SCHEMA_VERSION, module.version
        ));
    }
    if module.pointer_bytes as usize != std::mem::size_of::<usize>() {
        return Err(format!(
            "PC metadata pointer width mismatch: runtime {}, module {}",
            std::mem::size_of::<usize>(),
            module.pointer_bytes
        ));
    }
    if Some(module.architecture) != host_architecture() {
        return Err(format!(
            "PC metadata architecture {} does not match this runtime",
            module.architecture
        ));
    }
    let function_count = module.function_count as usize;
    if function_count > MAX_FUNCTIONS_PER_MODULE {
        return Err("PC metadata function count exceeds the runtime limit".into());
    }
    if function_count != 0 && module.functions_offset == 0 {
        return Err("PC metadata function table offset is zero".into());
    }
    Ok(())
}

fn registration_error(message: &str) -> ! {
    eprintln!("fatal: invalid compiler PC metadata: {message}");
    std::process::abort();
}

/// Register one immutable compiler PC table during process initialization.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt__pc_metadata_register(module: *const AbiMetadataModule) {
    let Some(module) = (unsafe { module.as_ref() }) else {
        registration_error("module pointer is null");
    };
    if let Err(message) = validate_module_header(module) {
        registration_error(&message);
    }
    let mut registry = registry().write().unwrap_or_else(|_| {
        registration_error("registry lock was poisoned");
    });
    let address = module as *const AbiMetadataModule as usize;
    if !registry.pending_modules.contains(&address) {
        registry.pending_modules.push(address);
    }
}

fn materialize_pending(registry: &mut Registry) {
    for address in std::mem::take(&mut registry.pending_modules) {
        let module = unsafe { &*(address as *const AbiMetadataModule) };
        let functions = match unsafe { index_module(module) } {
            Ok(functions) => functions,
            Err(message) => registration_error(&message),
        };
        registry.functions.extend(functions);
    }
    registry
        .functions
        .sort_unstable_by_key(|function| function.entry);
    for pair in registry.functions.windows(2) {
        if pair[0].entry == pair[1].entry {
            let previous =
                unsafe { copy_string(pair[0].module_base, pair[0].symbol, "function symbol") }
                    .unwrap_or_else(|_| "<invalid>".into());
            let current =
                unsafe { copy_string(pair[1].module_base, pair[1].symbol, "function symbol") }
                    .unwrap_or_else(|_| "<invalid>".into());
            registration_error(&format!(
                "function entry {:#x} is shared by '{previous}' and '{current}'",
                pair[0].entry
            ));
        }
    }
}

fn find_record<R>(
    registry: &Registry,
    pc: usize,
    include_roots: bool,
    include_frames: bool,
    use_record: impl FnOnce(&PcFunction, &PcRecord) -> R,
) -> Option<R> {
    let function_index = registry
        .functions
        .partition_point(|function| function.entry <= pc)
        .checked_sub(1)?;
    let function = &registry.functions[function_index];
    let offset = pc.checked_sub(function.entry)?;
    let offset = u32::try_from(offset).ok()?;
    let records: &[AbiRecord] = match unsafe {
        abi_slice(
            function.module_base,
            function.records_offset,
            function.record_count,
            "record table",
        )
    } {
        Ok(records) => records,
        Err(message) => registration_error(&message),
    };
    for pair in records.windows(2) {
        if pair[0].pc_offset >= pair[1].pc_offset {
            registration_error(&format!(
                "PC metadata records for function {:#x} are not strictly sorted",
                function.entry
            ));
        }
    }
    // Stack-map intrinsics are emitted immediately after calls. The native
    // unwinder reports the architectural return PC, while LLVM records the
    // intrinsic after any call-sequence cleanup instructions. Resolve that
    // return PC forward to the adjacent map rather than requiring equality.
    let index = records.partition_point(|record| record.pc_offset < offset);
    if index == records.len() {
        return None;
    }
    let record =
        match unsafe { copy_record(function, &records[index], include_roots, include_frames) } {
            Ok(record) => record,
            Err(message) => registration_error(&message),
        };
    Some(use_record(function, &record))
}

pub(crate) fn with_record_at_pc<R>(
    pc: usize,
    include_roots: bool,
    include_frames: bool,
    use_record: impl FnOnce(&PcFunction, &PcRecord) -> R,
) -> Option<R> {
    let registry_lock = registry();
    let registry = registry_lock.read().ok()?;
    if registry.pending_modules.is_empty() {
        return find_record(&registry, pc, include_roots, include_frames, use_record);
    }
    drop(registry);
    let mut registry = registry_lock.write().ok()?;
    materialize_pending(&mut registry);
    find_record(&registry, pc, include_roots, include_frames, use_record)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compiler_abi_layout_matches_64_bit_contract() {
        assert_eq!(std::mem::size_of::<AbiRootRecipe>(), 16);
        assert_eq!(std::mem::size_of::<AbiRootLocation>(), 24);
        assert_eq!(std::mem::size_of::<AbiString>(), 16);
        assert_eq!(std::mem::size_of::<AbiLogicalFrame>(), 40);
        assert_eq!(std::mem::size_of::<AbiRecord>(), 32);
        assert_eq!(std::mem::size_of::<AbiFunction>(), 48);
        assert_eq!(std::mem::size_of::<AbiMetadataModule>(), 24);
    }

    #[test]
    fn return_pc_lookup_resolves_forward_to_the_post_call_map() {
        let records = [AbiRecord {
            roots_offset: 0,
            logical_frames_offset: 0,
            pc_offset: 0x20,
            root_count: 0,
            logical_frame_count: 0,
            kind: 2,
            reserved: [0; 3],
        }];
        let anchor = 0_u8;
        let module_base = (&anchor as *const u8) as usize;
        let records_address = records.as_ptr() as usize;
        let records_offset = i64::try_from(records_address as i128 - module_base as i128).unwrap();
        let function = PcFunction {
            entry: 0x1000,
            stack_size: 32,
            module_base,
            records_offset,
            record_count: records.len(),
            symbol: AbiString {
                data_offset: 0,
                len: 0,
                reserved: 0,
            },
        };
        registry().write().unwrap().functions.push(function);
        assert!(with_record_at_pc(0x1020, false, false, |_, _| ()).is_some());
        assert!(with_record_at_pc(0x101c, false, false, |_, _| ()).is_some());
        assert!(with_record_at_pc(0x1021, false, false, |_, _| ()).is_none());
        registry()
            .write()
            .unwrap()
            .functions
            .retain(|function| function.entry != 0x1000);
    }
}
