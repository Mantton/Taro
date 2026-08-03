//! Registered compiler PC metadata.
//!
//! Generated sidecar objects expose this fixed C ABI only to their global
//! constructors. Registration copies every table into Rust-owned memory, so
//! stack walking never depends on unchecked compiler pointers beyond startup.

use std::{
    collections::BTreeMap,
    sync::{OnceLock, RwLock},
};

pub(crate) const PC_METADATA_SCHEMA_VERSION: u32 = 1;
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
    recipes: *const AbiRootRecipe,
    frame_offset: i32,
    recipe_count: u32,
    dwarf_register: u16,
    storage_deref_depth: u8,
    reserved: u8,
}

#[repr(C)]
#[derive(Clone, Copy)]
struct AbiString {
    data: *const u8,
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
    roots: *const AbiRootLocation,
    logical_frames: *const AbiLogicalFrame,
    pc_offset: u32,
    root_count: u32,
    logical_frame_count: u32,
    kind: u8,
    reserved: [u8; 3],
}

#[repr(C)]
struct AbiFunction {
    entry: *const u8,
    records: *const AbiRecord,
    symbol: AbiString,
    stack_size: u64,
    record_count: u32,
    reserved: u32,
}

#[repr(C)]
pub struct AbiMetadataModule {
    functions: *const AbiFunction,
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
    pub(crate) symbol: String,
    pub(crate) stack_size: u64,
    pub(crate) records: Vec<PcRecord>,
}

#[derive(Default)]
struct Registry {
    functions: BTreeMap<usize, PcFunction>,
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

unsafe fn abi_slice<'a, T>(pointer: *const T, count: usize, what: &str) -> Result<&'a [T], String> {
    if count == 0 {
        return Ok(&[]);
    }
    if pointer.is_null() {
        return Err(format!("PC metadata {what} pointer is null"));
    }
    Ok(unsafe { std::slice::from_raw_parts(pointer, count) })
}

unsafe fn copy_string(value: AbiString, what: &str) -> Result<String, String> {
    let len = value.len as usize;
    if len > MAX_STRING_BYTES {
        return Err(format!("PC metadata {what} exceeds the string limit"));
    }
    let bytes = unsafe { abi_slice(value.data, len, what)? };
    String::from_utf8(bytes.to_vec()).map_err(|_| format!("PC metadata {what} is not UTF-8"))
}

unsafe fn copy_module(module: &AbiMetadataModule) -> Result<Vec<PcFunction>, String> {
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
    let functions = unsafe { abi_slice(module.functions, function_count, "function table")? };
    let mut copied = Vec::with_capacity(function_count);
    for function in functions {
        let entry = function.entry as usize;
        if entry == 0 {
            return Err("PC metadata function entry is null".into());
        }
        let symbol = unsafe { copy_string(function.symbol, "function symbol")? };
        if symbol.is_empty() {
            return Err("PC metadata function symbol is empty".into());
        }
        let record_count = function.record_count as usize;
        if record_count > MAX_RECORDS_PER_FUNCTION {
            return Err(format!(
                "PC metadata record count for '{symbol}' is too large"
            ));
        }
        let records = unsafe { abi_slice(function.records, record_count, "record table")? };
        let mut copied_records = Vec::with_capacity(record_count);
        let mut previous_offset = None;
        for record in records {
            if previous_offset.is_some_and(|offset| offset >= record.pc_offset) {
                return Err(format!(
                    "PC metadata records for '{symbol}' are not strictly sorted"
                ));
            }
            previous_offset = Some(record.pc_offset);
            if !(1..=5).contains(&record.kind) {
                return Err(format!(
                    "PC metadata record for '{symbol}' has invalid kind"
                ));
            }
            let root_count = record.root_count as usize;
            if root_count > MAX_ROOTS_PER_RECORD {
                return Err(format!("PC metadata roots for '{symbol}' exceed the limit"));
            }
            let roots = unsafe { abi_slice(record.roots, root_count, "root table")? };
            let mut copied_roots = Vec::with_capacity(root_count);
            for root in roots {
                if root.storage_deref_depth > MAX_DEREF_DEPTH {
                    return Err(format!(
                        "PC metadata storage dereference depth for '{symbol}' is too large"
                    ));
                }
                let recipe_count = root.recipe_count as usize;
                if recipe_count > MAX_RECIPES_PER_ROOT {
                    return Err(format!(
                        "PC metadata recipes for '{symbol}' exceed the limit"
                    ));
                }
                let recipes = unsafe { abi_slice(root.recipes, recipe_count, "root recipes")? };
                let mut copied_recipes = Vec::with_capacity(recipe_count);
                for recipe in recipes {
                    if recipe.deref_depth > MAX_DEREF_DEPTH {
                        return Err(format!(
                            "PC metadata root dereference depth for '{symbol}' is too large"
                        ));
                    }
                    copied_recipes.push(RootRecipe {
                        offset: recipe.offset,
                        deref_depth: recipe.deref_depth,
                    });
                }
                copied_roots.push(RootLocation {
                    dwarf_register: root.dwarf_register,
                    frame_offset: root.frame_offset,
                    storage_deref_depth: root.storage_deref_depth,
                    recipes: copied_recipes,
                });
            }

            let frame_count = record.logical_frame_count as usize;
            if frame_count > MAX_FRAMES_PER_RECORD {
                return Err(format!(
                    "PC metadata frames for '{symbol}' exceed the limit"
                ));
            }
            let frames =
                unsafe { abi_slice(record.logical_frames, frame_count, "logical frame table")? };
            let mut copied_frames = Vec::with_capacity(frame_count);
            for frame in frames {
                copied_frames.push(LogicalFrame {
                    function: unsafe { copy_string(frame.function, "logical function")? },
                    file: unsafe { copy_string(frame.file, "logical source file")? },
                    line: frame.line,
                    column: frame.column,
                });
            }
            copied_records.push(PcRecord {
                pc_offset: record.pc_offset,
                kind: record.kind,
                roots: copied_roots,
                logical_frames: copied_frames,
            });
        }
        copied.push(PcFunction {
            entry,
            symbol,
            stack_size: function.stack_size,
            records: copied_records,
        });
    }
    Ok(copied)
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
    let functions = match unsafe { copy_module(module) } {
        Ok(functions) => functions,
        Err(message) => registration_error(&message),
    };
    let mut registry = registry().write().unwrap_or_else(|_| {
        registration_error("registry lock was poisoned");
    });
    for function in functions {
        match registry.functions.get(&function.entry) {
            Some(previous) if previous == &function => {}
            Some(previous) => registration_error(&format!(
                "function entry {:#x} is shared by '{}' and '{}'",
                function.entry, previous.symbol, function.symbol
            )),
            None => {
                registry.functions.insert(function.entry, function);
            }
        }
    }
}

pub(crate) fn with_record_at_pc<R>(
    pc: usize,
    use_record: impl FnOnce(&PcFunction, &PcRecord) -> R,
) -> Option<R> {
    let registry = registry().read().ok()?;
    let (_, function) = registry.functions.range(..=pc).next_back()?;
    let offset = pc.checked_sub(function.entry)?;
    let offset = u32::try_from(offset).ok()?;
    // Stack-map intrinsics are emitted immediately after calls. The native
    // unwinder reports the architectural return PC, while LLVM records the
    // intrinsic after any call-sequence cleanup instructions. Resolve that
    // return PC forward to the adjacent map rather than requiring equality.
    let index = function
        .records
        .partition_point(|record| record.pc_offset < offset);
    if index == function.records.len() {
        return None;
    }
    Some(use_record(function, &function.records[index]))
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
        let function = PcFunction {
            entry: 0x1000,
            symbol: "lookup_probe".into(),
            stack_size: 32,
            records: vec![PcRecord {
                pc_offset: 0x20,
                kind: 2,
                roots: Vec::new(),
                logical_frames: Vec::new(),
            }],
        };
        registry()
            .write()
            .unwrap()
            .functions
            .insert(function.entry, function);
        assert!(with_record_at_pc(0x1020, |_, _| ()).is_some());
        assert!(with_record_at_pc(0x101c, |_, _| ()).is_some());
        assert!(with_record_at_pc(0x1021, |_, _| ()).is_none());
        registry().write().unwrap().functions.remove(&0x1000);
    }
}
