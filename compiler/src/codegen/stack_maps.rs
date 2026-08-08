//! Parsing and normalization inputs for LLVM's machine stack-map section.
//!
//! LLVM's raw section is deliberately confined to the compiler. The runtime
//! consumes only Taro's versioned PC metadata, which is built from these owned
//! records after machine-code emission.

use serde::{Deserialize, Serialize};
use std::{
    borrow::Cow,
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
    ptr::NonNull,
    slice,
};

use super::pc_metadata::{
    PcArchitecture, PcFunction, PcLogicalFrame, PcMetadata, PcRecord, PcRootLocation,
    PcSafepointSelector,
};

pub(crate) const DESCRIPTOR_SCHEMA_VERSION: u32 = 3;
pub(crate) const PC_METADATA_SCHEMA_VERSION: u32 = 4;

/// Kind of machine site represented by a PC record.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[repr(u8)]
pub(crate) enum StackMapSiteKind {
    Poll = 1,
    Call = 2,
    Allocation = 3,
    Blocking = 4,
    Panic = 5,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[repr(u8)]
pub(crate) enum GcLayoutKind {
    Pointer = 1,
    Reference = 2,
    Aggregate = 3,
    Repeat = 4,
    Tagged = 5,
}

/// One node in the shared stack/heap/static GC layout graph.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[repr(C)]
pub(crate) struct GcLayoutNode {
    pub offset: u64,
    pub stride: u64,
    pub first_child: u32,
    pub child_count: u32,
    pub kind: GcLayoutKind,
    pub width: u8,
}

/// Typed layout associated with one LLVM stack-map operand.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct PendingRootOperand {
    /// Number of pointer loads needed to turn the direct machine location into
    /// the MIR local's storage address. Indirect ABI storage uses one.
    pub storage_deref_depth: u8,
    pub nodes: Vec<GcLayoutNode>,
}

/// A logical Taro frame to render for a PC, innermost first.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct PendingLogicalFrame {
    pub function: String,
    pub file: String,
    pub line: u32,
    pub column: u32,
}

/// Compiler meaning associated with one raw LLVM stack-map ID.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct PendingStackMapRecord {
    pub id: u64,
    pub emitted_function: String,
    pub kind: StackMapSiteKind,
    pub selector_value: u64,
    pub roots: Vec<PendingRootOperand>,
    pub logical_frames: Vec<PendingLogicalFrame>,
}

/// Package sidecar retained beside object or bitcode artifacts until machine
/// records can be normalized.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct PendingStackMapModule {
    pub schema_version: u32,
    pub target_triple: String,
    pub records: Vec<PendingStackMapRecord>,
}

impl PendingStackMapModule {
    pub fn new(target_triple: String, records: Vec<PendingStackMapRecord>) -> Self {
        Self {
            schema_version: DESCRIPTOR_SCHEMA_VERSION,
            target_triple,
            records,
        }
    }
}

/// Stable map ID for one site in a pre-optimization LLVM function.
///
/// LLVM may duplicate the intrinsic while inlining. Duplicate machine records
/// intentionally retain the same ID and therefore the same root layouts.
pub(crate) fn deterministic_map_id(
    package_identifier: &str,
    function_symbol: &str,
    ordinal: u64,
) -> u64 {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"taro-stack-map-id-v1\0");
    hasher.update(package_identifier.as_bytes());
    hasher.update(&[0]);
    hasher.update(function_symbol.as_bytes());
    hasher.update(&[0]);
    hasher.update(&ordinal.to_le_bytes());
    let mut bytes = [0u8; 8];
    bytes.copy_from_slice(&hasher.finalize().as_bytes()[..8]);
    u64::from_le_bytes(bytes)
}

pub(crate) fn write_pending_module(
    path: &Path,
    module: &PendingStackMapModule,
) -> Result<(), String> {
    let encoded = bincode::serialize(module)
        .map_err(|error| format!("failed to encode stack-map descriptors: {error}"))?;
    fs::write(path, encoded).map_err(|error| {
        format!(
            "failed to write stack-map descriptors '{}': {error}",
            path.display()
        )
    })
}

pub(crate) fn read_pending_modules(
    paths: impl IntoIterator<Item = PathBuf>,
    expected_triple: &str,
) -> Result<BTreeMap<u64, PendingStackMapRecord>, String> {
    let mut records = BTreeMap::new();
    for path in paths {
        let bytes = fs::read(&path).map_err(|error| {
            format!(
                "failed to read stack-map descriptors '{}': {error}",
                path.display()
            )
        })?;
        let module: PendingStackMapModule = bincode::deserialize(&bytes).map_err(|error| {
            format!(
                "failed to decode stack-map descriptors '{}': {error}",
                path.display()
            )
        })?;
        if module.schema_version != DESCRIPTOR_SCHEMA_VERSION {
            return Err(format!(
                "stack-map descriptor schema mismatch in '{}': {}",
                path.display(),
                module.schema_version
            ));
        }
        if module.target_triple != expected_triple {
            return Err(format!(
                "stack-map descriptor target mismatch in '{}': expected '{}', found '{}'",
                path.display(),
                expected_triple,
                module.target_triple
            ));
        }
        for record in module.records {
            if let Some(previous) = records.insert(record.id, record.clone())
                && previous != record
            {
                return Err(format!(
                    "stack-map ID {:#018x} has conflicting compiler descriptors",
                    record.id
                ));
            }
        }
    }
    Ok(records)
}

/// Validate path-discriminated records in one physical machine function.
///
/// A union is not safe for typed roots: an inactive enum or reference layout
/// may interpret storage initialized for another path. Each source site writes
/// a distinct selector value instead. Every record must retain the same
/// physical selector slot, equal-PC alternatives must use distinct values, and
/// LLVM machine duplicates of one source selector must preserve GC semantics.
fn validate_record_selectors(function: &PcFunction) -> Result<(), String> {
    if let Some(first) = function.records.first() {
        for record in &function.records[1..] {
            if record.selector.dwarf_register != first.selector.dwarf_register
                || record.selector.frame_offset != first.selector.frame_offset
            {
                return Err(format!(
                    "function '{}' has stack maps with different selector locations",
                    function.symbol
                ));
            }
        }
    }
    let mut sites = BTreeMap::<u64, &PcRecord>::new();
    for record in &function.records {
        if let Some(previous) = sites.insert(record.selector.value, record)
            && (previous.kind != record.kind
                || previous.roots != record.roots
                || previous.logical_frames != record.logical_frames)
        {
            return Err(format!(
                "function '{}' has machine duplicates of selector {} with different GC semantics",
                function.symbol, record.selector.value
            ));
        }
    }
    for group in function
        .records
        .chunk_by(|left, right| left.pc_offset == right.pc_offset)
    {
        let Some(first) = group.first() else {
            continue;
        };
        for (index, record) in group.iter().enumerate() {
            if group[..index]
                .iter()
                .any(|previous| previous.selector.value == record.selector.value)
            {
                return Err(format!(
                    "function '{}' has duplicate selector value {} at stack-map offset {}",
                    function.symbol, record.selector.value, first.pc_offset
                ));
            }
        }
    }
    Ok(())
}

/// Join LLVM's target-specific records to compiler descriptors and reject any
/// machine location the runtime could not evaluate precisely.
pub(crate) fn normalize_object(
    object: &Path,
    descriptor_paths: impl IntoIterator<Item = PathBuf>,
    expected_triple: &str,
) -> Result<PcMetadata, String> {
    let descriptors = read_pending_modules(descriptor_paths, expected_triple)?;
    let architecture = PcArchitecture::from_target_triple(expected_triple)?;
    let raw = match parse_object(object) {
        Ok(raw) => Some(raw),
        Err(error) if error.contains("does not contain an LLVM stack map section") => None,
        Err(error) => return Err(error),
    };
    let Some(raw) = raw else {
        return Ok(PcMetadata {
            version: PC_METADATA_SCHEMA_VERSION,
            architecture,
            pointer_bytes: architecture.pointer_bytes(),
            functions: Vec::new(),
        });
    };

    if !architecture.matches_llvm_name(&raw.architecture) {
        return Err(format!(
            "stack-map architecture mismatch: target '{}' produced '{}'",
            expected_triple, raw.architecture
        ));
    }
    if raw.pointer_bytes != architecture.pointer_bytes() {
        return Err(format!(
            "stack-map pointer width mismatch: target '{}' uses {} bytes, object reports {}",
            expected_triple,
            architecture.pointer_bytes(),
            raw.pointer_bytes
        ));
    }

    let mut functions: BTreeMap<String, PcFunction> = BTreeMap::new();
    for raw_record in &raw.records {
        let descriptor = descriptors.get(&raw_record.id).ok_or_else(|| {
            format!(
                "LLVM stack-map ID {:#018x} has no compiler descriptor",
                raw_record.id
            )
        })?;
        // The record is attributed to whichever function LLVM finally placed it
        // in, which is not always the one it was emitted into: inlining moves a
        // site into its caller, and duplicates it once per call site. The
        // descriptor supplies what the site *means* — its kind, its root
        // layout, the Taro frames it stands for — and that travels with the ID
        // wherever the code goes, so only the placement has to come from LLVM.
        let raw_function = &raw.functions[raw_record.function_index];
        if raw_record.locations.len() != descriptor.roots.len().saturating_add(1) {
            return Err(format!(
                "stack-map ID {:#018x} operand count mismatch: compiler described one selector and {} roots, LLVM emitted {} locations",
                raw_record.id,
                descriptor.roots.len(),
                raw_record.locations.len()
            ));
        }

        let selector_location = &raw_record.locations[0];
        if selector_location.kind != RawStackMapLocationKind::Direct {
            return Err(format!(
                "stack-map ID {:#018x} selector used {:?}; a direct frame location is required",
                raw_record.id, selector_location.kind
            ));
        }
        if selector_location.size != u16::from(raw.pointer_bytes) {
            return Err(format!(
                "stack-map ID {:#018x} selector has size {}, expected {}",
                raw_record.id, selector_location.size, raw.pointer_bytes
            ));
        }
        if !architecture.supports_dwarf_base_register(selector_location.dwarf_register) {
            return Err(format!(
                "stack-map ID {:#018x} selector uses unsupported DWARF base register {} for {:?}",
                raw_record.id, selector_location.dwarf_register, architecture
            ));
        }
        let selector = PcSafepointSelector {
            dwarf_register: selector_location.dwarf_register,
            frame_offset: i32::try_from(selector_location.value).map_err(|_| {
                format!(
                    "stack-map ID {:#018x} selector frame offset {} exceeds the PC metadata ABI",
                    raw_record.id, selector_location.value
                )
            })?,
            value: descriptor.selector_value,
        };

        let roots = raw_record
            .locations
            .iter()
            .skip(1)
            .zip(&descriptor.roots)
            .map(|(location, operand)| {
                if location.kind != RawStackMapLocationKind::Direct {
                    return Err(format!(
                        "stack-map ID {:#018x} root used {:?}; a direct frame location is required",
                        raw_record.id, location.kind
                    ));
                }
                if location.size != u16::from(raw.pointer_bytes) {
                    return Err(format!(
                        "stack-map ID {:#018x} root has size {}, expected {}",
                        raw_record.id, location.size, raw.pointer_bytes
                    ));
                }
                if !architecture.supports_dwarf_base_register(location.dwarf_register) {
                    return Err(format!(
                        "stack-map ID {:#018x} uses unsupported DWARF base register {} for {:?}",
                        raw_record.id, location.dwarf_register, architecture
                    ));
                }
                let frame_offset = i32::try_from(location.value).map_err(|_| {
                    format!(
                        "stack-map ID {:#018x} frame offset {} exceeds the PC metadata ABI",
                        raw_record.id, location.value
                    )
                })?;
                Ok(PcRootLocation {
                    dwarf_register: location.dwarf_register,
                    frame_offset,
                    storage_deref_depth: operand.storage_deref_depth,
                    nodes: operand.nodes.clone(),
                })
            })
            .collect::<Result<Vec<_>, String>>()?;
        let logical_frames = descriptor
            .logical_frames
            .iter()
            .map(|frame| PcLogicalFrame {
                function: frame.function.clone(),
                file: frame.file.clone(),
                line: frame.line,
                column: frame.column,
            })
            .collect();
        let record = PcRecord {
            pc_offset: raw_record.instruction_offset,
            kind: descriptor.kind,
            selector,
            roots,
            logical_frames,
        };
        let code_size = u32::try_from(raw_function.code_size).map_err(|_| {
            format!(
                "LLVM function '{}' is {} bytes, exceeding the PC metadata ABI",
                raw_function.symbol, raw_function.code_size
            )
        })?;
        if code_size == 0 {
            return Err(format!(
                "LLVM reported a zero code size for '{}'",
                raw_function.symbol
            ));
        }
        if raw_record.instruction_offset >= code_size {
            return Err(format!(
                "stack-map ID {:#018x} lies outside function '{}' (offset {}, size {})",
                raw_record.id, raw_function.symbol, raw_record.instruction_offset, code_size
            ));
        }
        let function = functions
            .entry(raw_function.symbol.clone())
            .or_insert_with(|| PcFunction {
                symbol: raw_function.symbol.clone(),
                stack_size: raw_function.stack_size,
                code_size,
                records: Vec::new(),
            });
        if function.stack_size != raw_function.stack_size || function.code_size != code_size {
            return Err(format!(
                "LLVM reported conflicting machine bounds for '{}'",
                raw_function.symbol
            ));
        }
        function.records.push(record);
    }

    for function in functions.values_mut() {
        function
            .records
            .sort_by_key(|record| (record.pc_offset, record.selector.value));
        function.records.dedup();
        validate_record_selectors(function)?;
    }

    Ok(PcMetadata {
        version: PC_METADATA_SCHEMA_VERSION,
        architecture,
        pointer_bytes: raw.pointer_bytes,
        functions: functions.into_values().collect(),
    })
}

#[repr(C)]
struct NativeParsedStackMap {
    _private: [u8; 0],
}

#[repr(C)]
struct NativeObjectRewrite {
    _private: [u8; 0],
}

unsafe extern "C" {
    fn taro_stack_map_parse_object(
        path: *const u8,
        path_length: usize,
    ) -> *mut NativeParsedStackMap;
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
    fn taro_stack_map_function_code_size(
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
    fn taro_stack_map_strip_object(
        input_path: *const u8,
        input_path_length: usize,
        output_path: *const u8,
        output_path_length: usize,
    ) -> *mut NativeObjectRewrite;
    fn taro_object_rewrite_dispose(result: *mut NativeObjectRewrite);
    fn taro_object_rewrite_is_valid(result: *const NativeObjectRewrite) -> bool;
    fn taro_object_rewrite_error(
        result: *const NativeObjectRewrite,
        length: *mut usize,
    ) -> *const u8;
}

struct NativeStackMap(NonNull<NativeParsedStackMap>);

impl NativeStackMap {
    fn parse(path: &Path) -> Result<Self, String> {
        let bytes = path_bytes(path)?;
        let parsed =
            NonNull::new(unsafe { taro_stack_map_parse_object(bytes.as_ptr(), bytes.len()) })
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

struct NativeRewrite(NonNull<NativeObjectRewrite>);

impl NativeRewrite {
    fn strip(input: &Path, output: &Path) -> Result<Self, String> {
        let input = path_bytes(input)?;
        let output = path_bytes(output)?;
        let rewritten = NonNull::new(unsafe {
            taro_stack_map_strip_object(input.as_ptr(), input.len(), output.as_ptr(), output.len())
        })
        .ok_or_else(|| "LLVM failed to allocate an object rewrite result".to_owned())?;
        let rewritten = Self(rewritten);
        if !unsafe { taro_object_rewrite_is_valid(rewritten.0.as_ptr()) } {
            return Err(read_native_string(|length| unsafe {
                taro_object_rewrite_error(rewritten.0.as_ptr(), length)
            })
            .unwrap_or_else(|error| format!("LLVM failed to strip stack-map data ({error})")));
        }
        Ok(rewritten)
    }
}

impl Drop for NativeRewrite {
    fn drop(&mut self) {
        unsafe { taro_object_rewrite_dispose(self.0.as_ptr()) };
    }
}

/// One machine function represented in an LLVM stack-map section.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RawStackMapFunction {
    pub symbol: String,
    pub stack_size: u64,
    pub code_size: u64,
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
            _ => Err(format!(
                "LLVM emitted unknown stack-map location kind {value}"
            )),
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
    let architecture =
        read_native_string(|length| unsafe { taro_stack_map_architecture(pointer, length) })?;
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
            return Err(format!(
                "LLVM stack-map function {index} has an empty symbol"
            ));
        }
        functions.push(RawStackMapFunction {
            symbol,
            stack_size: unsafe { taro_stack_map_function_stack_size(pointer, index) },
            code_size: unsafe { taro_stack_map_function_code_size(pointer, index) },
            record_start: unsafe { taro_stack_map_function_record_start(pointer, index) },
            record_count: unsafe { taro_stack_map_function_record_count(pointer, index) },
        });
    }

    let record_count = unsafe { taro_stack_map_record_count(pointer) };
    let mut records = Vec::with_capacity(record_count);
    for record_index in 0..record_count {
        let function_index = unsafe { taro_stack_map_record_function_index(pointer, record_index) };
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
                    taro_stack_map_location_dwarf_register(pointer, record_index, location_index)
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

/// Remove LLVM's implementation-specific stack-map section after it has been
/// normalized into Taro's stable sidecar ABI.
///
/// Rewriting to a sibling first keeps the original object intact if LLVM
/// rejects the input or the output cannot be flushed.
pub(crate) fn strip_object(path: &Path) -> Result<(), String> {
    let temporary = path.with_extension("stackmap-strip.tmp");
    let result = NativeRewrite::strip(path, &temporary);
    if let Err(error) = result {
        let _ = fs::remove_file(&temporary);
        return Err(format!(
            "failed to strip raw LLVM stack maps from '{}': {error}",
            path.display()
        ));
    }
    fs::rename(&temporary, path).map_err(|error| {
        let _ = fs::remove_file(&temporary);
        format!(
            "failed to replace '{}' with its stripped object: {error}",
            path.display()
        )
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
    use super::{
        PcFunction, PcRecord, PcSafepointSelector, RawStackMapLocationKind, StackMapSiteKind,
        parse_object, strip_object, validate_record_selectors,
    };
    use inkwell::{
        OptimizationLevel,
        context::Context,
        memory_buffer::MemoryBuffer,
        passes::PassBuilderOptions,
        targets::{CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetTriple},
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
                .run_passes("default<O2>", &machine, PassBuilderOptions::create())
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
        assert!(parsed.functions[0].code_size > 0);
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
    fn same_pc_records_remain_path_distinct() {
        let record = |value| PcRecord {
            pc_offset: 12,
            kind: StackMapSiteKind::Call,
            selector: PcSafepointSelector {
                dwarf_register: 29,
                frame_offset: -8,
                value,
            },
            roots: Vec::new(),
            logical_frames: Vec::new(),
        };
        let function = PcFunction {
            symbol: "same_pc".into(),
            stack_size: 32,
            code_size: 64,
            records: vec![record(1), record(2)],
        };

        validate_record_selectors(&function).expect("distinct selectors are path-safe");
        assert_eq!(function.records.len(), 2);
    }

    #[test]
    fn same_pc_records_reject_different_selector_slots() {
        let mut function = PcFunction {
            symbol: "bad_same_pc".into(),
            stack_size: 32,
            code_size: 64,
            records: vec![
                PcRecord {
                    pc_offset: 12,
                    kind: StackMapSiteKind::Call,
                    selector: PcSafepointSelector {
                        dwarf_register: 29,
                        frame_offset: -8,
                        value: 1,
                    },
                    roots: Vec::new(),
                    logical_frames: Vec::new(),
                },
                PcRecord {
                    pc_offset: 12,
                    kind: StackMapSiteKind::Call,
                    selector: PcSafepointSelector {
                        dwarf_register: 29,
                        frame_offset: -16,
                        value: 2,
                    },
                    roots: Vec::new(),
                    logical_frames: Vec::new(),
                },
            ],
        };
        function
            .records
            .sort_by_key(|record| (record.pc_offset, record.selector.value));

        assert!(validate_record_selectors(&function).is_err());
    }

    #[test]
    fn machine_duplicates_reject_changed_gc_semantics() {
        let record = |pc_offset, kind| PcRecord {
            pc_offset,
            kind,
            selector: PcSafepointSelector {
                dwarf_register: 29,
                frame_offset: -8,
                value: 1,
            },
            roots: Vec::new(),
            logical_frames: Vec::new(),
        };
        let function = PcFunction {
            symbol: "bad_duplicate".into(),
            stack_size: 32,
            code_size: 64,
            records: vec![
                record(12, StackMapSiteKind::Call),
                record(24, StackMapSiteKind::Poll),
            ],
        };

        let error = validate_record_selectors(&function).unwrap_err();
        assert!(error.contains("different GC semantics"));
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

    #[test]
    fn strips_normalized_sections_from_elf_and_macho_objects() {
        let directory = TestDirectory::new();
        for (triple, name) in [
            ("x86_64-unknown-linux-gnu", "strip-elf"),
            ("aarch64-apple-darwin", "strip-macho"),
        ] {
            let object = emit_probe_object(triple, OptimizationLevel::Default, &directory, name);
            assert!(parse_object(&object).is_ok());
            strip_object(&object).expect("strip raw stack-map section");
            let error = parse_object(&object).expect_err("stripped section must be absent");
            assert!(error.contains("does not contain an LLVM stack map section"));
        }
    }
}
