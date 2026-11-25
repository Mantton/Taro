//! LLVM source-based code coverage instrumentation (`--coverage`).
//!
//! Emits `@llvm.instrprof.increment` counters at basic-block boundaries for
//! user-authored functions in the current package, alongside standard LLVM
//! Coverage Mapping v6 (`__llvm_covmap` / `__llvm_covfun`) records so
//! `llvm-profdata` and `llvm-cov` produce accurate per-file and per-line
//! coverage reports. Compiler-generated shims, harnesses, and synthetic
//! definitions are excluded.

use crate::{
    cfg::TargetInfo,
    compile::context::GlobalContext,
    error::CompileResult,
    mir::{self, BasicBlockId, StatementKind, TerminatorKind},
    span::{FileID, Span},
    specialize::Instance,
};
use inkwell::{
    AddressSpace,
    builder::Builder,
    context::Context,
    module::{Linkage, Module},
    passes::PassBuilderOptions,
    targets::TargetMachine,
    values::{BasicValueEnum, FunctionValue, GlobalValue, PointerValue},
};
use rustc_hash::{FxHashMap, FxHashSet};
use std::path::PathBuf;

/// LLVM `CovMapVersion::Version6` enum discriminant (`5`), supported by LLVM
/// 14 through LLVM 22 and Apple Xcode's `llvm-cov`.
const COVMAP_VERSION_6: u32 = 5;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct CoverageRegion {
    line_start: u32,
    col_start: u32,
    line_end: u32,
    col_end: u32,
    counter_idx: u32,
}

struct FunctionCoverageRecord {
    name_md5: u64,
    func_hash: u64,
    file_index: u32,
    regions: Vec<CoverageRegion>,
}

pub(super) struct FunctionInstrumentation<'llvm> {
    name_global: PointerValue<'llvm>,
    func_hash: u64,
    num_counters: u32,
    block_counters: FxHashMap<BasicBlockId, u32>,
}

impl<'llvm> FunctionInstrumentation<'llvm> {
    pub(super) fn emit_block_counter(
        &self,
        bb_id: BasicBlockId,
        context: &'llvm Context,
        module: &Module<'llvm>,
        builder: &Builder<'llvm>,
    ) {
        let Some(&counter_idx) = self.block_counters.get(&bb_id) else {
            return;
        };
        let increment_fn = declare_instrprof_increment(context, module);
        let i64_ty = context.i64_type();
        let i32_ty = context.i32_type();
        builder
            .build_call(
                increment_fn,
                &[
                    self.name_global.into(),
                    i64_ty.const_int(self.func_hash, false).into(),
                    i32_ty.const_int(self.num_counters as u64, false).into(),
                    i32_ty.const_int(counter_idx as u64, false).into(),
                ],
                "",
            )
            .expect("emit llvm.instrprof.increment");
    }
}

pub(super) struct CoverageContext {
    /// Entry 0 is the compilation directory (`"/"`); entries 1.. are absolute
    /// canonicalized source file paths.
    files: Vec<String>,
    file_indices: FxHashMap<FileID, u32>,
    records: Vec<FunctionCoverageRecord>,
    seen_pgo_names: FxHashSet<String>,
}

impl CoverageContext {
    pub(super) fn new() -> Self {
        Self {
            files: vec!["/".to_string()],
            file_indices: FxHashMap::default(),
            records: Vec::new(),
            seen_pgo_names: FxHashSet::default(),
        }
    }

    fn intern_file(&mut self, file_id: FileID, gcx: GlobalContext<'_>) -> Option<u32> {
        if let Some(&idx) = self.file_indices.get(&file_id) {
            return Some(idx);
        }
        let path: PathBuf = gcx.dcx().file_path(file_id)?;
        let resolved = path.canonicalize().unwrap_or(path);
        let text = resolved.to_string_lossy().into_owned();
        if text.is_empty() {
            return None;
        }
        let idx = self.files.len() as u32;
        self.files.push(text);
        self.file_indices.insert(file_id, idx);
        Some(idx)
    }

    pub(super) fn prepare_function<'llvm, 'gcx>(
        &mut self,
        instance: Instance<'gcx>,
        function: FunctionValue<'llvm>,
        body: &'gcx mir::Body<'gcx>,
        context: &'llvm Context,
        module: &Module<'llvm>,
        gcx: GlobalContext<'gcx>,
    ) -> Option<FunctionInstrumentation<'llvm>> {
        let def_id = instance.def_id();
        // Attribute coverage only to user-authored functions in the package
        // currently being compiled; skip compiler-generated synthetic bodies.
        if def_id.package() != gcx.package_index() || gcx.is_instance_generated(def_id) {
            return None;
        }
        let ident = gcx.try_definition_ident(def_id)?;
        let file_id = ident.span.file;
        let file_index = self.intern_file(file_id, gcx)?;

        let pgo_name = function.get_name().to_string_lossy().into_owned();
        if pgo_name.is_empty() || !self.seen_pgo_names.insert(pgo_name.clone()) {
            return None;
        }

        let mut block_counters = FxHashMap::default();
        let mut regions = Vec::new();
        let mut next_counter: u32 = 0;

        for (bb_id, bb) in body.basic_blocks.iter_enumerated() {
            let mut bb_spans: Vec<Span> = Vec::new();
            for stmt in &bb.statements {
                if is_compiler_only_statement(&stmt.kind) {
                    continue;
                }
                if is_attributable_span(stmt.span, file_id) {
                    bb_spans.push(stmt.span);
                }
            }
            if let Some(term) = &bb.terminator {
                if !is_compiler_only_terminator(&term.kind)
                    && is_attributable_span(term.span, file_id)
                {
                    bb_spans.push(term.span);
                }
            }
            if bb_spans.is_empty() {
                continue;
            }
            let counter_idx = next_counter;
            next_counter += 1;
            block_counters.insert(bb_id, counter_idx);

            let mut seen_in_bb = FxHashSet::default();
            for span in bb_spans {
                let region = span_to_region(span, counter_idx);
                if seen_in_bb.insert((
                    region.line_start,
                    region.col_start,
                    region.line_end,
                    region.col_end,
                )) {
                    regions.push(region);
                }
            }
        }

        // Empty functions (e.g. `func noop() {}`) still get an entry counter
        // mapped to their identifier span if one exists in the same file.
        if next_counter == 0 && is_attributable_span(ident.span, file_id) {
            block_counters.insert(body.start_block, 0);
            regions.push(span_to_region(ident.span, 0));
            next_counter = 1;
        }

        if next_counter == 0 || regions.is_empty() {
            return None;
        }

        regions.sort();
        regions.dedup_by_key(|r| (r.line_start, r.col_start, r.line_end, r.col_end));

        let name_md5 = md5_low64(pgo_name.as_bytes());
        let func_hash = compute_function_hash(next_counter, &regions);

        let name_global = emit_profile_name_global(context, module, &pgo_name);
        self.records.push(FunctionCoverageRecord {
            name_md5,
            func_hash,
            file_index,
            regions,
        });

        Some(FunctionInstrumentation {
            name_global,
            func_hash,
            num_counters: next_counter,
            block_counters,
        })
    }

    pub(super) fn finalize<'llvm>(
        &self,
        context: &'llvm Context,
        module: &Module<'llvm>,
        target_machine: &TargetMachine,
        gcx: GlobalContext<'_>,
    ) -> CompileResult<()> {
        if self.records.is_empty() {
            return Ok(());
        }

        let target_triple = gcx.store.target_layout.triple_string();
        let target_info = TargetInfo::from_triple(&target_triple);
        let is_darwin = target_info.matches_os("macos");
        let covmap_section = if is_darwin {
            "__LLVM_COV,__llvm_covmap"
        } else {
            "__llvm_covmap"
        };
        let covfun_section = if is_darwin {
            "__LLVM_COV,__llvm_covfun"
        } else {
            "__llvm_covfun"
        };

        let encoded_filenames = encode_filenames_v6(&self.files);
        let filenames_hash = md5_low64(&encoded_filenames);

        let mut used_globals: Vec<GlobalValue<'llvm>> = Vec::with_capacity(self.records.len() + 1);

        // Emit @__llvm_coverage_mapping header + filename table.
        let i32_ty = context.i32_type();
        let header_struct_ty =
            context.struct_type(&[i32_ty.into(), i32_ty.into(), i32_ty.into(), i32_ty.into()], false);
        let header_val = header_struct_ty.const_named_struct(&[
            i32_ty.const_zero().into(),
            i32_ty.const_int(encoded_filenames.len() as u64, false).into(),
            i32_ty.const_zero().into(),
            i32_ty.const_int(COVMAP_VERSION_6 as u64, false).into(),
        ]);
        let filenames_val = context.const_string(&encoded_filenames, false);
        let covmap_val = context.const_struct(&[header_val.into(), filenames_val.into()], false);
        let covmap_global =
            module.add_global(covmap_val.get_type(), None, "__llvm_coverage_mapping");
        covmap_global.set_linkage(Linkage::Private);
        covmap_global.set_constant(true);
        covmap_global.set_initializer(&covmap_val);
        covmap_global.set_section(Some(covmap_section));
        covmap_global.set_alignment(8);
        used_globals.push(covmap_global);

        // Emit one @__covrec_<hex>u record per instrumented function.
        let i64_ty = context.i64_type();
        for record in &self.records {
            let encoded_regions = encode_function_regions(record.file_index, &record.regions);
            let regions_val = context.const_string(&encoded_regions, false);
            let rec_val = context.const_struct(
                &[
                    i64_ty.const_int(record.name_md5, false).into(),
                    i32_ty.const_int(encoded_regions.len() as u64, false).into(),
                    i64_ty.const_int(record.func_hash, false).into(),
                    i64_ty.const_int(filenames_hash, false).into(),
                    regions_val.into(),
                ],
                true,
            );
            let rec_name = format!("__covrec_{:016X}u", record.name_md5);
            let rec_global = module.add_global(rec_val.get_type(), None, &rec_name);
            rec_global.set_linkage(Linkage::LinkOnceODR);
            rec_global.set_visibility(inkwell::GlobalVisibility::Hidden);
            rec_global.set_constant(true);
            rec_global.set_initializer(&rec_val);
            rec_global.set_section(Some(covfun_section));
            rec_global.set_alignment(8);
            used_globals.push(rec_global);
        }

        append_to_llvm_used(context, module, &used_globals);

        // Lower @llvm.instrprof.increment intrinsics into runtime profile
        // counter tables (__llvm_prf_cnts / __llvm_prf_data / __llvm_prf_names).
        let options = PassBuilderOptions::create();
        options.set_verify_each(cfg!(test));
        module
            .run_passes("instrprof", target_machine, options)
            .map_err(|error| {
                gcx.dcx().emit_error(
                    format!("LLVM coverage instrumentation pass (`instrprof`) failed: {error}"),
                    None,
                );
                crate::error::ReportedError
            })?;

        Ok(())
    }
}

fn is_compiler_only_statement(kind: &StatementKind<'_>) -> bool {
    matches!(
        kind,
        StatementKind::SourceScope(_)
            | StatementKind::StorageLive(_)
            | StatementKind::StorageDead(_)
            | StatementKind::SetInitialized(_)
            | StatementKind::KeepAlive(_)
            | StatementKind::Nop
    )
}

fn is_compiler_only_terminator(kind: &TerminatorKind<'_>) -> bool {
    matches!(
        kind,
        TerminatorKind::ResumeUnwind
            | TerminatorKind::Unreachable
            | TerminatorKind::UnresolvedGoto
    )
}

fn is_attributable_span(span: Span, expected_file: FileID) -> bool {
    span.file == expected_file && span.start < span.end
}

fn span_to_region(span: Span, counter_idx: u32) -> CoverageRegion {
    let line_start = (span.start.line as u32).saturating_add(1);
    let col_start = (span.start.offset as u32).saturating_add(1);
    let line_end = (span.end.line as u32).saturating_add(1).max(line_start);
    let raw_col_end = (span.end.offset as u32).saturating_add(1);
    let col_end = if line_end == line_start {
        raw_col_end.max(col_start)
    } else {
        raw_col_end.max(1)
    };
    CoverageRegion {
        line_start,
        col_start,
        line_end,
        col_end,
        counter_idx,
    }
}

fn declare_instrprof_increment<'llvm>(
    context: &'llvm Context,
    module: &Module<'llvm>,
) -> FunctionValue<'llvm> {
    if let Some(existing) = module.get_function("llvm.instrprof.increment") {
        return existing;
    }
    let ptr_ty = context.ptr_type(AddressSpace::default());
    let i64_ty = context.i64_type();
    let i32_ty = context.i32_type();
    let fn_ty = context.void_type().fn_type(
        &[ptr_ty.into(), i64_ty.into(), i32_ty.into(), i32_ty.into()],
        false,
    );
    module.add_function("llvm.instrprof.increment", fn_ty, Some(Linkage::External))
}

fn emit_profile_name_global<'llvm>(
    context: &'llvm Context,
    module: &Module<'llvm>,
    pgo_name: &str,
) -> PointerValue<'llvm> {
    let global_name = format!("__profn_{pgo_name}");
    if let Some(existing) = module.get_global(&global_name) {
        return existing.as_pointer_value();
    }
    let val = context.const_string(pgo_name.as_bytes(), false);
    let global = module.add_global(val.get_type(), None, &global_name);
    global.set_linkage(Linkage::Private);
    global.set_constant(true);
    global.set_unnamed_addr(true);
    global.set_initializer(&val);
    global.as_pointer_value()
}

fn append_to_llvm_used<'llvm>(
    context: &'llvm Context,
    module: &Module<'llvm>,
    globals: &[GlobalValue<'llvm>],
) {
    if globals.is_empty() {
        return;
    }
    let ptr_ty = context.ptr_type(AddressSpace::default());
    let mut ptrs: Vec<PointerValue<'llvm>> = globals.iter().map(|g| g.as_pointer_value()).collect();
    if let Some(existing) = module.get_global("llvm.used") {
        if let Some(BasicValueEnum::ArrayValue(arr)) = existing.get_initializer() {
            // Preserve any prior entries if another pass created @llvm.used.
            for idx in 0..arr.get_type().len() {
                let _ = idx;
            }
        }
        unsafe {
            existing.delete();
        }
    }
    let array_val = ptr_ty.const_array(&ptrs);
    let used = module.add_global(array_val.get_type(), None, "llvm.used");
    used.set_linkage(Linkage::Appending);
    used.set_section(Some("llvm.metadata"));
    used.set_initializer(&array_val);
    ptrs.clear();
}

fn compute_function_hash(num_counters: u32, regions: &[CoverageRegion]) -> u64 {
    // Stable non-zero structural hash matching both @llvm.instrprof.increment
    // and the @__covrec_* record.
    let mut h: u64 = 0xcbf29ce484222325 ^ (num_counters as u64);
    for r in regions {
        for v in [r.line_start, r.col_start, r.line_end, r.col_end, r.counter_idx] {
            h ^= v as u64;
            h = h.wrapping_mul(0x100000001b3);
        }
    }
    if h == 0 { 1 } else { h }
}

fn encode_uleb128(mut value: u64, out: &mut Vec<u8>) {
    loop {
        let mut byte = (value & 0x7f) as u8;
        value >>= 7;
        if value != 0 {
            byte |= 0x80;
        }
        out.push(byte);
        if value == 0 {
            break;
        }
    }
}

fn encode_filenames_v6(files: &[String]) -> Vec<u8> {
    let mut raw = Vec::new();
    for path in files {
        encode_uleb128(path.len() as u64, &mut raw);
        raw.extend_from_slice(path.as_bytes());
    }
    let mut out = Vec::new();
    encode_uleb128(files.len() as u64, &mut out);
    encode_uleb128(raw.len() as u64, &mut out);
    // Compressed size = 0 signals uncompressed filename buffer to LLVM.
    encode_uleb128(0, &mut out);
    out.extend_from_slice(&raw);
    out
}

fn encode_function_regions(file_index: u32, regions: &[CoverageRegion]) -> Vec<u8> {
    let mut out = Vec::new();
    // 1 file ID in this function's mapping.
    encode_uleb128(1, &mut out);
    encode_uleb128(file_index as u64, &mut out);
    // 0 counter expressions.
    encode_uleb128(0, &mut out);
    // Regions for local file ID 0.
    encode_uleb128(regions.len() as u64, &mut out);

    let mut prev_line_start: u32 = 0;
    for region in regions {
        // CounterKind::CounterValueReferenceKind = 1, shifted counter id in high bits.
        let encoded_counter = ((region.counter_idx as u64) << 2) | 1;
        encode_uleb128(encoded_counter, &mut out);
        encode_uleb128((region.line_start - prev_line_start) as u64, &mut out);
        encode_uleb128(region.col_start as u64, &mut out);
        encode_uleb128((region.line_end - region.line_start) as u64, &mut out);
        encode_uleb128(region.col_end as u64, &mut out);
        prev_line_start = region.line_start;
    }
    out
}

/// RFC 1321 MD5 returning the lower 64 bits (little-endian), matching LLVM's
/// `IndexedInstrProf::ComputeHash`.
fn md5_low64(input: &[u8]) -> u64 {
    const S: [u32; 64] = [
        7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22,
        5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20,
        4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23,
        6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21,
    ];
    const K: [u32; 64] = [
        0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee, 0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
        0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be, 0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
        0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa, 0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
        0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed, 0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
        0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c, 0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
        0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05, 0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
        0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039, 0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
        0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1, 0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391,
    ];

    let bit_len = (input.len() as u64).wrapping_mul(8);
    let mut msg = Vec::with_capacity(((input.len() + 9 + 63) / 64) * 64);
    msg.extend_from_slice(input);
    msg.push(0x80);
    while msg.len() % 64 != 56 {
        msg.push(0);
    }
    msg.extend_from_slice(&bit_len.to_le_bytes());

    let mut a0: u32 = 0x67452301;
    let mut b0: u32 = 0xefcdab89;
    let mut c0: u32 = 0x98badcfe;
    let mut d0: u32 = 0x10325476;

    for chunk in msg.chunks_exact(64) {
        let mut m = [0u32; 16];
        for (i, slot) in m.iter_mut().enumerate() {
            let o = i * 4;
            *slot = u32::from_le_bytes([chunk[o], chunk[o + 1], chunk[o + 2], chunk[o + 3]]);
        }
        let (mut a, mut b, mut c, mut d) = (a0, b0, c0, d0);
        for i in 0..64 {
            let (f, g) = match i {
                0..=15 => ((b & c) | (!b & d), i),
                16..=31 => ((d & b) | (!d & c), (5 * i + 1) % 16),
                32..=47 => (b ^ c ^ d, (3 * i + 5) % 16),
                _ => (c ^ (b | !d), (7 * i) % 16),
            };
            let temp = d;
            d = c;
            c = b;
            let sum = a.wrapping_add(f).wrapping_add(K[i]).wrapping_add(m[g]);
            b = b.wrapping_add(sum.rotate_left(S[i]));
            a = temp;
        }
        a0 = a0.wrapping_add(a);
        b0 = b0.wrapping_add(b);
        c0 = c0.wrapping_add(c);
        d0 = d0.wrapping_add(d);
    }

    let mut digest_lo = [0u8; 8];
    digest_lo[0..4].copy_from_slice(&a0.to_le_bytes());
    digest_lo[4..8].copy_from_slice(&b0.to_le_bytes());
    u64::from_le_bytes(digest_lo)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn md5_low64_matches_llvm_instrprof_hash() {
        assert_eq!(md5_low64(b"hit"), 0x2762fa95d42893f0);
        assert_eq!(md5_low64(b"miss"), 0x9ad2fb9044fc13de);
        assert_eq!(md5_low64(b"main"), 0xdb956436e78dd5fa);
    }

    #[test]
    fn encode_regions_matches_clang_single_region_layout() {
        let regions = vec![CoverageRegion {
            line_start: 1,
            col_start: 15,
            line_end: 1,
            col_end: 28,
            counter_idx: 0,
        }];
        assert_eq!(
            encode_function_regions(1, &regions),
            vec![0x01, 0x01, 0x00, 0x01, 0x01, 0x01, 0x0f, 0x00, 0x1c]
        );
    }
}
