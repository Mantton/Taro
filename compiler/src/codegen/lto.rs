use std::{
    borrow::Cow,
    collections::BTreeSet,
    fs,
    path::{Path, PathBuf},
    ptr::NonNull,
    slice,
    time::Instant,
};

use inkwell::{
    context::Context,
    data_layout::DataLayout,
    memory_buffer::MemoryBuffer,
    module::{Linkage, Module},
    passes::PassBuilderOptions,
    targets::{FileType, TargetMachine, TargetTriple},
};

use crate::{
    codegen::artifact::ModuleArtifact,
    compile::{
        config::{BuildProfile, LtoMode, ModuleArtifactKind, OptLevel, OptimizationMode},
        context::GlobalContext,
    },
    error::CompileResult,
};

#[repr(C)]
struct NativeThinLtoCodegen {
    _private: [u8; 0],
}

unsafe extern "C" {
    fn taro_write_thin_lto_bitcode(
        module: *mut std::ffi::c_void,
        path: *const u8,
        path_length: usize,
    ) -> bool;
    fn taro_llvm_global_prefix(module: *mut std::ffi::c_void) -> u8;
    fn taro_thin_lto_create() -> *mut NativeThinLtoCodegen;
    fn taro_thin_lto_dispose(codegen: *mut NativeThinLtoCodegen);
    fn taro_thin_lto_set_optimization(
        codegen: *mut NativeThinLtoCodegen,
        ir_level: u32,
        codegen_level: u32,
    );
    fn taro_thin_lto_set_target(
        codegen: *mut NativeThinLtoCodegen,
        cpu: *const u8,
        cpu_length: usize,
        features: *const u8,
        features_length: usize,
    );
    fn taro_thin_lto_set_cache_dir(
        codegen: *mut NativeThinLtoCodegen,
        path: *const u8,
        path_length: usize,
    );
    fn taro_thin_lto_set_output_dir(
        codegen: *mut NativeThinLtoCodegen,
        path: *const u8,
        path_length: usize,
    );
    #[cfg(test)]
    fn taro_thin_lto_disable_codegen(codegen: *mut NativeThinLtoCodegen, disable: bool);
    fn taro_thin_lto_add_module(
        codegen: *mut NativeThinLtoCodegen,
        identifier: *const u8,
        identifier_length: usize,
        data: *const u8,
        data_length: usize,
    );
    fn taro_thin_lto_preserve_symbol(
        codegen: *mut NativeThinLtoCodegen,
        name: *const u8,
        name_length: usize,
    );
    fn taro_thin_lto_cross_reference_symbol(
        codegen: *mut NativeThinLtoCodegen,
        name: *const u8,
        name_length: usize,
    );
    fn taro_thin_lto_process(codegen: *mut NativeThinLtoCodegen);
    fn taro_thin_lto_object_count(codegen: *mut NativeThinLtoCodegen) -> usize;
    fn taro_thin_lto_object_path(
        codegen: *mut NativeThinLtoCodegen,
        index: usize,
        length: *mut usize,
    ) -> *const u8;
}

struct ThinLtoCodegen(NonNull<NativeThinLtoCodegen>);

impl ThinLtoCodegen {
    fn new() -> Result<Self, String> {
        NonNull::new(unsafe { taro_thin_lto_create() })
            .map(Self)
            .ok_or_else(|| "LLVM failed to allocate a ThinLTO code generator".into())
    }

    fn set_optimization(&mut self, level: u32) {
        unsafe { taro_thin_lto_set_optimization(self.0.as_ptr(), level, level) };
    }

    fn set_target(&mut self, cpu: &[u8], features: &[u8]) {
        unsafe {
            taro_thin_lto_set_target(
                self.0.as_ptr(),
                cpu.as_ptr(),
                cpu.len(),
                features.as_ptr(),
                features.len(),
            )
        };
    }

    fn set_cache_dir(&mut self, path: &Path) -> Result<(), String> {
        let bytes = path_bytes(path)?;
        unsafe { taro_thin_lto_set_cache_dir(self.0.as_ptr(), bytes.as_ptr(), bytes.len()) };
        Ok(())
    }

    fn set_output_dir(&mut self, path: &Path) -> Result<(), String> {
        let bytes = path_bytes(path)?;
        unsafe { taro_thin_lto_set_output_dir(self.0.as_ptr(), bytes.as_ptr(), bytes.len()) };
        Ok(())
    }

    #[cfg(test)]
    fn disable_codegen(&mut self) {
        unsafe { taro_thin_lto_disable_codegen(self.0.as_ptr(), true) };
    }

    fn add_module(&mut self, identifier: &[u8], data: &[u8]) {
        unsafe {
            taro_thin_lto_add_module(
                self.0.as_ptr(),
                identifier.as_ptr(),
                identifier.len(),
                data.as_ptr(),
                data.len(),
            )
        };
    }

    fn preserve_symbol(&mut self, name: &[u8]) {
        unsafe { taro_thin_lto_preserve_symbol(self.0.as_ptr(), name.as_ptr(), name.len()) };
    }

    fn cross_reference_symbol(&mut self, name: &[u8]) {
        unsafe { taro_thin_lto_cross_reference_symbol(self.0.as_ptr(), name.as_ptr(), name.len()) };
    }

    fn process(&mut self) {
        unsafe { taro_thin_lto_process(self.0.as_ptr()) };
    }

    fn object_paths(&self) -> Result<Vec<PathBuf>, String> {
        let count = unsafe { taro_thin_lto_object_count(self.0.as_ptr()) };
        let mut paths = Vec::with_capacity(count);
        for index in 0..count {
            let mut length = 0;
            let pointer = unsafe { taro_thin_lto_object_path(self.0.as_ptr(), index, &mut length) };
            if pointer.is_null() {
                return Err(format!(
                    "LLVM returned an invalid path for ThinLTO object {index}"
                ));
            }
            let bytes = unsafe { slice::from_raw_parts(pointer, length) };
            paths.push(path_from_bytes(bytes)?);
        }
        Ok(paths)
    }
}

impl Drop for ThinLtoCodegen {
    fn drop(&mut self) {
        unsafe { taro_thin_lto_dispose(self.0.as_ptr()) };
    }
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
        .ok_or_else(|| format!("ThinLTO path '{}' is not valid UTF-8", path.display()))
}

#[cfg(unix)]
fn path_from_bytes(bytes: &[u8]) -> Result<PathBuf, String> {
    use std::{ffi::OsString, os::unix::ffi::OsStringExt};
    Ok(PathBuf::from(OsString::from_vec(bytes.to_vec())))
}

/// Write ThinLTO-ready bitcode containing a per-module summary and content
/// hash. LLVM's C bitcode writer omits both, so the narrow native shim owns
/// this one serialization operation.
pub(crate) fn write_thin_lto_bitcode(module: &Module<'_>, path: &Path) -> Result<(), String> {
    let bytes = path_bytes(path)?;
    let written = unsafe {
        taro_write_thin_lto_bitcode(module.as_mut_ptr().cast(), bytes.as_ptr(), bytes.len())
    };
    written.then_some(()).ok_or_else(|| {
        format!(
            "LLVM failed to write ThinLTO bitcode to '{}'",
            path.display()
        )
    })
}

#[cfg(not(unix))]
fn path_from_bytes(bytes: &[u8]) -> Result<PathBuf, String> {
    String::from_utf8(bytes.to_vec())
        .map(PathBuf::from)
        .map_err(|_| "LLVM returned a non-UTF-8 ThinLTO object path".into())
}

fn full_lto_pipeline(profile: BuildProfile, optimization: OptimizationMode) -> &'static str {
    match optimization {
        // Baseline remains useful for compiler comparisons. Debug maps to O0;
        // the historical release baseline is closest to LLVM's O2 backend.
        OptimizationMode::Baseline => match profile {
            BuildProfile::Debug => "lto<O0>",
            BuildProfile::Release => "lto<O2>",
        },
        OptimizationMode::Level(OptLevel::O0) => "lto<O0>",
        OptimizationMode::Level(OptLevel::O1) => "lto<O1>",
        OptimizationMode::Level(OptLevel::O2) => "lto<O2>",
        OptimizationMode::Level(OptLevel::O3) => "lto<O3>",
        OptimizationMode::Level(OptLevel::Os) => "lto<Os>",
        OptimizationMode::Level(OptLevel::Oz) => "lto<Oz>",
    }
}

fn thin_lto_optimization_level(profile: BuildProfile, optimization: OptimizationMode) -> u32 {
    match optimization {
        OptimizationMode::Baseline => match profile {
            BuildProfile::Debug => 0,
            BuildProfile::Release => 2,
        },
        OptimizationMode::Level(OptLevel::O0) => 0,
        OptimizationMode::Level(OptLevel::O1) => 1,
        OptimizationMode::Level(OptLevel::O2 | OptLevel::Os | OptLevel::Oz) => 2,
        OptimizationMode::Level(OptLevel::O3) => 3,
    }
}

fn read_bitcode(path: &Path) -> Result<Vec<u8>, String> {
    fs::read(path)
        .map_err(|error| format!("failed to read LTO input '{}': {error}", path.display()))
}

fn parse_bitcode_bytes<'ctx>(
    context: &'ctx Context,
    path: &Path,
    bytes: &[u8],
    expected_triple: &TargetTriple,
    expected_layout: &DataLayout,
) -> Result<Module<'ctx>, String> {
    let mut terminated = Vec::with_capacity(bytes.len() + 1);
    terminated.extend_from_slice(bytes);
    terminated.push(0);
    let buffer = MemoryBuffer::create_from_memory_range_copy(&terminated, "taro-lto-input");
    let module = Module::parse_bitcode_from_buffer(&buffer, context).map_err(|error| {
        format!(
            "failed to parse LLVM bitcode for LTO from '{}': {error}",
            path.display()
        )
    })?;

    if module.get_triple() != *expected_triple {
        return Err(format!(
            "LTO input '{}' targets `{}`, expected `{}`",
            path.display(),
            module.get_triple(),
            expected_triple
        ));
    }
    if module.get_data_layout().as_str() != expected_layout.as_str() {
        return Err(format!(
            "LTO input '{}' has an incompatible target data layout",
            path.display()
        ));
    }

    Ok(module)
}

fn parse_bitcode<'ctx>(
    context: &'ctx Context,
    path: &Path,
    expected_triple: &TargetTriple,
    expected_layout: &DataLayout,
) -> Result<Module<'ctx>, String> {
    // Inkwell's path-based loader requires Unicode paths. Reading bytes through
    // std::fs preserves every valid platform path and lets us attach a stable
    // diagnostic name to the LLVM memory buffer.
    let bytes = read_bitcode(path)?;
    parse_bitcode_bytes(context, path, &bytes, expected_triple, expected_layout)
}

fn should_preserve_linkage(linkage: Linkage) -> bool {
    matches!(
        linkage,
        Linkage::Common
            | Linkage::DLLExport
            | Linkage::External
            | Linkage::ExternalWeak
            | Linkage::LinkOnceAny
            | Linkage::LinkOnceODR
            | Linkage::LinkOnceODRAutoHide
            | Linkage::WeakAny
            | Linkage::WeakODR
    )
}

fn linker_symbol_name(module: &Module<'_>, ir_name: &[u8]) -> Vec<u8> {
    // LLVM's legacy ThinLTO API consumes object-file symbol names. Taro's
    // generated external names need only the target data layout's global
    // prefix (`_` on Mach-O and 32-bit COFF, empty on ELF/64-bit COFF).
    let prefix = unsafe { taro_llvm_global_prefix(module.as_mut_ptr().cast()) };
    let mut name = Vec::with_capacity(ir_name.len() + usize::from(prefix != 0));
    if prefix != 0 {
        name.push(prefix);
    }
    name.extend_from_slice(ir_name);
    name
}

fn preserved_symbols(module: &Module<'_>) -> BTreeSet<Vec<u8>> {
    let mut symbols = BTreeSet::new();
    for function in module.get_functions() {
        let global = function.as_global_value();
        if !global.is_declaration() && should_preserve_linkage(function.get_linkage()) {
            symbols.insert(linker_symbol_name(module, function.get_name().to_bytes()));
        }
    }
    for global in module.get_globals() {
        if !global.is_declaration() && should_preserve_linkage(global.get_linkage()) {
            symbols.insert(linker_symbol_name(module, global.get_name().to_bytes()));
        }
    }
    symbols
}

fn declared_symbols(module: &Module<'_>) -> BTreeSet<Vec<u8>> {
    let mut symbols = BTreeSet::new();
    for function in module.get_functions() {
        if function.as_global_value().is_declaration() {
            symbols.insert(linker_symbol_name(module, function.get_name().to_bytes()));
        }
    }
    for global in module.get_globals() {
        if global.is_declaration() {
            symbols.insert(linker_symbol_name(module, global.get_name().to_bytes()));
        }
    }
    symbols
}

fn optimize_full_lto_module(
    module: &Module<'_>,
    target_machine: &TargetMachine,
    pipeline: &'static str,
) -> Result<(), String> {
    let options = PassBuilderOptions::create();
    options.set_verify_each(cfg!(test));
    module
        .run_passes(pipeline, target_machine, options)
        .map_err(|error| error.to_string())
}

/// Merge every participating Taro bitcode module, run LLVM's full-LTO
/// post-link pipeline, and emit one native object for the platform linker.
///
/// Native inputs such as attached std and the Rust runtime intentionally stay
/// outside this operation and are linked after the returned object.
pub fn emit_full_lto_object(gcx: GlobalContext<'_>) -> CompileResult<ModuleArtifact> {
    if gcx.config.codegen.lto != LtoMode::Full
        || gcx.config.codegen.artifact != ModuleArtifactKind::LlvmBitcode
    {
        gcx.dcx().emit_error(
            "full LTO requires LLVM bitcode module artifacts".into(),
            None,
        );
        return Err(crate::error::ReportedError);
    }

    let Some(root_artifact) = gcx.get_module_artifact(gcx.package_index()) else {
        gcx.dcx().emit_error(
            "root LLVM bitcode artifact is missing for full LTO".into(),
            None,
        );
        return Err(crate::error::ReportedError);
    };
    if root_artifact.kind != ModuleArtifactKind::LlvmBitcode {
        gcx.dcx().emit_error(
            "root module artifact is not LLVM bitcode for full LTO".into(),
            None,
        );
        return Err(crate::error::ReportedError);
    }

    let mut inputs = vec![root_artifact];
    inputs.extend(
        gcx.module_artifacts()
            .into_iter()
            .filter(|(package, artifact)| {
                *package != gcx.package_index() && artifact.kind == ModuleArtifactKind::LlvmBitcode
            })
            .map(|(_, artifact)| artifact),
    );

    let started_at = Instant::now();
    let context = Context::create();
    let expected_triple = gcx.store.target_layout.triple();
    let expected_layout = gcx.store.target_layout.data_layout();
    let mut modules = inputs.iter().map(|artifact| {
        parse_bitcode(&context, &artifact.path, &expected_triple, &expected_layout)
    });
    let merged = modules
        .next()
        .expect("root bitcode guarantees at least one LTO module")
        .map_err(|message| {
            gcx.dcx().emit_error(message, None);
            crate::error::ReportedError
        })?;
    for module in modules {
        let module = module.map_err(|message| {
            gcx.dcx().emit_error(message, None);
            crate::error::ReportedError
        })?;
        merged.link_in_module(module).map_err(|error| {
            gcx.dcx().emit_error(
                format!("failed to merge LLVM modules for full LTO: {error}"),
                None,
            );
            crate::error::ReportedError
        })?;
    }

    merged.verify().map_err(|error| {
        gcx.dcx().emit_error(
            format!("full-LTO module verification failed before optimization: {error}"),
            None,
        );
        crate::error::ReportedError
    })?;

    let target_machine = gcx.store.target_layout.create_target_machine(
        gcx.dcx(),
        gcx.config.profile,
        gcx.config.codegen.optimization,
    )?;
    let pipeline = full_lto_pipeline(gcx.config.profile, gcx.config.codegen.optimization);
    optimize_full_lto_module(&merged, &target_machine, pipeline).map_err(|error| {
        gcx.dcx().emit_error(
            format!("LLVM full-LTO pipeline `{pipeline}` failed: {error}"),
            None,
        );
        crate::error::ReportedError
    })?;
    merged.verify().map_err(|error| {
        gcx.dcx().emit_error(
            format!("full-LTO module verification failed after optimization: {error}"),
            None,
        );
        crate::error::ReportedError
    })?;

    if gcx.config.debug.dump_llvm {
        eprintln!("\n=== Full LTO LLVM IR for {} ===", gcx.config.name);
        eprintln!("{}", merged.print_to_string());
        eprintln!("=== End Full LTO LLVM Dump ===\n");
    }

    fs::create_dir_all(gcx.output_root()).map_err(|error| {
        gcx.dcx().emit_error(
            format!("failed to create full-LTO output directory: {error}"),
            None,
        );
        crate::error::ReportedError
    })?;
    let output = gcx
        .output_root()
        .join(format!("{}.lto.o", gcx.config.identifier));
    target_machine
        .write_to_file(&merged, FileType::Object, &output)
        .map_err(|error| {
            gcx.dcx()
                .emit_error(format!("failed to write full-LTO object: {error}"), None);
            crate::error::ReportedError
        })?;

    let module_suffix = if inputs.len() == 1 { "" } else { "s" };
    if gcx.config.debug.timings {
        eprintln!(
            "Full LTO – {} module{} in {:.3} ms",
            inputs.len(),
            module_suffix,
            started_at.elapsed().as_secs_f64() * 1000.0
        );
    } else {
        eprintln!("Full LTO – {} module{}", inputs.len(), module_suffix);
    }
    Ok(ModuleArtifact::new(ModuleArtifactKind::Object, output))
}

struct ThinLtoInput {
    identifier: Vec<u8>,
    bitcode: Vec<u8>,
}

/// Run LLVM ThinLTO across every participating Taro bitcode module and emit
/// one or more native objects for the platform linker.
///
/// The ThinLTO cache is separate from Taro's package metadata cache. Callers
/// disable it for `--no-incremental`, while generated objects are always
/// refreshed because they are immediate linker inputs. Native attached std and
/// runtime artifacts remain outside the ThinLTO operation.
pub fn emit_thin_lto_objects(
    gcx: GlobalContext<'_>,
    use_cache: bool,
) -> CompileResult<Vec<ModuleArtifact>> {
    if gcx.config.codegen.lto != LtoMode::Thin
        || gcx.config.codegen.artifact != ModuleArtifactKind::LlvmBitcode
    {
        gcx.dcx().emit_error(
            "ThinLTO requires LLVM bitcode module artifacts".into(),
            None,
        );
        return Err(crate::error::ReportedError);
    }

    let Some(root_artifact) = gcx.get_module_artifact(gcx.package_index()) else {
        gcx.dcx().emit_error(
            "root LLVM bitcode artifact is missing for ThinLTO".into(),
            None,
        );
        return Err(crate::error::ReportedError);
    };
    if root_artifact.kind != ModuleArtifactKind::LlvmBitcode {
        gcx.dcx().emit_error(
            "root module artifact is not LLVM bitcode for ThinLTO".into(),
            None,
        );
        return Err(crate::error::ReportedError);
    }

    let mut artifacts = vec![root_artifact];
    artifacts.extend(
        gcx.module_artifacts()
            .into_iter()
            .filter(|(package, artifact)| {
                *package != gcx.package_index() && artifact.kind == ModuleArtifactKind::LlvmBitcode
            })
            .map(|(_, artifact)| artifact),
    );

    let started_at = Instant::now();
    let context = Context::create();
    let expected_triple = gcx.store.target_layout.triple();
    let expected_layout = gcx.store.target_layout.data_layout();
    let mut symbols = BTreeSet::new();
    let mut declarations = BTreeSet::new();
    let mut inputs = Vec::with_capacity(artifacts.len());
    for artifact in &artifacts {
        let bitcode = read_bitcode(&artifact.path).map_err(|message| {
            gcx.dcx().emit_error(message, None);
            crate::error::ReportedError
        })?;
        let module = parse_bitcode_bytes(
            &context,
            &artifact.path,
            &bitcode,
            &expected_triple,
            &expected_layout,
        )
        .map_err(|message| {
            gcx.dcx().emit_error(message, None);
            crate::error::ReportedError
        })?;
        module.verify().map_err(|error| {
            gcx.dcx().emit_error(
                format!(
                    "ThinLTO input '{}' failed verification: {error}",
                    artifact.path.display()
                ),
                None,
            );
            crate::error::ReportedError
        })?;
        symbols.extend(preserved_symbols(&module));
        declarations.extend(declared_symbols(&module));
        inputs.push(ThinLtoInput {
            identifier: path_bytes(&artifact.path)
                .map_err(|message| {
                    gcx.dcx().emit_error(message, None);
                    crate::error::ReportedError
                })?
                .into_owned(),
            bitcode,
        });
    }

    let output_dir = gcx.output_root().join("thinlto-objects");
    if output_dir.exists() {
        fs::remove_dir_all(&output_dir).map_err(|error| {
            gcx.dcx().emit_error(
                format!(
                    "failed to reset ThinLTO output directory '{}': {error}",
                    output_dir.display()
                ),
                None,
            );
            crate::error::ReportedError
        })?;
    }
    fs::create_dir_all(&output_dir).map_err(|error| {
        gcx.dcx().emit_error(
            format!(
                "failed to create ThinLTO output directory '{}': {error}",
                output_dir.display()
            ),
            None,
        );
        crate::error::ReportedError
    })?;

    let mut codegen = ThinLtoCodegen::new().map_err(|message| {
        gcx.dcx().emit_error(message, None);
        crate::error::ReportedError
    })?;
    codegen.set_optimization(thin_lto_optimization_level(
        gcx.config.profile,
        gcx.config.codegen.optimization,
    ));
    codegen.set_target(
        gcx.store.target_layout.cpu().as_bytes(),
        gcx.store.target_layout.features().as_bytes(),
    );
    codegen.set_output_dir(&output_dir).map_err(|message| {
        gcx.dcx().emit_error(message, None);
        crate::error::ReportedError
    })?;

    if use_cache {
        let cache_dir = gcx.output_root().join("thinlto-cache");
        fs::create_dir_all(&cache_dir).map_err(|error| {
            gcx.dcx().emit_error(
                format!(
                    "failed to create ThinLTO cache directory '{}': {error}",
                    cache_dir.display()
                ),
                None,
            );
            crate::error::ReportedError
        })?;
        codegen.set_cache_dir(&cache_dir).map_err(|message| {
            gcx.dcx().emit_error(message, None);
            crate::error::ReportedError
        })?;
    }

    // Taro does not yet encode source-level export intent into LLVM linkage.
    // Preserve every externally visible definition so ThinLTO cannot change
    // observable symbol availability. Cross-module importing and inlining still
    // operate, but dead external definitions remain until export metadata is
    // precise enough to drive more aggressive internalization.
    for symbol in &symbols {
        codegen.preserve_symbol(symbol);
    }
    for symbol in declarations.intersection(&symbols) {
        codegen.cross_reference_symbol(symbol);
    }
    for input in &inputs {
        codegen.add_module(&input.identifier, &input.bitcode);
    }
    codegen.process();

    let output_paths = codegen.object_paths().map_err(|message| {
        gcx.dcx().emit_error(message, None);
        crate::error::ReportedError
    })?;
    if output_paths.is_empty() {
        gcx.dcx()
            .emit_error("LLVM ThinLTO produced no native objects".into(), None);
        return Err(crate::error::ReportedError);
    }
    for path in &output_paths {
        if !path.is_file() {
            gcx.dcx().emit_error(
                format!("LLVM ThinLTO object '{}' is missing", path.display()),
                None,
            );
            return Err(crate::error::ReportedError);
        }
    }

    let module_suffix = if inputs.len() == 1 { "" } else { "s" };
    let object_suffix = if output_paths.len() == 1 { "" } else { "s" };
    if gcx.config.debug.timings {
        eprintln!(
            "Thin LTO – {} module{}, {} object{} in {:.3} ms",
            inputs.len(),
            module_suffix,
            output_paths.len(),
            object_suffix,
            started_at.elapsed().as_secs_f64() * 1000.0
        );
    } else {
        eprintln!(
            "Thin LTO – {} module{}, {} object{}",
            inputs.len(),
            module_suffix,
            output_paths.len(),
            object_suffix
        );
    }

    Ok(output_paths
        .into_iter()
        .map(|path| ModuleArtifact::new(ModuleArtifactKind::Object, path))
        .collect())
}

#[cfg(test)]
mod tests {
    use super::{
        ThinLtoCodegen, declared_symbols, full_lto_pipeline, optimize_full_lto_module,
        parse_bitcode, preserved_symbols, thin_lto_optimization_level, write_thin_lto_bitcode,
    };
    use crate::{
        codegen::target::TargetLayout,
        compile::config::{BuildProfile, OptLevel, OptimizationMode},
        diagnostics::DiagCtx,
    };
    use inkwell::{
        context::Context, module::Linkage, passes::PassBuilderOptions, values::AnyValue,
    };
    use std::{fs, path::PathBuf};

    fn temporary_bitcode_path(name: &str) -> PathBuf {
        std::env::temp_dir().join(format!(
            "taro-full-lto-{name}-{}-{}.bc",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("time")
                .as_nanos()
        ))
    }

    #[test]
    fn full_lto_pipeline_tracks_optimization_policy() {
        assert_eq!(
            full_lto_pipeline(BuildProfile::Debug, OptimizationMode::Baseline),
            "lto<O0>"
        );
        assert_eq!(
            full_lto_pipeline(BuildProfile::Release, OptimizationMode::Level(OptLevel::O3)),
            "lto<O3>"
        );
        assert_eq!(
            full_lto_pipeline(BuildProfile::Release, OptimizationMode::Level(OptLevel::Oz)),
            "lto<Oz>"
        );
    }

    #[test]
    fn thin_lto_backend_level_tracks_optimization_policy() {
        assert_eq!(
            thin_lto_optimization_level(BuildProfile::Debug, OptimizationMode::Baseline),
            0
        );
        assert_eq!(
            thin_lto_optimization_level(BuildProfile::Release, OptimizationMode::Baseline),
            2
        );
        assert_eq!(
            thin_lto_optimization_level(
                BuildProfile::Release,
                OptimizationMode::Level(OptLevel::Os),
            ),
            2
        );
        assert_eq!(
            thin_lto_optimization_level(
                BuildProfile::Release,
                OptimizationMode::Level(OptLevel::O3),
            ),
            3
        );
    }

    #[test]
    fn bitcode_loader_validates_target_identity() {
        let diagnostics = DiagCtx::new(PathBuf::from("."));
        let layout = TargetLayout::new(&diagnostics, None, BuildProfile::Release)
            .unwrap_or_else(|_| panic!("host target layout"));
        let source_context = Context::create();
        let module = source_context.create_module("lto-input");
        module.set_triple(&layout.triple());
        module.set_data_layout(&layout.data_layout());
        module.add_function(
            "dependency",
            source_context.void_type().fn_type(&[], false),
            None,
        );
        let path = temporary_bitcode_path("target-identity");
        let bytes = module.write_bitcode_to_memory();
        let bytes = bytes
            .as_slice()
            .strip_suffix(&[0])
            .unwrap_or(bytes.as_slice());
        fs::write(&path, bytes).expect("write bitcode");

        let parse_context = Context::create();
        let parsed = parse_bitcode(
            &parse_context,
            &path,
            &layout.triple(),
            &layout.data_layout(),
        )
        .expect("matching target should parse");
        assert!(parsed.get_function("dependency").is_some());

        let x86_linux = inkwell::targets::TargetTriple::create("x86_64-unknown-linux-gnu");
        let wrong_triple = if layout.triple() == x86_linux {
            inkwell::targets::TargetTriple::create("aarch64-unknown-linux-gnu")
        } else {
            x86_linux
        };
        let error = parse_bitcode(&parse_context, &path, &wrong_triple, &layout.data_layout())
            .expect_err("mismatched target should fail");
        assert!(error.contains("expected"));
        let _ = fs::remove_file(path);
    }

    #[test]
    fn full_lto_optimizes_across_linked_module_boundaries() {
        let diagnostics = DiagCtx::new(PathBuf::from("."));
        let layout = TargetLayout::new(&diagnostics, None, BuildProfile::Release)
            .unwrap_or_else(|_| panic!("host target layout"));
        let context = Context::create();
        let root = context.create_module("root");
        let dependency = context.create_module("dependency");
        for module in [&root, &dependency] {
            module.set_triple(&layout.triple());
            module.set_data_layout(&layout.data_layout());
        }

        let function_type = context.i32_type().fn_type(&[], false);
        let dependency_function = dependency.add_function("dependency_value", function_type, None);
        let dependency_block = context.append_basic_block(dependency_function, "entry");
        let dependency_builder = context.create_builder();
        dependency_builder.position_at_end(dependency_block);
        dependency_builder
            .build_return(Some(&context.i32_type().const_int(42, false)))
            .expect("dependency return");

        let dependency_declaration = root.add_function("dependency_value", function_type, None);
        let entry = root.add_function("main", function_type, None);
        let entry_block = context.append_basic_block(entry, "entry");
        let entry_builder = context.create_builder();
        entry_builder.position_at_end(entry_block);
        let call = entry_builder
            .build_call(dependency_declaration, &[], "dependency_call")
            .expect("dependency call")
            .try_as_basic_value()
            .basic()
            .expect("dependency return value");
        entry_builder
            .build_return(Some(&call))
            .expect("entry return");

        root.link_in_module(dependency)
            .expect("modules should link");
        let target_machine = layout
            .create_target_machine(
                &diagnostics,
                BuildProfile::Release,
                OptimizationMode::Level(OptLevel::O2),
            )
            .unwrap_or_else(|_| panic!("target machine"));
        optimize_full_lto_module(&root, &target_machine, "lto<O2>")
            .expect("full LTO should optimize");

        let entry_ir = root
            .get_function("main")
            .expect("main should remain")
            .print_to_string()
            .to_string();
        assert!(entry_ir.contains("ret i32 42"), "{entry_ir}");
        assert!(
            !entry_ir.contains("call i32 @dependency_value"),
            "{entry_ir}"
        );
    }

    #[test]
    fn thin_lto_imports_and_optimizes_across_module_boundaries() {
        let diagnostics = DiagCtx::new(PathBuf::from("."));
        let layout = TargetLayout::new(&diagnostics, None, BuildProfile::Release)
            .unwrap_or_else(|_| panic!("host target layout"));
        let context = Context::create();
        let root = context.create_module("thin-root");
        let dependency = context.create_module("thin-dependency");
        for module in [&root, &dependency] {
            module.set_triple(&layout.triple());
            module.set_data_layout(&layout.data_layout());
        }

        let function_type = context.i32_type().fn_type(&[], false);
        let dependency_function = dependency.add_function("thin_value", function_type, None);
        let dependency_block = context.append_basic_block(dependency_function, "entry");
        let dependency_builder = context.create_builder();
        dependency_builder.position_at_end(dependency_block);
        dependency_builder
            .build_return(Some(&context.i32_type().const_int(42, false)))
            .expect("dependency return");

        // This definition is consumed by an opaque native object in the real
        // compiler (attached std reads the environment globals). It has no IR
        // use here, so only an exact linker-name preservation rule keeps it
        // externally visible through ThinLTO internalization.
        let opaque_export = root.add_global(context.i64_type(), None, "__opaque_export");
        opaque_export.set_linkage(Linkage::External);
        opaque_export.set_initializer(&context.i64_type().const_zero());

        let dependency_declaration = root.add_function("thin_value", function_type, None);
        let entry = root.add_function("main", function_type, None);
        let entry_block = context.append_basic_block(entry, "entry");
        let entry_builder = context.create_builder();
        entry_builder.position_at_end(entry_block);
        let call = entry_builder
            .build_call(dependency_declaration, &[], "thin_call")
            .expect("dependency call")
            .try_as_basic_value()
            .basic()
            .expect("dependency return value");
        entry_builder
            .build_return(Some(&call))
            .expect("entry return");

        let target_machine = layout
            .create_target_machine(
                &diagnostics,
                BuildProfile::Release,
                OptimizationMode::Level(OptLevel::O2),
            )
            .unwrap_or_else(|_| panic!("target machine"));
        for module in [&root, &dependency] {
            module
                .run_passes(
                    "thinlto-pre-link<O2>",
                    &target_machine,
                    PassBuilderOptions::create(),
                )
                .expect("ThinLTO pre-link pipeline");
        }

        let temp_root = std::env::temp_dir().join(format!(
            "taro-thin-lto-test-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("time")
                .as_nanos()
        ));
        let input_dir = temp_root.join("input");
        let output_dir = temp_root.join("output");
        fs::create_dir_all(&input_dir).expect("ThinLTO input directory");
        fs::create_dir_all(&output_dir).expect("ThinLTO output directory");
        let root_input = input_dir.join("thin-root.bc");
        let dependency_input = input_dir.join("thin-dependency.bc");
        write_thin_lto_bitcode(&root, &root_input).expect("root ThinLTO bitcode");
        write_thin_lto_bitcode(&dependency, &dependency_input).expect("dependency ThinLTO bitcode");
        let root_bitcode = fs::read(&root_input).expect("read root ThinLTO bitcode");
        let dependency_bitcode =
            fs::read(&dependency_input).expect("read dependency ThinLTO bitcode");

        let mut symbols = preserved_symbols(&root);
        symbols.extend(preserved_symbols(&dependency));
        let mut declarations = declared_symbols(&root);
        declarations.extend(declared_symbols(&dependency));

        let output_paths = {
            let mut codegen = ThinLtoCodegen::new().expect("ThinLTO code generator");
            codegen.set_optimization(2);
            codegen.set_target(layout.cpu().as_bytes(), layout.features().as_bytes());
            codegen
                .set_output_dir(&output_dir)
                .expect("ThinLTO output path");
            codegen.disable_codegen();
            for symbol in &symbols {
                codegen.preserve_symbol(symbol);
            }
            for symbol in declarations.intersection(&symbols) {
                codegen.cross_reference_symbol(symbol);
            }
            codegen.add_module(b"thin-root.bc", &root_bitcode);
            codegen.add_module(b"thin-dependency.bc", &dependency_bitcode);
            codegen.process();
            codegen.object_paths().expect("ThinLTO output paths")
        };

        assert_eq!(output_paths.len(), 2);
        let parse_context = Context::create();
        let mut main_ir = None;
        let mut opaque_export_linkage = None;
        for output in &output_paths {
            let module = parse_bitcode(
                &parse_context,
                output,
                &layout.triple(),
                &layout.data_layout(),
            )
            .expect("ThinLTO bitcode output");
            if let Some(main) = module.get_function("main") {
                main_ir = Some(main.print_to_string().to_string());
            }
            if let Some(global) = module.get_global("__opaque_export") {
                opaque_export_linkage = Some(global.get_linkage());
            }
        }
        let main_ir = main_ir.expect("preserved main function");
        assert!(main_ir.contains("ret i32 42"), "{main_ir}");
        assert!(!main_ir.contains("call i32 @thin_value"), "{main_ir}");
        assert_eq!(opaque_export_linkage, Some(Linkage::External));
        let _ = fs::remove_dir_all(temp_root);
    }
}
