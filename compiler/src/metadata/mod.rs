use crate::{
    PackageIndex,
    codegen::artifact::ModuleArtifact,
    compile::{
        config::{
            BuildProfile, Config, HarnessMode, LtoMode, ModuleArtifactKind, OptLevel,
            OptimizationMode,
        },
        context::GlobalContext,
    },
    hir::{Abi, DefinitionID, DefinitionKind, KnownAttribute},
    mir::Body,
};
use rustc_hash::FxHashSet;
use std::{
    cell::Cell,
    fmt, fs,
    io::{self, Read, Write},
    path::{Path, PathBuf},
};

pub mod wire;

const META_MAGIC: [u8; 8] = *b"TAROMETA";
// Reject cached MIR/artifacts from invalid receiver or generic inlining.
const META_FORMAT_VERSION: u32 = 32;

#[derive(Debug, Clone)]
pub struct DependencyFingerprint {
    pub identifier: String,
    pub fingerprint: String,
}

#[derive(Debug, Clone)]
pub struct PackageFingerprintInput {
    pub package_fingerprint: String,
    pub dependencies: Vec<DependencyFingerprint>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReuseMode {
    CodegenDependency,
    CodegenRoot,
    SemanticDependency,
}

#[derive(Debug, Clone)]
struct MetadataHeader {
    compiler_revision: String,
    package_identifier: String,
    package_index: u32,
    target_triple: String,
    target_cpu: String,
    target_features: String,
    profile: String,
    optimization: String,
    lto: String,
    overflow_checks: bool,
    no_std_prelude: bool,
    harness_mode: HarnessMode,
    package_fingerprint: String,
    dependency_fingerprints: Vec<DependencyFingerprint>,
    artifact_kind: Option<ModuleArtifactKind>,
    artifact_relpath: Option<String>,
    stack_map_descriptors_relpath: Option<String>,
    pc_metadata_relpath: Option<String>,
    payload_checksum_hex: String,
    has_semantic_payload: bool,
    has_mir_payload: bool,
    has_artifact_ref: bool,
    frontend_reusable: bool,
}

#[derive(Debug, Clone)]
pub struct LoadedMetadata {
    pub package_identifier: String,
    pub package_index: PackageIndex,
    pub artifact: Option<ModuleArtifact>,
    pub payload: wire::MetadataPayloadWire,
}

#[derive(Debug, Clone)]
pub enum MetadataLoadStatus {
    Hit(LoadedMetadata),
    Miss(String),
}

#[derive(Debug, Clone)]
pub struct HydrationError {
    message: String,
}

impl HydrationError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for HydrationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.message.fmt(f)
    }
}

impl std::error::Error for HydrationError {}

fn validate_mode_capabilities(header: &MetadataHeader, mode: ReuseMode) -> Result<(), String> {
    match mode {
        ReuseMode::CodegenDependency => {
            if !(header.has_semantic_payload && header.has_mir_payload && header.has_artifact_ref) {
                return Err("metadata missing required codegen capabilities".into());
            }
        }
        ReuseMode::CodegenRoot => {
            if !(header.has_semantic_payload && header.has_artifact_ref) {
                return Err("metadata missing required root codegen capabilities".into());
            }
        }
        ReuseMode::SemanticDependency => {
            if !header.has_semantic_payload {
                return Err("metadata missing required semantic capabilities".into());
            }
        }
    }
    Ok(())
}

fn validate_artifact_header(header: &MetadataHeader) -> Result<(), String> {
    let has_kind = header.artifact_kind.is_some();
    let has_path = header.artifact_relpath.is_some();
    if has_kind != header.has_artifact_ref || has_path != header.has_artifact_ref {
        return Err("metadata artifact capability mismatch".into());
    }
    if !header.has_artifact_ref {
        if header.stack_map_descriptors_relpath.is_some() || header.pc_metadata_relpath.is_some() {
            return Err("metadata companion artifact capability mismatch".into());
        }
        return Ok(());
    }
    if header.stack_map_descriptors_relpath.is_none() {
        return Err("metadata stack-map descriptor reference missing".into());
    }
    match header.artifact_kind {
        Some(ModuleArtifactKind::Object) if header.pc_metadata_relpath.is_none() => {
            Err("metadata PC metadata object reference missing".into())
        }
        Some(ModuleArtifactKind::LlvmBitcode) if header.pc_metadata_relpath.is_some() => {
            Err("LLVM bitcode metadata unexpectedly references a PC metadata object".into())
        }
        Some(_) => Ok(()),
        None => Err("metadata artifact kind missing".into()),
    }
}

fn validate_payload_capabilities(
    header: &MetadataHeader,
    payload: &wire::MetadataPayloadWire,
) -> Result<(), String> {
    if payload.semantic_payload.is_some() != header.has_semantic_payload {
        return Err("metadata semantic capability mismatch".into());
    }
    if payload.mir_payload.is_some() != header.has_mir_payload {
        return Err("metadata MIR capability mismatch".into());
    }
    if payload.inline_mir_payload.is_some() != header.has_mir_payload {
        return Err("metadata canonical inline MIR capability mismatch".into());
    }
    Ok(())
}

fn compiler_revision_stamp() -> String {
    env!("TARO_COMPILER_ID").to_owned()
}

fn profile_name(profile: BuildProfile) -> &'static str {
    match profile {
        BuildProfile::Debug => "debug",
        BuildProfile::Release => "release",
    }
}

fn optimization_name(mode: OptimizationMode) -> &'static str {
    match mode {
        OptimizationMode::Baseline => "baseline",
        OptimizationMode::Level(OptLevel::O0) => "o0",
        OptimizationMode::Level(OptLevel::O1) => "o1",
        OptimizationMode::Level(OptLevel::O2) => "o2",
        OptimizationMode::Level(OptLevel::O3) => "o3",
        OptimizationMode::Level(OptLevel::Os) => "os",
        OptimizationMode::Level(OptLevel::Oz) => "oz",
    }
}

fn lto_name(mode: LtoMode) -> &'static str {
    match mode {
        LtoMode::Off => "off",
        LtoMode::Full => "full",
        LtoMode::Thin => "thin",
    }
}

fn metadata_dir(output_root: &Path) -> PathBuf {
    output_root
        .parent()
        .map(|p| p.join("metadata"))
        .unwrap_or_else(|| output_root.join("metadata"))
}

fn resolve_metadata_artifact_path(output_root: &Path, relative: &str) -> Result<PathBuf, String> {
    let relative = Path::new(relative);
    let mut has_component = false;
    for component in relative.components() {
        match component {
            std::path::Component::Normal(_) => has_component = true,
            std::path::Component::CurDir
            | std::path::Component::ParentDir
            | std::path::Component::RootDir
            | std::path::Component::Prefix(_) => {
                return Err("metadata artifact path escapes its output directory".into());
            }
        }
    }
    if !has_component {
        return Err("metadata artifact path is empty".into());
    }
    Ok(output_root.join(relative))
}

fn relative_artifact_path(
    output_root: &Path,
    path: &Path,
    description: &str,
) -> io::Result<String> {
    if !path.exists() {
        return Err(io::Error::new(
            io::ErrorKind::NotFound,
            format!("{description} missing at '{}'", path.display()),
        ));
    }
    let relative = path.strip_prefix(output_root).map_err(|_| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!("{description} is outside the compiler output directory"),
        )
    })?;
    relative.to_str().map(str::to_owned).ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!("{description} relative path is not valid Unicode"),
        )
    })
}

fn resolve_companion_beside(primary: &Path, relative: &str) -> Result<PathBuf, String> {
    let relative = Path::new(relative);
    let name = relative
        .file_name()
        .ok_or_else(|| "metadata companion artifact path has no file name".to_owned())?;
    Ok(primary.with_file_name(name))
}

fn artifact_from_explicit_path(
    header: &MetadataHeader,
    kind: ModuleArtifactKind,
    primary: &Path,
) -> Result<ModuleArtifact, String> {
    if !primary.exists() {
        return Err(format!(
            "{} artifact missing at '{}'",
            kind.display_name(),
            primary.display()
        ));
    }
    let descriptor_relative = header
        .stack_map_descriptors_relpath
        .as_deref()
        .ok_or_else(|| "metadata stack-map descriptor reference missing".to_owned())?;
    let descriptors = resolve_companion_beside(primary, descriptor_relative)?;
    if !descriptors.exists() {
        return Err(format!(
            "stack-map descriptors missing at '{}'",
            descriptors.display()
        ));
    }
    let pc_metadata = match header.pc_metadata_relpath.as_deref() {
        Some(relative) => {
            let path = resolve_companion_beside(primary, relative)?;
            if !path.exists() {
                return Err(format!(
                    "PC metadata object missing at '{}'",
                    path.display()
                ));
            }
            Some(path)
        }
        None => None,
    };
    Ok(ModuleArtifact::new(kind, primary.to_path_buf()).with_stack_maps(descriptors, pc_metadata))
}

pub fn metadata_path_for_config(config: &Config, output_root: &Path) -> PathBuf {
    metadata_dir(output_root).join(format!("{}.taro_meta", config.identifier))
}

pub fn write_package_metadata<'ctx>(
    gcx: GlobalContext<'ctx>,
    fp: &PackageFingerprintInput,
    mode: ReuseMode,
) -> io::Result<PathBuf> {
    let pkg = gcx.package_index();
    let config = gcx.config;

    let (artifact_kind, artifact_relpath, stack_map_descriptors_relpath, pc_metadata_relpath) =
        match mode {
            ReuseMode::CodegenDependency | ReuseMode::CodegenRoot => {
                let artifact = gcx.get_module_artifact(pkg).ok_or_else(|| {
                    io::Error::new(
                        io::ErrorKind::NotFound,
                        format!("{} artifact missing from compiler state", config.identifier),
                    )
                })?;
                if artifact.kind != config.codegen.artifact {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "cached module artifact kind does not match codegen configuration",
                    ));
                }
                let artifact_relpath = relative_artifact_path(
                    gcx.output_root(),
                    &artifact.path,
                    artifact.kind.display_name(),
                )?;
                let descriptor_path = artifact.stack_map_descriptors.as_ref().ok_or_else(|| {
                    io::Error::new(
                        io::ErrorKind::InvalidData,
                        "module artifact is missing stack-map descriptors",
                    )
                })?;
                let stack_map_descriptors_relpath = relative_artifact_path(
                    gcx.output_root(),
                    descriptor_path,
                    "stack-map descriptors",
                )?;
                let pc_metadata_relpath = match artifact.kind {
                    ModuleArtifactKind::Object => {
                        let path = artifact.pc_metadata.as_ref().ok_or_else(|| {
                            io::Error::new(
                                io::ErrorKind::InvalidData,
                                "object artifact is missing its PC metadata object",
                            )
                        })?;
                        Some(relative_artifact_path(
                            gcx.output_root(),
                            path,
                            "PC metadata object",
                        )?)
                    }
                    ModuleArtifactKind::LlvmBitcode => {
                        if artifact.pc_metadata.is_some() {
                            return Err(io::Error::new(
                                io::ErrorKind::InvalidData,
                                "LLVM bitcode artifact unexpectedly has a PC metadata object",
                            ));
                        }
                        None
                    }
                };
                (
                    Some(artifact.kind),
                    Some(artifact_relpath),
                    Some(stack_map_descriptors_relpath),
                    pc_metadata_relpath,
                )
            }
            ReuseMode::SemanticDependency => (None, None, None, None),
        };

    let payload = build_payload_wire(gcx, mode)?;
    let payload_bytes = bincode::serialize(&payload)
        .map_err(|e| io::Error::other(format!("failed to serialize metadata payload: {e}")))?;
    let checksum = blake3::hash(&payload_bytes).to_hex().to_string();

    let has_semantic_payload = payload.semantic_payload.is_some();
    let has_mir_payload = payload.mir_payload.is_some() && payload.inline_mir_payload.is_some();
    let has_artifact_ref = artifact_relpath.is_some();
    let frontend_reusable = match mode {
        ReuseMode::CodegenDependency => has_semantic_payload && has_mir_payload && has_artifact_ref,
        ReuseMode::CodegenRoot => has_semantic_payload && has_artifact_ref,
        ReuseMode::SemanticDependency => has_semantic_payload,
    };

    let header = MetadataHeader {
        compiler_revision: compiler_revision_stamp(),
        package_identifier: config.identifier.to_string(),
        package_index: pkg.raw() as u32,
        target_triple: gcx
            .store
            .target_layout
            .triple()
            .as_str()
            .to_string_lossy()
            .into_owned(),
        target_cpu: gcx.store.target_layout.cpu().to_owned(),
        target_features: gcx.store.target_layout.features().to_owned(),
        profile: profile_name(config.profile).to_string(),
        optimization: optimization_name(config.codegen.optimization).to_string(),
        lto: lto_name(config.codegen.lto).to_string(),
        overflow_checks: config.overflow_checks,
        no_std_prelude: config.no_std_prelude,
        harness_mode: config.harness_mode,
        package_fingerprint: fp.package_fingerprint.clone(),
        dependency_fingerprints: fp.dependencies.clone(),
        artifact_kind,
        artifact_relpath,
        stack_map_descriptors_relpath,
        pc_metadata_relpath,
        payload_checksum_hex: checksum,
        has_semantic_payload,
        has_mir_payload,
        has_artifact_ref,
        frontend_reusable,
    };

    let path = metadata_path_for_config(config, gcx.output_root().as_path());
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }

    let mut file = fs::File::create(&path)?;
    write_envelope(&mut file, &header, &payload_bytes)?;
    file.flush()?;
    Ok(path)
}

/// Shared cache/attached-artifact compatibility gates. Attached artifacts omit
/// invocation-specific fingerprints, profile and frontend options.
fn validate_and_decode_payload(
    gcx: GlobalContext<'_>,
    header: &MetadataHeader,
    payload_bytes: &[u8],
    mode: ReuseMode,
    expected_fp: Option<&PackageFingerprintInput>,
) -> Result<wire::MetadataPayloadWire, String> {
    let config = gcx.config;
    if header.compiler_revision != compiler_revision_stamp() {
        return Err("metadata compiler revision mismatch".into());
    }
    if header.package_identifier != config.identifier.as_ref() {
        return Err("metadata package identifier mismatch".into());
    }
    if header.package_index != config.index.raw() as u32 {
        return Err("metadata package index mismatch".into());
    }
    if header.target_triple
        != gcx
            .store
            .target_layout
            .triple()
            .as_str()
            .to_string_lossy()
            .as_ref()
    {
        return Err("metadata target mismatch".into());
    }
    if header.target_cpu != gcx.store.target_layout.cpu()
        || header.target_features != gcx.store.target_layout.features()
    {
        return Err("metadata target CPU/features mismatch".into());
    }
    if expected_fp.is_some() && header.profile != profile_name(config.profile) {
        return Err("metadata profile mismatch".into());
    }
    if header.optimization != optimization_name(config.codegen.optimization) {
        return Err("metadata optimization mode mismatch".into());
    }
    if header.lto != lto_name(config.codegen.lto) {
        return Err("metadata LTO mode mismatch".into());
    }
    if header.has_artifact_ref && header.artifact_kind != Some(config.codegen.artifact) {
        return Err("metadata module artifact kind mismatch".into());
    }
    if let Some(expected_fp) = expected_fp {
        if header.overflow_checks != config.overflow_checks
            || header.no_std_prelude != config.no_std_prelude
            || header.harness_mode != config.harness_mode
        {
            return Err("metadata compile option mismatch".into());
        }
        if header.package_fingerprint != expected_fp.package_fingerprint {
            return Err("metadata package fingerprint mismatch".into());
        }

        if header.dependency_fingerprints.len() != expected_fp.dependencies.len() {
            return Err("metadata dependency fingerprint count mismatch".into());
        }

        for (actual, expected) in header
            .dependency_fingerprints
            .iter()
            .zip(expected_fp.dependencies.iter())
        {
            if actual.identifier != expected.identifier
                || actual.fingerprint != expected.fingerprint
            {
                return Err("metadata dependency fingerprint mismatch".into());
            }
        }
    }

    let payload_checksum = blake3::hash(payload_bytes).to_hex().to_string();
    if payload_checksum != header.payload_checksum_hex {
        return Err("metadata payload checksum mismatch".into());
    }

    if !header.frontend_reusable {
        return Err("metadata marked non-reusable".into());
    }

    validate_artifact_header(header)?;
    validate_mode_capabilities(header, mode)?;
    let payload: wire::MetadataPayloadWire = bincode::deserialize(payload_bytes)
        .map_err(|error| format!("failed to decode metadata payload: {error}"))?;
    validate_payload_capabilities(header, &payload)?;

    Ok(payload)
}

pub fn try_load_package_metadata<'ctx>(
    gcx: GlobalContext<'ctx>,
    expected_fp: &PackageFingerprintInput,
    mode: ReuseMode,
) -> MetadataLoadStatus {
    let config = gcx.config;
    let meta_path = metadata_path_for_config(config, gcx.output_root().as_path());
    let mut file = match fs::File::open(&meta_path) {
        Ok(file) => file,
        Err(e) if e.kind() == io::ErrorKind::NotFound => {
            return MetadataLoadStatus::Miss("metadata file missing".into());
        }
        Err(e) => {
            return MetadataLoadStatus::Miss(format!("failed to read metadata: {e}"));
        }
    };

    let (header, payload_bytes) = match read_envelope(&mut file) {
        Ok(v) => v,
        Err(e) => {
            return MetadataLoadStatus::Miss(format!("failed to decode metadata envelope: {e}"));
        }
    };

    let payload =
        match validate_and_decode_payload(gcx, &header, &payload_bytes, mode, Some(expected_fp)) {
            Ok(payload) => payload,
            Err(message) => return MetadataLoadStatus::Miss(message),
        };

    let artifact = if header.has_artifact_ref {
        let Some(kind) = header.artifact_kind else {
            return MetadataLoadStatus::Miss("metadata artifact kind missing".into());
        };
        let Some(artifact_relpath) = header.artifact_relpath.as_ref() else {
            return MetadataLoadStatus::Miss("metadata artifact reference missing".into());
        };
        let artifact_path =
            match resolve_metadata_artifact_path(gcx.output_root(), artifact_relpath) {
                Ok(path) => path,
                Err(message) => return MetadataLoadStatus::Miss(message),
            };
        let descriptor_path = match header.stack_map_descriptors_relpath.as_deref() {
            Some(relative) => match resolve_metadata_artifact_path(gcx.output_root(), relative) {
                Ok(path) => path,
                Err(message) => return MetadataLoadStatus::Miss(message),
            },
            None => {
                return MetadataLoadStatus::Miss(
                    "metadata stack-map descriptor reference missing".into(),
                );
            }
        };
        let pc_metadata_path = match header.pc_metadata_relpath.as_deref() {
            Some(relative) => match resolve_metadata_artifact_path(gcx.output_root(), relative) {
                Ok(path) => Some(path),
                Err(message) => return MetadataLoadStatus::Miss(message),
            },
            None => None,
        };
        if matches!(mode, ReuseMode::CodegenDependency | ReuseMode::CodegenRoot)
            && (!artifact_path.exists()
                || !descriptor_path.exists()
                || pc_metadata_path.as_ref().is_some_and(|path| !path.exists()))
        {
            return MetadataLoadStatus::Miss(format!(
                "cached {} artifact set is incomplete",
                kind.display_name()
            ));
        }
        if artifact_path.exists()
            && descriptor_path.exists()
            && pc_metadata_path.as_ref().is_none_or(|path| path.exists())
        {
            Some(
                ModuleArtifact::new(kind, artifact_path)
                    .with_stack_maps(descriptor_path, pc_metadata_path),
            )
        } else {
            None
        }
    } else {
        None
    };

    MetadataLoadStatus::Hit(LoadedMetadata {
        package_identifier: header.package_identifier,
        package_index: PackageIndex::new(header.package_index as usize),
        artifact,
        payload,
    })
}

/// Load metadata from explicit artifact paths (used for attached/prebuilt std artifacts).
///
/// This path intentionally skips invocation-specific profile/options/fingerprint matching.
/// Attached artifacts are instead validated by compiler revision, target codegen identity,
/// optimization mode, checksum, and payload capability gates.
pub fn try_load_package_metadata_from_paths<'ctx>(
    gcx: GlobalContext<'ctx>,
    mode: ReuseMode,
    metadata_path: &Path,
    artifact_path: Option<&Path>,
) -> MetadataLoadStatus {
    let mut file = match fs::File::open(metadata_path) {
        Ok(file) => file,
        Err(e) if e.kind() == io::ErrorKind::NotFound => {
            return MetadataLoadStatus::Miss(format!(
                "metadata file missing at '{}'",
                metadata_path.display()
            ));
        }
        Err(e) => {
            return MetadataLoadStatus::Miss(format!(
                "failed to read metadata at '{}': {}",
                metadata_path.display(),
                e
            ));
        }
    };

    let (header, payload_bytes) = match read_envelope(&mut file) {
        Ok(v) => v,
        Err(e) => {
            return MetadataLoadStatus::Miss(format!("failed to decode metadata envelope: {e}"));
        }
    };

    let payload = match validate_and_decode_payload(gcx, &header, &payload_bytes, mode, None) {
        Ok(payload) => payload,
        Err(message) => return MetadataLoadStatus::Miss(message),
    };

    let artifact = match mode {
        ReuseMode::CodegenDependency | ReuseMode::CodegenRoot => {
            let Some(kind) = header.artifact_kind else {
                return MetadataLoadStatus::Miss("metadata artifact kind missing".into());
            };
            let Some(path) = artifact_path else {
                return MetadataLoadStatus::Miss(format!(
                    "{} artifact path not provided",
                    kind.display_name()
                ));
            };
            match artifact_from_explicit_path(&header, kind, path) {
                Ok(artifact) => Some(artifact),
                Err(message) => return MetadataLoadStatus::Miss(message),
            }
        }
        ReuseMode::SemanticDependency => match (header.artifact_kind, artifact_path) {
            (Some(kind), Some(path)) => artifact_from_explicit_path(&header, kind, path).ok(),
            _ => None,
        },
    };

    MetadataLoadStatus::Hit(LoadedMetadata {
        package_identifier: header.package_identifier,
        package_index: PackageIndex::new(header.package_index as usize),
        artifact,
        payload,
    })
}

pub fn hydrate_loaded_metadata<'ctx>(
    gcx: GlobalContext<'ctx>,
    loaded: &LoadedMetadata,
    mode: ReuseMode,
) -> Result<(), HydrationError> {
    if loaded.package_identifier != gcx.config.identifier.as_ref() {
        return Err(HydrationError::new(
            "loaded metadata package identifier mismatch",
        ));
    }
    if loaded.package_index != gcx.package_index() {
        return Err(HydrationError::new(
            "loaded metadata package index mismatch",
        ));
    }

    let Some(semantic_payload) = loaded.payload.semantic_payload.as_deref() else {
        return Err(HydrationError::new("metadata missing semantic payload"));
    };
    let semantic: wire::SemanticPayloadWire = bincode::deserialize(semantic_payload)
        .map_err(|e| HydrationError::new(format!("failed to decode semantic payload: {e}")))?;

    if semantic.package_identifier != loaded.package_identifier {
        return Err(HydrationError::new(
            "semantic payload package identifier mismatch",
        ));
    }
    if semantic.package_index != loaded.package_index.raw() as u32 {
        return Err(HydrationError::new(
            "semantic payload package index mismatch",
        ));
    }

    let file_remap = wire::build_file_remap(gcx, &loaded.payload.file_table);
    let remap = wire::FileRemap {
        old_to_new: &file_remap,
    };

    let invalid_symbol_id = Cell::new(None);
    let symbol_table = wire::SymbolTableRef::new(&semantic.symbol_table, &invalid_symbol_id);
    let resolution_output =
        wire::resolution_output_from_wire(gcx, &semantic.resolution, remap, symbol_table).map_err(
            |e| HydrationError::new(format!("failed to decode resolution payload: {e}")),
        )?;
    let type_db = wire::type_database_from_wire(gcx, &semantic.type_db, remap, symbol_table);
    let (decoded_mir, decoded_inline_mir) = if matches!(mode, ReuseMode::CodegenDependency) {
        let Some(mir_payload) = loaded.payload.mir_payload.as_deref() else {
            return Err(HydrationError::new("metadata missing MIR payload"));
        };
        let Some(inline_mir_payload) = loaded.payload.inline_mir_payload.as_deref() else {
            return Err(HydrationError::new(
                "metadata missing canonical inline MIR payload",
            ));
        };
        let mir_payload: wire::MirPackageWire = bincode::deserialize(mir_payload)
            .map_err(|e| HydrationError::new(format!("failed to decode MIR payload: {e}")))?;
        let inline_mir_payload: wire::MirPackageWire = bincode::deserialize(inline_mir_payload)
            .map_err(|e| {
                HydrationError::new(format!(
                    "failed to decode canonical inline MIR payload: {e}"
                ))
            })?;
        (
            Some(wire::mir_package_from_wire(gcx, &mir_payload, remap)),
            Some(wire::mir_package_from_wire(gcx, &inline_mir_payload, remap)),
        )
    } else {
        (None, None)
    };

    if let Some(symbol_id) = invalid_symbol_id.get() {
        return Err(HydrationError::new(format!(
            "metadata references unknown symbol table id {}",
            symbol_id
        )));
    }

    let cached_artifact = if let Some(artifact) = loaded.artifact.as_ref() {
        Some(artifact.clone())
    } else if matches!(mode, ReuseMode::CodegenDependency | ReuseMode::CodegenRoot) {
        return Err(HydrationError::new("metadata missing module artifact"));
    } else {
        None
    };

    let std_registry = loaded
        .payload
        .std_items
        .as_ref()
        .map(|std_items| wire::std_registry_from_wire(std_items, remap));
    let decoded_synthetic_defs: Vec<_> = loaded
        .payload
        .synthetic_definitions
        .iter()
        .map(|synthetic| wire::synthetic_definition_from_wire(gcx, synthetic, remap))
        .collect();
    let emitted_instances: FxHashSet<_> = loaded
        .payload
        .emitted_instances
        .iter()
        .map(|instance| wire::instance_from_wire(gcx, instance))
        .collect();

    // Commit decoded metadata only after all decode/validation steps pass.
    let resolution_output = gcx.store.arenas.resolution_outputs.alloc(resolution_output);
    gcx.store
        .resolution_outputs
        .borrow_mut()
        .insert(gcx.package_index(), resolution_output);
    gcx.store
        .type_databases
        .borrow_mut()
        .insert(gcx.package_index(), type_db);
    if let Some(mir) = decoded_mir {
        let mir = gcx.store.alloc_mir_package(mir);
        gcx.store
            .mir_packages
            .borrow_mut()
            .insert(gcx.package_index(), mir);
    }
    if let Some(mir) = decoded_inline_mir {
        let mir = gcx.store.alloc_mir_package(mir);
        gcx.store
            .inline_mir_packages
            .borrow_mut()
            .insert(gcx.package_index(), mir);
    }
    if let Some(registry) = std_registry {
        *gcx.store.std_items.borrow_mut() = Some((gcx.package_index(), registry));
        gcx.store.std_provider_index.set(Some(gcx.package_index()));
    }
    for (id, def) in decoded_synthetic_defs {
        gcx.store.synthetic_definitions.borrow_mut().insert(id, def);
    }

    for instance in emitted_instances.iter().copied() {
        gcx.mark_instance_compiled(instance);
    }
    gcx.cache_emitted_instances(gcx.package_index(), emitted_instances);

    if let Some(artifact) = cached_artifact {
        gcx.cache_module_artifact(artifact);
    }

    gcx.store
        .package_mapping
        .borrow_mut()
        .insert(gcx.config.identifier.clone(), gcx.package_index());
    gcx.cache_package_ident(gcx.config.identifier.clone());

    if gcx.config.is_std_provider {
        gcx.store.std_provider_index.set(Some(gcx.package_index()));
    }

    Ok(())
}

fn build_payload_wire<'ctx>(
    gcx: GlobalContext<'ctx>,
    mode: ReuseMode,
) -> io::Result<wire::MetadataPayloadWire> {
    let pkg = gcx.package_index();

    let semantic = gcx.try_resolution_output(pkg).map(|resolution_output| {
        let mut symbols = wire::SymbolTableBuilder::default();
        let resolution = wire::resolution_output_to_wire(resolution_output, &mut symbols);
        let type_db =
            gcx.with_type_database(pkg, |db| wire::type_database_to_wire(db, &mut symbols));
        wire::SemanticPayloadWire {
            package_identifier: gcx.config.identifier.to_string(),
            package_index: pkg.raw() as u32,
            symbol_table: symbols.finish(),
            resolution,
            type_db,
        }
    });
    let semantic_payload =
        match semantic {
            Some(semantic) => Some(bincode::serialize(&semantic).map_err(|e| {
                io::Error::other(format!("failed to serialize semantic payload: {e}"))
            })?),
            None => None,
        };

    let (mir, inline_mir) = match mode {
        ReuseMode::CodegenDependency => {
            let mir_packages = gcx.store.mir_packages.borrow();
            let inline_packages = gcx.store.inline_mir_packages.borrow();
            let package = mir_packages.get(&pkg).copied();
            let inline_package = inline_packages.get(&pkg).copied();
            match (package, inline_package) {
                (Some(package), Some(inline_package)) => {
                    let inline_retained = reachable_mir_defs(
                        inline_package,
                        mir_roots_for_metadata(gcx, inline_package),
                    );
                    // Canonical retention is authoritative for which bodies are
                    // available to the inliner. Final MIR needs an additional,
                    // independent seed: global optimization and late method
                    // resolution can expose downstream codegen dependencies
                    // that were not direct canonical callees (for example a
                    // synthesized enum equality body used by an async poll).
                    // Keeping these only in the final store preserves
                    // source/metadata inlining parity while making every body
                    // needed for downstream monomorphization available.
                    let final_roots =
                        mir_roots_for_metadata(gcx, package).chain(inline_retained.iter().copied());
                    let final_retained = reachable_mir_defs(package, final_roots);
                    (
                        Some(wire::mir_package_to_wire_filtered(
                            package,
                            |def_id, _body| final_retained.contains(&def_id),
                        )),
                        Some(wire::mir_package_to_wire_filtered(
                            inline_package,
                            |def_id, _body| inline_retained.contains(&def_id),
                        )),
                    )
                }
                _ => (None, None),
            }
        }
        ReuseMode::CodegenRoot | ReuseMode::SemanticDependency => (None, None),
    };
    let mir_payload = match mir {
        Some(mir) => Some(
            bincode::serialize(&mir)
                .map_err(|e| io::Error::other(format!("failed to serialize MIR payload: {e}")))?,
        ),
        None => None,
    };
    let inline_mir_payload = match inline_mir {
        Some(mir) => Some(bincode::serialize(&mir).map_err(|e| {
            io::Error::other(format!(
                "failed to serialize canonical inline MIR payload: {e}"
            ))
        })?),
        None => None,
    };

    let std_items = {
        let std_items = gcx.store.std_items.borrow();
        std_items.as_ref().and_then(|(std_pkg, registry)| {
            if *std_pkg == pkg {
                Some(wire::std_registry_to_wire(registry))
            } else {
                None
            }
        })
    };

    let synthetic_definitions = {
        let defs = gcx.store.synthetic_definitions.borrow();
        defs.iter()
            .filter(|(id, _)| id.package() == pkg)
            .map(|(id, def)| wire::synthetic_definition_to_wire(*id, def))
            .collect()
    };

    let emitted_instances = gcx
        .emitted_instances_of(pkg)
        .into_iter()
        .map(wire::instance_to_wire)
        .collect();

    Ok(wire::MetadataPayloadWire {
        file_table: wire::file_table_from_dcx(gcx),
        semantic_payload,
        mir_payload,
        inline_mir_payload,
        std_items,
        synthetic_definitions,
        emitted_instances,
    })
}

fn mir_roots_for_metadata<'ctx>(
    gcx: GlobalContext<'ctx>,
    package: &'ctx crate::mir::MirPackage<'ctx>,
) -> impl Iterator<Item = DefinitionID> + 'ctx {
    package
        .functions
        .iter()
        .filter_map(move |(&definition, body)| {
            should_retain_mir_root_for_metadata(gcx, definition, body).then_some(definition)
        })
}

/// Follow local function and closure references once for each retained body.
/// Canonical and final MIR have distinct roots, but the reachability rule is the same.
fn reachable_mir_defs(
    package: &crate::mir::MirPackage<'_>,
    roots: impl IntoIterator<Item = DefinitionID>,
) -> FxHashSet<DefinitionID> {
    let mut retained = FxHashSet::default();
    let mut worklist: Vec<_> = roots.into_iter().collect();
    while let Some(definition) = worklist.pop() {
        let Some(body) = package.functions.get(&definition) else {
            continue;
        };
        if !retained.insert(definition) {
            continue;
        }
        crate::mir::for_each_function_constant_in_body(body, |callee, _args| {
            if !retained.contains(&callee) {
                worklist.push(callee);
            }
        });
    }
    retained
}

fn should_retain_mir_root_for_metadata<'ctx>(
    gcx: GlobalContext<'ctx>,
    def_id: DefinitionID,
    body: &Body<'_>,
) -> bool {
    // Closure bodies are nested definitions rather than resolver definitions.
    // Retain them through closure aggregates reachable from retained roots.
    if gcx.get_closure_captures(def_id).is_some() {
        return false;
    }

    // Method calls can resolve late during codegen (interface/default/witness paths).
    // Keep associated-function MIR available so those concrete targets can be lowered.
    if matches!(
        gcx.definition_kind(def_id),
        DefinitionKind::AssociatedFunction
    ) {
        return true;
    }

    // Generic definitions always need MIR for downstream monomorphization.
    if !gcx.generics_of(def_id).is_empty() {
        return true;
    }

    let mut has_inline_attr = false;
    for attr in gcx.attributes_of(def_id).iter() {
        match attr.as_known(gcx) {
            Some(KnownAttribute::Inline) => {
                has_inline_attr = true;
                break;
            }
            Some(KnownAttribute::NoInline) => {
                return false;
            }
            Some(_) | None => {}
        }
    }
    if has_inline_attr {
        return true;
    }

    // Keep every concrete callee that any supported optimization profile and
    // callsite bonus can pick up heuristically. This predicate is owned by the
    // inliner so source and hydrated dependencies cannot drift apart.
    // ABI-restricted callees are never inlined and don't need MIR in metadata.
    let signature = gcx.get_signature(def_id);
    if matches!(
        signature.abi,
        Some(Abi::Intrinsic | Abi::C | Abi::Blocking | Abi::Runtime)
    ) {
        return false;
    }

    crate::mir::optimize::inline::is_heuristic_inline_candidate(gcx, body)
}

fn write_envelope(out: &mut dyn Write, header: &MetadataHeader, payload: &[u8]) -> io::Result<()> {
    let header_bytes = encode_header(header);

    out.write_all(&META_MAGIC)?;
    out.write_all(&META_FORMAT_VERSION.to_le_bytes())?;
    out.write_all(&(header_bytes.len() as u32).to_le_bytes())?;
    out.write_all(&(payload.len() as u32).to_le_bytes())?;
    out.write_all(&header_bytes)?;
    out.write_all(payload)?;
    Ok(())
}

fn read_envelope(input: &mut dyn Read) -> io::Result<(MetadataHeader, Vec<u8>)> {
    let mut magic = [0u8; 8];
    input.read_exact(&mut magic)?;
    if magic != META_MAGIC {
        return Err(io::Error::other("metadata magic mismatch"));
    }

    let mut version_bytes = [0u8; 4];
    input.read_exact(&mut version_bytes)?;
    let version = u32::from_le_bytes(version_bytes);
    if version != META_FORMAT_VERSION {
        return Err(io::Error::other(format!(
            "metadata format version mismatch: {version}",
        )));
    }

    let header_len = read_u32(input)? as usize;
    let payload_len = read_u32(input)? as usize;

    let mut header_bytes = vec![0u8; header_len];
    input.read_exact(&mut header_bytes)?;
    let header = decode_header(&header_bytes)?;

    let mut payload = vec![0u8; payload_len];
    input.read_exact(&mut payload)?;

    Ok((header, payload))
}

fn encode_header(header: &MetadataHeader) -> Vec<u8> {
    let mut out = Vec::new();
    write_string(&mut out, &header.compiler_revision);
    write_string(&mut out, &header.package_identifier);
    out.extend_from_slice(&header.package_index.to_le_bytes());
    write_string(&mut out, &header.target_triple);
    write_string(&mut out, &header.target_cpu);
    write_string(&mut out, &header.target_features);
    write_string(&mut out, &header.profile);
    write_string(&mut out, &header.optimization);
    write_string(&mut out, &header.lto);
    out.push(header.overflow_checks as u8);
    out.push(header.no_std_prelude as u8);
    out.push(harness_mode_tag(header.harness_mode));
    write_string(&mut out, &header.package_fingerprint);

    out.extend_from_slice(&(header.dependency_fingerprints.len() as u32).to_le_bytes());
    for dep in &header.dependency_fingerprints {
        write_string(&mut out, &dep.identifier);
        write_string(&mut out, &dep.fingerprint);
    }

    write_optional_artifact_kind(&mut out, header.artifact_kind);
    write_optional_string(&mut out, header.artifact_relpath.as_deref());
    write_optional_string(&mut out, header.stack_map_descriptors_relpath.as_deref());
    write_optional_string(&mut out, header.pc_metadata_relpath.as_deref());
    write_string(&mut out, &header.payload_checksum_hex);
    out.push(header.has_semantic_payload as u8);
    out.push(header.has_mir_payload as u8);
    out.push(header.has_artifact_ref as u8);
    out.push(header.frontend_reusable as u8);
    out
}

fn decode_header(bytes: &[u8]) -> io::Result<MetadataHeader> {
    let mut cursor = std::io::Cursor::new(bytes);
    let compiler_revision = read_string(&mut cursor)?;
    let package_identifier = read_string(&mut cursor)?;
    let package_index = read_u32(&mut cursor)?;
    let target_triple = read_string(&mut cursor)?;
    let target_cpu = read_string(&mut cursor)?;
    let target_features = read_string(&mut cursor)?;
    let profile = read_string(&mut cursor)?;
    let optimization = read_string(&mut cursor)?;
    let lto = read_string(&mut cursor)?;

    let overflow_checks = read_bool(&mut cursor)?;
    let no_std_prelude = read_bool(&mut cursor)?;
    let harness_mode = read_harness_mode(&mut cursor)?;

    let package_fingerprint = read_string(&mut cursor)?;

    let dep_count = read_u32(&mut cursor)? as usize;
    let mut dependency_fingerprints = Vec::with_capacity(dep_count);
    for _ in 0..dep_count {
        dependency_fingerprints.push(DependencyFingerprint {
            identifier: read_string(&mut cursor)?,
            fingerprint: read_string(&mut cursor)?,
        });
    }

    let artifact_kind = read_optional_artifact_kind(&mut cursor)?;
    let artifact_relpath = read_optional_string(&mut cursor)?;
    let stack_map_descriptors_relpath = read_optional_string(&mut cursor)?;
    let pc_metadata_relpath = read_optional_string(&mut cursor)?;
    let payload_checksum_hex = read_string(&mut cursor)?;
    let has_semantic_payload = read_bool(&mut cursor)?;
    let has_mir_payload = read_bool(&mut cursor)?;
    let has_artifact_ref = read_bool(&mut cursor)?;
    let frontend_reusable = read_bool(&mut cursor)?;

    Ok(MetadataHeader {
        compiler_revision,
        package_identifier,
        package_index,
        target_triple,
        target_cpu,
        target_features,
        profile,
        optimization,
        lto,
        overflow_checks,
        no_std_prelude,
        harness_mode,
        package_fingerprint,
        dependency_fingerprints,
        artifact_kind,
        artifact_relpath,
        stack_map_descriptors_relpath,
        pc_metadata_relpath,
        payload_checksum_hex,
        has_semantic_payload,
        has_mir_payload,
        has_artifact_ref,
        frontend_reusable,
    })
}

fn write_string(out: &mut Vec<u8>, value: &str) {
    out.extend_from_slice(&(value.len() as u32).to_le_bytes());
    out.extend_from_slice(value.as_bytes());
}

fn write_optional_string(out: &mut Vec<u8>, value: Option<&str>) {
    match value {
        Some(value) => {
            out.push(1);
            write_string(out, value);
        }
        None => out.push(0),
    }
}

fn write_optional_artifact_kind(out: &mut Vec<u8>, value: Option<ModuleArtifactKind>) {
    out.push(match value {
        None => 0,
        Some(ModuleArtifactKind::Object) => 1,
        Some(ModuleArtifactKind::LlvmBitcode) => 2,
    });
}

fn read_string(input: &mut dyn Read) -> io::Result<String> {
    let len = read_u32(input)? as usize;
    let mut bytes = vec![0u8; len];
    input.read_exact(&mut bytes)?;
    String::from_utf8(bytes).map_err(|e| io::Error::other(format!("invalid utf8 string: {e}")))
}

fn read_optional_string(input: &mut dyn Read) -> io::Result<Option<String>> {
    let tag = read_u8(input)?;
    match tag {
        0 => Ok(None),
        1 => Ok(Some(read_string(input)?)),
        other => Err(io::Error::other(format!(
            "invalid optional string tag: {other}",
        ))),
    }
}

fn read_optional_artifact_kind(input: &mut dyn Read) -> io::Result<Option<ModuleArtifactKind>> {
    match read_u8(input)? {
        0 => Ok(None),
        1 => Ok(Some(ModuleArtifactKind::Object)),
        2 => Ok(Some(ModuleArtifactKind::LlvmBitcode)),
        other => Err(io::Error::other(format!(
            "invalid module artifact kind tag: {other}",
        ))),
    }
}

fn harness_mode_tag(mode: HarnessMode) -> u8 {
    match mode {
        HarnessMode::None => 0,
        HarnessMode::Test => 1,
        HarnessMode::Bench => 2,
    }
}

fn read_harness_mode(input: &mut dyn Read) -> io::Result<HarnessMode> {
    match read_u8(input)? {
        0 => Ok(HarnessMode::None),
        1 => Ok(HarnessMode::Test),
        2 => Ok(HarnessMode::Bench),
        other => Err(io::Error::other(format!(
            "invalid harness mode tag: {other}",
        ))),
    }
}

fn read_u8(input: &mut dyn Read) -> io::Result<u8> {
    let mut buf = [0u8; 1];
    input.read_exact(&mut buf)?;
    Ok(buf[0])
}

fn read_u32(input: &mut dyn Read) -> io::Result<u32> {
    let mut buf = [0u8; 4];
    input.read_exact(&mut buf)?;
    Ok(u32::from_le_bytes(buf))
}

fn read_bool(input: &mut dyn Read) -> io::Result<bool> {
    match read_u8(input)? {
        0 => Ok(false),
        1 => Ok(true),
        other => Err(io::Error::other(format!("invalid boolean value: {other}"))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    fn sample_header() -> MetadataHeader {
        MetadataHeader {
            compiler_revision: "rev".into(),
            package_identifier: "std".into(),
            package_index: 0,
            target_triple: "x86_64-unknown-linux-gnu".into(),
            target_cpu: "generic".into(),
            target_features: "".into(),
            profile: "release".into(),
            optimization: "baseline".into(),
            lto: "off".into(),
            overflow_checks: false,
            no_std_prelude: true,
            harness_mode: HarnessMode::None,
            package_fingerprint: "pkg-fp".into(),
            dependency_fingerprints: vec![],
            artifact_kind: Some(ModuleArtifactKind::Object),
            artifact_relpath: Some("std.o".into()),
            stack_map_descriptors_relpath: Some("std.stackmaps".into()),
            pc_metadata_relpath: Some("std.pcmeta.o".into()),
            payload_checksum_hex: "checksum".into(),
            has_semantic_payload: true,
            has_mir_payload: true,
            has_artifact_ref: true,
            frontend_reusable: true,
        }
    }

    fn sample_payload() -> wire::MetadataPayloadWire {
        wire::MetadataPayloadWire {
            file_table: vec![],
            semantic_payload: Some(vec![1, 2, 3]),
            mir_payload: Some(vec![4, 5, 6]),
            inline_mir_payload: Some(vec![7, 8, 9]),
            std_items: None,
            synthetic_definitions: vec![],
            emitted_instances: vec![],
        }
    }

    #[test]
    fn attached_metadata_skips_invocation_options_but_keeps_integrity_gates() {
        crate::mir::test_support::with_test_gcx(|gcx| {
            let payload = bincode::serialize(&sample_payload()).unwrap();
            let mut header = sample_header();
            header.compiler_revision = compiler_revision_stamp();
            header.package_identifier = gcx.config.identifier.to_string();
            header.package_index = gcx.package_index().raw() as u32;
            header.target_triple = gcx
                .store
                .target_layout
                .triple()
                .as_str()
                .to_string_lossy()
                .into_owned();
            header.target_cpu = gcx.store.target_layout.cpu().into();
            header.target_features = gcx.store.target_layout.features().into();
            header.optimization = optimization_name(gcx.config.codegen.optimization).into();
            header.lto = lto_name(gcx.config.codegen.lto).into();
            header.artifact_kind = Some(gcx.config.codegen.artifact);
            header.payload_checksum_hex = blake3::hash(&payload).to_hex().to_string();
            header.profile = profile_name(gcx.config.profile).into();
            header.overflow_checks = gcx.config.overflow_checks;
            header.no_std_prelude = gcx.config.no_std_prelude;
            header.harness_mode = gcx.config.harness_mode;
            let fingerprint = PackageFingerprintInput {
                package_fingerprint: header.package_fingerprint.clone(),
                dependencies: vec![],
            };
            let decode = |header: &MetadataHeader, cached: bool| {
                validate_and_decode_payload(
                    gcx,
                    header,
                    &payload,
                    ReuseMode::SemanticDependency,
                    cached.then_some(&fingerprint),
                )
            };
            assert!(decode(&header, true).is_ok());
            assert!(decode(&header, false).is_ok());
            let mut invocation = header.clone();
            invocation.profile = "different-profile".into();
            invocation.package_fingerprint = "different-source".into();
            assert_eq!(
                decode(&invocation, true).unwrap_err(),
                "metadata profile mismatch"
            );
            assert!(decode(&invocation, false).is_ok());
            for cached in [true, false] {
                let mut legacy = header.clone();
                legacy.compiler_revision = env!("CARGO_PKG_VERSION").into();
                assert_eq!(
                    decode(&legacy, cached).unwrap_err(),
                    "metadata compiler revision mismatch"
                );
                let mut corrupt = header.clone();
                corrupt.payload_checksum_hex.clear();
                assert_eq!(
                    decode(&corrupt, cached).unwrap_err(),
                    "metadata payload checksum mismatch"
                );
                let mut incompatible = header.clone();
                incompatible.target_cpu = "different-cpu".into();
                assert_eq!(
                    decode(&incompatible, cached).unwrap_err(),
                    "metadata target CPU/features mismatch"
                );
            }
        });
    }

    #[test]
    fn mir_retention_preserves_closures_cycles_and_final_only_callees() {
        use crate::mir::{
            AggregateKind, Constant, ConstantKind, MirPackage, Operand, Place, Rvalue, Statement,
            StatementKind,
            test_support::{minimal_body, with_test_gcx},
        };
        use crate::sema::resolve::models::DefinitionIndex;
        with_test_gcx(|gcx| {
            let def =
                |index| DefinitionID::new(gcx.package_index(), DefinitionIndex::from_raw(index));
            let args = gcx.store.interners.intern_generic_args(vec![]);
            let make_body = |owner, callees: &[u32]| {
                let mut body = minimal_body(gcx);
                body.owner = def(owner);
                let span = body.locals[body.return_local].span;
                for &callee in callees {
                    body.basic_blocks[body.start_block]
                        .statements
                        .push(Statement {
                            span,
                            kind: StatementKind::KeepAlive(Operand::Constant(Constant {
                                ty: gcx.types.void,
                                value: ConstantKind::Function(def(callee), args, gcx.types.void),
                            })),
                        });
                }
                body
            };
            let mut root = make_body(0, &[]);
            root.basic_blocks[root.start_block]
                .statements
                .push(Statement {
                    span: root.locals[root.return_local].span,
                    kind: StatementKind::Assign(
                        Place::from_local(root.return_local),
                        Rvalue::Aggregate {
                            kind: AggregateKind::Closure {
                                def_id: def(1),
                                captured_generics: args,
                            },
                            fields: Default::default(),
                        },
                    ),
                });
            // The closure reaches a cycle and an external definition without local MIR.
            let closure = make_body(1, &[2, 4]);
            let cycle = make_body(2, &[0]);
            let unreferenced = make_body(3, &[]);
            let late_callee = make_body(5, &[]);
            let canonical = MirPackage {
                functions: [&root, &closure, &cycle, &unreferenced, &late_callee]
                    .into_iter()
                    .map(|body| (body.owner, body))
                    .collect(),
                entry: None,
            };
            let inline_retained = reachable_mir_defs(&canonical, [def(0)]);
            assert_eq!(
                inline_retained,
                [def(0), def(1), def(2)].into_iter().collect()
            );

            // Final lowering replaces the closure edge with a synthesized callee.
            // Canonical candidates must survive, and only final MIR expands to it.
            let final_root = make_body(0, &[5]);
            let mut final_package = MirPackage {
                functions: canonical.functions.clone(),
                entry: None,
            };
            final_package.functions.insert(def(0), &final_root);
            let final_retained = reachable_mir_defs(&final_package, inline_retained);
            assert_eq!(
                final_retained,
                [def(0), def(1), def(2), def(5)].into_iter().collect()
            );
        });
    }

    #[test]
    fn mode_capabilities_reject_codegen_without_mir() {
        let mut header = sample_header();
        header.has_mir_payload = false;
        let err = validate_mode_capabilities(&header, ReuseMode::CodegenDependency).unwrap_err();
        assert!(err.contains("codegen"));
    }

    #[test]
    fn mode_capabilities_allow_semantic_only_metadata() {
        let mut header = sample_header();
        header.has_mir_payload = false;
        header.has_artifact_ref = false;
        header.artifact_kind = None;
        header.artifact_relpath = None;
        header.stack_map_descriptors_relpath = None;
        header.pc_metadata_relpath = None;
        assert!(validate_mode_capabilities(&header, ReuseMode::SemanticDependency).is_ok());
    }

    #[test]
    fn mode_capabilities_allow_root_artifact_without_mir() {
        let mut header = sample_header();
        header.has_mir_payload = false;
        assert!(validate_mode_capabilities(&header, ReuseMode::CodegenRoot).is_ok());
    }

    #[test]
    fn payload_capability_mismatch_is_detected() {
        let mut header = sample_header();
        header.has_mir_payload = false;
        let payload = sample_payload();
        let err = validate_payload_capabilities(&header, &payload).unwrap_err();
        assert!(err.contains("MIR capability mismatch"));
    }

    #[test]
    fn read_envelope_rejects_corrupted_magic() {
        let header = sample_header();
        let payload = b"payload";
        let mut bytes = Vec::new();
        write_envelope(&mut bytes, &header, payload).expect("envelope write should succeed");
        bytes[..META_MAGIC.len()].copy_from_slice(b"NOTAMETA");

        let mut cursor = Cursor::new(bytes);
        let err = read_envelope(&mut cursor).unwrap_err();
        assert!(err.to_string().contains("magic mismatch"));
    }

    #[test]
    fn envelope_round_trip_preserves_codegen_identity() {
        let header = sample_header();
        let payload = b"payload";
        let mut bytes = Vec::new();
        write_envelope(&mut bytes, &header, payload).expect("envelope write should succeed");

        let (decoded, decoded_payload) =
            read_envelope(&mut Cursor::new(bytes)).expect("envelope should decode");
        assert_eq!(decoded.target_triple, header.target_triple);
        assert_eq!(decoded.target_cpu, header.target_cpu);
        assert_eq!(decoded.target_features, header.target_features);
        assert_eq!(decoded.optimization, header.optimization);
        assert_eq!(decoded.lto, header.lto);
        assert_eq!(decoded.harness_mode, header.harness_mode);
        assert_eq!(decoded.artifact_kind, header.artifact_kind);
        assert_eq!(decoded.artifact_relpath, header.artifact_relpath);
        assert_eq!(
            decoded.stack_map_descriptors_relpath,
            header.stack_map_descriptors_relpath
        );
        assert_eq!(decoded.pc_metadata_relpath, header.pc_metadata_relpath);
        assert_eq!(decoded_payload, payload);
    }

    #[test]
    fn metadata_names_all_lto_modes() {
        assert_eq!(lto_name(LtoMode::Off), "off");
        assert_eq!(lto_name(LtoMode::Full), "full");
        assert_eq!(lto_name(LtoMode::Thin), "thin");
    }

    #[test]
    fn envelope_round_trip_preserves_bitcode_artifact_identity() {
        let mut header = sample_header();
        header.artifact_kind = Some(ModuleArtifactKind::LlvmBitcode);
        header.artifact_relpath = Some("std.bc".into());
        header.pc_metadata_relpath = None;
        let mut bytes = Vec::new();
        write_envelope(&mut bytes, &header, b"payload").expect("envelope write should succeed");

        let (decoded, _) = read_envelope(&mut Cursor::new(bytes)).expect("envelope should decode");
        assert_eq!(decoded.artifact_kind, Some(ModuleArtifactKind::LlvmBitcode));
        assert_eq!(decoded.artifact_relpath.as_deref(), Some("std.bc"));
    }

    #[test]
    fn artifact_capability_mismatch_is_detected() {
        let mut header = sample_header();
        header.artifact_kind = Some(ModuleArtifactKind::LlvmBitcode);
        header.artifact_relpath = None;

        let error = validate_artifact_header(&header).unwrap_err();
        assert!(error.contains("artifact capability mismatch"));
    }

    #[test]
    fn metadata_artifact_paths_cannot_escape_the_output_directory() {
        let output = Path::new("/workspace/target/debug/objects");
        assert_eq!(
            resolve_metadata_artifact_path(output, "deps/library.bc").unwrap(),
            output.join("deps/library.bc")
        );
        assert!(resolve_metadata_artifact_path(output, "../library.bc").is_err());
        assert!(resolve_metadata_artifact_path(output, "/tmp/library.bc").is_err());
    }

    #[test]
    fn read_envelope_rejects_old_metadata_version() {
        let header = sample_header();
        let payload = b"payload";
        let mut bytes = Vec::new();
        write_envelope(&mut bytes, &header, payload).expect("envelope write should succeed");

        let stale_version = META_FORMAT_VERSION
            .checked_sub(1)
            .expect("metadata format version should be positive");
        let version_offset = META_MAGIC.len();
        bytes[version_offset..version_offset + 4].copy_from_slice(&stale_version.to_le_bytes());

        let mut cursor = Cursor::new(bytes);
        let err = read_envelope(&mut cursor).unwrap_err();
        assert!(err.to_string().contains("version mismatch"));
    }
}
