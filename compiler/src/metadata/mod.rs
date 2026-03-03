use crate::{
    PackageIndex,
    compile::{
        config::{BuildProfile, Config},
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
const META_FORMAT_VERSION: u32 = 5;

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
    SemanticDependency,
}

#[derive(Debug, Clone)]
struct MetadataHeader {
    compiler_revision: String,
    package_identifier: String,
    package_index: u32,
    target_triple: String,
    profile: String,
    overflow_checks: bool,
    no_std_prelude: bool,
    test_mode: bool,
    package_fingerprint: String,
    dependency_fingerprints: Vec<DependencyFingerprint>,
    object_relpath: Option<String>,
    payload_checksum_hex: String,
    has_semantic_payload: bool,
    has_mir_payload: bool,
    has_object_ref: bool,
    frontend_reusable: bool,
}

#[derive(Debug, Clone)]
pub struct LoadedMetadata {
    pub package_identifier: String,
    pub package_index: PackageIndex,
    pub object_path: Option<PathBuf>,
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
            if !(header.has_semantic_payload && header.has_mir_payload && header.has_object_ref) {
                return Err("metadata missing required codegen capabilities".into());
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
    Ok(())
}

fn compiler_revision_stamp() -> String {
    std::option_env!("VERGEN_GIT_SHA")
        .unwrap_or(env!("CARGO_PKG_VERSION"))
        .to_string()
}

fn profile_name(profile: BuildProfile) -> &'static str {
    match profile {
        BuildProfile::Debug => "debug",
        BuildProfile::Release => "release",
    }
}

fn metadata_dir(output_root: &Path) -> PathBuf {
    output_root
        .parent()
        .map(|p| p.join("metadata"))
        .unwrap_or_else(|| output_root.join("metadata"))
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

    let object_relpath = match mode {
        ReuseMode::CodegenDependency => {
            let object_relpath = format!("{}.o", config.identifier);
            let object_path = gcx.output_root().join(&object_relpath);
            if !object_path.exists() {
                return Err(io::Error::new(
                    io::ErrorKind::NotFound,
                    format!("object file missing at '{}'", object_path.display()),
                ));
            }
            Some(object_relpath)
        }
        ReuseMode::SemanticDependency => None,
    };

    let payload = build_payload_wire(gcx, mode)?;
    let payload_bytes = bincode::serialize(&payload)
        .map_err(|e| io::Error::other(format!("failed to serialize metadata payload: {e}")))?;
    let checksum = blake3::hash(&payload_bytes).to_hex().to_string();

    let has_semantic_payload = payload.semantic_payload.is_some();
    let has_mir_payload = payload.mir_payload.is_some();
    let has_object_ref = object_relpath.is_some();
    let frontend_reusable = match mode {
        ReuseMode::CodegenDependency => has_semantic_payload && has_mir_payload && has_object_ref,
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
        profile: profile_name(config.profile).to_string(),
        overflow_checks: config.overflow_checks,
        no_std_prelude: config.no_std_prelude,
        test_mode: config.test_mode,
        package_fingerprint: fp.package_fingerprint.clone(),
        dependency_fingerprints: fp.dependencies.clone(),
        object_relpath,
        payload_checksum_hex: checksum,
        has_semantic_payload,
        has_mir_payload,
        has_object_ref,
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

    if header.compiler_revision != compiler_revision_stamp() {
        return MetadataLoadStatus::Miss("metadata compiler revision mismatch".into());
    }
    if header.package_identifier != config.identifier.as_ref() {
        return MetadataLoadStatus::Miss("metadata package identifier mismatch".into());
    }
    if header.package_index != config.index.raw() as u32 {
        return MetadataLoadStatus::Miss("metadata package index mismatch".into());
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
        return MetadataLoadStatus::Miss("metadata target mismatch".into());
    }
    if header.profile != profile_name(config.profile) {
        return MetadataLoadStatus::Miss("metadata profile mismatch".into());
    }
    if header.overflow_checks != config.overflow_checks
        || header.no_std_prelude != config.no_std_prelude
        || header.test_mode != config.test_mode
    {
        return MetadataLoadStatus::Miss("metadata compile option mismatch".into());
    }
    if header.package_fingerprint != expected_fp.package_fingerprint {
        return MetadataLoadStatus::Miss("metadata package fingerprint mismatch".into());
    }

    if header.dependency_fingerprints.len() != expected_fp.dependencies.len() {
        return MetadataLoadStatus::Miss("metadata dependency fingerprint count mismatch".into());
    }

    for (actual, expected) in header
        .dependency_fingerprints
        .iter()
        .zip(expected_fp.dependencies.iter())
    {
        if actual.identifier != expected.identifier || actual.fingerprint != expected.fingerprint {
            return MetadataLoadStatus::Miss("metadata dependency fingerprint mismatch".into());
        }
    }

    let payload_checksum = blake3::hash(&payload_bytes).to_hex().to_string();
    if payload_checksum != header.payload_checksum_hex {
        return MetadataLoadStatus::Miss("metadata payload checksum mismatch".into());
    }

    if !header.frontend_reusable {
        return MetadataLoadStatus::Miss("metadata marked non-reusable".into());
    }

    if let Err(message) = validate_mode_capabilities(&header, mode) {
        return MetadataLoadStatus::Miss(message);
    }

    let payload: wire::MetadataPayloadWire = match bincode::deserialize(&payload_bytes) {
        Ok(payload) => payload,
        Err(e) => {
            return MetadataLoadStatus::Miss(format!("failed to decode metadata payload: {e}"));
        }
    };

    if let Err(message) = validate_payload_capabilities(&header, &payload) {
        return MetadataLoadStatus::Miss(message);
    }

    let object_path = if header.has_object_ref {
        let Some(object_relpath) = header.object_relpath.as_ref() else {
            return MetadataLoadStatus::Miss("metadata object reference missing".into());
        };
        let object_path = gcx.output_root().join(object_relpath);
        if matches!(mode, ReuseMode::CodegenDependency) && !object_path.exists() {
            return MetadataLoadStatus::Miss("cached object file missing".into());
        }
        if object_path.exists() {
            Some(object_path)
        } else {
            None
        }
    } else {
        None
    };

    MetadataLoadStatus::Hit(LoadedMetadata {
        package_identifier: header.package_identifier,
        package_index: PackageIndex::new(header.package_index as usize),
        object_path,
        payload,
    })
}

/// Load metadata from explicit artifact paths (used for attached/prebuilt std artifacts).
///
/// This path intentionally skips local profile/options/fingerprint matching because
/// attached artifacts are validated by compiler revision + target + checksum + payload
/// capability gates instead.
pub fn try_load_package_metadata_from_paths<'ctx>(
    gcx: GlobalContext<'ctx>,
    mode: ReuseMode,
    metadata_path: &Path,
    object_path: Option<&Path>,
) -> MetadataLoadStatus {
    let config = gcx.config;
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

    if header.compiler_revision != compiler_revision_stamp() {
        return MetadataLoadStatus::Miss("metadata compiler revision mismatch".into());
    }
    if header.package_identifier != config.identifier.as_ref() {
        return MetadataLoadStatus::Miss("metadata package identifier mismatch".into());
    }
    if header.package_index != config.index.raw() as u32 {
        return MetadataLoadStatus::Miss("metadata package index mismatch".into());
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
        return MetadataLoadStatus::Miss("metadata target mismatch".into());
    }

    let payload_checksum = blake3::hash(&payload_bytes).to_hex().to_string();
    if payload_checksum != header.payload_checksum_hex {
        return MetadataLoadStatus::Miss("metadata payload checksum mismatch".into());
    }

    if !header.frontend_reusable {
        return MetadataLoadStatus::Miss("metadata marked non-reusable".into());
    }

    if let Err(message) = validate_mode_capabilities(&header, mode) {
        return MetadataLoadStatus::Miss(message);
    }

    let payload: wire::MetadataPayloadWire = match bincode::deserialize(&payload_bytes) {
        Ok(payload) => payload,
        Err(e) => {
            return MetadataLoadStatus::Miss(format!("failed to decode metadata payload: {e}"));
        }
    };

    if let Err(message) = validate_payload_capabilities(&header, &payload) {
        return MetadataLoadStatus::Miss(message);
    }

    let object_path = match mode {
        ReuseMode::CodegenDependency => {
            let Some(path) = object_path else {
                return MetadataLoadStatus::Miss("object file path not provided".into());
            };
            if !path.exists() {
                return MetadataLoadStatus::Miss(format!(
                    "object file missing at '{}'",
                    path.display()
                ));
            }
            Some(path.to_path_buf())
        }
        ReuseMode::SemanticDependency => object_path
            .filter(|path| path.exists())
            .map(|path| path.to_path_buf()),
    };

    MetadataLoadStatus::Hit(LoadedMetadata {
        package_identifier: header.package_identifier,
        package_index: PackageIndex::new(header.package_index as usize),
        object_path,
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
    let resolution_output = wire::resolution_output_from_wire(gcx, &semantic.resolution, remap, symbol_table)
        .map_err(|e| HydrationError::new(format!("failed to decode resolution payload: {e}")))?;
    let type_db = wire::type_database_from_wire(gcx, &semantic.type_db, remap, symbol_table);
    let decoded_mir = if matches!(mode, ReuseMode::CodegenDependency) {
        let Some(mir_payload) = loaded.payload.mir_payload.as_deref() else {
            return Err(HydrationError::new("metadata missing MIR payload"));
        };
        let mir_payload: wire::MirPackageWire = bincode::deserialize(mir_payload)
            .map_err(|e| HydrationError::new(format!("failed to decode MIR payload: {e}")))?;
        Some(wire::mir_package_from_wire(gcx, &mir_payload, remap))
    } else {
        None
    };

    if let Some(symbol_id) = invalid_symbol_id.get() {
        return Err(HydrationError::new(format!(
            "metadata references unknown symbol table id {}",
            symbol_id
        )));
    }

    let cached_object_path = if let Some(object_path) = loaded.object_path.as_ref() {
        Some(object_path.clone())
    } else if matches!(mode, ReuseMode::CodegenDependency) {
        return Err(HydrationError::new("metadata missing object reference"));
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

    if let Some(object_path) = cached_object_path {
        gcx.cache_object_file(object_path);
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

    let mir = match mode {
        ReuseMode::CodegenDependency => {
            let mir_packages = gcx.store.mir_packages.borrow();
            mir_packages.get(&pkg).copied().map(|package| {
                let retained = retained_mir_defs_for_metadata(gcx, package);
                wire::mir_package_to_wire_filtered(package, |def_id, _body| {
                    retained.contains(&def_id)
                })
            })
        }
        ReuseMode::SemanticDependency => None,
    };
    let mir_payload = match mir {
        Some(mir) => Some(
            bincode::serialize(&mir)
                .map_err(|e| io::Error::other(format!("failed to serialize MIR payload: {e}")))?,
        ),
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
        std_items,
        synthetic_definitions,
        emitted_instances,
    })
}

fn retained_mir_defs_for_metadata<'ctx>(
    gcx: GlobalContext<'ctx>,
    package: &crate::mir::MirPackage<'ctx>,
) -> FxHashSet<DefinitionID> {
    let mut retained = FxHashSet::default();
    let mut worklist: Vec<DefinitionID> = package
        .functions
        .iter()
        .filter_map(|(def_id, body)| {
            if should_retain_mir_root_for_metadata(gcx, *def_id, body) {
                Some(*def_id)
            } else {
                None
            }
        })
        .collect();
    let mut local_callees = Vec::new();

    while let Some(def_id) = worklist.pop() {
        if !retained.insert(def_id) {
            continue;
        }

        let Some(body) = package.functions.get(&def_id).copied() else {
            continue;
        };

        local_callees.clear();
        crate::mir::for_each_function_constant_in_body(body, |callee, _args| {
            local_callees.push(callee);
        });
        for callee in local_callees.iter().copied() {
            if package.functions.contains_key(&callee) && !retained.contains(&callee) {
                worklist.push(callee);
            }
        }
    }

    retained
}

fn should_retain_mir_root_for_metadata<'ctx>(
    gcx: GlobalContext<'ctx>,
    def_id: DefinitionID,
    body: &Body<'_>,
) -> bool {
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

    // Keep concretely-small callees that the inliner can pick up heuristically.
    // ABI-restricted callees are never inlined and don't need MIR in metadata.
    let signature = gcx.get_signature(def_id);
    if matches!(signature.abi, Some(Abi::Intrinsic | Abi::C | Abi::Runtime)) {
        return false;
    }

    crate::mir::optimize::inline::is_body_small(body)
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
    write_string(&mut out, &header.profile);
    out.push(header.overflow_checks as u8);
    out.push(header.no_std_prelude as u8);
    out.push(header.test_mode as u8);
    write_string(&mut out, &header.package_fingerprint);

    out.extend_from_slice(&(header.dependency_fingerprints.len() as u32).to_le_bytes());
    for dep in &header.dependency_fingerprints {
        write_string(&mut out, &dep.identifier);
        write_string(&mut out, &dep.fingerprint);
    }

    write_optional_string(&mut out, header.object_relpath.as_deref());
    write_string(&mut out, &header.payload_checksum_hex);
    out.push(header.has_semantic_payload as u8);
    out.push(header.has_mir_payload as u8);
    out.push(header.has_object_ref as u8);
    out.push(header.frontend_reusable as u8);
    out
}

fn decode_header(bytes: &[u8]) -> io::Result<MetadataHeader> {
    let mut cursor = std::io::Cursor::new(bytes);
    let compiler_revision = read_string(&mut cursor)?;
    let package_identifier = read_string(&mut cursor)?;
    let package_index = read_u32(&mut cursor)?;
    let target_triple = read_string(&mut cursor)?;
    let profile = read_string(&mut cursor)?;

    let overflow_checks = read_bool(&mut cursor)?;
    let no_std_prelude = read_bool(&mut cursor)?;
    let test_mode = read_bool(&mut cursor)?;

    let package_fingerprint = read_string(&mut cursor)?;

    let dep_count = read_u32(&mut cursor)? as usize;
    let mut dependency_fingerprints = Vec::with_capacity(dep_count);
    for _ in 0..dep_count {
        dependency_fingerprints.push(DependencyFingerprint {
            identifier: read_string(&mut cursor)?,
            fingerprint: read_string(&mut cursor)?,
        });
    }

    let object_relpath = read_optional_string(&mut cursor)?;
    let payload_checksum_hex = read_string(&mut cursor)?;
    let has_semantic_payload = read_bool(&mut cursor)?;
    let has_mir_payload = read_bool(&mut cursor)?;
    let has_object_ref = read_bool(&mut cursor)?;
    let frontend_reusable = read_bool(&mut cursor)?;

    Ok(MetadataHeader {
        compiler_revision,
        package_identifier,
        package_index,
        target_triple,
        profile,
        overflow_checks,
        no_std_prelude,
        test_mode,
        package_fingerprint,
        dependency_fingerprints,
        object_relpath,
        payload_checksum_hex,
        has_semantic_payload,
        has_mir_payload,
        has_object_ref,
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
            profile: "release".into(),
            overflow_checks: false,
            no_std_prelude: true,
            test_mode: false,
            package_fingerprint: "pkg-fp".into(),
            dependency_fingerprints: vec![],
            object_relpath: Some("std.o".into()),
            payload_checksum_hex: "checksum".into(),
            has_semantic_payload: true,
            has_mir_payload: true,
            has_object_ref: true,
            frontend_reusable: true,
        }
    }

    fn sample_payload() -> wire::MetadataPayloadWire {
        wire::MetadataPayloadWire {
            file_table: vec![],
            semantic_payload: Some(vec![1, 2, 3]),
            mir_payload: Some(vec![4, 5, 6]),
            std_items: None,
            synthetic_definitions: vec![],
            emitted_instances: vec![],
        }
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
        header.has_object_ref = false;
        assert!(validate_mode_capabilities(&header, ReuseMode::SemanticDependency).is_ok());
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
}
