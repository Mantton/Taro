use crate::{
    PackageIndex,
    compile::{
        config::{BuildProfile, Config},
        context::GlobalContext,
    },
};
use std::{
    fs,
    io::{self, Read, Write},
    path::{Path, PathBuf},
};

const META_MAGIC: [u8; 8] = *b"TAROMETA";
const META_FORMAT_VERSION: u32 = 1;

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
    object_relpath: String,
    payload_checksum_hex: String,
}

#[derive(Debug, Clone)]
struct MetadataPayload {
    emitted_instance_count: u32,
}

#[derive(Debug, Clone)]
pub struct LoadedMetadata {
    pub package_identifier: String,
    pub package_index: PackageIndex,
    pub object_path: PathBuf,
}

#[derive(Debug, Clone)]
pub enum MetadataLoadStatus {
    Hit(LoadedMetadata),
    Miss(String),
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
) -> io::Result<PathBuf> {
    let pkg = gcx.package_index();
    let config = gcx.config;

    let object_relpath = format!("{}.o", config.identifier);
    let object_path = gcx.output_root().join(&object_relpath);
    if !object_path.exists() {
        return Err(io::Error::new(
            io::ErrorKind::NotFound,
            format!("object file missing at '{}'", object_path.display()),
        ));
    }

    let emitted_instance_count = gcx.emitted_instances_of(pkg).len() as u32;
    let payload = encode_payload(&MetadataPayload {
        emitted_instance_count,
    });
    let checksum = blake3::hash(&payload).to_hex().to_string();

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
    };

    let path = metadata_path_for_config(config, gcx.output_root().as_path());
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }

    let mut file = fs::File::create(&path)?;
    write_envelope(&mut file, &header, &payload)?;
    file.flush()?;
    Ok(path)
}

pub fn try_load_package_metadata<'ctx>(
    gcx: GlobalContext<'ctx>,
    expected_fp: &PackageFingerprintInput,
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

    let (header, payload) = match read_envelope(&mut file) {
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

    let payload_checksum = blake3::hash(&payload).to_hex().to_string();
    if payload_checksum != header.payload_checksum_hex {
        return MetadataLoadStatus::Miss("metadata payload checksum mismatch".into());
    }

    let _payload = match decode_payload(&payload) {
        Ok(payload) => payload,
        Err(e) => {
            return MetadataLoadStatus::Miss(format!("failed to decode metadata payload: {e}"));
        }
    };

    let object_path = gcx.output_root().join(&header.object_relpath);
    if !object_path.exists() {
        return MetadataLoadStatus::Miss("cached object file missing".into());
    }

    MetadataLoadStatus::Hit(LoadedMetadata {
        package_identifier: header.package_identifier,
        package_index: PackageIndex::new(header.package_index as usize),
        object_path,
    })
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

    write_string(&mut out, &header.object_relpath);
    write_string(&mut out, &header.payload_checksum_hex);
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

    let object_relpath = read_string(&mut cursor)?;
    let payload_checksum_hex = read_string(&mut cursor)?;

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
    })
}

fn encode_payload(payload: &MetadataPayload) -> Vec<u8> {
    payload.emitted_instance_count.to_le_bytes().to_vec()
}

fn decode_payload(bytes: &[u8]) -> io::Result<MetadataPayload> {
    if bytes.len() != 4 {
        return Err(io::Error::other("invalid metadata payload length"));
    }

    let mut count = [0u8; 4];
    count.copy_from_slice(bytes);
    Ok(MetadataPayload {
        emitted_instance_count: u32::from_le_bytes(count),
    })
}

fn write_string(out: &mut Vec<u8>, value: &str) {
    out.extend_from_slice(&(value.len() as u32).to_le_bytes());
    out.extend_from_slice(value.as_bytes());
}

fn read_string(input: &mut dyn Read) -> io::Result<String> {
    let len = read_u32(input)? as usize;
    let mut bytes = vec![0u8; len];
    input.read_exact(&mut bytes)?;
    String::from_utf8(bytes).map_err(|e| io::Error::other(format!("invalid utf8 string: {e}")))
}

fn read_u32(input: &mut dyn Read) -> io::Result<u32> {
    let mut buf = [0u8; 4];
    input.read_exact(&mut buf)?;
    Ok(u32::from_le_bytes(buf))
}

fn read_bool(input: &mut dyn Read) -> io::Result<bool> {
    let mut buf = [0u8; 1];
    input.read_exact(&mut buf)?;
    match buf[0] {
        0 => Ok(false),
        1 => Ok(true),
        other => Err(io::Error::other(format!("invalid boolean value: {other}"))),
    }
}
