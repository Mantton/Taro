//! Runtime archive compatibility manifests.
//!
//! A manifest is generated beside every runtime archive and validated before
//! the archive reaches the linker. This turns wrong-target, stale-ABI, and
//! mismatched archive failures into deterministic compiler diagnostics.

use compiler::runtime_abi::{
    RUNTIME_ABI_REVISION, RUNTIME_MANIFEST_SCHEMA, fingerprint, required_symbols_for_target,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::{
    collections::HashSet,
    ffi::OsString,
    fs,
    path::{Path, PathBuf},
    process::Command,
};

const MANIFEST_SUFFIX: &str = ".manifest.toml";

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
struct RuntimeArtifactManifest {
    schema_version: u32,
    abi_revision: u32,
    abi_fingerprint: String,
    target: String,
    architecture: String,
    archive_sha256: String,
}

pub(crate) fn manifest_path(archive: &Path) -> PathBuf {
    let mut filename = archive
        .file_name()
        .map(OsString::from)
        .unwrap_or_else(|| OsString::from("libtaro_runtime.a"));
    filename.push(MANIFEST_SUFFIX);
    archive.with_file_name(filename)
}

/// Validate the runtime exports, then write the compatibility manifest beside
/// the archive. `target == None` deliberately records a host-only artifact.
pub(crate) fn write_manifest(archive: &Path, target: Option<&str>) -> Result<PathBuf, String> {
    let bytes = read_archive(archive)?;
    let architecture = archive_architecture(&bytes)?;
    let target_label = target.unwrap_or("host");
    let symbol_target = target.unwrap_or(if cfg!(unix) { "host-unix" } else { "host" });

    if let Some(target) = target {
        ensure_target_architecture(target, &architecture)?;
    }
    validate_required_symbols(archive, symbol_target)?;

    let manifest = RuntimeArtifactManifest {
        schema_version: RUNTIME_MANIFEST_SCHEMA,
        abi_revision: RUNTIME_ABI_REVISION,
        abi_fingerprint: fingerprint(),
        target: target_label.to_owned(),
        architecture,
        archive_sha256: sha256_hex(&bytes),
    };
    let serialized = toml::to_string_pretty(&manifest)
        .map_err(|error| format!("failed to serialize runtime manifest: {error}"))?;
    let path = manifest_path(archive);
    fs::write(&path, serialized).map_err(|error| {
        format!(
            "failed to write runtime manifest `{}`: {error}",
            path.display()
        )
    })?;
    Ok(path)
}

/// Validate a runtime archive against the compiler and its selected target.
pub(crate) fn validate(
    archive: &Path,
    requested_target: Option<&str>,
    effective_target: &str,
) -> Result<(), String> {
    let path = manifest_path(archive);
    let serialized = fs::read_to_string(&path).map_err(|error| {
        if error.kind() == std::io::ErrorKind::NotFound {
            format!(
                "runtime compatibility manifest not found at `{}`; regenerate the runtime distribution or run `taro runtime-manifest {}{}`",
                path.display(),
                archive.display(),
                requested_target
                    .map(|target| format!(" --target {target}"))
                    .unwrap_or_default()
            )
        } else {
            format!(
                "failed to read runtime compatibility manifest `{}`: {error}",
                path.display()
            )
        }
    })?;
    let manifest: RuntimeArtifactManifest = toml::from_str(&serialized).map_err(|error| {
        format!(
            "runtime compatibility manifest `{}` is invalid: {error}",
            path.display()
        )
    })?;

    if manifest.schema_version != RUNTIME_MANIFEST_SCHEMA {
        return Err(format!(
            "runtime manifest schema mismatch for `{}`: compiler requires {}, manifest provides {}",
            archive.display(),
            RUNTIME_MANIFEST_SCHEMA,
            manifest.schema_version
        ));
    }
    if manifest.abi_revision != RUNTIME_ABI_REVISION {
        return Err(format!(
            "runtime ABI revision mismatch for `{}`: compiler requires {}, manifest provides {}",
            archive.display(),
            RUNTIME_ABI_REVISION,
            manifest.abi_revision
        ));
    }
    let expected_fingerprint = fingerprint();
    if manifest.abi_fingerprint != expected_fingerprint {
        return Err(format!(
            "runtime ABI fingerprint mismatch for `{}`: the archive was built for a different compiler runtime ABI",
            archive.display()
        ));
    }

    let expected_target = requested_target.unwrap_or("host");
    if manifest.target != expected_target {
        return Err(format!(
            "runtime target mismatch for `{}`: compiler requested `{expected_target}`, manifest provides `{}`",
            archive.display(),
            manifest.target
        ));
    }

    let bytes = read_archive(archive)?;
    let checksum = sha256_hex(&bytes);
    if manifest.archive_sha256 != checksum {
        return Err(format!(
            "runtime archive checksum mismatch for `{}`: the archive does not match its compatibility manifest",
            archive.display()
        ));
    }

    let detected_architecture = archive_architecture(&bytes)?;
    if manifest.architecture != detected_architecture {
        return Err(format!(
            "runtime archive architecture mismatch for `{}`: manifest records `{}`, archive contains `{detected_architecture}`",
            archive.display(),
            manifest.architecture
        ));
    }
    ensure_target_architecture(effective_target, &detected_architecture)
}

fn validate_required_symbols(archive: &Path, target: &str) -> Result<(), String> {
    let output = Command::new("nm")
        .arg("-g")
        .arg(archive)
        .output()
        .map_err(|error| {
            format!(
                "failed to inspect runtime symbols in `{}` with `nm`: {error}",
                archive.display()
            )
        })?;
    if !output.status.success() {
        return Err(format!(
            "failed to inspect runtime symbols in `{}` with `nm`: {}",
            archive.display(),
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }

    let output = String::from_utf8_lossy(&output.stdout);
    let symbols = defined_symbols(&output);
    let mut missing = required_symbols_for_target(target)
        .filter(|symbol| !symbols.contains(*symbol))
        .collect::<Vec<_>>();
    missing.sort_unstable();
    if missing.is_empty() {
        return Ok(());
    }

    Err(format!(
        "runtime archive `{}` is missing required ABI symbols: {}",
        archive.display(),
        missing.join(", ")
    ))
}

fn defined_symbols(output: &str) -> HashSet<&str> {
    let mut symbols = HashSet::new();
    for line in output.lines() {
        let fields = line.split_whitespace().collect::<Vec<_>>();
        if fields.len() < 2 {
            continue;
        }
        let kind = fields[fields.len() - 2];
        if matches!(kind, "U" | "u" | "w" | "v") {
            continue;
        }
        let symbol = fields[fields.len() - 1];
        symbols.insert(symbol);
        if let Some(unprefixed) = symbol.strip_prefix('_') {
            symbols.insert(unprefixed);
        }
    }
    symbols
}

fn read_archive(archive: &Path) -> Result<Vec<u8>, String> {
    fs::read(archive).map_err(|error| {
        format!(
            "failed to read runtime archive `{}`: {error}",
            archive.display()
        )
    })
}

fn sha256_hex(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn ensure_target_architecture(target: &str, actual: &str) -> Result<(), String> {
    let expected = target_architecture(target)?;
    if expected == actual {
        return Ok(());
    }
    Err(format!(
        "runtime architecture mismatch: target `{target}` requires `{expected}`, archive contains `{actual}`"
    ))
}

fn target_architecture(target: &str) -> Result<&'static str, String> {
    let architecture = target.split('-').next().unwrap_or(target);
    match architecture {
        "aarch64" | "aarch64_be" | "arm64" | "arm64e" => Ok("aarch64"),
        "x86_64" | "x86_64h" | "amd64" => Ok("x86_64"),
        "i386" | "i486" | "i586" | "i686" | "x86" => Ok("x86"),
        architecture if architecture.starts_with("arm") || architecture.starts_with("thumb") => {
            Ok("arm")
        }
        architecture if architecture.starts_with("riscv64") => Ok("riscv64"),
        "powerpc64" | "powerpc64le" => Ok("powerpc64"),
        "powerpc" => Ok("powerpc"),
        "s390x" => Ok("s390x"),
        "loongarch64" => Ok("loongarch64"),
        architecture if architecture.starts_with("wasm") => Ok("wasm"),
        _ => Err(format!(
            "cannot determine runtime architecture for target `{target}`"
        )),
    }
}

fn archive_architecture(bytes: &[u8]) -> Result<String, String> {
    const MAGIC: &[u8] = b"!<arch>\n";
    if !bytes.starts_with(MAGIC) {
        return Err("runtime library is not a supported static archive".into());
    }

    let mut offset = MAGIC.len();
    while offset + 60 <= bytes.len() {
        let header = &bytes[offset..offset + 60];
        if &header[58..60] != b"`\n" {
            return Err("runtime archive contains an invalid member header".into());
        }
        let size_text = std::str::from_utf8(&header[48..58])
            .map_err(|_| "runtime archive contains an invalid member size")?;
        let size = size_text
            .trim()
            .parse::<usize>()
            .map_err(|_| "runtime archive contains an invalid member size")?;
        let data_start = offset + 60;
        let data_end = data_start
            .checked_add(size)
            .filter(|end| *end <= bytes.len())
            .ok_or("runtime archive member extends past the end of the file")?;
        let mut member = &bytes[data_start..data_end];

        let name = std::str::from_utf8(&header[..16]).unwrap_or("").trim();
        if let Some(length) = name.strip_prefix("#1/") {
            let length = length
                .trim()
                .parse::<usize>()
                .map_err(|_| "runtime archive contains an invalid BSD member name")?;
            if length > member.len() {
                return Err("runtime archive contains a truncated BSD member name".into());
            }
            member = &member[length..];
        }

        if let Some(architecture) = object_architecture(member) {
            return Ok(architecture.to_owned());
        }
        offset = data_end + (size & 1);
    }

    Err("could not detect an object architecture in the runtime archive".into())
}

fn object_architecture(bytes: &[u8]) -> Option<&'static str> {
    if bytes.len() >= 20 && bytes.starts_with(b"\x7fELF") {
        let machine = match bytes[5] {
            1 => u16::from_le_bytes([bytes[18], bytes[19]]),
            2 => u16::from_be_bytes([bytes[18], bytes[19]]),
            _ => return None,
        };
        return match machine {
            3 => Some("x86"),
            20 => Some("powerpc"),
            21 => Some("powerpc64"),
            22 => Some("s390x"),
            40 => Some("arm"),
            62 => Some("x86_64"),
            183 => Some("aarch64"),
            243 => Some("riscv64"),
            258 => Some("loongarch64"),
            _ => None,
        };
    }

    if bytes.len() >= 8 {
        let (little_endian, macho) = match &bytes[..4] {
            b"\xcf\xfa\xed\xfe" | b"\xce\xfa\xed\xfe" => (true, true),
            b"\xfe\xed\xfa\xcf" | b"\xfe\xed\xfa\xce" => (false, true),
            _ => (true, false),
        };
        if macho {
            let cpu = if little_endian {
                u32::from_le_bytes(bytes[4..8].try_into().ok()?)
            } else {
                u32::from_be_bytes(bytes[4..8].try_into().ok()?)
            };
            return match cpu {
                7 => Some("x86"),
                12 => Some("arm"),
                18 => Some("powerpc"),
                0x0100_0007 => Some("x86_64"),
                0x0100_000c => Some("aarch64"),
                0x0100_0012 => Some("powerpc64"),
                _ => None,
            };
        }
    }

    if bytes.starts_with(b"\0asm") {
        return Some("wasm");
    }

    if bytes.len() >= 2 {
        let machine = u16::from_le_bytes([bytes[0], bytes[1]]);
        return match machine {
            0x014c => Some("x86"),
            0x01c0 | 0x01c4 => Some("arm"),
            0x8664 => Some("x86_64"),
            0xaa64 | 0xa641 | 0xa64e => Some("aarch64"),
            _ => None,
        };
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::{SystemTime, UNIX_EPOCH};

    fn archive_with(member: &[u8]) -> Vec<u8> {
        let mut archive = b"!<arch>\n".to_vec();
        let mut header = [b' '; 60];
        header[..8].copy_from_slice(b"test.o/ ");
        let size = format!("{:<10}", member.len());
        header[48..58].copy_from_slice(size.as_bytes());
        header[58..60].copy_from_slice(b"`\n");
        archive.extend_from_slice(&header);
        archive.extend_from_slice(member);
        if member.len() % 2 != 0 {
            archive.push(b'\n');
        }
        archive
    }

    fn temp_archive(name: &str, bytes: &[u8]) -> PathBuf {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock")
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "taro-runtime-manifest-{}-{name}-{nonce}.a",
            std::process::id()
        ));
        fs::write(&path, bytes).expect("write archive");
        path
    }

    #[test]
    fn sidecar_appends_manifest_suffix() {
        assert_eq!(
            manifest_path(Path::new("/tmp/libtaro_runtime.a")),
            PathBuf::from("/tmp/libtaro_runtime.a.manifest.toml")
        );
    }

    #[test]
    fn detects_elf_and_macho_architectures() {
        let mut elf = vec![0; 20];
        elf[..4].copy_from_slice(b"\x7fELF");
        elf[5] = 1;
        elf[18..20].copy_from_slice(&183_u16.to_le_bytes());
        assert_eq!(
            archive_architecture(&archive_with(&elf)).unwrap(),
            "aarch64"
        );

        let mut macho = vec![0; 8];
        macho[..4].copy_from_slice(b"\xcf\xfa\xed\xfe");
        macho[4..8].copy_from_slice(&0x0100_0007_u32.to_le_bytes());
        assert_eq!(
            archive_architecture(&archive_with(&macho)).unwrap(),
            "x86_64"
        );
    }

    #[test]
    fn parses_defined_symbols_and_macho_prefixes() {
        let symbols = defined_symbols(
            "000000 T ___rt__async_poll\n         U ___rt__async_create\n000000 T __gc__collect\n",
        );
        assert!(symbols.contains("__rt__async_poll"));
        assert!(symbols.contains("__gc__collect"));
        assert!(!symbols.contains("__rt__async_create"));
    }

    #[test]
    fn validation_rejects_stale_abi_revision() {
        let mut object = vec![0; 20];
        object[..4].copy_from_slice(b"\x7fELF");
        object[5] = 1;
        object[18..20].copy_from_slice(&62_u16.to_le_bytes());
        let archive_bytes = archive_with(&object);
        let archive = temp_archive("stale", &archive_bytes);
        let manifest = RuntimeArtifactManifest {
            schema_version: RUNTIME_MANIFEST_SCHEMA,
            abi_revision: RUNTIME_ABI_REVISION + 1,
            abi_fingerprint: fingerprint(),
            target: "x86_64-unknown-linux-gnu".into(),
            architecture: "x86_64".into(),
            archive_sha256: sha256_hex(&archive_bytes),
        };
        fs::write(
            manifest_path(&archive),
            toml::to_string(&manifest).expect("manifest"),
        )
        .expect("write manifest");

        let error = validate(
            &archive,
            Some("x86_64-unknown-linux-gnu"),
            "x86_64-unknown-linux-gnu",
        )
        .unwrap_err();
        assert!(error.contains("ABI revision mismatch"), "{error}");

        let _ = fs::remove_file(manifest_path(&archive));
        let _ = fs::remove_file(archive);
    }

    #[test]
    fn validation_rejects_stale_abi_fingerprint() {
        let mut object = vec![0; 20];
        object[..4].copy_from_slice(b"\x7fELF");
        object[5] = 1;
        object[18..20].copy_from_slice(&62_u16.to_le_bytes());
        let archive_bytes = archive_with(&object);
        let archive = temp_archive("fingerprint", &archive_bytes);
        let manifest = RuntimeArtifactManifest {
            schema_version: RUNTIME_MANIFEST_SCHEMA,
            abi_revision: RUNTIME_ABI_REVISION,
            abi_fingerprint: "stale".into(),
            target: "x86_64-unknown-linux-gnu".into(),
            architecture: "x86_64".into(),
            archive_sha256: sha256_hex(&archive_bytes),
        };
        fs::write(
            manifest_path(&archive),
            toml::to_string(&manifest).expect("manifest"),
        )
        .expect("write manifest");

        let error = validate(
            &archive,
            Some("x86_64-unknown-linux-gnu"),
            "x86_64-unknown-linux-gnu",
        )
        .unwrap_err();
        assert!(error.contains("ABI fingerprint mismatch"), "{error}");

        let _ = fs::remove_file(manifest_path(&archive));
        let _ = fs::remove_file(archive);
    }

    #[test]
    fn validation_rejects_wrong_target_before_linking() {
        let mut object = vec![0; 20];
        object[..4].copy_from_slice(b"\x7fELF");
        object[5] = 1;
        object[18..20].copy_from_slice(&183_u16.to_le_bytes());
        let archive_bytes = archive_with(&object);
        let archive = temp_archive("target", &archive_bytes);
        let manifest = RuntimeArtifactManifest {
            schema_version: RUNTIME_MANIFEST_SCHEMA,
            abi_revision: RUNTIME_ABI_REVISION,
            abi_fingerprint: fingerprint(),
            target: "host".into(),
            architecture: "aarch64".into(),
            archive_sha256: sha256_hex(&archive_bytes),
        };
        fs::write(
            manifest_path(&archive),
            toml::to_string(&manifest).expect("manifest"),
        )
        .expect("write manifest");

        let error = validate(
            &archive,
            Some("aarch64-unknown-linux-gnu"),
            "aarch64-unknown-linux-gnu",
        )
        .unwrap_err();
        assert!(error.contains("runtime target mismatch"), "{error}");

        let _ = fs::remove_file(manifest_path(&archive));
        let _ = fs::remove_file(archive);
    }

    #[test]
    fn validation_rejects_manifest_archive_checksum_drift() {
        let mut object = vec![0; 20];
        object[..4].copy_from_slice(b"\x7fELF");
        object[5] = 1;
        object[18..20].copy_from_slice(&62_u16.to_le_bytes());
        let archive_bytes = archive_with(&object);
        let archive = temp_archive("checksum", &archive_bytes);
        let manifest = RuntimeArtifactManifest {
            schema_version: RUNTIME_MANIFEST_SCHEMA,
            abi_revision: RUNTIME_ABI_REVISION,
            abi_fingerprint: fingerprint(),
            target: "x86_64-unknown-linux-gnu".into(),
            architecture: "x86_64".into(),
            archive_sha256: "0".repeat(64),
        };
        fs::write(
            manifest_path(&archive),
            toml::to_string(&manifest).expect("manifest"),
        )
        .expect("write manifest");

        let error = validate(
            &archive,
            Some("x86_64-unknown-linux-gnu"),
            "x86_64-unknown-linux-gnu",
        )
        .unwrap_err();
        assert!(error.contains("checksum mismatch"), "{error}");

        let _ = fs::remove_file(manifest_path(&archive));
        let _ = fs::remove_file(archive);
    }

    #[test]
    fn validation_rejects_archive_for_wrong_architecture() {
        let mut object = vec![0; 20];
        object[..4].copy_from_slice(b"\x7fELF");
        object[5] = 1;
        object[18..20].copy_from_slice(&183_u16.to_le_bytes());
        let archive_bytes = archive_with(&object);
        let archive = temp_archive("architecture", &archive_bytes);
        let manifest = RuntimeArtifactManifest {
            schema_version: RUNTIME_MANIFEST_SCHEMA,
            abi_revision: RUNTIME_ABI_REVISION,
            abi_fingerprint: fingerprint(),
            target: "host".into(),
            architecture: "aarch64".into(),
            archive_sha256: sha256_hex(&archive_bytes),
        };
        fs::write(
            manifest_path(&archive),
            toml::to_string(&manifest).expect("manifest"),
        )
        .expect("write manifest");

        let error = validate(&archive, None, "x86_64-unknown-linux-gnu").unwrap_err();
        assert!(error.contains("architecture mismatch"), "{error}");

        let _ = fs::remove_file(manifest_path(&archive));
        let _ = fs::remove_file(archive);
    }
}
