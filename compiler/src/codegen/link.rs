use std::{fs, path::PathBuf, process::Command};

use crate::{compile::config::PackageKind, compile::context::GlobalContext, error::CompileResult};

/// Link all known object files into a single executable for the current package.
/// Assumes `taro_start`/`main` are already present in the LLVM output.
pub fn link_executable(gcx: GlobalContext) -> CompileResult<Option<PathBuf>> {
    let objects = gcx.all_object_files();
    if objects.is_empty() {
        gcx.dcx()
            .emit_error("no object files available for linking".into(), None);
        return Err(crate::error::ReportedError);
    }

    // Only produce an executable for executable/both packages.
    match gcx.config.kind {
        PackageKind::Executable | PackageKind::Both => {}
        PackageKind::Library => return Ok(None),
    }

    let out_dir = gcx.output_root().clone();
    if let Err(e) = fs::create_dir_all(&out_dir) {
        let msg = format!("failed to create output directory: {e}");
        gcx.dcx().emit_error(msg.into(), None);
        return Err(crate::error::ReportedError);
    }
    let base = out_dir
        .parent()
        .map(|p| p.to_path_buf())
        .unwrap_or(out_dir.clone());
    let output = gcx
        .config
        .executable_out
        .clone()
        .unwrap_or_else(|| base.join(gcx.config.identifier.as_ref()));

    let mut cmd = Command::new("clang");
    cmd.args(objects.iter().map(PathBuf::as_path));
    cmd.arg("-o").arg(&output);

    // On macOS, ensure the SDK root is set so -lSystem can be found.
    #[cfg(target_os = "macos")]
    if let Some(sdk_path) = macos_sdk_path() {
        cmd.arg("-isysroot").arg(&sdk_path);
        cmd.arg(format!("-Wl,-syslibroot,{}", sdk_path.display()));
    }

    match cmd.status() {
        Ok(status) if status.success() => Ok(Some(output)),
        Ok(status) => {
            let msg = format!("linker failed with status {status}");
            gcx.dcx().emit_error(msg.into(), None);
            Err(crate::error::ReportedError)
        }
        Err(e) => {
            let msg = format!("failed to invoke linker: {e}");
            gcx.dcx().emit_error(msg.into(), None);
            Err(crate::error::ReportedError)
        }
    }
}

#[cfg(target_os = "macos")]
fn macos_sdk_path() -> Option<PathBuf> {
    let out = Command::new("xcrun")
        .args(["--sdk", "macosx", "--show-sdk-path"])
        .output()
        .ok()?;
    if !out.status.success() {
        return None;
    }
    let raw = String::from_utf8_lossy(&out.stdout);
    let path = raw.trim();
    if path.is_empty() {
        None
    } else {
        Some(PathBuf::from(path))
    }
}
