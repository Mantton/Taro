use crate::package::manifest::Manifest;
use compiler::{constants::MANIFEST_FILE, error::ReportedError};
use std::path::PathBuf;

pub fn sync_dependencies(root: PathBuf) -> Result<(), ReportedError> {
    // TODO: Lockfile
    let _ = download_packages(root).map_err(|err| ReportedError)?; // TODO: report
    Ok(())
}

pub fn download_packages(root: PathBuf) -> Result<(), String> {
    let root_manifest = Manifest::parse(&root.join(MANIFEST_FILE))?;
    let package_name = root_manifest.package_name();
    Ok(())
}
