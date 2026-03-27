pub use compiler::package::lockfile::{
    LockFile, LockPackage, LockSourceType, canonical_git_cache_key, equivalent, load,
    node_from_git, node_from_path, write,
};

use crate::package::manifest::{ResolvedPackage, ResolvedSource};
use compiler::package::utils::canonicalize_git_url;

pub fn node_from_resolved(package: &ResolvedPackage) -> Result<String, String> {
    match &package.source {
        ResolvedSource::Path { abs } => Ok(node_from_path(&package.package.0, abs)),
        ResolvedSource::Git { url, revision, .. } => {
            let canonical = canonicalize_git_url(url)?;
            Ok(node_from_git(
                &package.package.0,
                &canonical,
                &revision.to_string(),
            ))
        }
    }
}
