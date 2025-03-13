mod config;
mod git;
mod graph;
mod identifier;
mod lockfile;
mod manifest;
mod sync;

pub const LOCKFILE_VERSION: u8 = 1;

pub use config::CompilerConfig;
pub use git::download_dependency;
pub use identifier::PackageIdentifier;
pub use lockfile::LockFile;
pub use manifest::Manifest;
pub use sync::sync_dependencies;
