pub const FILE_EXTENSION: &str = "tr";
pub const SOURCE_DIRECTORY: &str = "src";
pub const ROOT_MODULE_NAME: &str = "main";
pub const MANIFEST_FILE: &str = "package.toml";
pub const LOCK_FILE: &str = "package.lock";
pub const LANGUAGE_HOME: &str = "TARO_HOME";
/// Per-user directory for downloaded packages, kept outside the SDK so that a
/// read-only or system-wide install works and upgrades keep the cache.
pub const CACHE_HOME: &str = "TARO_CACHE";
pub const PACKAGE_STORE: &str = "packages"; // <cache>/packages
pub const PACKAGE_SOURCE: &str = "sources"; // <cache>/sources
pub const VCS_REMOTE_NAME: &str = "origin";
pub const STD_PREFIX: &str = "std";
pub const STD_PACKAGE_PATH: &str = "github.com/taro/std";
