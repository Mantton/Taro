use compiler::compile::config::BuildProfile;
use std::{
    hash::{Hash, Hasher},
    path::{Path, PathBuf},
};

pub(super) fn profile_dir_name(profile: BuildProfile) -> &'static str {
    match profile {
        BuildProfile::Debug => "debug",
        BuildProfile::Release => "release",
    }
}

pub(super) fn script_target_dir(file_path: &Path, profile_dir: &str) -> PathBuf {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    file_path.hash(&mut hasher);
    let hash = format!("{:x}", hasher.finish());

    std::env::temp_dir()
        .join("taro-scripts")
        .join(hash)
        .join(profile_dir)
}

#[cfg(test)]
mod tests {
    use super::{profile_dir_name, script_target_dir};
    use compiler::compile::config::BuildProfile;
    use std::path::Path;

    #[test]
    fn profile_dir_names_match_build_profiles() {
        assert_eq!(profile_dir_name(BuildProfile::Debug), "debug");
        assert_eq!(profile_dir_name(BuildProfile::Release), "release");
    }

    #[test]
    fn script_target_dirs_are_profile_scoped() {
        let path = Path::new("/workspace/example/main.tr");

        let debug = script_target_dir(path, "debug");
        let release = script_target_dir(path, "release");

        assert_ne!(debug, release);
        assert_eq!(
            debug
                .parent()
                .and_then(Path::parent)
                .and_then(Path::file_name),
            Some("taro-scripts".as_ref())
        );
        assert_eq!(debug.file_name(), Some("debug".as_ref()));
        assert_eq!(release.file_name(), Some("release".as_ref()));
    }
}
