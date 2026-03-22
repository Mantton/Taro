use crate::constants::{MANIFEST_FILE, SOURCE_DIRECTORY};
use std::path::{Path, PathBuf};

pub fn resolve_package_root(file_path: &Path) -> Result<Option<PathBuf>, String> {
    let file_path = file_path
        .canonicalize()
        .map_err(|e| format!("failed to canonicalize '{}': {}", file_path.display(), e))?;

    if let Some(root) = resolve_package_root_from_src_ancestor(file_path.as_path())? {
        return Ok(Some(root));
    }

    resolve_package_root_from_manifest_ancestor(file_path.as_path())
}

pub fn resolve_package_root_from_src_ancestor(file_path: &Path) -> Result<Option<PathBuf>, String> {
    for ancestor in file_path.ancestors().skip(1) {
        if ancestor.file_name().and_then(|name| name.to_str()) != Some(SOURCE_DIRECTORY) {
            continue;
        }

        let Some(package_root) = ancestor.parent() else {
            continue;
        };
        if !package_root.join(MANIFEST_FILE).is_file() {
            continue;
        }
        if package_root_owns_file(package_root, file_path) {
            return package_root
                .canonicalize()
                .map(Some)
                .map_err(|e| format!("failed to canonicalize '{}': {}", package_root.display(), e));
        }
    }

    Ok(None)
}

pub fn resolve_package_root_from_manifest_ancestor(
    file_path: &Path,
) -> Result<Option<PathBuf>, String> {
    for ancestor in file_path.ancestors().skip(1) {
        if ancestor.join(MANIFEST_FILE).is_file() && package_root_owns_file(ancestor, file_path) {
            return ancestor
                .canonicalize()
                .map(Some)
                .map_err(|e| format!("failed to canonicalize '{}': {}", ancestor.display(), e));
        }
    }

    Ok(None)
}

pub fn package_root_owns_file(package_root: &Path, file_path: &Path) -> bool {
    file_path.starts_with(package_root.join(SOURCE_DIRECTORY))
}

#[cfg(test)]
mod tests {
    use super::resolve_package_root;
    use std::fs::{create_dir_all, write};
    use std::path::{Path, PathBuf};

    fn temp_dir(name: &str) -> PathBuf {
        let path = std::env::temp_dir().join(format!(
            "taro-package-discover-{}-{}-{}",
            name,
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("time")
                .as_nanos()
        ));
        create_dir_all(&path).expect("temp dir");
        path
    }

    fn write_file(path: &Path, contents: &str) {
        if let Some(parent) = path.parent() {
            create_dir_all(parent).expect("parent dir");
        }
        write(path, contents).expect("write file");
    }

    fn write_manifest(path: &Path, contents: &str) {
        write_file(&path.join("package.toml"), contents);
    }

    #[test]
    fn file_under_src_resolves_to_package_root() {
        let root = temp_dir("package-owner");
        write_manifest(
            &root,
            "[package]\nname = \"github.com/example/root\"\nkind = \"executable\"\n",
        );
        let file = root.join("src").join("main.tr");
        write_file(&file, "fn main() {}\n");

        let owner = resolve_package_root(&file).expect("owner").expect("package");
        assert_eq!(owner, root.canonicalize().expect("canonical root"));
    }

    #[test]
    fn prefers_nearest_nested_package() {
        let root = temp_dir("nested-package");
        write_manifest(
            &root,
            "[package]\nname = \"github.com/example/root\"\nkind = \"executable\"\n",
        );
        let nested = root.join("nested");
        write_manifest(
            &nested,
            "[package]\nname = \"github.com/example/nested\"\nkind = \"library\"\n",
        );

        let file = nested.join("src").join("lib.tr");
        write_file(&file, "fn nested() {}\n");

        let owner = resolve_package_root(&file).expect("owner").expect("package");
        assert_eq!(owner, nested.canonicalize().expect("canonical nested"));
    }

    #[test]
    fn files_outside_src_are_not_package_owned() {
        let root = temp_dir("outside-src");
        write_manifest(
            &root,
            "[package]\nname = \"github.com/example/root\"\nkind = \"executable\"\n",
        );
        let file = root.join("tests").join("main.tr");
        write_file(&file, "fn main() {}\n");

        let owner = resolve_package_root(&file).expect("owner");
        assert!(owner.is_none());
    }

    #[test]
    fn no_manifest_returns_none() {
        let root = temp_dir("script-fallback");
        let file = root.join("standalone.tr");
        write_file(&file, "fn main() {}\n");

        let owner = resolve_package_root(&file).expect("owner");
        assert!(owner.is_none());
    }
}
