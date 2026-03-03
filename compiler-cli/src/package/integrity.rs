use std::{
    fs::File,
    io::Read,
    os::unix::ffi::OsStrExt,
    path::{Path, PathBuf},
};

pub fn hash_directory(path: &Path) -> Result<String, String> {
    if !path.is_dir() {
        return Err(format!(
            "cannot hash '{}': path is not a directory",
            path.display()
        ));
    }

    let mut hasher = blake3::Hasher::new();
    hash_directory_inner(path, path, &mut hasher)?;
    Ok(format!("blake3:{}", hasher.finalize().to_hex()))
}

fn hash_directory_inner(
    root: &Path,
    current: &Path,
    hasher: &mut blake3::Hasher,
) -> Result<(), String> {
    let mut entries: Vec<PathBuf> = std::fs::read_dir(current)
        .map_err(|e| format!("failed to read directory '{}': {}", current.display(), e))?
        .map(|entry| {
            entry.map(|e| e.path()).map_err(|e| {
                format!(
                    "failed to read directory entry in '{}': {}",
                    current.display(),
                    e
                )
            })
        })
        .collect::<Result<_, _>>()?;

    entries.sort();

    for entry in entries {
        let relative = entry.strip_prefix(root).map_err(|e| {
            format!(
                "failed to compute relative path for '{}': {}",
                entry.display(),
                e
            )
        })?;

        if relative == Path::new(".git")
            || relative
                .components()
                .next()
                .map(|segment| segment.as_os_str() == ".git")
                .unwrap_or(false)
        {
            continue;
        }

        let metadata = std::fs::symlink_metadata(&entry)
            .map_err(|e| format!("failed to stat '{}': {}", entry.display(), e))?;
        if metadata.is_dir() {
            hasher.update(b"dir\0");
            hasher.update(relative.as_os_str().as_bytes());
            hasher.update(b"\0");
            hash_directory_inner(root, &entry, hasher)?;
            continue;
        }

        if metadata.file_type().is_symlink() {
            let target = std::fs::read_link(&entry)
                .map_err(|e| format!("failed to read symlink '{}': {}", entry.display(), e))?;
            hasher.update(b"symlink\0");
            hasher.update(relative.as_os_str().as_bytes());
            hasher.update(b"\0");
            hasher.update(target.as_os_str().as_bytes());
            hasher.update(b"\0");
            continue;
        }

        if metadata.is_file() {
            hasher.update(b"file\0");
            hasher.update(relative.as_os_str().as_bytes());
            hasher.update(b"\0");

            let mut file = File::open(&entry)
                .map_err(|e| format!("failed to open '{}': {}", entry.display(), e))?;
            let mut buffer = [0u8; 8192];
            loop {
                let bytes = file
                    .read(&mut buffer)
                    .map_err(|e| format!("failed to read '{}': {}", entry.display(), e))?;
                if bytes == 0 {
                    break;
                }
                hasher.update(&buffer[..bytes]);
            }
            hasher.update(b"\0");
            continue;
        }

        return Err(format!(
            "unsupported filesystem entry encountered while hashing '{}'",
            entry.display()
        ));
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::hash_directory;
    use std::path::PathBuf;

    fn temp_dir(name: &str) -> PathBuf {
        let mut dir = std::env::temp_dir();
        dir.push(format!(
            "taro-integrity-test-{}-{}-{}",
            name,
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("time")
                .as_nanos()
        ));
        dir
    }

    #[test]
    fn hash_directory_is_stable_for_same_contents() {
        let dir = temp_dir("stable");
        std::fs::create_dir_all(dir.join("a")).expect("mkdir");
        std::fs::write(dir.join("a/file.txt"), b"hello").expect("write");
        std::fs::write(dir.join("b.txt"), b"world").expect("write");

        let a = hash_directory(&dir).expect("hash");
        let b = hash_directory(&dir).expect("hash");
        assert_eq!(a, b);

        std::fs::remove_dir_all(&dir).expect("cleanup");
    }

    #[test]
    fn hash_directory_changes_when_contents_change() {
        let dir = temp_dir("changes");
        std::fs::create_dir_all(&dir).expect("mkdir");
        std::fs::write(dir.join("file.txt"), b"one").expect("write");
        let before = hash_directory(&dir).expect("hash");

        std::fs::write(dir.join("file.txt"), b"two").expect("write");
        let after = hash_directory(&dir).expect("hash");

        assert_ne!(before, after);
        std::fs::remove_dir_all(&dir).expect("cleanup");
    }
}
