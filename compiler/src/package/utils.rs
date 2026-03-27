use crate::constants::LANGUAGE_HOME;
use ecow::EcoString;
use std::path::{Path, PathBuf};

pub fn normalize_module_path(input: &str) -> Result<String, String> {
    let mut s = input.trim().replace('\\', "/");

    if let Some(rest) = s.strip_prefix("https://") {
        s = rest.to_string();
    } else if let Some(rest) = s.strip_prefix("http://") {
        s = rest.to_string();
    } else if let Some(rest) = s.strip_prefix("ssh://") {
        s = rest.to_string();
    } else if let Some(rest) = s.strip_prefix("git@")
        && let Some((host, path)) = rest.split_once(':')
    {
        s = format!("{host}/{}", path);
    }

    while s.contains("//") {
        s = s.replace("//", "/");
    }
    s = s.trim_end_matches('/').to_string();
    if s.is_empty() {
        return Err("empty module path".into());
    }

    let (host, rest) = s
        .split_once('/')
        .ok_or_else(|| "module path must be host/owner/repo".to_string())?;
    let host = host.to_ascii_lowercase();

    let mut parts: Vec<&str> = rest.split('/').collect();
    if parts.len() < 2 {
        return Err("module path must include owner/repo".into());
    }

    let repo_idx = 1.min(parts.len() - 1);
    parts[repo_idx] = parts[repo_idx].trim_end_matches(".git");

    if !host
        .chars()
        .all(|c| c.is_ascii_alphanumeric() || c == '.' || c == '-')
    {
        return Err("invalid host segment".into());
    }

    for seg in &parts {
        if seg.is_empty()
            || !seg
                .chars()
                .all(|c| c.is_ascii_alphanumeric() || c == '.' || c == '-' || c == '_')
        {
            return Err(format!("invalid path segment `{seg}`"));
        }
    }

    Ok(format!("{host}/{}", parts.join("/")))
}

pub fn derive_git_url(module_path: &str) -> Option<EcoString> {
    if module_path.starts_with("http://")
        || module_path.starts_with("https://")
        || module_path.starts_with("ssh://")
        || module_path.starts_with("git@")
    {
        return Some(module_path.into());
    }

    let mut parts = module_path.split('/');
    let host = parts.next()?;
    let owner = parts.next()?;
    let repo = parts.next()?;
    Some(
        format!(
            "https://{}/{}/{}.git",
            host,
            owner,
            repo.trim_end_matches(".git")
        )
        .into(),
    )
}

pub fn canonicalize_git_url(input: &str) -> Result<String, String> {
    let module_path = normalize_module_path(input)?;
    derive_git_url(&module_path)
        .map(|url| url.to_string())
        .ok_or_else(|| format!("cannot canonicalize git url '{}'", input))
}

pub fn canonicalize_rel(base: &Path, p: PathBuf) -> Result<PathBuf, String> {
    let abs = if p.is_absolute() { p } else { base.join(p) };
    std::fs::canonicalize(&abs)
        .map_err(|e| format!("failed to canonicalize {}: {e}", abs.display()))
}

pub fn infer_language_home_from_executable(exe_path: &Path) -> Option<PathBuf> {
    let bin_dir = exe_path.parent()?;
    if bin_dir.file_name()?.to_str()? != "bin" {
        return None;
    }

    let toolchain_root = bin_dir.parent()?;
    let taro_lib = toolchain_root.join("lib").join("taro");
    taro_lib.is_dir().then(|| toolchain_root.to_path_buf())
}

pub fn language_home() -> Result<PathBuf, String> {
    if let Some(val) = std::env::var_os(LANGUAGE_HOME) {
        let path = PathBuf::from(val);
        return path.canonicalize().map_err(|e| {
            format!(
                "{}='{}' is not a valid directory: {}",
                LANGUAGE_HOME,
                path.display(),
                e
            )
        });
    }

    if let Ok(exe_path) = std::env::current_exe()
        && let Some(path) = infer_language_home_from_executable(&exe_path)
    {
        return path.canonicalize().map_err(|e| {
            format!(
                "inferred {}='{}' from executable '{}' but it is not a valid directory: {}",
                LANGUAGE_HOME,
                path.display(),
                exe_path.display(),
                e
            )
        });
    }

    Err(format!(
        "failed to resolve {}.\nSet {} to your taro toolchain root, or install taro/taro-lsp under <toolchain>/bin with compiler libraries under <toolchain>/lib/taro.",
        LANGUAGE_HOME, LANGUAGE_HOME
    ))
}

pub fn get_package_name(input: &str) -> Result<EcoString, String> {
    let s = input.trim();

    if s.is_empty() || s.ends_with('/') {
        return Err("invalid package name".to_string());
    }

    let mut parts = s.split('/');
    let (host, author, package) = (parts.next(), parts.next(), parts.next());

    if let (Some(h), Some(a), Some(p)) = (host, author, package) {
        if !h.is_empty() && !a.is_empty() && !p.is_empty() && parts.next().is_none() {
            return Ok(p.into());
        }
    }

    Err("invalid package name".to_string())
}

#[cfg(test)]
mod tests {
    use super::{canonicalize_git_url, infer_language_home_from_executable};
    use std::{fs::create_dir_all, path::PathBuf};

    #[test]
    fn canonicalizes_equivalent_git_urls() {
        let https = canonicalize_git_url("https://github.com/Org/Repo.git").expect("https");
        let ssh = canonicalize_git_url("git@github.com:Org/Repo.git").expect("ssh");
        let raw = canonicalize_git_url("github.com/Org/Repo").expect("raw");

        assert_eq!(https, "https://github.com/Org/Repo.git");
        assert_eq!(ssh, https);
        assert_eq!(raw, https);
    }

    #[test]
    fn infers_language_home_from_toolchain_bin_layout() {
        let root = temp_dir("toolchain-home");
        create_dir_all(root.join("lib").join("taro")).expect("toolchain lib");

        let inferred =
            infer_language_home_from_executable(&root.join("bin").join("taro-lsp")).expect("home");

        assert_eq!(inferred, root);
    }

    #[test]
    fn does_not_infer_language_home_without_toolchain_layout() {
        let root = temp_dir("toolchain-home-missing-lib");

        assert_eq!(
            infer_language_home_from_executable(&root.join("bin").join("taro-lsp")),
            None
        );
        assert_eq!(
            infer_language_home_from_executable(
                &root.join("target").join("debug").join("taro-lsp")
            ),
            None
        );
    }

    fn temp_dir(prefix: &str) -> PathBuf {
        let path = std::env::temp_dir().join(format!(
            "taro-{}-{}",
            prefix,
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("time")
                .as_nanos()
        ));
        create_dir_all(&path).expect("temp dir");
        path
    }
}
