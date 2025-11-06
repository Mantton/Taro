use std::path::{Path, PathBuf};

use compiler::constants::LANGUAGE_HOME;
use ecow::EcoString;

pub fn normalize_module_path(input: &str) -> Result<String, String> {
    let mut s = input.trim().replace('\\', "/");

    // strip common URL/SSH prefixes
    if let Some(rest) = s.strip_prefix("https://") {
        s = rest.to_string();
    } else if let Some(rest) = s.strip_prefix("http://") {
        s = rest.to_string();
    } else if let Some(rest) = s.strip_prefix("ssh://") {
        s = rest.to_string();
    } else if let Some(rest) = s.strip_prefix("git@") {
        if let Some((host, path)) = rest.split_once(':') {
            s = format!("{host}/{}", path);
        }
    }

    // collapse slashes, strip trailing slash
    while s.contains("//") {
        s = s.replace("//", "/");
    }
    s = s.trim_end_matches('/').to_string();
    if s.is_empty() {
        return Err("empty module path".into());
    }

    // split host/rest
    let (host, rest) = s
        .split_once('/')
        .ok_or("module path must be host/owner/repo")?;
    let host = host.to_ascii_lowercase();

    // split owner/repo[/sub/...]
    let mut parts: Vec<&str> = rest.split('/').collect();
    if parts.len() < 2 {
        return Err("module path must include owner/repo".into());
    }

    // strip ".git" from repo segment only
    let repo_idx = 1.min(parts.len() - 1);
    parts[repo_idx] = parts[repo_idx].trim_end_matches(".git");

    // minimal validation
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
    // host/owner/repo[/sub/...]
    if module_path.starts_with("http://")
        || module_path.starts_with("https://")
        || module_path.starts_with("ssh://")
        || module_path.starts_with("git@")
    {
        return Some(module_path.into());
    }
    let mut it = module_path.split('/');
    let host = it.next()?;
    let owner = it.next()?;
    let repo = it.next()?;
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

pub fn canonicalize_rel(base: &Path, p: PathBuf) -> Result<PathBuf, String> {
    let abs = if p.is_absolute() { p } else { base.join(p) };
    std::fs::canonicalize(&abs)
        .map_err(|e| format!("failed to canonicalize {}: {e}", abs.display()))
}

pub fn language_home() -> Result<PathBuf, String> {
    let val = std::env::var(LANGUAGE_HOME).map_err(|e| {
        format!(
            "failed to read {}: {}\nSet {} to your taro language home directory.",
            LANGUAGE_HOME, e, LANGUAGE_HOME
        )
    })?;

    let path = PathBuf::from(val);

    path.canonicalize().map_err(|e| {
        format!(
            "{}='{}' is not a valid directory: {}",
            LANGUAGE_HOME,
            path.display(),
            e
        )
    })
}

pub fn get_package_name(input: &str) -> Result<EcoString, String> {
    let s = input.trim();

    // no trailing slash, must be exactly 3 non-empty segments
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
