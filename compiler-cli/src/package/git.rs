use crate::package::{
    manifest::{RefSpec, ResolvedPackage, Selector},
    utils::language_home,
};
use compiler::constants::{PACKAGE_STORE, VCS_REMOTE_NAME};
use ecow::EcoString;
use git2::{Oid, Repository, build::CheckoutBuilder};
use std::path::PathBuf;

pub fn checkout_branch(repo: &git2::Repository, name: &str) -> Result<Oid, git2::Error> {
    let branch = repo.find_branch(name, git2::BranchType::Local)?;
    let refname = branch
        .get()
        .name()
        .ok_or_else(|| git2::Error::from_str("Non-UTF8 branch refname"))?;

    let oid = repo.refname_to_id(refname)?;

    // Attach HEAD to the branch, then update the working tree to match it.
    repo.set_head(refname)?;
    repo.checkout_head(Some(
        CheckoutBuilder::new().force(), // overwrite local changes; remove if you prefer "safe" checkout
    ))?;
    Ok(oid)
}

pub fn checkout_detached(
    repo: &git2::Repository,
    commit: &git2::Commit,
) -> Result<Oid, git2::Error> {
    // Put HEAD in detached state at the commit, then update the working tree to match it.
    repo.set_head_detached(commit.id())?;
    repo.checkout_head(Some(
        CheckoutBuilder::new().force(), // overwrite local changes; remove if you prefer "safe" checkout
    ))?;
    Ok(commit.id())
}

pub fn branch_exists(repo: &git2::Repository, name: &str) -> bool {
    repo.find_branch(name, git2::BranchType::Local).is_ok()
}

/// Reference: https://github.com/rust-lang/git2-rs/blob/master/examples/fetch.rs
pub fn fetch_repo(repo: &git2::Repository) -> Result<(), git2::Error> {
    let mut remote = repo
        .find_remote(VCS_REMOTE_NAME)
        .or_else(|_| repo.remote_anonymous(VCS_REMOTE_NAME))?;
    let mut callbacks = git2::RemoteCallbacks::new();
    callbacks.credentials(|_url, _username_from_url, _allowed_types| git2::Cred::default());

    let mut fetch_options = git2::FetchOptions::new();
    fetch_options.remote_callbacks(callbacks);
    fetch_options.download_tags(git2::AutotagOption::All); // Include all tags

    remote.fetch(
        &[
            "refs/heads/*:refs/remotes/origin/*",
            "refs/tags/*:refs/tags/*",
        ],
        Some(&mut fetch_options),
        None,
    )?;

    // Disconnect the underlying connection to prevent from idling.
    remote.disconnect()?;

    remote.update_tips(
        None,
        git2::RemoteUpdateFlags::UPDATE_FETCHHEAD,
        git2::AutotagOption::All,
        None,
    )?;

    Ok(())
}

pub fn checkout_refspec(
    repo: &Repository,
    refspec: &RefSpec,
) -> Result<(git2::Oid, Selector), git2::Error> {
    if repo.is_bare() {
        return Err(git2::Error::from_str(
            "Cannot checkout in a bare repository",
        ));
    }

    match refspec {
        RefSpec::Commit(revision) => {
            let commit = repo.revparse_single(&revision)?.peel_to_commit()?;
            let oid = checkout_detached(repo, &commit)?;
            return Ok((oid, Selector::Commit(oid)));
        }
        RefSpec::Tag(tag) => {
            // Try a fully qualified tag ref first; fall back to generic revparse.
            let obj = repo
                .revparse_single(&format!("refs/tags/{tag}"))
                .or_else(|_| repo.revparse_single(&tag))?;
            let commit = obj.peel_to_commit()?;
            let oid = checkout_detached(repo, &commit)?;
            return Ok((oid, Selector::Tag(tag.clone())));
        }
        RefSpec::Branch(name) => {
            let oid = checkout_branch(repo, &name)?;
            return Ok((oid, Selector::Branch(name.clone())));
        }
        RefSpec::DefaultBranch => {
            if branch_exists(repo, "main") {
                checkout_branch(repo, "main").map(|oid| (oid, Selector::Branch("main".into())))
            } else if branch_exists(repo, "master") {
                checkout_branch(repo, "master").map(|oid| (oid, Selector::Branch("master".into())))
            } else if let Ok(head) = repo.head() {
                if head.is_branch() {
                    if let Some(name) = head.shorthand() {
                        return checkout_branch(repo, name)
                            .map(|oid| (oid, Selector::Branch(name.into())));
                    }
                }
                Err(git2::Error::from_str(
                    "No 'main' or 'master' found, and HEAD is not a local branch",
                ))
            } else {
                Err(git2::Error::from_str(
                    "No 'main' or 'master' found, and no usable HEAD",
                ))
            }
        }
        RefSpec::Version(version_req) => {
            checkout_version_req(repo, version_req).map(|(oid, tag)| (oid, Selector::Tag(tag)))
        }
    }
}

fn checkout_version_req(
    repo: &Repository,
    req: &semver::VersionReq,
) -> Result<(Oid, EcoString), git2::Error> {
    let tag = best_tag_for_version_req(repo, req)?;
    let obj = repo
        .revparse_single(&format!("refs/tags/{tag}"))
        .or_else(|_| repo.revparse_single(&tag))?; // fallback if tag is peeled
    let commit = obj.peel_to_commit()?;
    checkout_detached(repo, &commit).map(|oid| (oid, tag.into()))
}

fn best_tag_for_version_req(
    repo: &Repository,
    req: &semver::VersionReq,
) -> Result<String, git2::Error> {
    let names = repo.tag_names(None)?; // all tag names
    let mut candidates: Vec<(semver::Version, String)> = Vec::new();

    for name in names.iter().flatten() {
        if let Some(ver) = parse_tag_version(name) {
            if req.matches(&ver) {
                candidates.push((ver, name.to_string()));
            }
        }
    }

    if candidates.is_empty() {
        return Err(git2::Error::from_str(&format!(
            "No tag satisfies version requirement: {req}"
        )));
    }

    // Pick the highest semver that matches the requirement
    candidates.sort_by(|a, b| a.0.cmp(&b.0));
    let (_v, name) = candidates.pop().unwrap();
    Ok(name)
}

pub fn parse_tag_version(tag: &str) -> Option<semver::Version> {
    // Accept "1.2.3" or "v1.2.3"
    semver::Version::parse(tag).ok().or_else(|| {
        tag.strip_prefix('v')
            .and_then(|s| semver::Version::parse(s).ok())
    })
}

pub fn install_revision(package: ResolvedPackage, revision: Oid) -> Result<PathBuf, String> {
    let source = language_home()?
        .join(PACKAGE_STORE)
        .join(package.package.hashed_name());

    let destination = package.path()?;

    let repo = Repository::open(&source).map_err(|err| {
        format!(
            "failed to open source for '{}' @ {:?}: {}",
            package.package.0, source, err
        )
    })?;

    // Find Commit
    // Resolve the commit (use `find_commit` for an Oid)
    let commit = repo.find_commit(revision).map_err(|_| {
        format!(
            "unable to locate revision {} of package {}",
            revision, package.package.0
        )
    })?;

    // We need a working directory to materialize files
    let workdir = repo.workdir().ok_or_else(|| {
        format!(
            "source repository at {:?} is bare; cannot checkout to working directory",
            source
        )
    })?;

    // Detach HEAD at the requested commit and checkout files
    repo.set_head_detached(commit.id())
        .map_err(|e| format!("failed to detach HEAD: {}", e))?;
    let mut co = CheckoutBuilder::new();
    co.force().remove_untracked(true).remove_ignored(true);
    repo.checkout_head(Some(&mut co))
        .map_err(|e| format!("failed to checkout tree: {}", e))?;

    // Ensure destination exists
    std::fs::create_dir_all(&destination).map_err(|err| {
        format!(
            "failed to create install location for {}: {}",
            package.package.0, err
        )
    })?;

    // Copy the *working tree* contents (not the .git dir)
    let mut options = fs_extra::dir::CopyOptions::new();
    options.overwrite = true;
    options.content_only = true;
    fs_extra::dir::copy(workdir, &destination, &options).map_err(|err| {
        format!(
            "failed to copy directory from {:?} to {:?}: {}",
            workdir, destination, err
        )
    })?;

    // Remove any `.git` that may have been copied (extra safety)
    let git_dir = destination.join(".git");
    if git_dir.is_dir() {
        std::fs::remove_dir_all(&git_dir)
            .map_err(|err| format!("failed to remove .git at {:?}: {}", git_dir, err))?;
    }

    Ok(destination)
}
