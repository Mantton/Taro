use super::{identifier::PackageIdentifier, manifest::Dependency};
use git2::{
    AutotagOption, Cred, FetchOptions, RemoteCallbacks, RemoteUpdateFlags, Repository,
    build::CheckoutBuilder,
};
use std::{fs, path::PathBuf};
use taroc_constants::VCS_REMOTE_NAME;

pub fn download_dependency(
    package: &PackageIdentifier,
    metadata: &Dependency,
) -> Result<PathBuf, String> {
    let package_source = package.source_path()?;
    let package_repository = package.source_repository();

    let mut possibly_outdated = false;
    let repo = if package_source.exists() {
        possibly_outdated = true;
        match Repository::open(&package_source) {
            Ok(repo) => repo,
            Err(err) => {
                return Err(format!(
                    "failed to open package source `{}`: {}",
                    package_repository, err
                ));
            }
        }
    } else {
        // Create & Clone Repo
        fs::create_dir_all(&package_source).map_err(|err| {
            format!(
                "failed to create package source directory `{:?}`, {}",
                package_source, err
            )
        })?;

        println!("Cloning package repository '{}'", &package_repository);
        match Repository::clone(&package_repository, &package_source) {
            Ok(repo) => repo,
            Err(err) => return Err(format!("failed to clone `{}`: {}", package_repository, err)),
        }
    };

    let revision = if let Some(commit) = metadata.commit() {
        commit
    } else if let Some(version) = metadata.version() {
        format!("v{}", version)
    } else {
        todo!("cannot download dependency without valid revision")
    };

    let mut commit = repo
        .revparse_single(&revision)
        .ok()
        .map(|o| o.peel_to_commit().ok())
        .flatten();

    // unresolved, and repo could be updated
    if commit.is_none() && possibly_outdated {
        fetch_repo(&repo, &package.name).map_err(|err| {
            format!(
                "Failed to fetch repository `{}`: {}",
                package_repository, err
            )
        })?;
        // try again
        commit = repo
            .revparse_single(&revision)
            .ok()
            .map(|o| o.peel_to_commit().ok())
            .flatten();
    }

    let Some(commit) = commit else {
        let message = format!(
            "Cannot locate revision {} of package {}",
            revision, package.name
        );
        return Err(message);
    };

    repo.set_head_detached(commit.id()).map_err(|err| {
        format!(
            "failed to checkout revision '{}' of package '{}': {}",
            revision, package_repository, err
        )
    })?;

    Ok(package_source)
}

/// Reference: https://github.com/rust-lang/git2-rs/blob/master/examples/fetch.rs
fn fetch_repo(repo: &Repository, name: &String) -> Result<(), git2::Error> {
    let mut remote = repo
        .find_remote(VCS_REMOTE_NAME)
        .or_else(|_| repo.remote_anonymous(VCS_REMOTE_NAME))?;
    let mut callbacks = RemoteCallbacks::new();
    callbacks.credentials(|_url, _username_from_url, _allowed_types| Cred::default());

    let mut fetch_options = FetchOptions::new();
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
        RemoteUpdateFlags::UPDATE_FETCHHEAD,
        AutotagOption::All,
        None,
    )?;

    Ok(())
}

pub fn install_revision(package: String, revision: String) -> Result<(), String> {
    let identifier = PackageIdentifier::from(package.clone());
    let source = identifier.source_path()?;
    let revision = revision.strip_prefix("commit-").unwrap_or(&revision);
    let destination = identifier.install_path(revision.into())?;

    let repository = Repository::open(&source).map_err(|err| {
        format!(
            "failed to open source for '{}' @ {:?}: {}",
            package, source, err
        )
    })?;

    // Find Commit
    let commit = repository
        .revparse_single(&revision)
        .ok()
        .map(|o| o.peel_to_commit().ok())
        .flatten()
        .ok_or_else(|| {
            format!(
                "unable to locate revision {} of package {}",
                revision, package
            )
        })?;

    let mut checkout_builder = CheckoutBuilder::new();
    checkout_builder.force(); // Ensures checkout overwrites changes in the working directory
    repository
        .checkout_tree(commit.as_object(), Some(&mut checkout_builder))
        .map_err(|err| format!("failed to checkout tree: {}", err))?;

    fs::create_dir_all(&destination)
        .map_err(|err| format!("failed to create install location for {}: {}", package, err))?;

    // Copy entire source directory to destination
    let mut options = fs_extra::dir::CopyOptions::new();
    options.overwrite = true;
    options.content_only = true; // Copy contents
    fs_extra::dir::copy(&source, &destination, &options).map_err(|err| {
        format!(
            "Failed to copy directory from {:?} to {:?}: {}",
            source, destination, err
        )
    })?;

    // Remove the `.git` folder from the destination
    let git_dir = &destination.join(".git");
    if git_dir.exists() {
        fs::remove_dir_all(&git_dir)
            .map_err(|err| format!("Failed to remove .git directory at {:?}: {}", git_dir, err))?;
    }

    Ok(())
}
