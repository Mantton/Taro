use crate::package::{
    git::{self, checkout_refspec, fetch_repo},
    integrity,
    lockfile::{self, LockFile, LockPackage, LockSourceType},
    manifest::{
        DependencyGraph, Manifest, NormalizedManifest, PackageIdentifier, RefSpec, ResolvedPackage,
        ResolvedSource, Selector, SourceSpec, UnresolvedDependency, ValidatedDependencyGraph,
    },
    utils::{canonicalize_git_url, language_home},
};
use compiler::{
    constants::{LOCK_FILE, MANIFEST_FILE, PACKAGE_STORE},
    error::{CompileResult, ReportedError},
};
use ecow::EcoString;
use petgraph::algo::toposort;
use rustc_hash::{FxHashMap, FxHashSet};
use std::{collections::BTreeMap, path::PathBuf};

#[derive(Clone, Copy, Debug, Default)]
pub struct SyncOptions {
    pub locked: bool,
    pub update_lock: bool,
    pub strict_env: bool,
}

impl SyncOptions {
    pub fn strict_mode(self) -> bool {
        (self.locked || self.strict_env) && !self.update_lock
    }
}

pub fn sync_dependencies(
    root: PathBuf,
    options: SyncOptions,
) -> Result<ValidatedDependencyGraph, ReportedError> {
    let root = std::fs::canonicalize(&root).map_err(|e| {
        eprintln!(
            "error: failed to canonicalize root path '{}': {}",
            root.display(),
            e
        );
        ReportedError
    })?;

    let lock_path = root.join(LOCK_FILE);
    let existing_lock = lockfile::load(&lock_path).map_err(|e| {
        eprintln!("error: {}", e);
        ReportedError
    })?;

    if options.strict_mode() && existing_lock.is_none() {
        eprintln!(
            "error: lockfile '{}' is required in strict mode; run without --locked (or with --update-lock) to create it",
            lock_path.display()
        );
        return Err(ReportedError);
    }

    let arena = Arenas {
        unresolved: Default::default(),
        resolved: Default::default(),
    };

    let mut actor = Actor {
        arenas: &arena,
        options,
        lockfile: existing_lock.clone(),
        root_package: None,
        resolution_map: Default::default(),
        package_manifests: Default::default(),
        package_dependencies: Default::default(),
        resolved_package_dependencies: Default::default(),
        expected_tree_hashes: Default::default(),
        installed_tree_hashes: Default::default(),
        warnings: Default::default(),
    };

    let graph = actor.sync(root)?;
    actor.emit_warnings();

    let desired_lock = actor.build_lockfile().map_err(|e| {
        eprintln!("error: failed to build lockfile: {}", e);
        ReportedError
    })?;

    let lock_changed = if let Some(current) = existing_lock {
        !lockfile::equivalent(&current, &desired_lock)
    } else {
        true
    };

    if lock_changed {
        if options.strict_mode() {
            eprintln!(
                "error: lockfile '{}' is out of date; run without --locked (or with --update-lock) to refresh it",
                lock_path.display()
            );
            return Err(ReportedError);
        }

        lockfile::write(&lock_path, &desired_lock).map_err(|e| {
            eprintln!("error: {}", e);
            ReportedError
        })?;

        eprintln!(
            "warning: updated dependency lockfile at '{}'",
            lock_path.display()
        );
    }

    Ok(graph)
}

struct Actor<'arena> {
    arenas: &'arena Arenas,
    options: SyncOptions,
    lockfile: Option<LockFile>,
    root_package: Option<RPkg<'arena>>,

    resolution_map: FxHashMap<UPkg<'arena>, RPkg<'arena>>,

    package_manifests: FxHashMap<RPkg<'arena>, NormalizedManifest>,
    package_dependencies: FxHashMap<RPkg<'arena>, Vec<(EcoString, UPkg<'arena>)>>,
    resolved_package_dependencies: FxHashMap<RPkg<'arena>, FxHashMap<EcoString, RPkg<'arena>>>,

    expected_tree_hashes: FxHashMap<RPkg<'arena>, String>,
    installed_tree_hashes: FxHashMap<RPkg<'arena>, String>,
    warnings: FxHashSet<String>,
}

struct Arenas {
    unresolved: internment::Arena<UnresolvedDependency>,
    resolved: internment::Arena<ResolvedPackage>,
}

type UPkg<'a> = internment::ArenaIntern<'a, UnresolvedDependency>;
type RPkg<'a> = internment::ArenaIntern<'a, ResolvedPackage>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct GitGroupKey {
    package: PackageIdentifier,
    canonical_url: EcoString,
}

#[derive(Clone)]
struct GitRequest<'a> {
    udep: UPkg<'a>,
    refspec: RefSpec,
    requested: EcoString,
}

impl<'a> Actor<'a> {
    fn intern_udep(&self, value: UnresolvedDependency) -> UPkg<'a> {
        self.arenas.unresolved.intern(value)
    }

    fn intern_rdep(&self, value: ResolvedPackage) -> RPkg<'a> {
        self.arenas.resolved.intern(value)
    }
}

impl<'a> Actor<'a> {
    fn sync(&mut self, root: PathBuf) -> CompileResult<ValidatedDependencyGraph> {
        let root_package = self.load_root_package(root)?;
        self.resolve_package_selections(root_package)?;
        self.install_dependencies()?;
        self.cache_package_resolution_map();
        let graph = self.build_dependency_graph()?;
        let graph = self.validate_graph(graph)?;
        Ok(graph)
    }

    fn emit_warnings(&self) {
        let mut warnings: Vec<_> = self.warnings.iter().cloned().collect();
        warnings.sort();
        for warning in warnings {
            eprintln!("warning: {}", warning);
        }
    }

    fn warn_once(&mut self, warning: impl Into<String>) {
        self.warnings.insert(warning.into());
    }
}

impl<'a> Actor<'a> {
    fn load_root_package(&mut self, root_path: PathBuf) -> CompileResult<RPkg<'a>> {
        let root_manifest = Manifest::parse(root_path.join(MANIFEST_FILE)).map_err(|e| {
            eprintln!(
                "error: failed to parse manifest at '{}': {}",
                root_path.display(),
                e
            );
            ReportedError
        })?;
        let root_manifest = root_manifest.normalize(root_path.clone()).map_err(|e| {
            eprintln!(
                "error: failed to normalize manifest at '{}': {}",
                root_path.display(),
                e
            );
            ReportedError
        })?;
        let root_package = self.intern_rdep(ResolvedPackage {
            package: root_manifest.path.clone(),
            source: ResolvedSource::Path {
                abs: root_path.clone(),
            },
            kind: root_manifest.kind,
            no_std_prelude: root_manifest.no_std_prelude,
        });
        self.root_package = Some(root_package);
        self.package_manifests.insert(root_package, root_manifest);
        Ok(root_package)
    }

    fn resolve_package_selections(&mut self, root_package: RPkg<'a>) -> CompileResult<()> {
        let mut active_git_selections = FxHashMap::<GitGroupKey, RPkg<'a>>::default();

        for _ in 0..64 {
            self.resolution_map.clear();
            self.package_dependencies.clear();
            self.expected_tree_hashes.clear();

            let mut pending = vec![root_package];
            let mut seen_packages = FxHashSet::default();
            let mut git_groups = FxHashMap::<GitGroupKey, Vec<GitRequest<'a>>>::default();

            while let Some(package) = pending.pop() {
                if !seen_packages.insert(package) {
                    continue;
                }

                let manifest = self
                    .package_manifests
                    .get(&package)
                    .ok_or_else(|| {
                        eprintln!(
                            "error: internal resolver missing manifest for '{}'",
                            package.package.0
                        );
                        ReportedError
                    })?
                    .clone();
                let is_root_manifest = Some(package) == self.root_package;
                let mut deps_for_package = Vec::new();

                for (alias, dependency) in manifest.dependencies.clone().into_iter() {
                    if matches!(dependency.source, SourceSpec::Path { .. }) && !is_root_manifest {
                        eprintln!(
                            "error: dependency '{}' declares a transitive path dependency ('{}'), but path dependencies are only allowed in the root manifest",
                            manifest.path.0, dependency.package.0
                        );
                        return Err(ReportedError);
                    }

                    let udep = self.intern_udep(dependency);
                    deps_for_package.push((alias, udep));

                    match &udep.source {
                        SourceSpec::Path { .. } => {
                            let selection = self.resolve_path_dependency(udep).map_err(|err| {
                                eprintln!("error: failed to resolve path dependency: {}", err);
                                ReportedError
                            })?;
                            self.resolution_map.insert(udep, selection);
                            pending.push(selection);
                        }
                        SourceSpec::Git { url, refspec } => {
                            let canonical_url = canonicalize_git_url(url).map_err(|err| {
                                eprintln!("error: failed to resolve git dependency: {}", err);
                                ReportedError
                            })?;
                            let key = GitGroupKey {
                                package: udep.package.clone(),
                                canonical_url: canonical_url.into(),
                            };
                            let requested = refspec.request_string();
                            git_groups.entry(key.clone()).or_default().push(GitRequest {
                                udep,
                                refspec: refspec.clone(),
                                requested,
                            });

                            if let Some(selection) = active_git_selections.get(&key) {
                                pending.push(*selection);
                            }
                        }
                    }
                }

                self.package_dependencies.insert(package, deps_for_package);
            }

            let mut next_git_selections = FxHashMap::<GitGroupKey, RPkg<'a>>::default();
            for (key, requests) in git_groups {
                let (selection, manifest, expected_tree_hash) =
                    self.resolve_git_group(&key, &requests).map_err(|err| {
                        eprintln!("error: failed to resolve git dependency: {}", err);
                        ReportedError
                    })?;

                for request in requests {
                    self.resolution_map.insert(request.udep, selection);
                }

                self.package_manifests.entry(selection).or_insert(manifest);
                if let Some(hash) = expected_tree_hash {
                    self.expected_tree_hashes.insert(selection, hash);
                }
                next_git_selections.insert(key, selection);
            }

            let selected_manifest_not_traversed = next_git_selections
                .values()
                .any(|selection| !seen_packages.contains(selection));
            if next_git_selections == active_git_selections && !selected_manifest_not_traversed {
                return Ok(());
            }

            active_git_selections = next_git_selections;
        }

        eprintln!("error: dependency resolution did not converge");
        Err(ReportedError)
    }

    fn resolve_path_dependency(&mut self, dependency: UPkg<'a>) -> Result<RPkg<'a>, String> {
        let SourceSpec::Path { abs } = &dependency.source else {
            return Err(format!(
                "dependency '{}' is not a path dependency",
                dependency.package.0
            ));
        };
        let manifest = Manifest::parse(abs.join(MANIFEST_FILE))?;
        let manifest = manifest.normalize(abs.clone())?;
        let dependency = self.intern_rdep(ResolvedPackage {
            package: dependency.package.clone(),
            source: ResolvedSource::Path { abs: abs.clone() },
            kind: manifest.kind,
            no_std_prelude: manifest.no_std_prelude,
        });
        self.package_manifests.entry(dependency).or_insert(manifest);
        Ok(dependency)
    }

    fn resolve_git_group(
        &mut self,
        key: &GitGroupKey,
        requests: &[GitRequest<'a>],
    ) -> Result<(RPkg<'a>, NormalizedManifest, Option<String>), String> {
        let request_strings = normalized_request_strings(requests);
        for request in requests {
            if request.refspec.is_mutable() {
                self.warn_once(format!(
                    "dependency '{}' uses mutable selector '{}'",
                    key.package.0, request.requested
                ));
            }
        }

        let lock_hit = if self.options.update_lock {
            None
        } else {
            self.lockfile.as_ref().and_then(|lock| {
                lock.find_git_requests(&key.package.0, key.canonical_url.as_ref(), &request_strings)
            })
        };

        let (package_source, revision, selector, expected_tree_hash) = if let Some(entry) = lock_hit
        {
            let revision_str = entry.revision.as_ref().ok_or_else(|| {
                format!("lockfile entry for '{}' is missing revision", key.package.0)
            })?;
            let revision = git2::Oid::from_str(revision_str).map_err(|e| {
                format!(
                    "invalid lockfile revision '{}' for '{}': {}",
                    revision_str, key.package.0, e
                )
            })?;
            let package_source = self.ensure_package_cache(
                &key.package,
                key.canonical_url.as_ref(),
                Some(revision),
            )?;
            let repo = git2::Repository::open(&package_source).map_err(|err| {
                format!(
                    "failed to open package cache for '{}' at '{}': {}",
                    key.package.0,
                    package_source.display(),
                    err
                )
            })?;
            git::checkout_revision(&repo, revision)?;
            (
                package_source,
                revision,
                Selector::Commit(revision),
                entry.tree_hash.clone(),
            )
        } else {
            let package_source =
                self.ensure_package_cache(&key.package, key.canonical_url.as_ref(), None)?;
            let repo = git2::Repository::open(&package_source).map_err(|err| {
                format!(
                    "failed to open package cache for '{}' at '{}': {}",
                    key.package.0,
                    package_source.display(),
                    err
                )
            })?;
            let (revision, selector) = checkout_group_requests(&repo, key, requests)
                .map_err(|err| format!("failed to checkout dependency – {}", err))?;
            (package_source, revision, selector, None)
        };

        let manifest = Manifest::parse(package_source.join(MANIFEST_FILE))?;
        let manifest = manifest.normalize(package_source.clone())?;
        let dependency = self.intern_rdep(ResolvedPackage {
            package: key.package.clone(),
            source: ResolvedSource::Git {
                url: key.canonical_url.clone(),
                revision,
                selector,
                requests: request_strings.into_iter().map(EcoString::from).collect(),
            },
            kind: manifest.kind,
            no_std_prelude: manifest.no_std_prelude,
        });

        Ok((dependency, manifest, expected_tree_hash))
    }

    fn ensure_package_cache(
        &self,
        package: &PackageIdentifier,
        canonical_url: &str,
        required_revision: Option<git2::Oid>,
    ) -> Result<PathBuf, String> {
        let store_root = language_home()?.join(PACKAGE_STORE);
        std::fs::create_dir_all(&store_root).map_err(|e| {
            format!(
                "failed to create package cache root '{}': {}",
                store_root.display(),
                e
            )
        })?;

        let cache_key = lockfile::canonical_git_cache_key(&package.0, canonical_url);
        let cache_path = store_root.join(cache_key);
        let legacy_path = store_root.join(package.hashed_name());

        if !cache_path.exists() && legacy_path.exists() {
            let legacy_repo = git2::Repository::open(&legacy_path).map_err(|e| {
                format!(
                    "failed to open legacy cache at '{}': {}",
                    legacy_path.display(),
                    e
                )
            })?;

            git::ensure_repo_origin(&legacy_repo, canonical_url).map_err(|e| {
                format!(
                    "legacy cache '{}' failed origin validation ({}). Remove that directory and retry",
                    legacy_path.display(),
                    e
                )
            })?;

            std::fs::rename(&legacy_path, &cache_path).map_err(|e| {
                format!(
                    "failed to migrate legacy cache from '{}' to '{}': {}",
                    legacy_path.display(),
                    cache_path.display(),
                    e
                )
            })?;
        }

        if cache_path.exists() {
            let repo = git2::Repository::open(&cache_path).map_err(|err| {
                format!(
                    "failed to open package cache '{}': {}",
                    cache_path.display(),
                    err
                )
            })?;
            git::ensure_repo_origin(&repo, canonical_url).map_err(|e| {
                format!(
                    "package cache '{}' failed origin validation ({}). Remove that directory and retry",
                    cache_path.display(),
                    e
                )
            })?;
            if let Some(revision) = required_revision
                && git::revision_exists(&repo, revision)
            {
                return Ok(cache_path);
            }
            fetch_repo(&repo).map_err(|err| {
                format!(
                    "failed to fetch repository '{}' from '{}': {}",
                    canonical_url,
                    cache_path.display(),
                    err
                )
            })?;
        } else {
            eprintln!("Cloning package repository '{}'", canonical_url);
            git2::Repository::clone(canonical_url, &cache_path)
                .map_err(|err| format!("failed to clone '{}': {}", canonical_url, err))?;
        }

        if let Some(revision) = required_revision {
            let repo = git2::Repository::open(&cache_path).map_err(|err| {
                format!(
                    "failed to open package cache '{}': {}",
                    cache_path.display(),
                    err
                )
            })?;
            if !git::revision_exists(&repo, revision) {
                return Err(format!(
                    "locked revision {} for '{}' is unavailable in cache '{}'",
                    revision,
                    package.0,
                    cache_path.display()
                ));
            }
        }

        Ok(cache_path)
    }

    fn install_dependencies(&mut self) -> CompileResult<()> {
        for &selection in self.package_dependencies.keys() {
            if let ResolvedSource::Git { revision, .. } = &selection.source {
                let expected_hash = self.expected_tree_hashes.get(&selection).cloned();
                let mut final_hash = None;

                for attempt in 0..2 {
                    let destination = git::install_revision(selection.as_ref().clone(), *revision)
                        .map_err(|e| {
                            eprintln!(
                                "error: failed to install git revision for '{}': {}",
                                selection.package.0, e
                            );
                            ReportedError
                        })?;

                    let actual_hash = integrity::hash_directory(&destination).map_err(|e| {
                        eprintln!(
                            "error: failed to compute integrity hash for '{}': {}",
                            selection.package.0, e
                        );
                        ReportedError
                    })?;

                    if let Some(expected) = expected_hash.as_deref() {
                        if actual_hash != expected {
                            if attempt == 0 {
                                eprintln!(
                                    "warning: integrity mismatch for '{}' after install; retrying once",
                                    selection.package.0
                                );
                                continue;
                            }

                            eprintln!(
                                "error: integrity verification failed for '{}' (expected '{}', found '{}')",
                                selection.package.0, expected, actual_hash
                            );
                            return Err(ReportedError);
                        }
                    }

                    final_hash = Some(actual_hash);
                    break;
                }

                let Some(hash) = final_hash else {
                    eprintln!(
                        "error: failed to install '{}' with a verified hash",
                        selection.package.0
                    );
                    return Err(ReportedError);
                };

                self.installed_tree_hashes.insert(selection, hash);
            }
        }

        Ok(())
    }

    fn cache_package_resolution_map(&mut self) {
        for (&package, unresolved) in &self.package_dependencies {
            let mut resolved = FxHashMap::default();
            for (name, dependency) in unresolved {
                let Some(&dependency_resolution) = self.resolution_map.get(&dependency) else {
                    unreachable!("expected dependency resolution")
                };

                resolved.insert(name.clone(), dependency_resolution);
            }

            self.resolved_package_dependencies.insert(package, resolved);
        }
    }

    fn build_dependency_graph(&self) -> Result<DependencyGraph, ReportedError> {
        let mut graph = DependencyGraph::new();
        let mut nodes = FxHashMap::<RPkg<'a>, petgraph::graph::NodeIndex>::default();
        let mut idx = |p: RPkg<'a>, g: &mut DependencyGraph| {
            *nodes
                .entry(p)
                .or_insert_with(|| g.add_node(p.as_ref().clone()))
        };

        for (&pkg, deps) in &self.resolved_package_dependencies {
            let pkg_ix = idx(pkg, &mut graph);
            for (name, &dependency) in deps {
                let dep_ix = idx(dependency, &mut graph);
                graph.add_edge(dep_ix, pkg_ix, name.clone());
            }
        }

        Ok(graph)
    }

    fn validate_graph(&self, graph: DependencyGraph) -> CompileResult<ValidatedDependencyGraph> {
        match toposort(&graph, None) {
            Ok(order) => {
                debug_assert!(!order.is_empty(), "non empty compilation list");
                debug_assert!(
                    order.last().map(|&index| &graph[index])
                        == self.root_package.as_ref().map(|v| v.as_ref()),
                    "target package is last on compilation list"
                );

                Ok(ValidatedDependencyGraph {
                    graph,
                    ordered: order,
                })
            }
            Err(cycle) => {
                let index = cycle.node_id();
                let members = cycle_members(&graph, index);
                eprintln!("error: dependency cycle detected at {:?}", graph[index]);
                for member in members {
                    eprintln!("  - {:?}", member);
                }
                Err(ReportedError)
            }
        }
    }

    fn build_lockfile(&self) -> Result<LockFile, String> {
        let root = self
            .root_package
            .ok_or_else(|| "root package was not initialized".to_string())?;

        let mut selections: Vec<_> = self
            .package_dependencies
            .keys()
            .copied()
            .filter(|selection| *selection != root)
            .collect();
        selections.sort_by(|a, b| a.package.0.cmp(&b.package.0));

        let mut node_map = FxHashMap::default();
        for selection in &selections {
            let node = lockfile::node_from_resolved(selection.as_ref())?;
            node_map.insert(*selection, node);
        }

        let mut output = LockFile::new();
        for selection in selections {
            let node = node_map
                .get(&selection)
                .cloned()
                .ok_or_else(|| format!("missing node id for '{}'", selection.package.0))?;

            let mut deps = BTreeMap::new();
            if let Some(dependency_map) = self.resolved_package_dependencies.get(&selection) {
                let mut sorted_deps: Vec<_> = dependency_map.iter().collect();
                sorted_deps.sort_by(|(a, _), (b, _)| a.cmp(b));

                for (alias, dependency) in sorted_deps {
                    if *dependency == root {
                        continue;
                    }
                    let dep_node = node_map.get(dependency).ok_or_else(|| {
                        format!(
                            "missing node id for transitive dependency '{}'",
                            dependency.package.0
                        )
                    })?;
                    deps.insert(alias.to_string(), dep_node.clone());
                }
            }

            let package = match &selection.source {
                ResolvedSource::Path { abs } => LockPackage {
                    node,
                    name: selection.package.0.to_string(),
                    kind: selection.kind,
                    no_std_prelude: selection.no_std_prelude,
                    source_type: LockSourceType::Path,
                    url: None,
                    path: Some(abs.display().to_string()),
                    requests: vec!["path".into()],
                    revision: None,
                    tree_hash: None,
                    deps,
                },
                ResolvedSource::Git {
                    url,
                    revision,
                    requests,
                    ..
                } => {
                    let tree_hash = self
                        .installed_tree_hashes
                        .get(&selection)
                        .cloned()
                        .ok_or_else(|| {
                            format!(
                                "missing installed hash for git dependency '{}'",
                                selection.package.0
                            )
                        })?;

                    LockPackage {
                        node,
                        name: selection.package.0.to_string(),
                        kind: selection.kind,
                        no_std_prelude: selection.no_std_prelude,
                        source_type: LockSourceType::Git,
                        url: Some(url.to_string()),
                        path: None,
                        requests: requests.iter().map(ToString::to_string).collect(),
                        revision: Some(revision.to_string()),
                        tree_hash: Some(tree_hash),
                        deps,
                    }
                }
            };

            output.package.push(package);
        }

        Ok(output.normalized())
    }
}

fn normalized_request_strings(requests: &[GitRequest<'_>]) -> Vec<String> {
    let mut out = requests
        .iter()
        .map(|request| request.requested.to_string())
        .collect::<Vec<_>>();
    out.sort();
    out.dedup();
    out
}

fn checkout_group_requests(
    repo: &git2::Repository,
    key: &GitGroupKey,
    requests: &[GitRequest<'_>],
) -> Result<(git2::Oid, Selector), String> {
    let mut version_reqs = Vec::new();
    let mut fixed_refspecs = Vec::new();
    let request_strings = normalized_request_strings(requests);

    for request in requests {
        match &request.refspec {
            RefSpec::Version(req) => version_reqs.push(req.clone()),
            _ => fixed_refspecs.push(request.refspec.clone()),
        }
    }

    let mut selected = if version_reqs.is_empty() {
        None
    } else {
        let (revision, tag) = git::checkout_version_reqs(repo, &version_reqs).map_err(|err| {
            format!(
                "no tag for '{}' from '{}' satisfies all requests [{}]: {}",
                key.package.0,
                key.canonical_url,
                request_strings.join(", "),
                err
            )
        })?;
        Some((revision, Selector::Tag(tag)))
    };

    for refspec in fixed_refspecs {
        let (revision, selector) = checkout_refspec(repo, &refspec).map_err(|err| {
            format!(
                "failed to resolve selector '{}' for '{}' from '{}': {}",
                refspec.request_string(),
                key.package.0,
                key.canonical_url,
                err
            )
        })?;

        if let Some((selected_revision, _)) = selected {
            if selected_revision != revision {
                return Err(format!(
                    "conflicting selectors for '{}' from '{}' [{}] resolve to different revisions",
                    key.package.0,
                    key.canonical_url,
                    request_strings.join(", ")
                ));
            }
        } else {
            selected = Some((revision, selector));
        }
    }

    selected.ok_or_else(|| {
        format!(
            "no requests collected for '{}' from '{}'",
            key.package.0, key.canonical_url
        )
    })
}

use petgraph::algo::tarjan_scc;

fn cycle_members(g: &DependencyGraph, start: petgraph::prelude::NodeIndex) -> Vec<ResolvedPackage> {
    let sccs = tarjan_scc(g);
    if let Some(scc) = sccs.into_iter().find(|c| c.contains(&start)) {
        return scc.into_iter().map(|ix| g[ix].clone()).collect();
    }
    vec![g[start].clone()]
}

#[cfg(test)]
mod tests {
    use super::{GitGroupKey, GitRequest, SyncOptions, checkout_group_requests};
    use crate::package::manifest::{PackageIdentifier, RefSpec, SourceSpec, UnresolvedDependency};
    use crate::package::{integrity, lockfile};
    use compiler::compile::config::PackageKind;
    use compiler::constants::PACKAGE_STORE;
    use ecow::EcoString;
    use git2::{Oid, Repository, Signature};
    use std::ffi::OsString;
    use std::path::{Path, PathBuf};
    use std::sync::{
        Mutex, OnceLock,
        atomic::{AtomicU64, Ordering},
    };

    fn temp_dir(name: &str) -> PathBuf {
        static NEXT_ID: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "taro-sync-test-{}-{}-{}-{}",
            name,
            std::process::id(),
            NEXT_ID.fetch_add(1, Ordering::Relaxed),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("time")
                .as_nanos()
        ));
        std::fs::create_dir_all(&path).expect("temp dir");
        path
    }

    fn commit_file(repo: &Repository, root: &Path, contents: &str) -> Oid {
        std::fs::write(root.join("package.toml"), contents).expect("write package");
        let mut index = repo.index().expect("index");
        index
            .add_path(Path::new("package.toml"))
            .expect("add package");
        index.write().expect("write index");
        let tree_oid = index.write_tree().expect("tree");
        let tree = repo.find_tree(tree_oid).expect("find tree");
        let sig = Signature::now("Taro Test", "taro@example.com").expect("signature");
        let parents = if let Ok(head) = repo.head() {
            vec![head.peel_to_commit().expect("parent")]
        } else {
            vec![]
        };
        let parent_refs = parents.iter().collect::<Vec<_>>();
        repo.commit(Some("HEAD"), &sig, &sig, "test commit", &tree, &parent_refs)
            .expect("commit")
    }

    fn tag(repo: &Repository, name: &str, oid: Oid) {
        let sig = Signature::now("Taro Test", "taro@example.com").expect("signature");
        let object = repo.find_object(oid, None).expect("object");
        repo.tag(name, &object, &sig, name, false).expect("tag");
    }

    fn write_manifest(path: &Path, contents: &str) {
        std::fs::create_dir_all(path).expect("manifest dir");
        std::fs::write(path.join("package.toml"), contents).expect("manifest");
    }

    fn tagged_repo(tags: &[&str]) -> (PathBuf, Repository, Vec<Oid>) {
        let root = temp_dir("git");
        let repo = Repository::init(&root).expect("repo");
        let mut revisions = Vec::new();
        for tag_name in tags {
            let revision = commit_file(
                &repo,
                &root,
                &format!(
                    "[package]\nname = \"github.com/example/dep\"\nkind = \"library\"\n# {tag_name}\n"
                ),
            );
            tag(&repo, tag_name, revision);
            revisions.push(revision);
        }
        (root, repo, revisions)
    }

    fn key() -> GitGroupKey {
        GitGroupKey {
            package: PackageIdentifier("github.com/example/dep".into()),
            canonical_url: EcoString::from("https://github.com/example/dep.git"),
        }
    }

    fn request<'a>(
        arena: &'a internment::Arena<UnresolvedDependency>,
        refspec: RefSpec,
    ) -> GitRequest<'a> {
        let key = key();
        let udep = arena.intern(UnresolvedDependency {
            package: key.package,
            source: SourceSpec::Git {
                url: key.canonical_url,
                refspec: refspec.clone(),
            },
        });
        GitRequest {
            udep,
            requested: refspec.request_string(),
            refspec,
        }
    }

    fn env_lock() -> &'static Mutex<()> {
        static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
        LOCK.get_or_init(|| Mutex::new(()))
    }

    struct TaroHomeGuard {
        previous: Option<OsString>,
    }

    impl TaroHomeGuard {
        fn set(path: &Path) -> Self {
            let previous = std::env::var_os("TARO_HOME");
            unsafe { std::env::set_var("TARO_HOME", path) };
            Self { previous }
        }
    }

    impl Drop for TaroHomeGuard {
        fn drop(&mut self) {
            if let Some(previous) = self.previous.take() {
                unsafe { std::env::set_var("TARO_HOME", previous) };
            } else {
                unsafe { std::env::remove_var("TARO_HOME") };
            }
        }
    }

    #[test]
    fn group_versions_select_highest_tag_satisfying_all_ranges() {
        let (_root, repo, revisions) = tagged_repo(&["v1.0.0", "v1.1.0", "v1.2.0"]);
        let arena = internment::Arena::new();
        let requests = vec![
            request(&arena, RefSpec::Version("^1.0".parse().expect("req"))),
            request(
                &arena,
                RefSpec::Version(">=1.0.0, <1.2.0".parse().expect("req")),
            ),
        ];

        let (revision, selector) =
            checkout_group_requests(&repo, &key(), &requests).expect("compatible selection");

        assert_eq!(revision, revisions[1]);
        assert_eq!(
            selector,
            crate::package::manifest::Selector::Tag("v1.1.0".into())
        );
    }

    #[test]
    fn group_versions_respect_zero_major_compatibility() {
        let (_root, repo, revisions) = tagged_repo(&["v0.1.0", "v0.1.5", "v0.2.0"]);
        let arena = internment::Arena::new();
        let requests = vec![request(
            &arena,
            RefSpec::Version("^0.1.0".parse().expect("req")),
        )];

        let (revision, selector) =
            checkout_group_requests(&repo, &key(), &requests).expect("zero-major selection");

        assert_eq!(revision, revisions[1]);
        assert_eq!(
            selector,
            crate::package::manifest::Selector::Tag("v0.1.5".into())
        );
    }

    #[test]
    fn group_versions_reject_incompatible_ranges() {
        let (_root, repo, _revisions) = tagged_repo(&["v1.0.0", "v2.0.0"]);
        let arena = internment::Arena::new();
        let requests = vec![
            request(&arena, RefSpec::Version("^1.0".parse().expect("req"))),
            request(&arena, RefSpec::Version("=2.0.0".parse().expect("req"))),
        ];

        let err = checkout_group_requests(&repo, &key(), &requests)
            .expect_err("incompatible ranges should fail");

        assert!(err.contains("satisfies all requests"));
    }

    #[test]
    fn fixed_selectors_must_resolve_to_same_revision() {
        let (_root, repo, _revisions) = tagged_repo(&["v1.0.0", "v1.1.0"]);
        let arena = internment::Arena::new();
        let requests = vec![
            request(&arena, RefSpec::Tag("v1.0.0".into())),
            request(&arena, RefSpec::Tag("v1.1.0".into())),
        ];

        let err = checkout_group_requests(&repo, &key(), &requests)
            .expect_err("different fixed revisions should fail");

        assert!(err.contains("resolve to different revisions"));
    }

    #[test]
    fn fixed_and_version_selectors_can_coalesce_on_same_revision() {
        let (_root, repo, revisions) = tagged_repo(&["v1.0.0", "v1.1.0"]);
        let arena = internment::Arena::new();
        let requests = vec![
            request(&arena, RefSpec::Version("=1.0.0".parse().expect("req"))),
            request(&arena, RefSpec::Tag("v1.0.0".into())),
        ];

        let (revision, selector) = checkout_group_requests(&repo, &key(), &requests)
            .expect("same revision should coalesce");

        assert_eq!(revision, revisions[0]);
        assert_eq!(
            selector,
            crate::package::manifest::Selector::Tag("v1.0.0".into())
        );
    }

    #[test]
    fn sync_accepts_both_packages_as_path_dependencies() {
        let workspace = temp_dir("both-path");
        let dep = workspace.join("dep");
        let root = workspace.join("root");

        write_manifest(
            &dep,
            "[package]\nname = \"github.com/example/dep\"\nkind = \"both\"\n",
        );
        write_manifest(
            &root,
            "[package]\nname = \"github.com/example/root\"\nkind = \"executable\"\n\n[require]\n\"github.com/example/dep\" = { path = \"../dep\" }\n",
        );

        let graph = match super::sync_dependencies(root, SyncOptions::default()) {
            Ok(graph) => graph,
            Err(_) => panic!("sync should succeed"),
        };

        let mut ordered = graph.ordered_packages();
        let (dep_node, dependency) = ordered.next().expect("dependency first");
        let (root_node, root) = ordered.next().expect("root last");
        assert!(ordered.next().is_none());
        assert_eq!(dependency.package.0.as_ref(), "github.com/example/dep");
        assert_eq!(dependency.kind, PackageKind::Both);
        assert_eq!(root.package.0.as_ref(), "github.com/example/root");
        assert!(
            graph
                .dependencies_for(dep_node)
                .expect("leaf dependencies")
                .is_empty()
        );
        let dependencies = graph
            .dependencies_for(root_node)
            .expect("root dependencies");
        assert_eq!(dependencies.len(), 1);
        assert_eq!(
            dependencies["dep"],
            dependency.unique_identifier().expect("identifier").as_str()
        );
    }

    #[test]
    fn locked_sync_uses_cached_revision_without_fetching() {
        let _guard = env_lock()
            .lock()
            .unwrap_or_else(|poison| poison.into_inner());
        let workspace = temp_dir("locked-cache");
        let home = workspace.join("home");
        let root = workspace.join("root");
        let package_name = "github.com/example/dep";
        let canonical_url = "https://github.com/example/dep.git";
        let cache_path = home
            .join(PACKAGE_STORE)
            .join(lockfile::canonical_git_cache_key(
                package_name,
                canonical_url,
            ));
        std::fs::create_dir_all(&cache_path).expect("cache path");
        let repo = Repository::init(&cache_path).expect("cache repo");
        repo.remote("origin", canonical_url).expect("origin");
        let revision = commit_file(
            &repo,
            &cache_path,
            "[package]\nname = \"github.com/example/dep\"\nkind = \"library\"\n",
        );
        tag(&repo, "v1.2.0", revision);
        let tree_hash = integrity::hash_directory(&cache_path).expect("tree hash");

        write_manifest(
            &root,
            "[package]\nname = \"github.com/example/root\"\nkind = \"executable\"\n\n[require]\n\"github.com/example/dep\" = \"^1.2\"\n",
        );

        let mut lock = lockfile::LockFile::new();
        lock.package.push(lockfile::LockPackage {
            node: lockfile::node_from_git(package_name, canonical_url, &revision.to_string()),
            name: package_name.into(),
            kind: PackageKind::Library,
            no_std_prelude: false,
            source_type: lockfile::LockSourceType::Git,
            url: Some(canonical_url.into()),
            path: None,
            requests: vec!["version:^1.2".into()],
            revision: Some(revision.to_string()),
            tree_hash: Some(tree_hash),
            deps: Default::default(),
        });
        lockfile::write(&root.join("package.lock"), &lock).expect("lockfile");

        let _home = TaroHomeGuard::set(&home);
        let graph = match super::sync_dependencies(
            root,
            SyncOptions {
                locked: true,
                update_lock: false,
                strict_env: false,
            },
        ) {
            Ok(graph) => graph,
            Err(_) => panic!("locked sync should succeed"),
        };

        assert_eq!(graph.ordered.len(), 2);
    }

    #[test]
    fn update_lock_disables_strict_mode_even_in_ci() {
        let options = SyncOptions {
            locked: false,
            update_lock: true,
            strict_env: true,
        };

        assert!(!options.strict_mode());
    }
}
