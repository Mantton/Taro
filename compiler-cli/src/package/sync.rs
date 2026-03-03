use crate::package::{
    git::{self, checkout_refspec, fetch_repo, parse_tag_version},
    integrity,
    lockfile::{self, LockFile, LockPackage, LockSourceType},
    manifest::{
        DependencyGraph, DependencyGraphEdge, Manifest, NormalizedManifest, PackageIdentifier,
        ResolvedPackage, ResolvedSource, Selector, SourceSpec, UnresolvedDependency,
        ValidatedDependencyGraph,
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
        package_selections: Default::default(),
        resolution_map: Default::default(),
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
    package_selections: FxHashMap<PackageIdentifier, Vec<RPkg<'arena>>>,

    package_dependencies:
        FxHashMap<RPkg<'arena>, FxHashMap<PackageIdentifier, (EcoString, UPkg<'arena>)>>,
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

struct PendingManifest<'a> {
    manifest: NormalizedManifest,
    package: RPkg<'a>,
    is_root_manifest: bool,
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
        let dependencies = self.download_packages(root)?;
        self.select_versions(dependencies);
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
    fn download_packages(&mut self, root_path: PathBuf) -> CompileResult<Vec<RPkg<'a>>> {
        let mut seen = FxHashSet::default();
        let mut packages = vec![];

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

        let mut manifests = vec![PendingManifest {
            manifest: root_manifest,
            package: root_package,
            is_root_manifest: true,
        }];

        while let Some(pending) = manifests.pop() {
            packages.push(pending.package);
            let mut udeps_for_instance = FxHashMap::default();

            for (name, dependency) in pending.manifest.dependencies.clone().into_iter() {
                if matches!(dependency.source, SourceSpec::Path { .. }) && !pending.is_root_manifest
                {
                    eprintln!(
                        "error: dependency '{}' declares a transitive path dependency ('{}'), but path dependencies are only allowed in the root manifest",
                        pending.manifest.path.0, dependency.package.0
                    );
                    return Err(ReportedError);
                }

                let udep = self.intern_udep(dependency);
                if udeps_for_instance
                    .insert(udep.package.clone(), (name, udep))
                    .is_some()
                {
                    eprintln!(
                        "warning: package '{}' has multiple dependency entries targeting '{}'",
                        pending.manifest.path.0, udep.package.0
                    );
                };

                if seen.insert(udep) {
                    let (dependency_resolution, dependency_manifest) =
                        self.download_dependency(udep).map_err(|err| {
                            eprintln!("error: failed to download dependency: {}", err);
                            ReportedError
                        })?;

                    self.resolution_map.insert(udep, dependency_resolution);

                    manifests.push(PendingManifest {
                        manifest: dependency_manifest,
                        package: dependency_resolution,
                        is_root_manifest: false,
                    });
                }
            }

            self.package_dependencies
                .insert(pending.package, udeps_for_instance);
        }

        Ok(packages)
    }

    fn download_dependency(
        &mut self,
        dependency: UPkg<'a>,
    ) -> Result<(RPkg<'a>, NormalizedManifest), String> {
        match &dependency.source {
            SourceSpec::Path { abs } => {
                let manifest = Manifest::parse(abs.join(MANIFEST_FILE))?;
                let manifest = manifest.normalize(abs.clone())?;
                let dependency = self.intern_rdep(ResolvedPackage {
                    package: dependency.package.clone(),
                    source: ResolvedSource::Path { abs: abs.clone() },
                    kind: manifest.kind,
                    no_std_prelude: manifest.no_std_prelude,
                });
                Ok((dependency, manifest))
            }
            SourceSpec::Git { url, refspec } => {
                let canonical_url = canonicalize_git_url(url)?;
                let package_source =
                    self.ensure_package_cache(&dependency.package, &canonical_url)?;

                let repo = git2::Repository::open(&package_source).map_err(|err| {
                    format!(
                        "failed to open package cache for '{}' at '{}': {}",
                        dependency.package.0,
                        package_source.display(),
                        err
                    )
                })?;

                if refspec.is_mutable() {
                    self.warn_once(format!(
                        "dependency '{}' uses mutable selector '{}'",
                        dependency.package.0,
                        refspec.request_string()
                    ));
                }

                let requested = refspec.request_string();
                let lock_hit = if self.options.update_lock {
                    None
                } else {
                    self.lockfile.as_ref().and_then(|lock| {
                        lock.find_git_request(
                            &dependency.package.0,
                            &canonical_url,
                            requested.as_ref(),
                        )
                    })
                };

                let (revision, selector, expected_tree_hash) = if let Some(entry) = lock_hit {
                    let revision_str = entry.revision.as_ref().ok_or_else(|| {
                        format!(
                            "lockfile entry for '{}' is missing revision",
                            dependency.package.0
                        )
                    })?;
                    let revision = git2::Oid::from_str(revision_str).map_err(|e| {
                        format!(
                            "invalid lockfile revision '{}' for '{}': {}",
                            revision_str, dependency.package.0, e
                        )
                    })?;

                    git::checkout_revision(&repo, revision)?;
                    (
                        revision,
                        Selector::Commit(revision),
                        entry.tree_hash.clone(),
                    )
                } else {
                    let (revision, selector) = checkout_refspec(&repo, refspec)
                        .map_err(|err| format!("failed to checkout dependency – {}", err))?;
                    (revision, selector, None)
                };

                let manifest = Manifest::parse(package_source.join(MANIFEST_FILE))?;
                let manifest = manifest.normalize(package_source.clone())?;

                let dependency = self.intern_rdep(ResolvedPackage {
                    package: dependency.package.clone(),
                    source: ResolvedSource::Git {
                        url: canonical_url.clone().into(),
                        revision,
                        selector,
                        requested,
                    },
                    kind: manifest.kind,
                    no_std_prelude: manifest.no_std_prelude,
                });

                if let Some(hash) = expected_tree_hash {
                    self.expected_tree_hashes.insert(dependency, hash);
                }

                Ok((dependency, manifest))
            }
        }
    }

    fn ensure_package_cache(
        &self,
        package: &PackageIdentifier,
        canonical_url: &str,
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

        Ok(cache_path)
    }

    fn select_versions(&mut self, packages: Vec<RPkg<'a>>) {
        let mut by_package: FxHashMap<PackageIdentifier, Vec<RPkg<'a>>> = Default::default();

        for dep in packages {
            by_package.entry(dep.package.clone()).or_default().push(dep);
        }

        let pairs: FxHashMap<PackageIdentifier, Vec<RPkg<'a>>> = by_package
            .iter()
            .map(|(package, usages)| (package.clone(), self.select_versions_of(usages)))
            .collect();

        self.package_selections = pairs;
    }

    fn select_versions_of(&self, usages: &[RPkg<'a>]) -> Vec<RPkg<'a>> {
        let mut local_selections = FxHashMap::<PathBuf, RPkg<'a>>::default();
        let mut revision_selections = FxHashMap::<(EcoString, git2::Oid), RPkg<'a>>::default();
        let mut tag_selections =
            FxHashMap::<(EcoString, u64), (semver::Version, RPkg<'a>)>::default();

        for &usage in usages {
            match &usage.source {
                ResolvedSource::Path { abs } => {
                    local_selections.entry(abs.clone()).or_insert(usage);
                }
                ResolvedSource::Git {
                    url,
                    revision,
                    selector,
                    ..
                } => match selector {
                    Selector::Tag(raw) => {
                        if let Some(version) = parse_tag_version(raw) {
                            let major = version.major;

                            match tag_selections.entry((url.clone(), major)) {
                                std::collections::hash_map::Entry::Occupied(mut entry) => {
                                    let (current_version, _) = entry.get();
                                    if version > *current_version {
                                        entry.insert((version, usage));
                                    }
                                }
                                std::collections::hash_map::Entry::Vacant(entry) => {
                                    entry.insert((version, usage));
                                }
                            }
                        } else {
                            revision_selections
                                .entry((url.clone(), *revision))
                                .or_insert(usage);
                        }
                    }
                    Selector::Commit(_) | Selector::Branch(_) => {
                        revision_selections
                            .entry((url.clone(), *revision))
                            .or_insert(usage);
                    }
                },
            }
        }

        local_selections
            .into_iter()
            .map(|(_, value)| value)
            .chain(revision_selections.into_iter().map(|(_, value)| value))
            .chain(tag_selections.into_iter().map(|(_, (_, value))| value))
            .collect()
    }

    fn install_dependencies(&mut self) -> CompileResult<()> {
        let selections: FxHashSet<_> = self
            .package_selections
            .values()
            .flatten()
            .copied()
            .collect();

        for &selection in &selections {
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
        let selections: FxHashSet<_> = self
            .package_selections
            .values()
            .flatten()
            .copied()
            .collect();

        for &selection in &selections {
            self.resolved_package_dependencies
                .entry(selection)
                .or_default();
        }

        for package in selections {
            let Some(unresolved) = self.package_dependencies.get(&package) else {
                continue;
            };
            let mut resolved = FxHashMap::default();
            for (_, (name, dependency)) in unresolved {
                let Some(&dependency_resolution) = self.resolution_map.get(&dependency) else {
                    unreachable!("expected dependency resolution")
                };

                let Some(candidates) = self.package_selections.get(&dependency_resolution.package)
                else {
                    unreachable!("expected dependency candidates")
                };

                let Some(selection) = find_selection(dependency_resolution, candidates) else {
                    unreachable!("expected dependency selection")
                };

                resolved.insert(name.clone(), selection);
            }

            self.resolved_package_dependencies.insert(package, resolved);
        }
    }

    fn build_dependency_graph(&self) -> Result<DependencyGraph, ReportedError> {
        let mut graph = DependencyGraph::new();
        let mut nodes = FxHashMap::<ResolvedPackage, petgraph::graph::NodeIndex>::default();
        let mut idx = |p: RPkg<'a>, g: &mut DependencyGraph| {
            *nodes
                .entry(p.as_ref().clone())
                .or_insert_with(|| g.add_node(p.as_ref().clone()))
        };

        for (&pkg, deps) in &self.resolved_package_dependencies {
            let pkg_ix = idx(pkg, &mut graph);
            for (name, &dependency) in deps {
                let dep_ix = idx(dependency, &mut graph);
                let edge = DependencyGraphEdge {
                    dependency: dependency.as_ref().clone(),
                    name: name.clone(),
                };
                graph.add_edge(dep_ix, pkg_ix, edge);
            }
        }

        Ok(graph)
    }

    fn validate_graph(&self, graph: DependencyGraph) -> CompileResult<ValidatedDependencyGraph> {
        match toposort(&graph, None) {
            Ok(order) => {
                let items: Vec<ResolvedPackage> =
                    order.into_iter().map(|i| graph[i].clone()).collect();
                debug_assert!(!items.is_empty(), "non empty compilation list");
                debug_assert!(
                    items.last().cloned() == self.root_package.map(|v| v.as_ref().clone()),
                    "target package is last on compilation list"
                );

                Ok(ValidatedDependencyGraph {
                    graph,
                    ordered: items,
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
            .package_selections
            .values()
            .flatten()
            .copied()
            .filter(|selection| *selection != root)
            .collect();
        selections.sort_by(|a, b| a.package.0.cmp(&b.package.0));
        selections.dedup();

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
                    requested: "path".into(),
                    revision: None,
                    tree_hash: None,
                    deps,
                },
                ResolvedSource::Git {
                    url,
                    revision,
                    requested,
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
                        requested: requested.to_string(),
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

fn find_selection<'a>(dependency: RPkg<'a>, candidates: &[RPkg<'a>]) -> Option<RPkg<'a>> {
    for &candidate in candidates {
        if dependency == candidate {
            return Some(candidate);
        }

        let valid = match (&dependency.source, &candidate.source) {
            (ResolvedSource::Path { abs: dep_path }, ResolvedSource::Path { abs: can_path }) => {
                dep_path == can_path
            }
            (
                ResolvedSource::Git {
                    selector: dep_selector,
                    url: dep_url,
                    ..
                },
                ResolvedSource::Git {
                    selector: can_selector,
                    url: can_url,
                    ..
                },
            ) => {
                if dep_url != can_url {
                    false
                } else if let Selector::Tag(dep) = dep_selector
                    && let Selector::Tag(can) = can_selector
                {
                    match (parse_tag_version(dep), parse_tag_version(can)) {
                        (Some(dep), Some(can)) => dep.major == can.major,
                        _ => dep == can,
                    }
                } else {
                    dep_selector == can_selector
                }
            }
            _ => false,
        };

        if valid {
            return Some(candidate);
        }
    }

    None
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
    use super::{SyncOptions, find_selection};
    use crate::package::manifest::{PackageIdentifier, ResolvedPackage, ResolvedSource, Selector};
    use compiler::compile::config::PackageKind;
    use ecow::EcoString;

    #[test]
    fn find_selection_does_not_cross_git_urls() {
        let dep = ResolvedPackage {
            package: PackageIdentifier("github.com/example/lib".into()),
            source: ResolvedSource::Git {
                url: "https://github.com/example/lib.git".into(),
                revision: git2::Oid::from_str("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
                    .expect("oid"),
                selector: Selector::Tag("v1.2.0".into()),
                requested: EcoString::from("version:^1.2"),
            },
            kind: PackageKind::Library,
            no_std_prelude: false,
        };

        let candidate = ResolvedPackage {
            package: PackageIdentifier("github.com/example/lib".into()),
            source: ResolvedSource::Git {
                url: "https://github.com/another/lib.git".into(),
                revision: git2::Oid::from_str("bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb")
                    .expect("oid"),
                selector: Selector::Tag("v1.9.0".into()),
                requested: EcoString::from("version:^1.2"),
            },
            kind: PackageKind::Library,
            no_std_prelude: false,
        };

        let arena: internment::Arena<ResolvedPackage> = internment::Arena::new();
        let dep_i = arena.intern(dep);
        let candidate_i = arena.intern(candidate);

        assert!(find_selection(dep_i, &[candidate_i]).is_none());
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
