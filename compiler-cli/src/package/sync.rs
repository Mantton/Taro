use crate::package::{
    git::{self, checkout_refspec, fetch_repo, parse_tag_version},
    manifest::{
        DependencyGraph, DependencyGraphEdge, Manifest, NormalizedManifest, PackageIdentifier,
        ResolvedPackage, ResolvedSource, Selector, SourceSpec, UnresolvedDependency,
        ValidatedDependencyGraph,
    },
    utils::language_home,
};
use compiler::{
    constants::{MANIFEST_FILE, PACKAGE_STORE},
    error::{CompileResult, ReportedError},
};
use ecow::EcoString;
use petgraph::algo::toposort;
use rustc_hash::{FxHashMap, FxHashSet};
use std::path::PathBuf;

pub fn sync_dependencies(root: PathBuf) -> Result<ValidatedDependencyGraph, ReportedError> {
    // TODO: Lockfiles!
    let arena = Arenas {
        unresolved: Default::default(),
        resolved: Default::default(),
    };

    let mut actor = Actor {
        arenas: &arena,
        root_package: None,
        package_selections: Default::default(),
        resolution_map: Default::default(),
        package_dependencies: Default::default(),
        resolved_package_dependencies: Default::default(),
    };

    actor.sync(root)
}

struct Actor<'arena> {
    arenas: &'arena Arenas,
    root_package: Option<RPkg<'arena>>,

    resolution_map: FxHashMap<UPkg<'arena>, RPkg<'arena>>,
    package_selections: FxHashMap<PackageIdentifier, Vec<RPkg<'arena>>>,

    package_dependencies:
        FxHashMap<RPkg<'arena>, FxHashMap<PackageIdentifier, (EcoString, UPkg<'arena>)>>,
    resolved_package_dependencies: FxHashMap<RPkg<'arena>, FxHashMap<EcoString, RPkg<'arena>>>,
}

struct Arenas {
    unresolved: internment::Arena<UnresolvedDependency>,
    resolved: internment::Arena<ResolvedPackage>,
}

type UPkg<'a> = internment::ArenaIntern<'a, UnresolvedDependency>;
type RPkg<'a> = internment::ArenaIntern<'a, ResolvedPackage>;

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
}

impl<'a> Actor<'a> {
    fn download_packages(&mut self, root_path: PathBuf) -> CompileResult<Vec<RPkg<'a>>> {
        let root_path = std::fs::canonicalize(&root_path).map_err(|_| ReportedError)?;
        let mut seen = FxHashSet::default();
        let mut packages = vec![];

        let root_manifest =
            Manifest::parse(root_path.join(MANIFEST_FILE)).map_err(|_| ReportedError)?;
        let root_manifest = root_manifest
            .normalize(root_path.clone())
            .map_err(|_| ReportedError)?;
        let root_package = self.intern_rdep(ResolvedPackage {
            package: root_manifest.path.clone(),
            source: ResolvedSource::Path {
                abs: root_path.clone(),
            },
        });
        self.root_package = Some(root_package);

        let mut manifests = vec![(root_manifest, root_package)];
        while let Some((package_manifest, package_resolution)) = manifests.pop() {
            packages.push(package_resolution);
            let mut udeps_for_instance = FxHashMap::default();

            for (name, dependency) in package_manifest.dependencies.clone().into_iter() {
                let udep = self.intern_udep(dependency);
                if udeps_for_instance
                    .insert(udep.package.clone(), (name, udep))
                    .is_some()
                {
                    println!(
                        "'{}' – Multiple Depenencies link to '{}'",
                        package_manifest.path.0, udep.package.0
                    );
                };

                if seen.insert(udep) {
                    // Download this dep -> gives us its own concrete instance (RDep)
                    let (dependency_resolution, dependency_manifest) =
                        self.download_dependency(udep).map_err(|err| {
                            println!("failed to download dependency – {}", err);
                            ReportedError
                        })?;

                    // Remember the resolution
                    self.resolution_map.insert(udep, dependency_resolution);

                    // Push that instance/manifest to continue walking
                    manifests.push((dependency_manifest, dependency_resolution));
                }
            }

            self.package_dependencies
                .insert(package_resolution, udeps_for_instance);
        }

        Ok(packages)
    }

    fn download_dependency(
        &self,
        dependency: UPkg<'a>,
    ) -> Result<(RPkg<'a>, NormalizedManifest), String> {
        match &dependency.source {
            SourceSpec::Path { abs } => {
                let manifest = Manifest::parse(abs.join(MANIFEST_FILE))?;
                let manifest = manifest.normalize(abs.clone())?;
                let dependency = self.intern_rdep(ResolvedPackage {
                    package: dependency.package.clone(),
                    source: ResolvedSource::Path { abs: abs.clone() },
                });
                return Ok((dependency, manifest));
            }
            SourceSpec::Git { url, refspec } => {
                let package_source = language_home()?
                    .join(PACKAGE_STORE)
                    .join(dependency.package.hashed_name());
                let repo = if package_source.exists() {
                    let repo = match git2::Repository::open(&package_source) {
                        Ok(repo) => repo,
                        Err(err) => {
                            return Err(format!(
                                "failed to open package source `{}`: {}",
                                url, err
                            ));
                        }
                    };

                    fetch_repo(&repo)
                        .map_err(|err| format!("Failed to fetch repository `{}`: {}", url, err))?;

                    repo
                } else {
                    // Create & Clone Repo
                    std::fs::create_dir_all(&package_source).map_err(|err| {
                        format!(
                            "failed to create package source directory `{:?}`, {}",
                            package_source, err
                        )
                    })?;

                    println!("Cloning package repository '{}'", &url);
                    match git2::Repository::clone(&url, &package_source) {
                        Ok(repo) => repo,
                        Err(err) => return Err(format!("failed to clone `{}`: {}", url, err)),
                    }
                };

                let (revision, selector) = checkout_refspec(&repo, refspec)
                    .map_err(|err| format!("failed to checkout repo – {}", err))?;
                let manifest = Manifest::parse(package_source.join(MANIFEST_FILE))?;
                let manifest = manifest.normalize(package_source.clone())?;

                let dependency = self.intern_rdep(ResolvedPackage {
                    package: dependency.package.clone(),
                    source: ResolvedSource::Git {
                        url: url.clone(),
                        revision,
                        selector,
                    },
                });
                return Ok((dependency, manifest));
            }
        }
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
        let mut revision_selections = FxHashMap::<git2::Oid, RPkg<'a>>::default();
        let mut tag_selections = FxHashMap::<u64, (semver::Version, RPkg<'a>)>::default();
        for &usage in usages {
            match &usage.source {
                ResolvedSource::Path { abs } => {
                    if !local_selections.contains_key(abs) {
                        local_selections.insert(abs.clone(), usage);
                    }
                }
                ResolvedSource::Git {
                    revision, selector, ..
                } => match selector {
                    Selector::Tag(raw) => {
                        let version = parse_tag_version(raw).unwrap();
                        let major = version.major;

                        match tag_selections.entry(major) {
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
                    }
                    Selector::Commit(_) | Selector::Branch(_) => {
                        revision_selections
                            .entry(*revision)
                            .or_insert_with(|| usage.clone());
                    }
                },
            }
        }

        let all: Vec<_> = local_selections
            .into_iter()
            .map(|(_, value)| value)
            .chain(revision_selections.into_iter().map(|(_, value)| value))
            .chain(tag_selections.into_iter().map(|(_, (_, value))| value))
            .collect();

        all
    }

    fn install_dependencies(&self) -> CompileResult<()> {
        let selections: FxHashSet<_> = self
            .package_selections
            .values()
            .flatten()
            .copied()
            .collect();

        for &selection in selections.iter() {
            match &selection.source {
                ResolvedSource::Git { revision, .. } => {
                    git::install_revision(selection.as_ref().clone(), *revision)
                        .map_err(|_| ReportedError)?;
                }
                _ => {}
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

        // Fill
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
                // dep -> pkg (deps first)
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
                println!("{:?}", graph[index]);

                for i in members {
                    println!("{:?}", i);
                }
                return Err(ReportedError);
            }
        }
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
                    ..
                },
                ResolvedSource::Git {
                    selector: can_selector,
                    ..
                },
            ) => {
                if let Selector::Tag(dep) = dep_selector
                    && let Selector::Tag(can) = can_selector
                {
                    let dep = parse_tag_version(dep).unwrap();
                    let can = parse_tag_version(can).unwrap();
                    dep.major == can.major
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

fn cycle_members<'a>(
    g: &DependencyGraph,
    start: petgraph::prelude::NodeIndex,
) -> Vec<ResolvedPackage> {
    let sccs = tarjan_scc(g);
    if let Some(scc) = sccs.into_iter().find(|c| c.contains(&start)) {
        return scc.into_iter().map(|ix| g[ix].clone()).collect();
    }
    // Fallback: just the one node
    vec![g[start].clone()]
}
