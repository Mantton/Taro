use super::lockfile::LockFile;
use petgraph::{
    graph::{DiGraph, NodeIndex},
    visit::{DfsPostOrder, EdgeRef},
};
use std::collections::{HashMap, HashSet};
use taroc_constants::STD_PREFIX;

pub struct DependencyGraph {
    graph: DiGraph<String, ()>,
    _nodes: HashMap<String, NodeIndex>,
}

impl From<&LockFile> for DependencyGraph {
    fn from(lockfile: &LockFile) -> Self {
        let mut graph = DiGraph::<String, ()>::new();
        let mut node_map = HashMap::new();

        // add std package
        let std_index = graph.add_node(STD_PREFIX.into());
        node_map.insert(STD_PREFIX.into(), std_index);

        // add root package
        let root_index = graph.add_node(lockfile.name.clone());
        node_map.insert(lockfile.name.clone(), root_index);

        let mut unique = HashSet::new();

        // check duplicates
        for package in lockfile.package.iter() {
            if unique.contains(&package.name) {
                unique.remove(&package.name);
            } else {
                unique.insert(&package.name);
            }
        }

        // add dependency nodes
        for package in lockfile.package.iter() {
            let identifier = if unique.contains(&package.name) {
                package.name.clone()
            } else {
                package.qualified()
            };

            if node_map.contains_key(&identifier) {
                panic!("duplicated packages in node map!");
            }

            let index = graph.add_node(identifier.clone());
            node_map.insert(identifier, index);
        }

        // add dependency edges
        graph.add_edge(root_index, std_index, ()); // root_package -> std

        for package in lockfile.package.iter() {
            let package_index = node_map
                .get(&package.name)
                .or_else(|| node_map.get(&package.qualified()))
                .expect("expected pacakge to be indexed")
                .clone();

            graph.add_edge(package_index, std_index, ()); // dependency -> std
            if package.direct {
                graph.add_edge(root_index, package_index, ()); // package -> dependency
            }

            let Some(dependencies) = &package.require else {
                continue;
            };

            for dependency in dependencies {
                let require_index = node_map
                    .get(dependency)
                    .expect(format!("dependency not found in lockfile! {}", dependency).as_str());

                graph.add_edge(package_index, *require_index, ()); // package -> dependency
            }
        }

        DependencyGraph {
            graph,
            _nodes: node_map,
        }
    }
}

impl DependencyGraph {
    pub fn compilation_order(&self) -> Vec<String> {
        let mut visited = HashSet::new();
        let mut result = Vec::new();
        let mut dfs = DfsPostOrder::empty(&self.graph);

        // Perform DFS on all nodes
        for node in self.graph.node_indices() {
            if !visited.contains(&node.index()) {
                dfs.move_to(node);
                while let Some(nx) = dfs.next(&self.graph) {
                    if !visited.contains(&nx.index()) {
                        visited.insert(nx.index());
                        result.push(self.graph[nx].clone());
                    }
                }
            }
        }

        result
    }
}

impl DependencyGraph {
    pub fn check_cycles(&self) -> Result<(), Vec<String>> {
        let mut state: HashMap<NodeIndex, u8> = self
            .graph
            .node_indices()
            .map(|node| (node, 0)) // 0 = Unvisited
            .collect();
        let mut stack = Vec::new();

        for node in self.graph.node_indices() {
            if state[&node] == 0 && dfs_cyle(&self.graph, node, &mut state, &mut stack) {
                let cycle = stack
                    .into_iter()
                    .map(|idx| self.graph[idx].clone())
                    .collect();

                return Err(cycle);
            }
        }

        Ok(())
    }
}

fn dfs_cyle(
    graph: &DiGraph<String, ()>,
    node: NodeIndex,
    state: &mut HashMap<NodeIndex, u8>,
    stack: &mut Vec<NodeIndex>,
) -> bool {
    state.insert(node, 1); // Mark as Visiting
    stack.push(node);

    for edge in graph.edges(node) {
        let neighbor = edge.target();
        match state.get(&neighbor) {
            Some(1) => {
                // Cycle detected
                stack.push(neighbor);
                return true;
            }
            Some(0) => {
                // Continue DFS
                if dfs_cyle(graph, neighbor, state, stack) {
                    return true;
                }
            }
            _ => {}
        }
    }

    stack.pop();
    state.insert(node, 2); // Mark as Visited
    false
}

pub fn build_graph(lockfile: &LockFile) -> Result<DependencyGraph, String> {
    let graph = DependencyGraph::from(lockfile);
    let cycle_result = graph.check_cycles();

    if let Err(cycle) = cycle_result {
        let message = format!("cyclic dependencies detected:\n{}", cycle.join("\n"));
        return Err(message);
    }

    Ok(graph)
}
