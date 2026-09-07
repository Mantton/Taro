use petgraph::algo::kosaraju_scc;
use petgraph::graph::{DiGraph, NodeIndex};
use petgraph::visit::{Dfs, EdgeRef};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    compile::context::Gcx,
    error::CompileResult,
    hir::{self, DefinitionID},
    sema::models::{InterfaceDefinition, InterfaceReference},
    span::Spanned,
};

pub fn run(package: &hir::Package, context: Gcx) -> CompileResult<()> {
    Actor::run(package, context)
}

struct Actor<'ctx> {
    context: Gcx<'ctx>,
    graph: DiGraph<DefinitionID, &'ctx Spanned<InterfaceReference<'ctx>>>,
    nodes: FxHashMap<DefinitionID, NodeIndex>,
}

impl<'ctx> Actor<'ctx> {
    fn new(context: Gcx<'ctx>) -> Actor<'ctx> {
        Actor {
            context,
            graph: Default::default(),
            nodes: Default::default(),
        }
    }

    fn run(_: &hir::Package, context: Gcx<'ctx>) -> CompileResult<()> {
        let mut actor = Actor::new(context);
        let interfaces = context.with_session_type_database(|db| db.def_to_iface_def.clone());
        let superinterfaces = actor.validate(interfaces);
        context.with_session_type_database(|db| db.interface_to_supers = superinterfaces);
        context.dcx().ok()
    }
}

impl<'ctx> Actor<'ctx> {
    fn validate(
        &mut self,
        interfaces: FxHashMap<DefinitionID, &'ctx InterfaceDefinition<'_>>,
    ) -> FxHashMap<DefinitionID, FxHashSet<DefinitionID>> {
        // Seed local definitions, then follow parents through their owning package.
        // Imported interfaces are not present in the session's type database.
        for (&id, _) in &interfaces {
            let index = self.graph.add_node(id);
            self.nodes.insert(id, index);
        }

        let mut pending: Vec<_> = interfaces.values().copied().collect();
        while let Some(interface) = pending.pop() {
            let child = self.nodes[&interface.id];

            for superface in &interface.superfaces {
                let parent_id = superface.value.id;
                let parent = *self.nodes.entry(parent_id).or_insert_with(|| {
                    pending.push(
                        self.context
                            .get_interface_definition(parent_id)
                            .expect("resolved superinterface must have a definition"),
                    );
                    self.graph.add_node(parent_id)
                });
                self.graph.add_edge(child, parent, &superface);
            }
        }

        // Check Circular references
        let sccs = kosaraju_scc(&self.graph);
        for comp in sccs {
            if comp.len() > 1 || self.graph.contains_edge(comp[0], comp[0]) {
                let nodes: Vec<_> = comp.iter().map(|&n| self.graph[n]).collect();
                let span = self
                    .graph
                    .edge_references()
                    .find(|e| {
                        // 2. Keep the first edge whose source AND target
                        //    are both in our cycle component `comp`
                        comp.contains(&e.source()) && comp.contains(&e.target())
                    })
                    .map(|e| e.weight().span)
                    .expect("ICE: ");

                let context = self.context;
                let mut cycle_display: Vec<_> = nodes
                    .iter()
                    .map(|node| {
                        context
                            .symbol_text(context.definition_ident(*node).symbol)
                            .to_string()
                    })
                    .collect();

                // complte final -> n(0)
                if let Some(first) = cycle_display.first().cloned() {
                    cycle_display.push(first);
                }

                let message = format!(
                    "circular interface super-requirements\n\tcycle: {}",
                    cycle_display.join(" -> ")
                );

                self.context.dcx().emit_error(message, Some(span));
                continue;
            }
        }

        // compute superinterfaces
        let mut superinterfaces = FxHashMap::default();
        for &start_id in interfaces.keys() {
            let node = self.nodes[&start_id];
            let mut dfs = Dfs::new(&self.graph, node);
            let mut set = FxHashSet::default();
            while let Some(nx) = dfs.next(&self.graph) {
                let idx = self.graph[nx];
                if idx != start_id {
                    set.insert(idx);
                }
            }
            superinterfaces.insert(start_id, set);
        }

        superinterfaces
    }
}
