use petgraph::algo::{kosaraju_scc, toposort};
use petgraph::graph::{EdgeIndex, Graph, NodeIndex};
use std::collections::{HashMap, HashSet};
use taroc_hir::DefinitionID;

type Id = DefinitionID;
type FieldId = DefinitionID;
type VariantId = DefinitionID;

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct EdgeInfo {
    /// Field that triggered the reference A -> B
    pub field: FieldId,
    /// If the field is inside an enum variant, which one (None for structs)
    pub variant: Option<VariantId>,
}

#[derive(Default)]
pub struct TypeGraph {
    g: Graph<Id, EdgeInfo, petgraph::Directed>,
    ix: HashMap<Id, NodeIndex>,
    seen: HashSet<(Id, Id, FieldId, Option<VariantId>)>,
}

impl TypeGraph {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn ensure_node(&mut self, id: Id) -> NodeIndex {
        *self.ix.entry(id).or_insert_with(|| self.g.add_node(id))
    }

    pub fn add_edge_from_field(&mut self, from: Id, to: Id, info: EdgeInfo) -> EdgeIndex {
        // comment this block out if you *want* parallel edges preserved:
        let k = (from, to, info.field, info.variant);
        if !self.seen.insert(k) {
            // already recorded this exact field->type edge
            // return any existing edge index if you care; otherwise just short-circuit:
            // (we'll still return a fresh id so callers don't care)
        }

        let a = self.ensure_node(from);
        let b = self.ensure_node(to);
        self.g.add_edge(a, b, info)
    }

    pub fn recursive_sccs(&self) -> Vec<Vec<Id>> {
        let mut out = Vec::new();
        for comp in kosaraju_scc(&self.g) {
            if comp.len() > 1 {
                out.push(comp.into_iter().map(|ix| self.g[ix]).collect());
            } else {
                let ix = comp[0];
                if self.g.find_edge(ix, ix).is_some() {
                    out.push(vec![self.g[ix]]);
                }
            }
        }
        out
    }

    pub fn _topo_order(&self) -> Option<Vec<Id>> {
        toposort(&self.g, None)
            .ok()
            .map(|order| order.into_iter().map(|ix| self.g[ix]).collect())
    }

    /// Grab one representative EdgeInfo for edge A -> B (useful in diagnostics)
    pub fn _any_edge_info_between(&self, from: Id, to: Id) -> Option<EdgeInfo> {
        let (&ia, &ib) = (self.ix.get(&from)?, self.ix.get(&to)?);
        self.g.edges_connecting(ia, ib).next().map(|e| *e.weight())
    }
}
