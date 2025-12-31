use crate::sema::models::{Constraint, InterfaceReference, Ty};
use rustc_hash::FxHashSet;

/// Holds the canonical constraints in scope for a definition.
/// Used during normalization to resolve projections from generic bounds.
#[derive(Debug, Clone, Default)]
pub struct ParamEnv<'ctx> {
    constraints: Vec<Constraint<'ctx>>,
}

impl<'ctx> ParamEnv<'ctx> {
    pub fn new(constraints: Vec<Constraint<'ctx>>) -> Self {
        ParamEnv { constraints }
    }

    pub fn empty() -> Self {
        ParamEnv {
            constraints: vec![],
        }
    }

    pub fn constraints(&self) -> &[Constraint<'ctx>] {
        &self.constraints
    }

    /// Get all interface bounds for a given type (considering type equalities).
    pub fn bounds_for(&self, ty: Ty<'ctx>) -> Vec<InterfaceReference<'ctx>> {
        let eq_set = self.equivalent_types(ty);
        let mut out: FxHashSet<InterfaceReference<'ctx>> = FxHashSet::default();

        for constraint in &self.constraints {
            if let Constraint::Bound { ty, interface } = constraint {
                if eq_set.contains(ty) {
                    out.insert(*interface);
                }
            }
        }

        out.into_iter().collect()
    }

    /// Build transitive closure of type equalities for a type.
    pub fn equivalent_types(&self, ty: Ty<'ctx>) -> FxHashSet<Ty<'ctx>> {
        let mut edges = Vec::new();
        for constraint in &self.constraints {
            if let Constraint::TypeEquality(a, b) = constraint {
                edges.push((*a, *b));
            }
        }

        let mut seen: FxHashSet<Ty<'ctx>> = FxHashSet::default();
        let mut stack = vec![ty];
        seen.insert(ty);

        while let Some(cur) = stack.pop() {
            for (a, b) in edges.iter() {
                if *a == cur && seen.insert(*b) {
                    stack.push(*b);
                } else if *b == cur && seen.insert(*a) {
                    stack.push(*a);
                }
            }
        }

        seen
    }

    /// Check if two types are equivalent via in-scope type equalities.
    pub fn types_equal(&self, a: Ty<'ctx>, b: Ty<'ctx>) -> bool {
        if a == b {
            return true;
        }
        self.equivalent_types(a).contains(&b)
    }
}
