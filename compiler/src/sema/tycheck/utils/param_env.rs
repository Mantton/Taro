use crate::sema::models::{Constraint, InterfaceReference, Ty};
use rustc_hash::FxHashSet;

/// Holds the canonical constraints in scope for a definition.
/// Used during normalization to resolve projections from generic bounds.
#[derive(Debug, Clone, Default)]
pub struct ParamEnv<'ctx> {
    type_equalities: Vec<(Ty<'ctx>, Ty<'ctx>)>,
    bounds: Vec<(Ty<'ctx>, InterfaceReference<'ctx>)>,
}

impl<'ctx> ParamEnv<'ctx> {
    pub fn new(constraints: Vec<Constraint<'ctx>>) -> Self {
        let mut type_equalities = Vec::new();
        let mut bounds = Vec::new();
        for constraint in &constraints {
            match *constraint {
                Constraint::TypeEquality(lhs, rhs) => type_equalities.push((lhs, rhs)),
                Constraint::Bound { ty, interface } => bounds.push((ty, interface)),
            }
        }

        ParamEnv {
            type_equalities,
            bounds,
        }
    }

    pub fn has_type_equalities(&self) -> bool {
        !self.type_equalities.is_empty()
    }

    pub fn normalization_set_capacity_hint(&self) -> usize {
        self.type_equalities
            .len()
            .saturating_add(self.bounds.len())
            .max(8)
    }

    /// Get all interface bounds for a given type (considering type equalities).
    pub fn bounds_for(&self, ty: Ty<'ctx>) -> Vec<InterfaceReference<'ctx>> {
        if self.bounds.is_empty() {
            return Vec::new();
        }

        if self.type_equalities.is_empty() {
            let mut out = Vec::new();
            for (bound_ty, interface) in &self.bounds {
                if *bound_ty == ty && !out.contains(interface) {
                    out.push(*interface);
                }
            }
            return out;
        }

        let eq_set = self.equivalent_types(ty);
        let mut out: FxHashSet<InterfaceReference<'ctx>> = FxHashSet::default();
        out.reserve(self.bounds.len());

        for (bound_ty, interface) in &self.bounds {
            if eq_set.contains(bound_ty) {
                out.insert(*interface);
            }
        }

        out.into_iter().collect()
    }

    /// Build transitive closure of type equalities for a type.
    pub fn equivalent_types(&self, ty: Ty<'ctx>) -> FxHashSet<Ty<'ctx>> {
        let mut seen: FxHashSet<Ty<'ctx>> = FxHashSet::default();
        if self.type_equalities.is_empty() {
            seen.insert(ty);
            return seen;
        }
        seen.reserve(self.type_equalities.len().saturating_add(1));

        let mut stack = Vec::with_capacity(self.type_equalities.len().saturating_add(1));
        stack.push(ty);
        seen.insert(ty);

        while let Some(cur) = stack.pop() {
            for (a, b) in self.type_equalities.iter() {
                if *a == cur && seen.insert(*b) {
                    stack.push(*b);
                } else if *b == cur && seen.insert(*a) {
                    stack.push(*a);
                }
            }
        }

        seen
    }
}
