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

    pub fn add_constraint(&mut self, constraint: Constraint<'ctx>) {
        match constraint {
            Constraint::TypeEquality(lhs, rhs) => {
                if !self.type_equalities.contains(&(lhs, rhs))
                    && !self.type_equalities.contains(&(rhs, lhs))
                {
                    self.type_equalities.push((lhs, rhs));
                }
            }
            Constraint::Bound { ty, interface } => {
                let item = (ty, interface);
                if !self.bounds.contains(&item) {
                    self.bounds.push(item);
                }
            }
        }
    }

    pub fn extend_from(&mut self, other: &ParamEnv<'ctx>) {
        for &(lhs, rhs) in &other.type_equalities {
            self.add_constraint(Constraint::TypeEquality(lhs, rhs));
        }

        for &(ty, interface) in &other.bounds {
            self.add_constraint(Constraint::Bound { ty, interface });
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

    /// Materialize this environment for the interface-selection engine.
    ///
    /// The constraint solver keeps bounds split by kind for fast lookup, while
    /// `InterfaceGoal` carries a canonical slice so recursive obligations from
    /// conditional conformances can consult the caller's generic assumptions.
    pub fn constraints(&self) -> Vec<Constraint<'ctx>> {
        let mut constraints =
            Vec::with_capacity(self.type_equalities.len().saturating_add(self.bounds.len()));
        constraints.extend(
            self.type_equalities
                .iter()
                .map(|&(lhs, rhs)| Constraint::TypeEquality(lhs, rhs)),
        );
        constraints.extend(
            self.bounds
                .iter()
                .map(|&(ty, interface)| Constraint::Bound { ty, interface }),
        );
        constraints
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

    /// Find a bound after resolving inference variables owned by the caller.
    /// Call-site constraints are often registered before argument inference
    /// finishes, so their stored self type can be an inference variable even
    /// when the projection being normalized already has a concrete self type.
    pub fn first_bound_for_interface_resolved(
        &self,
        ty: Ty<'ctx>,
        interface_id: crate::hir::DefinitionID,
        mut resolve: impl FnMut(Ty<'ctx>) -> Ty<'ctx>,
    ) -> Option<InterfaceReference<'ctx>> {
        let mut equivalent = FxHashSet::default();
        equivalent.insert(resolve(ty));

        // Preserve the normal ParamEnv equality closure after resolving
        // call-site inference variables. Either side of an equality may have
        // been registered before inference selected its concrete type.
        loop {
            let mut changed = false;
            for &(lhs, rhs) in &self.type_equalities {
                let lhs = resolve(lhs);
                let rhs = resolve(rhs);
                if equivalent.contains(&lhs) && equivalent.insert(rhs) {
                    changed = true;
                } else if equivalent.contains(&rhs) && equivalent.insert(lhs) {
                    changed = true;
                }
            }

            if !changed {
                break;
            }
        }

        self.bounds.iter().find_map(|(bound_ty, interface)| {
            (interface.id == interface_id && equivalent.contains(&resolve(*bound_ty)))
                .then_some(*interface)
        })
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
