use rustc_hash::FxHashMap;
use std::cell::RefCell;
use taroc_context::GlobalContext;
use taroc_hir::DefinitionID;
use taroc_span::Span;
use taroc_ty::{Constraint, GenericArgument, GenericArguments, GenericParameter};

use crate::utils;

/// Maps Generic Parameter IDs to concrete Types.
#[derive(Debug, Clone, Default)]
pub struct SubstitutionMap<'ctx> {
    map: FxHashMap<GenericParameter, GenericArgument<'ctx>>,
}

impl<'ctx> SubstitutionMap<'ctx> {
    pub fn new() -> Self {
        Self {
            map: Default::default(),
        }
    }
    pub fn insert(&mut self, param: GenericParameter, concrete_ty: GenericArgument<'ctx>) {
        self.map.insert(param, concrete_ty);
    }
    pub fn get(&self, param: &GenericParameter) -> Option<&GenericArgument<'ctx>> {
        self.map.get(param)
    }

    /// Merge in all entries from `other`. Panic if any key already exists.
    pub fn extend(&mut self, other: Self) {
        for (param_id, arg) in other.map {
            let entry = self.map.entry(param_id);
            match entry {
                std::collections::hash_map::Entry::Occupied(entry) => {
                    if entry.get() == &arg {
                        continue;
                    }

                    unreachable!("ICE: cannot overwrite substitution")
                }
                std::collections::hash_map::Entry::Vacant(entry) => {
                    entry.insert(arg);
                }
            }
        }
    }
}

pub struct InferenceContext<'ctx> {
    pub context: GlobalContext<'ctx>,       // read‑only db
    pub constraints: Vec<Constraint<'ctx>>, // collected this pass
    pub constraint_spans: Vec<Span>,
}

impl<'ctx> InferenceContext<'ctx> {
    pub fn new(context: GlobalContext<'ctx>) -> Self {
        Self {
            context,
            constraints: Vec::new(),
            constraint_spans: Vec::new(),
        }
    }

    /// Duplicate `sig.bounds` with the given arguments.
    pub fn instantiate_definition_constraints(
        &mut self,
        id: DefinitionID,
        args: GenericArguments<'ctx>,
    ) {
        let subst = utils::create_substitution_map(id, args, self.context);
        let definition = self.context.predicates_of(id);
        for (constraint, _) in definition.constraints.iter() {
            let dup = utils::substitute_constraint(*constraint, &subst, self.context);
            self.constraints.push(dup);
        }
    }
}
