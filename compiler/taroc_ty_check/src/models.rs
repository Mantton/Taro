use rustc_hash::FxHashMap;
use taroc_ty::{GenericArgument, GenericParameter};

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
