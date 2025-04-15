use rustc_hash::FxHashMap;
use taroc_hir::DefinitionID;
use taroc_ty::GenericArgument;

/// Maps Generic Parameter IDs to concrete Types.
#[derive(Debug, Clone, Default)]
pub struct SubstitutionMap<'ctx> {
    map: FxHashMap<DefinitionID, GenericArgument<'ctx>>,
}

impl<'ctx> SubstitutionMap<'ctx> {
    pub fn new() -> Self {
        Self {
            map: Default::default(),
        }
    }
    pub fn insert(&mut self, param_id: DefinitionID, concrete_ty: GenericArgument<'ctx>) {
        self.map.insert(param_id, concrete_ty);
    }
    pub fn get(&self, param_id: &DefinitionID) -> Option<&GenericArgument<'ctx>> {
        self.map.get(param_id)
    }
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }
}
