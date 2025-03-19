use taroc_hir::{DefinitionID, DefinitionKind, NodeID, PartialRes};
use taroc_ty::Ty;

use crate::GlobalContext;

impl<'ctx> GlobalContext<'ctx> {
    pub fn def_id(self, id: NodeID, package: usize) -> DefinitionID {
        let resolutions = self.context.store.resolutions.borrow();
        let package = resolutions.get(&package).expect("package");
        let def = package.node_to_def.get(&id).expect("res");
        *def
    }

    pub fn def_kind(self, id: DefinitionID) -> DefinitionKind {
        let resolutions = self.context.store.resolutions.borrow();
        let package = resolutions.get(&id.package().index()).expect("package");
        let partial_res = package.def_to_kind.get(&id).expect("res");
        partial_res.clone()
    }

    pub fn partial_res(self, id: NodeID, package: usize) -> PartialRes {
        let resolutions = self.context.store.resolutions.borrow();
        let package = resolutions.get(&package).expect("package");
        let partial_res = package.partial_resolution_map.get(&id).expect("res");
        partial_res.clone()
    }

    pub fn type_of(self, id: DefinitionID) -> Ty<'ctx> {
        let database = self.context.store.types.borrow();
        return *database.def_to_ty.get(&id).unwrap();
    }

    pub fn generics_of(self, id: DefinitionID) -> taroc_ty::Generics {
        let database = self.context.store.types.borrow();
        return database.def_to_generics.get(&id).unwrap().clone();
    }
}
