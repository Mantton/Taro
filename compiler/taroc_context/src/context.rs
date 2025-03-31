use crate::{CompilerSession, GlobalContext};
use taroc_hir::{DefinitionID, DefinitionKind, NodeID, Resolution};
use taroc_span::Symbol;
use taroc_ty::{
    EnumDefinition, GenericArgument, GenericParameter, InterfaceDefinition, StructDefinition, Ty,
    TyKind,
};

impl<'ctx> GlobalContext<'ctx> {
    pub fn set_session(self, session: CompilerSession) {
        *self.session.borrow_mut() = Some(session);
    }

    pub fn session(self) -> CompilerSession {
        self.session
            .borrow()
            .clone()
            .expect("current compiler session")
    }

    pub fn def_id(self, id: NodeID) -> DefinitionID {
        let resolutions = self.context.store.resolutions.borrow();
        let package = resolutions
            .get(&self.session().package_index)
            .expect("package");
        let def = package.node_to_def.get(&id).expect("res");
        *def
    }

    pub fn def_kind(self, id: DefinitionID) -> DefinitionKind {
        let resolutions = self.context.store.resolutions.borrow();
        let package = resolutions.get(&id.package().index()).expect("package");
        let partial_res = package.def_to_kind.get(&id).expect("res");
        partial_res.clone()
    }

    pub fn resolution(self, id: NodeID) -> Resolution {
        let resolutions = self.context.store.resolutions.borrow();
        let package = resolutions
            .get(&self.session().package_index)
            .expect("package");
        let res = package.resolution_map.get(&id).expect("res");
        res.clone()
    }

    pub fn resolution_generics(self, id: DefinitionID) -> Option<Vec<(Symbol, DefinitionID)>> {
        let resolutions = self.context.store.resolutions.borrow();
        let package = resolutions.get(&id.package().index()).expect("package");
        return package.generics_map.get(&id).cloned();
    }

    pub fn type_of(self, id: DefinitionID) -> Ty<'ctx> {
        let database = self.context.store.types.borrow();
        let database = database.get(&id.package().index()).expect("package types");
        return *database
            .def_to_ty
            .get(&id)
            .expect("expected typeof of definition");
    }

    pub fn generics_of(self, id: DefinitionID) -> taroc_ty::Generics {
        let database = self.context.store.types.borrow();
        let database = database.get(&id.package().index()).expect("package types");

        if let Some(x) = database.def_to_generics.get(&id) {
            x.clone()
        } else {
            taroc_ty::Generics { parameters: vec![] }
        }
    }

    pub fn cache_generics(self, id: DefinitionID, generics: taroc_ty::Generics) {
        let mut cache = self.context.store.types.borrow_mut();
        let package_index = id.package().index();
        let database = cache.entry(package_index).or_insert(Default::default());
        let ok = database.def_to_generics.insert(id, generics).is_none();
        debug_assert!(ok, "duplicated generic information")
    }

    pub fn cache_type(self, id: DefinitionID, ty: taroc_ty::Ty<'ctx>) {
        let mut cache = self.context.store.types.borrow_mut();
        let package_index = id.package().index();
        let database = cache.entry(package_index).or_insert(Default::default());
        database.def_to_ty.insert(id, ty);
    }

    pub fn cache_struct_def(self, id: DefinitionID, def: taroc_ty::StructDefinition<'ctx>) {
        let mut cache = self.context.store.types.borrow_mut();
        let package_index = id.package().index();
        let database = cache.entry(package_index).or_insert(Default::default());
        database.structs.insert(id, def);
    }

    pub fn cache_enum_def(self, id: DefinitionID, def: taroc_ty::EnumDefinition<'ctx>) {
        let mut cache = self.context.store.types.borrow_mut();
        let package_index = id.package().index();
        let database = cache.entry(package_index).or_insert(Default::default());
        database.enums.insert(id, def);
    }

    pub fn cache_interface_def(self, id: DefinitionID, def: taroc_ty::InterfaceDefinition<'ctx>) {
        let mut cache = self.context.store.types.borrow_mut();
        let package_index = id.package().index();
        let database = cache.entry(package_index).or_insert(Default::default());
        database.interfaces.insert(id, def);
    }

    pub fn update_struct_def<F>(self, id: DefinitionID, action: F)
    where
        F: FnOnce(&mut StructDefinition<'ctx>),
    {
        let mut cache = self.context.store.types.borrow_mut();
        let package_index = id.package().index();
        let database = cache.entry(package_index).or_insert(Default::default());
        let entry = database.structs.get_mut(&id).expect("struct definition");
        action(entry);
    }

    pub fn update_enum_def<F>(self, id: DefinitionID, action: F)
    where
        F: FnOnce(&mut EnumDefinition<'ctx>),
    {
        let mut cache = self.context.store.types.borrow_mut();
        let package_index = id.package().index();
        let database = cache.entry(package_index).or_insert(Default::default());
        let entry = database.enums.get_mut(&id).expect("enum definition");
        action(entry);
    }

    pub fn update_interface_def<F>(self, id: DefinitionID, action: F)
    where
        F: FnOnce(&mut InterfaceDefinition<'ctx>),
    {
        let mut cache = self.context.store.types.borrow_mut();
        let package_index = id.package().index();
        let database = cache.entry(package_index).or_insert(Default::default());
        let entry = database
            .interfaces
            .get_mut(&id)
            .expect("interface definition");
        action(entry);
    }

    pub fn type_arguments(self, id: DefinitionID) -> taroc_ty::GenericArguments<'ctx> {
        let generics = self.generics_of(id);

        let args: Vec<GenericArgument<'ctx>> = if generics.parameters.is_empty() {
            vec![]
        } else {
            generics
                .parameters
                .iter()
                .map(|param| {
                    let kind = TyKind::Parameter(GenericParameter {
                        index: param.index,
                        name: param.name,
                    });
                    let ty = self.store.interners.intern_ty(kind);
                    self.cache_type(param.id, ty);
                    let argument = GenericArgument::Type(ty);
                    argument
                })
                .collect()
        };

        self.store.interners.mk_args(args)
    }
}
