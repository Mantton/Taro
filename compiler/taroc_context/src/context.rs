use crate::{CompilerSession, GlobalContext, TypeDatabase};
use taroc_hir::{DefinitionID, DefinitionKind, NodeID, PackageIndex, PartialResolution};
use taroc_resolve_models::DefinitionContext;
use taroc_span::{Identifier, Symbol};
use taroc_ty::{
    EnumDefinition, GenericArgument, GenericParameter, LabeledFunctionSignature, StructDefinition,
    Ty, TyKind,
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

    #[track_caller]
    pub fn def_id(self, id: NodeID) -> DefinitionID {
        let resolutions = self.context.store.resolutions.borrow();
        let package = resolutions
            .get(&self.session().package_index)
            .expect("package");
        let def = package.node_to_def.get(&id).expect("res");
        *def
    }

    #[track_caller]
    pub fn parent(self, id: DefinitionID) -> DefinitionID {
        let resolutions = self.context.store.resolutions.borrow();
        let package = resolutions.get(&id.package().index()).expect("package");
        let def = package.def_to_parent.get(&id).expect("parent of id");
        *def
    }

    pub fn def_kind(self, id: DefinitionID) -> DefinitionKind {
        let resolutions = self.context.store.resolutions.borrow();
        let package = resolutions.get(&id.package().index()).expect("package");
        let kind = package.def_to_kind.get(&id).expect("res");
        *kind
    }

    #[track_caller]
    pub fn ident_for(self, id: DefinitionID) -> Identifier {
        let resolutions = self.context.store.resolutions.borrow();
        let package = resolutions.get(&id.package().index()).expect("package");
        let symbol = package.def_to_ident.get(&id).expect("def identifier");
        *symbol
    }

    pub fn def_parent(self, id: DefinitionID) -> DefinitionID {
        let resolutions = self.context.store.resolutions.borrow();
        let package = resolutions.get(&id.package().index()).expect("package");
        let parent = package.def_to_parent.get(&id).expect("def parent");
        *parent
    }

    #[track_caller]
    pub fn def_context(self, id: DefinitionID) -> Option<DefinitionContext<'ctx>> {
        let resolutions = self.context.store.resolutions.borrow();
        let package = resolutions.get(&id.package().index()).expect("package");
        let ctx = package.def_to_context.get(&id);
        ctx.cloned()
    }

    #[track_caller]
    pub fn resolution(self, id: NodeID) -> PartialResolution {
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

    #[track_caller]
    pub fn type_of(self, id: DefinitionID) -> Ty<'ctx> {
        let kind = self.def_kind(id);

        if matches!(kind, DefinitionKind::Interface) {
            panic!("ICE: fetching type_of interface")
        }

        let database = self.context.store.types.borrow();
        let database = database.get(&id.package().index()).expect("package types");
        return *database
            .def_to_ty
            .get(&id)
            .expect("expected typeof of definition");
    }

    pub fn type_of_opt(self, id: DefinitionID) -> Option<Ty<'ctx>> {
        let database = self.context.store.types.borrow();
        let database = database.get(&id.package().index()).expect("package types");
        return database.def_to_ty.get(&id).cloned();
    }

    #[track_caller]
    pub fn type_of_node(self, id: NodeID) -> Ty<'ctx> {
        let database = self.context.store.types.borrow();
        let database = database
            .get(&self.session().index().index())
            .expect("package types");
        return *database
            .node_to_ty
            .get(&id)
            .expect("expected typeof of node");
    }

    pub fn generics_of(self, id: DefinitionID) -> &'ctx taroc_ty::Generics {
        let database = self.context.store.types.borrow();
        let database = database.get(&id.package().index()).expect("package types");

        if let Some(x) = database.def_to_generics.get(&id) {
            x
        } else {
            self.context.store.interners.alloc(taroc_ty::Generics {
                parameters: vec![],
                has_self: false,
            })
        }
    }

    pub fn cache_generics(self, id: DefinitionID, generics: taroc_ty::Generics) {
        let mut cache = self.context.store.types.borrow_mut();
        let package_index = id.package().index();
        let database = cache.entry(package_index).or_insert(Default::default());
        let generics = self.context.store.interners.alloc(generics);
        let ok = database.def_to_generics.insert(id, generics).is_none();
        debug_assert!(ok, "duplicated generic information")
    }

    pub fn cache_def_constraints(
        self,
        id: DefinitionID,
        constraints: taroc_ty::DefinitionConstraints<'ctx>,
    ) {
        let mut cache = self.context.store.types.borrow_mut();
        let package_index = id.package().index();
        let database = cache.entry(package_index).or_insert(Default::default());
        let ok = database
            .def_to_constraints
            .insert(id, constraints)
            .is_none();
        debug_assert!(ok, "duplicated constraint information")
    }

    pub fn cache_type(self, id: DefinitionID, ty: taroc_ty::Ty<'ctx>) {
        let mut cache = self.context.store.types.borrow_mut();
        let package_index = id.package().index();
        let database = cache.entry(package_index).or_insert(Default::default());
        database.def_to_ty.insert(id, ty);
    }

    pub fn cache_type_of_node(self, id: NodeID, ty: taroc_ty::Ty<'ctx>) {
        let mut cache = self.context.store.types.borrow_mut();
        let package_index = self.session().package_index;
        let database = cache.entry(package_index).or_insert(Default::default());
        database.node_to_ty.insert(id, ty);
    }

    pub fn cache_signature(self, id: DefinitionID, sig: taroc_ty::LabeledFunctionSignature<'ctx>) {
        let mut cache = self.context.store.types.borrow_mut();
        let package_index = id.package().index();
        let database = cache.entry(package_index).or_insert(Default::default());
        let alloc = self.context.store.interners.alloc(sig);
        database.def_to_fn_signature.insert(id, alloc);
    }

    pub fn fn_signature(self, id: DefinitionID) -> &'ctx LabeledFunctionSignature<'ctx> {
        let database = self.context.store.types.borrow();
        let database = database.get(&id.package().index()).expect("package types");
        return database
            .def_to_fn_signature
            .get(&id)
            .expect("expected fn sig of definition");
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

    pub fn with_type_database<F, T>(self, index: PackageIndex, func: F) -> T
    where
        F: FnOnce(&mut TypeDatabase<'ctx>) -> T,
    {
        let mut cache = self.context.store.types.borrow_mut();
        let database = cache.entry(index.index()).or_insert(Default::default());
        func(database)
    }

    pub fn ty_to_def(self, ty: Ty<'ctx>) -> Option<DefinitionID> {
        match ty.kind() {
            TyKind::Bool => self.context.store.common_types.mappings.bool.get(),
            TyKind::Rune => self.context.store.common_types.mappings.rune.get(),
            TyKind::Int(int_ty) => match int_ty {
                taroc_ty::IntTy::ISize => self.context.store.common_types.mappings.int.get(),
                taroc_ty::IntTy::I8 => self.context.store.common_types.mappings.int8.get(),
                taroc_ty::IntTy::I16 => self.context.store.common_types.mappings.int16.get(),
                taroc_ty::IntTy::I32 => self.context.store.common_types.mappings.int32.get(),
                taroc_ty::IntTy::I64 => self.context.store.common_types.mappings.int64.get(),
            },
            TyKind::UInt(uint_ty) => match uint_ty {
                taroc_ty::UIntTy::USize => self.context.store.common_types.mappings.uint.get(),
                taroc_ty::UIntTy::U8 => self.context.store.common_types.mappings.uint8.get(),
                taroc_ty::UIntTy::U16 => self.context.store.common_types.mappings.uint16.get(),
                taroc_ty::UIntTy::U32 => self.context.store.common_types.mappings.uint32.get(),
                taroc_ty::UIntTy::U64 => self.context.store.common_types.mappings.uint64.get(),
            },
            TyKind::Float(float_ty) => match float_ty {
                taroc_ty::FloatTy::F32 => self.context.store.common_types.mappings.float32.get(),
                taroc_ty::FloatTy::F64 => self.context.store.common_types.mappings.float64.get(),
            },
            TyKind::Pointer(_, mutability) => match mutability {
                taroc_hir::Mutability::Mutable => {
                    self.context.store.common_types.mappings.ptr.get()
                }
                taroc_hir::Mutability::Immutable => {
                    self.context.store.common_types.mappings.const_ptr.get()
                }
            },
            TyKind::Reference(_, mutability) => match mutability {
                taroc_hir::Mutability::Mutable => {
                    self.context.store.common_types.mappings.mut_ref.get()
                }
                taroc_hir::Mutability::Immutable => {
                    self.context.store.common_types.mappings.const_ref.get()
                }
            },
            TyKind::Array(..) => self.context.store.common_types.mappings.array.get(),
            TyKind::Tuple(..) => None,
            TyKind::Adt(def, ..) => Some(def.id),
            TyKind::Existential(..) => None,
            TyKind::Parameter(..) => None,
            TyKind::Function { .. } => None,
            TyKind::AssociatedType { .. } => None,
            TyKind::Infer(..) => None,
            TyKind::Error => None,
            TyKind::FnDef(id, ..) => Some(id),
            _ => None,
        }
    }

    pub fn predicates_of(self, id: DefinitionID) -> taroc_ty::DefinitionConstraints<'ctx> {
        let database = self.context.store.types.borrow();
        let database = database.get(&id.package().index()).expect("package types");
        return database
            .def_to_constraints
            .get(&id)
            .cloned()
            .unwrap_or_default();
    }
}
