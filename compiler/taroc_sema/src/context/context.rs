use crate::normalize::constraints::canon_predicates_of;
use crate::ty::{
    GenericArgument, GenericParameter, InterfaceReference, LabeledFunctionSignature, ParamEnv,
    SpannedConstraints, Ty, TyKind,
};
use crate::{CompilerSession, GlobalContext, TypeDatabase};
use taroc_hir::{DefinitionID, DefinitionKind, NodeID, PackageIndex, PartialResolution};
use taroc_resolve_models::DefinitionContext;
use taroc_span::{Identifier, Symbol};

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
        let package = resolutions.get(&self.session().index()).expect("package");
        let def = package.node_to_def.get(&id).expect("def_id");
        *def
    }

    #[track_caller]
    pub fn parent(self, id: DefinitionID) -> DefinitionID {
        let resolutions = self.context.store.resolutions.borrow();
        let package = resolutions.get(&id.package()).expect("package");
        let def = package.def_to_parent.get(&id).expect("parent of id");
        *def
    }

    pub fn def_kind(self, id: DefinitionID) -> DefinitionKind {
        let resolutions = self.context.store.resolutions.borrow();
        let package = resolutions.get(&id.package()).expect("package");
        let kind = package.def_to_kind.get(&id).expect("res");
        *kind
    }

    #[track_caller]
    pub fn ident_for(self, id: DefinitionID) -> Identifier {
        let resolutions = self.context.store.resolutions.borrow();
        let package = resolutions.get(&id.package()).expect("package");
        let symbol = package.def_to_ident.get(&id).expect("def identifier");
        *symbol
    }

    pub fn def_parent(self, id: DefinitionID) -> DefinitionID {
        let resolutions = self.context.store.resolutions.borrow();
        let package = resolutions.get(&id.package()).expect("package");
        let parent = package.def_to_parent.get(&id).expect("def parent");
        *parent
    }

    #[track_caller]
    pub fn def_context(self, id: DefinitionID) -> Option<DefinitionContext<'ctx>> {
        let resolutions = self.context.store.resolutions.borrow();
        let package = resolutions.get(&id.package()).expect("package");
        let ctx = package.def_to_context.get(&id);
        ctx.cloned()
    }

    #[track_caller]
    pub fn resolution(self, id: NodeID) -> PartialResolution {
        let resolutions = self.context.store.resolutions.borrow();
        let package = resolutions.get(&self.session().index()).expect("package");
        let res = package.resolution_map.get(&id).expect("res");
        res.clone()
    }

    pub fn resolution_generics(self, id: DefinitionID) -> Option<Vec<(Symbol, DefinitionID)>> {
        let resolutions = self.context.store.resolutions.borrow();
        let package = resolutions.get(&id.package()).expect("package");
        return package.generics_map.get(&id).cloned();
    }

    #[track_caller]
    pub fn type_of(self, id: DefinitionID) -> Ty<'ctx> {
        let kind = self.def_kind(id);

        if matches!(kind, DefinitionKind::Interface) {
            panic!("ICE: fetching type_of interface")
        }

        let database = self.context.store.types.borrow();
        let database = database.get(&id.package()).expect("package types");
        return *database
            .def_to_ty
            .get(&id)
            .expect("expected typeof of definition");
    }

    pub fn type_of_opt(self, id: DefinitionID) -> Option<Ty<'ctx>> {
        let database = self.context.store.types.borrow();
        let database = database.get(&id.package()).expect("package types");
        return database.def_to_ty.get(&id).cloned();
    }

    #[track_caller]
    pub fn type_of_node(self, id: NodeID) -> Ty<'ctx> {
        let database = self.context.store.types.borrow();
        let database = database
            .get(&self.session().index())
            .expect("package types");
        return *database
            .node_to_ty
            .get(&id)
            .expect("expected typeof of node");
    }

    pub fn generics_of(self, id: DefinitionID) -> &'ctx crate::ty::Generics {
        let database = self.context.store.types.borrow();
        let database = database.get(&id.package()).expect("package types");

        if let Some(x) = database.def_to_generics.get(&id) {
            x
        } else {
            self.context.store.interners.alloc(crate::ty::Generics {
                parameters: vec![],
                has_self: false,
            })
        }
    }

    pub fn cache_generics(self, id: DefinitionID, generics: crate::ty::Generics) {
        let mut cache = self.context.store.types.borrow_mut();
        let package_index = id.package();
        let database = cache.entry(package_index).or_insert(Default::default());
        let generics = self.context.store.interners.alloc(generics);
        let ok = database.def_to_generics.insert(id, generics).is_none();
        debug_assert!(ok, "duplicated generic information")
    }

    pub fn cache_def_constraints(self, id: DefinitionID, constraints: SpannedConstraints<'ctx>) {
        let mut cache = self.context.store.types.borrow_mut();
        let package_index = id.package();
        let database = cache.entry(package_index).or_insert(Default::default());
        let constraints = self.context.store.interners.alloc(constraints);
        let ok = database
            .def_to_constraints
            .insert(id, constraints)
            .is_none();
        debug_assert!(ok, "duplicated constraint information")
    }

    pub fn cache_type(self, id: DefinitionID, ty: crate::ty::Ty<'ctx>) {
        let mut cache = self.context.store.types.borrow_mut();
        let package_index = id.package();
        let database = cache.entry(package_index).or_insert(Default::default());
        database.def_to_ty.insert(id, ty);
    }

    pub fn cache_type_of_node(self, id: NodeID, ty: crate::ty::Ty<'ctx>) {
        let mut cache = self.context.store.types.borrow_mut();
        let package_index = self.session().index();
        let database = cache.entry(package_index).or_insert(Default::default());
        database.node_to_ty.insert(id, ty);
    }

    pub fn cache_signature(self, id: DefinitionID, sig: crate::ty::LabeledFunctionSignature<'ctx>) {
        let mut cache = self.context.store.types.borrow_mut();
        let package_index = id.package();
        let database = cache.entry(package_index).or_insert(Default::default());
        let alloc = self.context.store.interners.alloc(sig);
        database.def_to_fn_signature.insert(id, alloc);
    }

    pub fn fn_signature(self, id: DefinitionID) -> &'ctx LabeledFunctionSignature<'ctx> {
        let database = self.context.store.types.borrow();
        let database = database.get(&id.package()).expect("package types");
        return database
            .def_to_fn_signature
            .get(&id)
            .expect("expected fn sig of definition");
    }

    pub fn type_arguments(self, id: DefinitionID) -> crate::ty::GenericArguments<'ctx> {
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
                    let ty = self.mk_ty(kind);
                    self.cache_type(param.id, ty);
                    let argument = GenericArgument::Type(ty);
                    argument
                })
                .collect()
        };

        self.store.interners.mk_args(args)
    }

    #[track_caller]
    pub fn with_type_database<F, T>(self, index: PackageIndex, func: F) -> T
    where
        F: FnOnce(&mut TypeDatabase<'ctx>) -> T,
    {
        let mut cache = self.context.store.types.borrow_mut();
        let database = cache.entry(index).or_insert(Default::default());
        func(database)
    }

    #[track_caller]
    pub fn with_session_type_database<F, T>(self, func: F) -> T
    where
        F: FnOnce(&mut TypeDatabase<'ctx>) -> T,
    {
        let index = self.session().index();
        self.with_type_database(index, func)
    }

    pub fn ty_to_def(self, ty: Ty<'ctx>) -> Option<DefinitionID> {
        match ty.kind() {
            TyKind::Bool => self.context.store.common_types.mappings.bool.get(),
            TyKind::Rune => self.context.store.common_types.mappings.rune.get(),
            TyKind::Int(int_ty) => match int_ty {
                crate::ty::IntTy::ISize => self.context.store.common_types.mappings.int.get(),
                crate::ty::IntTy::I8 => self.context.store.common_types.mappings.int8.get(),
                crate::ty::IntTy::I16 => self.context.store.common_types.mappings.int16.get(),
                crate::ty::IntTy::I32 => self.context.store.common_types.mappings.int32.get(),
                crate::ty::IntTy::I64 => self.context.store.common_types.mappings.int64.get(),
            },
            TyKind::UInt(uint_ty) => match uint_ty {
                crate::ty::UIntTy::USize => self.context.store.common_types.mappings.uint.get(),
                crate::ty::UIntTy::U8 => self.context.store.common_types.mappings.uint8.get(),
                crate::ty::UIntTy::U16 => self.context.store.common_types.mappings.uint16.get(),
                crate::ty::UIntTy::U32 => self.context.store.common_types.mappings.uint32.get(),
                crate::ty::UIntTy::U64 => self.context.store.common_types.mappings.uint64.get(),
            },
            TyKind::Float(float_ty) => match float_ty {
                crate::ty::FloatTy::F32 => self.context.store.common_types.mappings.float32.get(),
                crate::ty::FloatTy::F64 => self.context.store.common_types.mappings.float64.get(),
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
            TyKind::Error => None,
            TyKind::FnDef(id, ..) => Some(id),
            _ => None,
        }
    }
}

impl<'ctx> GlobalContext<'ctx> {
    pub fn predicates_of(self, id: DefinitionID) -> &'ctx SpannedConstraints<'ctx> {
        let database = self.context.store.types.borrow();
        let database = database.get(&id.package()).expect("package types");
        return database
            .def_to_constraints
            .get(&id)
            .cloned()
            .unwrap_or_else(|| self.context.store.interners.alloc(vec![]));
    }
    pub fn canon_predicates_of(self, id: DefinitionID) -> &'ctx SpannedConstraints<'ctx> {
        {
            let database = self.context.store.types.borrow();
            let database = database.get(&id.package()).expect("package types");
            let result = database.def_to_canon_constraints.get(&id).cloned();

            if let Some(result) = result {
                return result;
            }
        }

        let prepared = self
            .context
            .store
            .interners
            .alloc(canon_predicates_of(id, self));

        {
            let mut database = self.context.store.types.borrow_mut();
            let database = database.get_mut(&id.package()).expect("package types");
            database.def_to_canon_constraints.insert(id, prepared);
        }

        return prepared;
    }

    pub fn mk_ty(self, k: TyKind<'ctx>) -> Ty<'ctx> {
        self.store.interners.intern_ty(k)
    }
}

impl<'ctx> GlobalContext<'ctx> {
    pub fn param_env(self, id: DefinitionID) -> ParamEnv<'ctx> {
        let predicates = self.canon_predicates_of(id);
        let constraints: Vec<_> = predicates.iter().map(|p| p.value).collect();
        let constraints = self.store.interners.intern_slice(&constraints);
        ParamEnv { constraints }
    }

    pub fn try_simple_type(self, ty: Ty<'ctx>) -> Option<crate::ty::SimpleType> {
        use crate::ty::SimpleType;
        match ty.kind() {
            TyKind::Bool => Some(SimpleType::Bool),
            TyKind::Rune => Some(SimpleType::Rune),
            TyKind::String => Some(SimpleType::String),
            TyKind::Int(i) => Some(SimpleType::Int(i)),
            TyKind::UInt(u) => Some(SimpleType::UInt(u)),
            TyKind::Float(f) => Some(SimpleType::Float(f)),
            TyKind::Pointer(_, m) => Some(SimpleType::Pointer(m)),
            TyKind::Reference(_, m) => Some(SimpleType::Reference(m)),
            TyKind::Array(..) => Some(SimpleType::Array),
            TyKind::Adt(def, ..) => Some(SimpleType::Adt(def.id)),
            _ => None,
        }
    }

    pub fn has_conformance(
        self,
        ty: Ty<'ctx>,
        interface: InterfaceReference<'ctx>,
    ) -> crate::ty::ConformanceResult {
        let Some(simple) = self.try_simple_type(ty) else {
            return crate::ty::ConformanceResult::NotConformant;
        };

        let databases = self.context.store.types.borrow();
        for db in databases.values() {
            if let Some(records) = db.conformances.get(&simple) {
                for r in records {
                    // Check ID and None-Self Arguments
                    if r.interface.id == interface.id
                        && r.interface.arguments[1..] == r.interface.arguments[1..]
                    {
                        if r.is_conditional {
                            return crate::ty::ConformanceResult::Conforms(Some(r.extension));
                        } else {
                            return crate::ty::ConformanceResult::Conforms(None);
                        }
                    }
                }
            }
        }
        crate::ty::ConformanceResult::NotConformant
    }
}

impl<'ctx> GlobalContext<'ctx> {
    pub fn unsafe_ref<T>(&self, a: &T) -> &'ctx T {
        unsafe { std::mem::transmute(a) }
    }
}
