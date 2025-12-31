use crate::{
    PackageIndex,
    codegen::target::TargetLayout,
    compile::config::Config,
    diagnostics::DiagCtx,
    error::CompileResult,
    hir::{self, DefinitionID},
    mir::{self, Body},
    sema::{
        models::{
            ConformanceRecord, ConformanceWitness, Const, EnumDefinition, EnumVariant, FloatTy,
            GenericArgument, GenericParameter, Generics, IntTy, InterfaceDefinition,
            InterfaceReference, InterfaceRequirements, LabeledFunctionSignature, StructDefinition,
            Ty, TyKind, UIntTy, Constraint,
        },
        resolve::models::{
            DefinitionKind, PrimaryType, ResolutionOutput, ScopeData, ScopeEntryData, TypeHead,
            UsageEntryData, Visibility,
        },
    },
    specialize::Instance,
    thir::VariantIndex,
    utils::intern::{Interned, InternedInSet, InternedSet},
};
use crate::{constants::STD_PREFIX, span::Symbol};
use bumpalo::Bump;
use ecow::EcoString;
use rustc_hash::{FxHashMap, FxHashSet};
use std::rc::Rc;
use std::{cell::RefCell, ops::Deref, path::PathBuf};

pub type Gcx<'gcx> = GlobalContext<'gcx>;

#[derive(Clone, Copy)]
pub struct GlobalContext<'arena> {
    context: &'arena CompilerContext<'arena>,
    pub config: &'arena Config,
}

impl<'arena> Deref for GlobalContext<'arena> {
    type Target = &'arena CompilerContext<'arena>;
    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &self.context
    }
}

impl<'arena> GlobalContext<'arena> {
    pub fn new(
        context: &'arena CompilerContext<'arena>,
        config: &'arena Config,
    ) -> GlobalContext<'arena> {
        GlobalContext { context, config }
    }

    pub fn package_index(self) -> PackageIndex {
        self.config.index
    }

    pub fn cache_package_ident(self, ident: EcoString) {
        self.context
            .store
            .package_idents
            .borrow_mut()
            .insert(self.package_index(), ident);
    }

    pub fn package_ident(self, pkg: PackageIndex) -> Option<EcoString> {
        self.context
            .store
            .package_idents
            .borrow()
            .get(&pkg)
            .cloned()
    }
}

impl<'arena> GlobalContext<'arena> {
    pub fn cache_type(self, id: DefinitionID, ty: Ty<'arena>) {
        let mut cache = self.context.store.type_databases.borrow_mut();
        let package_index = id.package();
        let database = cache.entry(package_index).or_insert(Default::default());
        database.def_to_ty.insert(id, ty);
    }

    pub fn cache_const(self, id: DefinitionID, value: Const<'arena>) {
        let mut cache = self.context.store.type_databases.borrow_mut();
        let package_index = id.package();
        let database = cache.entry(package_index).or_insert(Default::default());
        database.def_to_const.insert(id, value);
    }

    pub fn cache_constraints(
        self,
        id: DefinitionID,
        constraints: Vec<crate::span::Spanned<Constraint<'arena>>>,
    ) {
        let mut cache = self.context.store.type_databases.borrow_mut();
        let package_index = id.package();
        let database = cache.entry(package_index).or_insert(Default::default());
        database.def_to_constraints.insert(id, constraints);
    }

    pub fn constraints_of(
        self,
        id: DefinitionID,
    ) -> Vec<crate::span::Spanned<Constraint<'arena>>> {
        self.with_type_database(id.package(), |db| {
            db.def_to_constraints.get(&id).cloned().unwrap_or_default()
        })
    }

    pub fn cache_canonical_constraints(
        self,
        id: DefinitionID,
        constraints: Vec<crate::span::Spanned<Constraint<'arena>>>,
    ) {
        let mut cache = self.context.store.type_databases.borrow_mut();
        let package_index = id.package();
        let database = cache.entry(package_index).or_insert(Default::default());
        database.def_to_canon_constraints.insert(id, constraints);
    }

    pub fn canonical_constraints_of(
        self,
        id: DefinitionID,
    ) -> Vec<crate::span::Spanned<Constraint<'arena>>> {
        self.with_type_database(id.package(), |db| {
            db.def_to_canon_constraints
                .get(&id)
                .cloned()
                .unwrap_or_default()
        })
    }

    pub fn cache_alias_type(self, id: DefinitionID, ty: Ty<'arena>) {
        self.with_type_database(id.package(), |db| {
            db.resolved_aliases.insert(id, ty);
        });
    }

    pub fn cache_signature(self, id: DefinitionID, sig: LabeledFunctionSignature<'arena>) {
        let mut cache = self.context.store.type_databases.borrow_mut();
        let package_index = id.package();
        let database = cache.entry(package_index).or_insert(Default::default());
        let alloc = self.context.store.arenas.function_signatures.alloc(sig);
        database.def_to_fn_sig.insert(id, alloc);
    }

    pub fn cache_struct_definition(self, id: DefinitionID, def: StructDefinition<'arena>) {
        let mut cache = self.context.store.type_databases.borrow_mut();
        let package_index = id.package();
        let database = cache.entry(package_index).or_insert(Default::default());
        let alloc = self.context.store.arenas.struct_definitions.alloc(def);
        database.def_to_struct_def.insert(id, alloc);
    }

    pub fn cache_enum_definition(self, id: DefinitionID, def: EnumDefinition<'arena>) {
        let mut cache = self.context.store.type_databases.borrow_mut();
        let package_index = id.package();
        let database = cache.entry(package_index).or_insert(Default::default());
        let alloc = self.context.store.arenas.enum_definitions.alloc(def);
        database.def_to_enum_def.insert(id, alloc);
    }

    pub fn cache_extension_type_head(self, extension_id: DefinitionID, head: TypeHead) {
        self.with_type_database(extension_id.package(), |db| {
            db.extension_to_type_head.insert(extension_id, head.clone());
            db.type_head_to_extensions
                .entry(head)
                .or_default()
                .push(extension_id);
        });
    }

    pub fn cache_generics(self, id: DefinitionID, generics: Generics) {
        let mut cache = self.context.store.type_databases.borrow_mut();
        let package_index = id.package();
        let database = cache.entry(package_index).or_insert(Default::default());
        let generics = self.context.store.arenas.generics.alloc(generics);
        let ok = database.def_to_generics.insert(id, generics).is_none();
        debug_assert!(ok, "duplicated generic information")
    }

    pub fn cache_attributes(self, id: DefinitionID, attributes: hir::AttributeList) {
        let mut cache = self.context.store.type_databases.borrow_mut();
        let package_index = id.package();
        let database = cache.entry(package_index).or_insert(Default::default());
        let attributes = self.context.store.arenas.global.alloc(attributes);
        let ok = database.def_to_attributes.insert(id, attributes).is_none();
        debug_assert!(ok, "duplicated attribute information")
    }
}

impl<'arena> GlobalContext<'arena> {
    #[track_caller]
    #[inline]
    pub fn with_type_database<F, T>(self, index: PackageIndex, func: F) -> T
    where
        F: FnOnce(&mut TypeDatabase<'arena>) -> T,
    {
        let mut cache = self.context.store.type_databases.borrow_mut();
        let database = cache.entry(index).or_insert(Default::default());
        func(database)
    }

    #[track_caller]
    #[inline]
    pub fn with_session_type_database<F, T>(self, func: F) -> T
    where
        F: FnOnce(&mut TypeDatabase<'arena>) -> T,
    {
        self.with_type_database(self.package_index(), func)
    }
}

impl<'arena> GlobalContext<'arena> {
    #[inline]
    pub fn get_type(self, id: DefinitionID) -> Ty<'arena> {
        self.with_type_database(id.package(), |db| {
            *db.def_to_ty.get(&id).expect("type of definition")
        })
    }

    pub fn try_get_const(self, id: DefinitionID) -> Option<Const<'arena>> {
        self.with_type_database(id.package(), |db| db.def_to_const.get(&id).copied())
    }

    #[inline]
    pub fn get_const(self, id: DefinitionID) -> Const<'arena> {
        self.with_type_database(id.package(), |db| {
            *db.def_to_const.get(&id).expect("const value")
        })
    }

    pub fn try_get_alias_type(self, id: DefinitionID) -> Option<Ty<'arena>> {
        self.with_type_database(id.package(), |db| db.resolved_aliases.get(&id).copied())
    }

    #[inline]
    pub fn get_alias_type(self, id: DefinitionID) -> Ty<'arena> {
        self.with_type_database(id.package(), |db| {
            *db.resolved_aliases
                .get(&id)
                .expect("alias type of definition")
        })
    }

    pub fn get_signature(self, id: DefinitionID) -> &'arena LabeledFunctionSignature<'arena> {
        self.with_type_database(id.package(), |db| {
            *db.def_to_fn_sig
                .get(&id)
                .expect("fn signature of definition")
        })
    }

    #[track_caller]
    pub fn get_struct_definition(self, id: DefinitionID) -> &'arena StructDefinition<'arena> {
        self.with_type_database(id.package(), |db| db.def_to_struct_def.get(&id).cloned())
            .expect("struct definition of definition")
    }

    pub fn get_enum_definition(self, id: DefinitionID) -> &'arena EnumDefinition<'arena> {
        self.with_type_database(id.package(), |db| {
            *db.def_to_enum_def
                .get(&id)
                .expect("enum definition of definition")
        })
    }

    pub fn enum_variant_by_index(
        self,
        enum_id: DefinitionID,
        index: VariantIndex,
    ) -> EnumVariant<'arena> {
        let def = self.get_enum_definition(enum_id);
        *def.variants.get(index.index()).expect("enum variant index")
    }

    pub fn get_interface_requirements(
        self,
        id: DefinitionID,
    ) -> Option<&'arena InterfaceRequirements<'arena>> {
        self.with_type_database(id.package(), |db| {
            db.interface_requirements.get(&id).copied()
        })
    }

    pub fn get_extension_type_head(self, extension_id: DefinitionID) -> Option<TypeHead> {
        self.with_type_database(extension_id.package(), |db| {
            db.extension_to_type_head.get(&extension_id).cloned()
        })
    }

    /// Get the Self type for an extension.
    /// - For struct/enum extensions: returns the concrete type
    /// - For interface extensions: returns the Self type parameter
    pub fn get_extension_self_ty(self, extension_id: DefinitionID) -> Option<Ty<'arena>> {
        let head = self.get_extension_type_head(extension_id)?;
        match head {
            TypeHead::Nominal(target_id) => match self.definition_kind(target_id) {
                DefinitionKind::Interface => {
                    // For interface extensions, Self is the abstract Self parameter
                    Some(self.types.self_type_parameter)
                }
                DefinitionKind::Struct | DefinitionKind::Enum => {
                    // For concrete type extensions, Self is the actual type
                    Some(self.get_type(target_id))
                }
                _ => None,
            },
            TypeHead::Primary(p) => Some(match p {
                PrimaryType::Int(k) => Ty::new_int(self, k),
                PrimaryType::UInt(k) => Ty::new_uint(self, k),
                PrimaryType::Float(k) => Ty::new_float(self, k),
                PrimaryType::String => self.types.string,
                PrimaryType::Bool => self.types.bool,
                PrimaryType::Rune => self.types.rune,
            }),
            TypeHead::GcPtr => Some(Ty::new(TyKind::GcPtr, self)),
            TypeHead::Tuple(_)
            | TypeHead::Reference(_)
            | TypeHead::Pointer(_)
            | TypeHead::Array => None, // TODO: complex type extensions
        }
    }

    pub fn get_mir_body(self, id: DefinitionID) -> &'arena mir::Body<'arena> {
        let packages = self.context.store.mir_packages.borrow();
        let package = packages.get(&id.package()).expect("mir package");
        *package.functions.get(&id).expect("mir body")
    }

    pub fn resolution_output(self, pkg: PackageIndex) -> &'arena ResolutionOutput<'arena> {
        let outputs = self.context.store.resolution_outputs.borrow();
        *outputs.get(&pkg).expect("resolution output")
    }

    pub fn definition_ident(self, id: DefinitionID) -> crate::span::Identifier {
        let output = self.resolution_output(id.package());
        *output
            .definition_to_ident
            .get(&id)
            .expect("identifier for definition")
    }

    pub fn is_std_gc_ptr(self, id: DefinitionID) -> bool {
        let ident = self.definition_ident(id);
        if ident.symbol.as_str() != "GcPtr" {
            return false;
        }
        matches!(
            self.package_ident(id.package())
                .as_ref()
                .map(|s| s.as_str()),
            Some(STD_PREFIX)
        )
    }

    pub fn definition_kind(self, id: DefinitionID) -> DefinitionKind {
        let output = self.resolution_output(id.package());
        *output.definition_to_kind.get(&id).expect("definition kind")
    }

    pub fn std_package_index(self) -> Option<PackageIndex> {
        self.context
            .store
            .package_idents
            .borrow()
            .iter()
            .find_map(|(idx, ident)| (ident.as_str() == STD_PREFIX).then_some(*idx))
    }

    pub fn find_std_type(self, name: &str) -> Option<DefinitionID> {
        let pkg = self.std_package_index()?;
        let output = self.resolution_output(pkg);
        output.definition_to_ident.iter().find_map(|(id, ident)| {
            let kind = output.definition_to_kind.get(id)?;
            if matches!(
                kind,
                DefinitionKind::Interface
                    | DefinitionKind::Struct
                    | DefinitionKind::Enum
                    | DefinitionKind::TypeAlias
            ) && ident.symbol.as_str() == name
            {
                Some(*id)
            } else {
                None
            }
        })
    }

    pub fn definition_visibility(self, id: DefinitionID) -> Visibility {
        let output = self.resolution_output(id.package());
        output
            .definition_to_visibility
            .get(&id)
            .copied()
            .unwrap_or(Visibility::Public)
    }

    pub fn definition_parent(self, id: DefinitionID) -> Option<DefinitionID> {
        let output = self.resolution_output(id.package());
        output.definition_to_parent.get(&id).copied()
    }

    pub fn is_visibility_allowed(self, visibility: Visibility, from: DefinitionID) -> bool {
        match visibility {
            Visibility::Public => true,
            Visibility::FilePrivate(file) => self.definition_ident(from).span.file == file,
            Visibility::Private(owner) => self.is_within_definition(from, owner),
        }
    }

    pub fn is_definition_visible(self, target: DefinitionID, from: DefinitionID) -> bool {
        let visibility = self.definition_visibility(target);
        self.is_visibility_allowed(visibility, from)
    }

    fn is_within_definition(self, mut current: DefinitionID, owner: DefinitionID) -> bool {
        if current == owner {
            return true;
        }
        while let Some(parent) = self.definition_parent(current) {
            if parent == owner {
                return true;
            }
            current = parent;
        }
        false
    }

    pub fn cache_object_file(self, path: PathBuf) {
        self.context
            .store
            .object_files
            .borrow_mut()
            .insert(self.package_index(), path);
    }

    pub fn get_object_file(self, pkg: PackageIndex) -> Option<PathBuf> {
        self.context.store.object_files.borrow().get(&pkg).cloned()
    }

    pub fn cache_specializations(self, pkg: PackageIndex, instances: FxHashSet<Instance<'arena>>) {
        self.context
            .store
            .specialization_instances
            .borrow_mut()
            .insert(pkg, instances);
    }

    pub fn specializations_of(self, pkg: PackageIndex) -> Vec<Instance<'arena>> {
        let cache = self.context.store.specialization_instances.borrow();
        match cache.get(&pkg) {
            Some(instances) => instances.iter().copied().collect(),
            None => Vec::new(),
        }
    }

    /// Mark an instance as compiled (to avoid duplicate compilation).
    pub fn mark_instance_compiled(self, instance: Instance<'arena>) {
        self.context
            .store
            .compiled_instances
            .borrow_mut()
            .insert(instance);
    }

    /// Check if an instance has already been compiled.
    pub fn is_instance_compiled(self, instance: Instance<'arena>) -> bool {
        self.context
            .store
            .compiled_instances
            .borrow()
            .contains(&instance)
    }

    pub fn all_object_files(self) -> Vec<PathBuf> {
        let mut inputs: Vec<PathBuf> = self
            .context
            .store
            .object_files
            .borrow()
            .values()
            .cloned()
            .collect();
        inputs.extend(self.context.store.all_link_inputs());
        inputs
    }

    pub fn output_root(self) -> &'arena PathBuf {
        &self.context.store.output_root
    }

    pub fn generics_of(self, id: DefinitionID) -> &'arena Generics {
        let mut database = self.context.store.type_databases.borrow_mut();
        let database = database.entry(id.package()).or_default();

        if let Some(x) = database.def_to_generics.get(&id) {
            x
        } else if let Some(empty) = database.empty_generics {
            empty
        } else {
            let generics = self.context.store.arenas.generics.alloc(Generics {
                parameters: vec![],
                has_self: false,
                parent: None,
                parent_count: 0,
            });
            database.empty_generics = Some(generics);
            generics
        }
    }

    pub fn attributes_of(self, id: DefinitionID) -> &'arena hir::AttributeList {
        let mut database = self.context.store.type_databases.borrow_mut();
        let database = database.entry(id.package()).or_default();

        if let Some(attrs) = database.def_to_attributes.get(&id) {
            *attrs
        } else if let Some(empty) = database.empty_attributes {
            empty
        } else {
            let empty = self.context.store.arenas.global.alloc(Vec::new());
            database.empty_attributes = Some(empty);
            empty
        }
    }
}

pub struct CompilerContext<'arena> {
    pub dcx: Rc<DiagCtx>,
    pub store: CompilerStore<'arena>,
    pub types: CommonTypes<'arena>,
}

impl<'arena> CompilerContext<'arena> {
    pub fn new(dcx: Rc<DiagCtx>, store: CompilerStore<'arena>) -> CompilerContext<'arena> {
        let types = CommonTypes::new(&store.interners);
        CompilerContext { dcx, store, types }
    }

    pub fn dcx(&self) -> &DiagCtx {
        &self.dcx
    }
}

pub struct CompilerStore<'arena> {
    pub arenas: &'arena CompilerArenas<'arena>,
    pub interners: CompilerInterners<'arena>,
    pub resolution_outputs: RefCell<FxHashMap<PackageIndex, &'arena ResolutionOutput<'arena>>>,
    pub package_mapping: RefCell<FxHashMap<EcoString, PackageIndex>>,
    pub package_idents: RefCell<FxHashMap<PackageIndex, EcoString>>,
    pub type_databases: RefCell<FxHashMap<PackageIndex, TypeDatabase<'arena>>>,
    pub mir_packages: RefCell<FxHashMap<PackageIndex, &'arena mir::MirPackage<'arena>>>,
    pub llvm_modules: RefCell<FxHashMap<PackageIndex, String>>,
    pub object_files: RefCell<FxHashMap<PackageIndex, PathBuf>>,
    pub link_inputs: RefCell<Vec<PathBuf>>,
    pub output_root: PathBuf,
    pub specialization_instances: RefCell<FxHashMap<PackageIndex, FxHashSet<Instance<'arena>>>>,
    /// Global set of instances that have been compiled (to avoid duplicate work)
    pub compiled_instances: RefCell<FxHashSet<Instance<'arena>>>,
    /// Target-specific layout information (shared between MIR and codegen).
    pub target_layout: TargetLayout,
}

impl<'arena> CompilerStore<'arena> {
    pub fn new(
        arenas: &'arena CompilerArenas<'arena>,
        output_root: PathBuf,
    ) -> CompileResult<CompilerStore<'arena>> {
        let target_layout = TargetLayout::for_host()?;
        Ok(CompilerStore {
            arenas,
            interners: CompilerInterners::new(arenas),
            package_mapping: Default::default(),
            package_idents: Default::default(),
            resolution_outputs: Default::default(),
            type_databases: Default::default(),
            mir_packages: Default::default(),
            llvm_modules: Default::default(),
            object_files: Default::default(),
            link_inputs: Default::default(),
            output_root,
            specialization_instances: Default::default(),
            compiled_instances: Default::default(),
            target_layout,
        })
    }

    pub fn add_link_input(&self, path: PathBuf) {
        self.link_inputs.borrow_mut().push(path);
    }

    pub fn all_link_inputs(&self) -> Vec<PathBuf> {
        self.link_inputs.borrow().clone()
    }
}

impl<'arena> CompilerStore<'arena> {
    pub fn alloc_mir_package(
        &self,
        package: mir::MirPackage<'arena>,
    ) -> &'arena mir::MirPackage<'arena> {
        self.arenas.mir_packages.alloc(package)
    }
}
pub struct CompilerInterners<'arena> {
    arenas: &'arena CompilerArenas<'arena>,
    types: InternedSet<'arena, TyKind<'arena>>,
    type_lists: InternedSet<'arena, Vec<Ty<'arena>>>,
    generic_arguments: InternedSet<'arena, Vec<GenericArgument<'arena>>>,
}
impl<'arena> CompilerInterners<'arena> {
    pub fn new(arenas: &'arena CompilerArenas<'arena>) -> CompilerInterners<'arena> {
        CompilerInterners {
            arenas,
            types: InternedSet::new(),
            type_lists: InternedSet::new(),
            generic_arguments: InternedSet::new(),
        }
    }

    pub fn intern_ty(&self, k: TyKind<'arena>) -> Ty<'arena> {
        let ptr = self
            .types
            .intern(k, |k| {
                let k = self.arenas.types.alloc(k);
                return InternedInSet(k);
            })
            .0;

        Ty::with_kind(Interned::new_unchecked(ptr))
    }

    pub fn intern_ty_list(&self, items: Vec<Ty<'arena>>) -> &'arena [Ty<'arena>] {
        let ik = self
            .type_lists
            .intern(items, |k| {
                let k = self.arenas.type_lists.alloc(k);
                return InternedInSet(k);
            })
            .0;

        ik
    }

    pub fn intern_generic_args(
        &self,
        items: Vec<GenericArgument<'arena>>,
    ) -> &'arena [GenericArgument<'arena>] {
        let ik = self
            .generic_arguments
            .intern(items, |k| {
                let k = self.arenas.generic_arguments.alloc(k);
                return InternedInSet(k);
            })
            .0;
        ik
    }
}

pub struct CompilerArenas<'arena> {
    pub configs: typed_arena::Arena<Config>,
    pub scopes: typed_arena::Arena<ScopeData<'arena>>,
    pub scope_entries: typed_arena::Arena<ScopeEntryData<'arena>>,
    pub usage_entries: typed_arena::Arena<UsageEntryData<'arena>>,
    pub resolution_outputs: typed_arena::Arena<ResolutionOutput<'arena>>,
    pub types: typed_arena::Arena<TyKind<'arena>>,
    pub type_lists: typed_arena::Arena<Vec<Ty<'arena>>>,
    pub function_signatures: typed_arena::Arena<LabeledFunctionSignature<'arena>>,
    pub struct_definitions: typed_arena::Arena<StructDefinition<'arena>>,
    pub enum_definitions: typed_arena::Arena<EnumDefinition<'arena>>,
    pub mir_bodies: typed_arena::Arena<Body<'arena>>,
    pub mir_packages: typed_arena::Arena<mir::MirPackage<'arena>>,
    pub generics: typed_arena::Arena<Generics>,
    pub generic_arguments: typed_arena::Arena<Vec<GenericArgument<'arena>>>,
    pub interface_definitions: typed_arena::Arena<InterfaceDefinition<'arena>>,
    pub interface_requirements: typed_arena::Arena<InterfaceRequirements<'arena>>,

    pub global: Bump,
}

impl<'arena> CompilerArenas<'arena> {
    pub fn new() -> CompilerArenas<'arena> {
        CompilerArenas {
            configs: Default::default(),
            scopes: Default::default(),
            scope_entries: Default::default(),
            usage_entries: Default::default(),
            resolution_outputs: Default::default(),
            types: Default::default(),
            type_lists: Default::default(),
            function_signatures: Default::default(),
            struct_definitions: Default::default(),
            enum_definitions: Default::default(),
            mir_bodies: Default::default(),
            mir_packages: Default::default(),
            generics: Default::default(),
            generic_arguments: Default::default(),
            interface_definitions: Default::default(),
            interface_requirements: Default::default(),
            global: Bump::new(),
        }
    }
}

pub struct CommonTypes<'arena> {
    pub bool: Ty<'arena>,
    pub rune: Ty<'arena>,
    pub string: Ty<'arena>,
    pub void: Ty<'arena>,

    pub uint: Ty<'arena>,
    pub uint8: Ty<'arena>,
    pub uint16: Ty<'arena>,
    pub uint32: Ty<'arena>,
    pub uint64: Ty<'arena>,

    pub int: Ty<'arena>,
    pub int8: Ty<'arena>,
    pub int16: Ty<'arena>,
    pub int32: Ty<'arena>,
    pub int64: Ty<'arena>,

    pub float32: Ty<'arena>,
    pub float64: Ty<'arena>,

    pub self_type_parameter: Ty<'arena>,

    pub error: Ty<'arena>,
}

impl<'a> CommonTypes<'a> {
    pub fn new(interner: &CompilerInterners<'a>) -> CommonTypes<'a> {
        let mk = |ty| interner.intern_ty(ty);

        CommonTypes {
            bool: mk(TyKind::Bool),
            rune: mk(TyKind::Rune),
            string: mk(TyKind::String),
            void: {
                let list = interner.intern_ty_list(vec![]);
                mk(TyKind::Tuple(list))
            },

            uint: mk(TyKind::UInt(UIntTy::USize)),
            uint8: mk(TyKind::UInt(UIntTy::U8)),
            uint16: mk(TyKind::UInt(UIntTy::U16)),
            uint32: mk(TyKind::UInt(UIntTy::U32)),
            uint64: mk(TyKind::UInt(UIntTy::U64)),

            int: mk(TyKind::Int(IntTy::ISize)),
            int8: mk(TyKind::Int(IntTy::I8)),
            int16: mk(TyKind::Int(IntTy::I16)),
            int32: mk(TyKind::Int(IntTy::I32)),
            int64: mk(TyKind::Int(IntTy::I64)),

            float32: mk(TyKind::Float(FloatTy::F32)),
            float64: mk(TyKind::Float(FloatTy::F64)),

            self_type_parameter: {
                let parameter = GenericParameter {
                    index: 0,
                    name: Symbol::new("Self"),
                };

                let kind = TyKind::Parameter(parameter);
                mk(kind)
            },

            error: mk(TyKind::Error),
        }
    }
}

#[derive(Debug, Default)]
pub struct TypeDatabase<'arena> {
    pub def_to_ty: FxHashMap<DefinitionID, Ty<'arena>>,
    pub def_to_const: FxHashMap<DefinitionID, Const<'arena>>,
    pub def_to_fn_sig: FxHashMap<DefinitionID, &'arena LabeledFunctionSignature<'arena>>,
    pub def_to_struct_def: FxHashMap<DefinitionID, &'arena StructDefinition<'arena>>,
    pub def_to_enum_def: FxHashMap<DefinitionID, &'arena EnumDefinition<'arena>>,
    pub def_to_constraints: FxHashMap<DefinitionID, Vec<crate::span::Spanned<Constraint<'arena>>>>,
    pub def_to_canon_constraints:
        FxHashMap<DefinitionID, Vec<crate::span::Spanned<Constraint<'arena>>>>,
    pub extension_to_type_head: FxHashMap<DefinitionID, TypeHead>,
    pub type_head_to_extensions: FxHashMap<TypeHead, Vec<DefinitionID>>,
    pub type_head_to_members: FxHashMap<TypeHead, TypeMemberIndex>,
    pub def_to_generics: FxHashMap<DefinitionID, &'arena Generics>,
    pub def_to_attributes: FxHashMap<DefinitionID, &'arena hir::AttributeList>,
    pub def_to_iface_def: FxHashMap<DefinitionID, &'arena InterfaceDefinition<'arena>>,
    pub interface_to_supers: FxHashMap<DefinitionID, FxHashSet<DefinitionID>>,
    pub conformances: FxHashMap<TypeHead, Vec<ConformanceRecord<'arena>>>,
    pub interface_requirements: FxHashMap<DefinitionID, &'arena InterfaceRequirements<'arena>>,
    pub conformance_witnesses:
        FxHashMap<(TypeHead, InterfaceReference<'arena>), ConformanceWitness<'arena>>,
    /// Revised alias table
    pub alias_table: crate::sema::models::PackageAliasTable,
    /// Resolved alias types (cached after lowering)
    pub resolved_aliases: FxHashMap<DefinitionID, Ty<'arena>>,
    pub empty_generics: Option<&'arena Generics>,
    pub empty_attributes: Option<&'arena hir::AttributeList>,
}

#[derive(Default, Debug, Clone)]
pub struct MemberSet {
    pub members: Vec<DefinitionID>,
    pub fingerprints: FxHashMap<u64, DefinitionID>,
}

#[derive(Default, Debug, Clone)]
pub struct TypeMemberIndex {
    pub static_functions: FxHashMap<Symbol, MemberSet>,
    pub instance_functions: FxHashMap<Symbol, MemberSet>,
    pub operators: FxHashMap<hir::OperatorKind, MemberSet>,
}

impl<'arena> GlobalContext<'arena> {}
