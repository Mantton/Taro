use crate::span::Symbol;
use crate::thir::FieldIndex;
use crate::{
    PackageIndex,
    compile::config::Config,
    diagnostics::DiagCtx,
    hir::{self, DefinitionID},
    mir::{self, Body},
    sema::{
        models::{FloatTy, IntTy, LabeledFunctionSignature, StructDefinition, Ty, TyKind, UIntTy},
        resolve::models::{
            DefinitionKind, ResolutionOutput, ScopeData, ScopeEntryData, TypeHead, UsageEntryData,
        },
        tycheck::solve::Adjustment,
    },
    utils::intern::{Interned, InternedInSet, InternedSet},
};
use bumpalo::Bump;
use ecow::EcoString;
use rustc_hash::FxHashMap;
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

    pub fn cache_extension_type_head(self, extension_id: DefinitionID, head: TypeHead) {
        self.with_type_database(extension_id.package(), |db| {
            db.extension_to_type_head.insert(extension_id, head.clone());
            db.type_head_to_extensions
                .entry(head)
                .or_default()
                .push(extension_id);
        });
    }

    pub fn cache_node_type(self, id: hir::NodeID, ty: Ty<'arena>) {
        self.with_session_type_database(|db| {
            db.node_to_ty.insert(id, ty);
        });
    }

    pub fn cache_node_adjustments(self, id: hir::NodeID, adjustments: Vec<Adjustment<'arena>>) {
        if adjustments.is_empty() {
            return;
        }
        self.with_session_type_database(|db| {
            db.node_to_adjustments.insert(id, adjustments);
        });
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

    pub fn get_signature(self, id: DefinitionID) -> &'arena LabeledFunctionSignature<'arena> {
        self.with_type_database(id.package(), |db| {
            *db.def_to_fn_sig
                .get(&id)
                .expect("fn signature of definition")
        })
    }

    pub fn get_struct_definition(self, id: DefinitionID) -> &'arena StructDefinition<'arena> {
        self.with_type_database(id.package(), |db| {
            *db.def_to_struct_def
                .get(&id)
                .expect("struct definition of definition")
        })
    }

    pub fn node_adjustments(self, id: hir::NodeID) -> Option<Vec<Adjustment<'arena>>> {
        self.with_session_type_database(|db| db.node_to_adjustments.get(&id).cloned())
    }

    pub fn get_extension_type_head(self, extension_id: DefinitionID) -> Option<TypeHead> {
        self.with_type_database(extension_id.package(), |db| {
            db.extension_to_type_head.get(&extension_id).cloned()
        })
    }

    #[track_caller]
    pub fn get_node_type(self, id: hir::NodeID) -> Ty<'arena> {
        self.with_session_type_database(|db| db.node_to_ty.get(&id).cloned())
            .expect("type of node")
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

    pub fn definition_kind(self, id: DefinitionID) -> DefinitionKind {
        let output = self.resolution_output(id.package());
        *output.definition_to_kind.get(&id).expect("definition kind")
    }

    pub fn definition_parent(self, id: DefinitionID) -> Option<DefinitionID> {
        let output = self.resolution_output(id.package());
        output.definition_to_parent.get(&id).copied()
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
}

impl<'arena> CompilerStore<'arena> {
    pub fn new(
        arenas: &'arena CompilerArenas<'arena>,
        output_root: PathBuf,
    ) -> CompilerStore<'arena> {
        CompilerStore {
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
        }
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
}
impl<'arena> CompilerInterners<'arena> {
    pub fn new(arenas: &'arena CompilerArenas<'arena>) -> CompilerInterners<'arena> {
        CompilerInterners {
            arenas,
            types: InternedSet::new(),
            type_lists: InternedSet::new(),
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
    pub mir_bodies: typed_arena::Arena<Body<'arena>>,
    pub mir_packages: typed_arena::Arena<mir::MirPackage<'arena>>,
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
            mir_bodies: Default::default(),
            mir_packages: Default::default(),
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

            error: mk(TyKind::Error),
        }
    }
}

#[derive(Debug, Default)]
pub struct TypeDatabase<'arena> {
    pub def_to_ty: FxHashMap<DefinitionID, Ty<'arena>>,
    pub def_to_fn_sig: FxHashMap<DefinitionID, &'arena LabeledFunctionSignature<'arena>>,
    pub def_to_struct_def: FxHashMap<DefinitionID, &'arena StructDefinition<'arena>>,
    pub extension_to_type_head: FxHashMap<DefinitionID, TypeHead>,
    pub type_head_to_extensions: FxHashMap<TypeHead, Vec<DefinitionID>>,
    pub type_head_to_members: FxHashMap<TypeHead, TypeMemberIndex>,
    pub node_to_ty: FxHashMap<hir::NodeID, Ty<'arena>>,
    pub node_to_adjustments: FxHashMap<hir::NodeID, Vec<Adjustment<'arena>>>,
    pub node_to_field_index: FxHashMap<hir::NodeID, usize>,
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

impl<'arena> GlobalContext<'arena> {
    pub fn cache_field_index(self, id: hir::NodeID, index: usize) {
        self.with_session_type_database(|db| {
            db.node_to_field_index.insert(id, index);
        });
    }

    pub fn get_field_index(self, id: hir::NodeID) -> Option<FieldIndex> {
        self.with_session_type_database(|db| db.node_to_field_index.get(&id).copied())
    }
}
