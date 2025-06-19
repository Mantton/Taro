use crate::ty::{
    ConformanceRecord, DefinitionFunctionsData, EnumDefinition, FloatTy, GenericArgument,
    GenericParameter, IntTy, InterfaceDefinition, LabeledFunctionSignature, PackageAliasTable,
    SimpleType, SpannedConstraints, StructDefinition, Ty, TyKind, UIntTy,
};
use bumpalo::Bump;
use rustc_hash::{FxHashMap, FxHashSet};
use std::{
    borrow::Borrow,
    cell::{Cell, RefCell},
    hash::{Hash, Hasher},
    marker::PhantomData,
    rc::Rc,
};
use taroc_data_structures::Interned;
use taroc_hir::{DefinitionID, DefinitionKind, NodeID, PackageIndex, PartialResolution};
use taroc_resolve_models::DefinitionContext;
use taroc_span::{FileID, Identifier, Symbol};

pub struct ContextStore<'ctx> {
    pub interners: ContextInterners<'ctx>,
    pub resolutions: RefCell<FxHashMap<PackageIndex, ResolutionData<'ctx>>>,
    pub package_mapping: RefCell<FxHashMap<String, PackageIndex>>,
    pub types: RefCell<FxHashMap<PackageIndex, TypeDatabase<'ctx>>>,
    pub common_types: CommonTypes<'ctx>,
}

impl<'ctx> ContextStore<'ctx> {
    pub fn new(arenas: &'ctx ContextArenas<'ctx>) -> ContextStore<'ctx> {
        let interners = ContextInterners::new(arenas);
        let common_types = CommonTypes::new(&interners);
        ContextStore {
            interners,
            common_types,
            package_mapping: RefCell::default(),
            resolutions: RefCell::default(),
            types: RefCell::default(),
        }
    }
}

pub struct ContextArenas<'ctx> {
    pub resolve: Bump,
    pub types: Bump,
    pub arena: Bump,
    _data: PhantomData<DefinitionContext<'ctx>>,
}

impl<'ctx> ContextArenas<'ctx> {
    pub fn new() -> ContextArenas<'ctx> {
        ContextArenas {
            resolve: Bump::new(),
            types: Bump::new(),
            arena: Bump::new(),
            _data: PhantomData::default(),
        }
    }
}

pub struct ContextInterners<'ctx> {
    pub arenas: &'ctx ContextArenas<'ctx>,
    ty: InternedSet<'ctx, TyKind<'ctx>>,
    ty_list: InternedSet<'ctx, Vec<Ty<'ctx>>>,
    generic_arguments: InternedSet<'ctx, Vec<GenericArgument<'ctx>>>,
}

impl<'ctx> ContextInterners<'ctx> {
    pub fn new(arenas: &'ctx ContextArenas<'ctx>) -> ContextInterners<'ctx> {
        ContextInterners {
            arenas,
            ty: InternedSet::new(),
            ty_list: InternedSet::new(),
            generic_arguments: InternedSet::new(),
        }
    }
}

impl<'ctx> ContextInterners<'ctx> {
    pub fn intern_ty(&self, kind: TyKind<'ctx>) -> Ty<'ctx> {
        let ik = self
            .ty
            .intern(kind, |k| {
                let k = self.arenas.types.alloc(k);
                return InternedInSet(k);
            })
            .0;

        let i = Interned::new_unchecked(ik);
        return Ty::with_kind(i);
    }

    pub fn intern_ty_list(&self, items: &Vec<Ty<'ctx>>) -> &'ctx [Ty<'ctx>] {
        let ik = self
            .ty_list
            .intern_ref(items, || {
                let k = self.arenas.types.alloc(items.clone());
                return InternedInSet(k);
            })
            .0;

        ik
    }

    pub fn intern_generic_args(
        &self,
        items: &Vec<GenericArgument<'ctx>>,
    ) -> &'ctx [GenericArgument<'ctx>] {
        let ik = self
            .generic_arguments
            .intern_ref(items, || {
                let k = self.arenas.types.alloc(items.clone());
                return InternedInSet(k);
            })
            .0;

        ik
    }

    pub fn mk_args(&self, args: Vec<GenericArgument<'ctx>>) -> &'ctx [GenericArgument<'ctx>] {
        return self.arenas.types.alloc_slice_copy(&args);
    }

    pub fn intern<T>(&self, value: T) -> Interned<T> {
        let value = self.arenas.arena.alloc(value);
        Interned::new_unchecked(value)
    }

    pub fn alloc<T>(&self, value: T) -> &'ctx T {
        self.arenas.arena.alloc(value)
    }

    pub fn intern_slice<T: Copy>(&self, value: &[T]) -> &'ctx [T] {
        let value = self.arenas.arena.alloc_slice_copy(value);
        value
    }
}

pub struct ResolutionData<'ctx> {
    pub root: DefinitionContext<'ctx>,
    pub node_to_def: FxHashMap<NodeID, DefinitionID>,
    pub def_to_kind: FxHashMap<DefinitionID, DefinitionKind>,
    pub def_to_context: FxHashMap<DefinitionID, DefinitionContext<'ctx>>,
    pub def_to_ident: FxHashMap<DefinitionID, Identifier>,
    pub def_to_parent: FxHashMap<DefinitionID, DefinitionID>,
    pub resolution_map: FxHashMap<NodeID, PartialResolution>,
    pub generics_map: FxHashMap<DefinitionID, Vec<(Symbol, DefinitionID)>>,
    pub file_to_imports: FxHashMap<FileID, FxHashSet<PackageIndex>>,
}

#[derive(Debug, Default)]
pub struct TypeDatabase<'ctx> {
    pub def_to_ty: FxHashMap<DefinitionID, Ty<'ctx>>,
    pub def_to_generics: FxHashMap<DefinitionID, &'ctx crate::ty::Generics>,
    pub def_to_constraints: FxHashMap<DefinitionID, &'ctx SpannedConstraints<'ctx>>,
    pub def_to_canon_constraints: FxHashMap<DefinitionID, &'ctx SpannedConstraints<'ctx>>,
    pub structs: FxHashMap<DefinitionID, &'ctx StructDefinition<'ctx>>,
    pub enums: FxHashMap<DefinitionID, EnumDefinition<'ctx>>,
    pub interfaces: FxHashMap<DefinitionID, &'ctx InterfaceDefinition<'ctx>>,
    pub functions: FxHashMap<DefinitionID, LabeledFunctionSignature<'ctx>>,
    pub def_to_functions: FxHashMap<DefinitionID, Rc<RefCell<DefinitionFunctionsData<'ctx>>>>,
    pub def_to_fn_signature: FxHashMap<DefinitionID, &'ctx LabeledFunctionSignature<'ctx>>,
    pub extension_ty_map: FxHashMap<DefinitionID, SimpleType>,
    pub alias_table: PackageAliasTable,
    pub node_to_ty: FxHashMap<NodeID, Ty<'ctx>>,
    pub superinterfaces: FxHashMap<DefinitionID, FxHashSet<DefinitionID>>,
    pub conformances: FxHashMap<SimpleType, Vec<ConformanceRecord<'ctx>>>,
}

pub struct CommonTypes<'ctx> {
    pub bool: Ty<'ctx>,
    pub rune: Ty<'ctx>,
    pub string: Ty<'ctx>,
    pub void: Ty<'ctx>,

    pub uint: Ty<'ctx>,
    pub uint8: Ty<'ctx>,
    pub uint16: Ty<'ctx>,
    pub uint32: Ty<'ctx>,
    pub uint64: Ty<'ctx>,

    pub int: Ty<'ctx>,
    pub int8: Ty<'ctx>,
    pub int16: Ty<'ctx>,
    pub int32: Ty<'ctx>,
    pub int64: Ty<'ctx>,

    pub float32: Ty<'ctx>,
    pub float64: Ty<'ctx>,

    pub error: Ty<'ctx>,
    pub self_type_parameter: Ty<'ctx>,

    pub mappings: CommonTypeMapping,
}

#[derive(Default)]
pub struct CommonTypeMapping {
    pub array: Cell<Option<DefinitionID>>,
    pub ptr: Cell<Option<DefinitionID>>,
    pub const_ptr: Cell<Option<DefinitionID>>,
    pub mut_ref: Cell<Option<DefinitionID>>,
    pub const_ref: Cell<Option<DefinitionID>>,

    pub bool: Cell<Option<DefinitionID>>,
    pub rune: Cell<Option<DefinitionID>>,

    pub uint: Cell<Option<DefinitionID>>,
    pub uint8: Cell<Option<DefinitionID>>,
    pub uint16: Cell<Option<DefinitionID>>,
    pub uint32: Cell<Option<DefinitionID>>,
    pub uint64: Cell<Option<DefinitionID>>,

    pub int: Cell<Option<DefinitionID>>,
    pub int8: Cell<Option<DefinitionID>>,
    pub int16: Cell<Option<DefinitionID>>,
    pub int32: Cell<Option<DefinitionID>>,
    pub int64: Cell<Option<DefinitionID>>,

    pub float32: Cell<Option<DefinitionID>>,
    pub float64: Cell<Option<DefinitionID>>,

    pub foundation: RefCell<FxHashMap<Symbol, DefinitionID>>,
}

impl<'a> CommonTypes<'a> {
    pub fn new(interner: &ContextInterners<'a>) -> CommonTypes<'a> {
        let mk = |ty| interner.intern_ty(ty);

        CommonTypes {
            bool: mk(TyKind::Bool),
            rune: mk(TyKind::Rune),
            string: mk(TyKind::String),
            void: {
                let list = interner.intern_ty_list(&vec![]);
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

            self_type_parameter: {
                let parameter = GenericParameter {
                    index: 0,
                    name: Symbol::with("Self"),
                };

                let kind = TyKind::Parameter(parameter);
                mk(kind)
            },

            mappings: Default::default(),
        }
    }
}

pub struct WrappedHashSet<K> {
    wrapped: RefCell<FxHashSet<K>>,
}

impl<K> WrappedHashSet<K> {
    pub fn new() -> WrappedHashSet<K> {
        WrappedHashSet {
            wrapped: RefCell::new(FxHashSet::default()),
        }
    }
}

type InternedSet<'tcx, T> = WrappedHashSet<InternedInSet<'tcx, T>>;
// This type holds a `T` in the interner. The `T` is stored in the arena and
// this type just holds a pointer to it, but it still effectively owns it. It
// impls `Borrow` so that it can be looked up using the original
// (non-arena-memory-owning) types.
struct InternedInSet<'tcx, T: ?Sized>(&'tcx T);

impl<'tcx, T: 'tcx + ?Sized> Clone for InternedInSet<'tcx, T> {
    fn clone(&self) -> Self {
        InternedInSet(self.0)
    }
}

impl<'tcx, T: 'tcx + ?Sized> Copy for InternedInSet<'tcx, T> {}

impl<'tcx> Borrow<TyKind<'tcx>> for InternedInSet<'tcx, TyKind<'tcx>> {
    fn borrow(&self) -> &TyKind<'tcx> {
        &self.0
    }
}

impl<'tcx> Borrow<Vec<Ty<'tcx>>> for InternedInSet<'tcx, Vec<Ty<'tcx>>> {
    fn borrow(&self) -> &Vec<Ty<'tcx>> {
        &self.0
    }
}

impl<'tcx> Borrow<Vec<GenericArgument<'tcx>>> for InternedInSet<'tcx, Vec<GenericArgument<'tcx>>> {
    fn borrow(&self) -> &Vec<GenericArgument<'tcx>> {
        &self.0
    }
}
// impl<'tcx> PartialEq for InternedInSet<'tcx, TyKind<'tcx>> {
//     fn eq(&self, other: &InternedInSet<'tcx, TyKind<'tcx>>) -> bool {
//         // The `Borrow` trait requires that `x.borrow() == y.borrow()` equals
//         // `x == y`.
//         self.0 == other.0
//     }
// }

// impl<'tcx> Eq for InternedInSet<'tcx, TyKind<'tcx>> {}

// impl<'tcx> Hash for InternedInSet<'tcx, TyKind<'tcx>> {
//     fn hash<H: Hasher>(&self, s: &mut H) {
//         // The `Borrow` trait requires that `x.borrow().hash(s) == x.hash(s)`.
//         self.0.hash(s)
//     }
// }

impl<'tcx, T> PartialEq for InternedInSet<'tcx, T>
where
    T: ?Sized + PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<'tcx, T> Eq for InternedInSet<'tcx, T> where T: ?Sized + Eq {}

impl<'tcx, T> Hash for InternedInSet<'tcx, T>
where
    T: ?Sized + Hash,
{
    fn hash<H: Hasher>(&self, s: &mut H) {
        self.0.hash(s)
    }
}

impl<K: Eq + Hash + Copy> WrappedHashSet<K> {
    #[inline]
    pub fn intern<Q>(&self, value: Q, make: impl FnOnce(Q) -> K) -> K
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        let mut set = self.wrapped.borrow_mut();
        if let Some(v) = set.get(&value) {
            return *v;
        } else {
            let v = make(value);
            set.insert(v);
            v
        }
    }

    #[inline]
    pub fn intern_ref<Q: ?Sized>(&self, value: &Q, make: impl FnOnce() -> K) -> K
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        let mut set = self.wrapped.borrow_mut();
        if let Some(v) = set.get(value) {
            return *v;
        } else {
            let v = make();
            set.insert(v);
            v
        }
    }
}
