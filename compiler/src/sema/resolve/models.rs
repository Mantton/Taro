use crate::{
    ast::{self, Identifier, NodeID},
    span::{FileID, Span},
    utils::intern::Interned,
};
use ecow::EcoString;
use index_vec::define_index_type;
use rustc_hash::FxHashMap;
use std::cell::{Cell, RefCell};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DefinitionKind {
    Module,
    Struct,
    Enum,
    Function,
    Constant,
    ModuleVariable,
    Interface,
    TypeAlias,
    Namespace,
    Extension,
    Import,
    Export,
    TypeParameter,
    ConstParameter,
    Field,
    Variant,
    AssociatedFunction,
    AssociatedConstant,
    AssociatedInitializer,
    AssociatedType,
    EnumVariant,
    Ctor(CtorOf, CtorKind),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CtorOf {
    Struct,
    EnumVariant,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CtorKind {
    Function,
    Constant,
}

impl CtorKind {
    pub fn from_variant(vdata: &ast::VariantKind) -> CtorKind {
        match *vdata {
            ast::VariantKind::Tuple(..) | ast::VariantKind::Struct(..) => CtorKind::Function,
            ast::VariantKind::Unit => CtorKind::Constant,
        }
    }
}

index_vec::define_index_type! {
    pub struct PackageIndex = u32;
}

impl PackageIndex {
    pub const LOCAL: PackageIndex = PackageIndex { _raw: 0 };
}

index_vec::define_index_type! {
    pub struct DefinitionIndex = u32;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DefinitionID {
    package_index: PackageIndex,
    definition_index: DefinitionIndex,
}

impl DefinitionID {
    pub fn new(package: PackageIndex, index: DefinitionIndex) -> DefinitionID {
        DefinitionID {
            package_index: package,
            definition_index: index,
        }
    }

    pub fn is_local(&self, index: usize) -> bool {
        self.package_index == PackageIndex::from_usize(index)
    }

    pub fn package(&self) -> PackageIndex {
        self.package_index
    }
}

pub type Scope<'arena> = Interned<'arena, ScopeData<'arena>>;

#[derive(Debug, Clone)]
pub struct ScopeData<'arena> {
    pub parent: Option<Scope<'arena>>,
    pub kind: ScopeKind,
    pub table: RefCell<ScopeTable<'arena>>,

    pub glob_imports: RefCell<Vec<UsageEntry<'arena>>>,
    pub glob_exports: RefCell<Vec<UsageEntry<'arena>>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ScopeKind {
    Block(NodeID),
    File(FileID),
    Definition(DefinitionID, DefinitionKind),
}

pub type ScopeTable<'arena> = FxHashMap<EcoString, NameEntry<'arena>>;

#[derive(Debug, Default, Clone)]
pub struct NameEntry<'arena> {
    pub ty: Option<ScopeEntry<'arena>>,
    pub values: Vec<ScopeEntry<'arena>>, // overload set
    pub module: Option<ScopeEntry<'arena>>,
}

impl<'a> ScopeData<'a> {
    pub fn new(kind: ScopeKind, parent: Option<Scope<'a>>) -> ScopeData<'a> {
        ScopeData {
            parent,
            kind,
            table: Default::default(),
            glob_imports: Default::default(),
            glob_exports: Default::default(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ScopeNamespace {
    Type,
    Value,
    Module,
}

pub type ScopeEntry<'arena> = Interned<'arena, ScopeEntryData<'arena>>;

#[derive(Debug, Clone)]
pub struct ScopeEntryData<'arena> {
    pub kind: ScopeEntryKind<'arena>,
    pub span: Span,
}

impl<'arena> ScopeEntryData<'arena> {
    pub fn definition_id(&self) -> DefinitionID {
        match &self.kind {
            ScopeEntryKind::Resolution(Resolution::Definition(id, _)) => *id,
            ScopeEntryKind::Usage { used_entry, .. } => used_entry.definition_id(),
            _ => {
                unreachable!("cannot request def id ")
            }
        }
    }

    pub fn resolution(&self) -> Resolution {
        match &self.kind {
            ScopeEntryKind::Resolution(resolution) => resolution.clone(),
            ScopeEntryKind::Usage { used_entry, .. } => used_entry.resolution(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ScopeEntryKind<'a> {
    Resolution(Resolution),
    Usage {
        used_entry: ScopeEntry<'a>,
        used_scope: Scope<'a>,
        user: UsageEntry<'a>,
    },
}

pub struct ActiveScope<'a> {
    pub current: Option<Scope<'a>>,
    pub file: Option<Scope<'a>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Resolution {
    Definition(DefinitionID, DefinitionKind),
    SelfTypeAlias(DefinitionID),
    InterfaceSelfTypeParameter(DefinitionID),
    FunctionSet(Vec<DefinitionID>),
    Error,
}

pub type UsageEntry<'arena> = Interned<'arena, UsageEntryData<'arena>>;

#[derive(Debug, Clone)]
pub struct UsageEntryData<'a> {
    pub span: Span,
    pub module_path: Vec<Identifier>,
    pub kind: UsageKind,
    pub is_import: bool,
    pub scope: Scope<'a>,
    pub is_resolved: Cell<bool>,
    pub module_scope: Cell<Option<Scope<'a>>>,
}

#[derive(Debug, Clone)]
pub enum UsageKind {
    Glob { id: NodeID },
    Single(UsageBinding),
}

#[derive(Debug, Clone)]
pub struct UsageBinding {
    pub node_id: NodeID,
    pub source: Identifier,
    pub target: Identifier,
}

pub struct LexicalScope<'a> {
    pub source: LexicalScopeSource<'a>,
    pub table: FxHashMap<EcoString, Resolution>,
}

impl<'a> LexicalScope<'a> {
    pub fn new(source: LexicalScopeSource<'a>) -> LexicalScope<'a> {
        LexicalScope {
            source,
            table: Default::default(),
        }
    }

    pub fn define(&mut self, name: EcoString, resolution: Resolution) {
        self.table.insert(name, resolution);
    }
}

pub enum LexicalScopeSource<'a> {
    Plain,
    DefBoundary(DefinitionID),
    Scoped(Scope<'a>),
}

pub enum LexicalScopeBinding<'arena> {
    Declaration(Holder<'arena>),
    Resolution(Resolution),
}

#[derive(Debug)]
pub enum ResolvedValue<'a> {
    Scope(Scope<'a>),
    Resolution(Resolution),
}

impl<'a> ResolvedValue<'a> {
    pub fn resolution(&self) -> Resolution {
        match self {
            ResolvedValue::Scope(scope) => match scope.kind {
                ScopeKind::Definition(id, kind) => Resolution::Definition(id, kind),
                _ => {
                    unreachable!("unable to fetch resolution of non definition scopes")
                }
            },
            ResolvedValue::Resolution(resolution) => resolution.clone(),
        }
    }
}

pub enum Holder<'a> {
    Single(ScopeEntry<'a>),
    Overloaded(Vec<ScopeEntry<'a>>),
}

impl<'a> Holder<'a> {
    pub fn resolution(&self) -> Resolution {
        match self {
            Holder::Single(entry) => entry.resolution(),
            Holder::Overloaded(entries) => {
                let ids = entries.iter().map(|e| e.definition_id());
                Resolution::FunctionSet(ids.collect())
            }
        }
    }

    pub fn all_entries(&self) -> Vec<ScopeEntry<'a>> {
        match self {
            Holder::Single(entry) => vec![*entry],
            Holder::Overloaded(entries) => entries.clone(),
        }
    }
}

#[derive(Debug)]
pub enum ResolutionError {
    NotAModule(Identifier),
    NotAType(Identifier),
    UnknownSymbol(Identifier),
    AlreadyInScope(Identifier, Span),
}
