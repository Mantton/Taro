use std::cell::RefCell;

use ecow::EcoString;
use index_vec::define_index_type;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::ast::{Identifier, NodeID, Variant, VariantKind};
use crate::package::PackageIndex;
use crate::sema::resolve::resolver::Resolver;
use crate::span::{FileID, Span};
use crate::{ast, error::CompileResult};

mod define;
mod resolver;
mod tag;

pub fn resolve_package(package: &ast::Package) -> CompileResult<()> {
    let mut resolver = Resolver::new();
    tag::tag_package_symbols(package, &mut resolver)?;
    define::define_package_symbols(package, &mut resolver)?;
    Ok(())
}

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
    pub fn from_variant(vdata: &VariantKind) -> CtorKind {
        match *vdata {
            VariantKind::Tuple(..) | VariantKind::Struct(..) => CtorKind::Function,
            VariantKind::Unit => CtorKind::Constant,
        }
    }
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

define_index_type! {
    pub struct ScopeID = u32;
}

pub enum ScopeKind {
    Block(NodeID),
    File(FileID),
    Definition(DefinitionID),
    Module(usize),
}

pub struct Scope {
    parent: Option<ScopeID>,
    kind: ScopeKind,
    table: RefCell<ScopeTable>,

    glob_imports: RefCell<Vec<UsageID>>,
    glob_exports: RefCell<Vec<UsageID>>,
}

pub type ScopeTable = FxHashMap<ScopeKey, ScopeEntrySet>;

impl Scope {
    pub fn new(kind: ScopeKind, parent: Option<ScopeID>) -> Scope {
        Scope {
            parent,
            kind,
            table: Default::default(),
            glob_imports: Default::default(),
            glob_exports: Default::default(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ScopeKey {
    pub name: EcoString,
    pub namespace: ScopeNamespace,
    pub disambiguator: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ScopeNamespace {
    Type,
    Value,
    Module,
}

pub type ScopeEntrySet = FxHashSet<ScopeEntryID>;

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct ScopeEntry {
    pub kind: ScopeEntryKind,
    pub span: Span,
}

define_index_type! {
    pub struct ScopeEntryID = u32;
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum ScopeEntryKind {
    Resolution(Resolution),
    Usage,
}

pub struct ActiveScope {
    pub current: Option<ScopeID>,
    pub file: Option<ScopeID>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Resolution {
    Definition(DefinitionID, DefinitionKind),
    Error,
}

define_index_type! {
    pub struct UsageID = u32;
}

pub struct UsageEntry {
    pub span: Span,
    pub module_path: Vec<Identifier>,
    pub kind: UsageKind,
    pub is_import: bool,
    pub scope_id: ScopeID,
    pub is_resolved: bool,
}

pub enum UsageKind {
    Glob { id: NodeID },
    Single(UsageBinding),
}

pub struct UsageBinding {
    pub node_id: NodeID,
    pub source: Identifier,
    pub target: Identifier,
}
