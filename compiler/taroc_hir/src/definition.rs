use super::NodeID;
use index_vec::IndexVec;
use rustc_hash::FxHashSet;

pub struct Definitions {
    table: DefinitionTable,
}

impl Definitions {
    pub fn new() -> Self {
        Definitions {
            table: Default::default(),
        }
    }

    pub fn create_def(&mut self, parent: DefinitionID) -> DefinitionID {
        assert!(parent.package_index == 0, "Must be local package");
        let index = self.table.next(Some(parent.definition_index));
        DefinitionID {
            definition_index: index,
            package_index: PackageIndex::new(0),
        }
    }
}

#[derive(Default)]
pub struct DefinitionTable {
    index_to_parent: IndexVec<DefinitionIndex, Option<DefinitionIndex>>,
}

impl DefinitionTable {
    fn next(&mut self, parent: Option<DefinitionIndex>) -> DefinitionIndex {
        let index = DefinitionIndex::from(self.index_to_parent.len());
        self.index_to_parent.push(parent);
        index
    }
}

index_vec::define_index_type! {
    pub struct DefinitionIndex = u32;
}

index_vec::define_index_type! {
    pub struct PackageIndex = u32;
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

    pub fn is_local(&self) -> bool {
        self.package_index == PackageIndex::new(0)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DefinitionKind {
    Module,
    Struct,
    Enum,
    Function,
    Constructor(CtorOf, CtorKind),
    Variable,
    Interface,
    TypeAlias,
    Namespace,
    Bridged,
    Import,
    Export,
    Extension,
    Conformance,
    Extern,
    TypeParameter,
    Field,
    Variant,
    ComputedProperty,
}

impl DefinitionKind {
    pub fn description(&self) -> &'static str {
        match self {
            DefinitionKind::Module => "module",
            DefinitionKind::Struct => "struct",
            DefinitionKind::Enum => "enum",
            DefinitionKind::Function => "function",
            DefinitionKind::Constructor(_, _) => "constructor",
            DefinitionKind::Variable => "local variable",
            DefinitionKind::Interface => "interface",
            DefinitionKind::TypeAlias => "type alias",
            DefinitionKind::Namespace => "namespace",
            DefinitionKind::Bridged => "bridged namespace",
            DefinitionKind::Import => "import",
            DefinitionKind::Extension => "extension",
            DefinitionKind::Conformance => "conformance",
            DefinitionKind::Extern => "extern",
            DefinitionKind::TypeParameter => "type parameter",
            DefinitionKind::Field => "field",
            DefinitionKind::Variant => "variant",
            DefinitionKind::Export => "export",
            DefinitionKind::ComputedProperty => "computed property",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SymbolNamespace {
    Type,
    Value,
}

#[derive(Debug, Clone)]
pub enum Resolution {
    Definition(DefinitionID, DefinitionKind),
    FunctionSet(FxHashSet<DefinitionID>),
    InterfaceSelfTypeAlias(DefinitionID),
    SelfTypeAlias(DefinitionID),
    ConformanceSelfTypeAlias {
        ty: DefinitionID,
        interface: DefinitionID,
        conformance: DefinitionID,
    },
    Local(NodeID),
    Error,
}

impl Resolution {
    pub fn def_id(&self) -> Option<DefinitionID> {
        match self {
            Resolution::Definition(i, _) => Some(*i),
            Resolution::FunctionSet(_) => None,
            Resolution::InterfaceSelfTypeAlias(i) => Some(*i),
            Resolution::ConformanceSelfTypeAlias { conformance, .. } => Some(*conformance),
            Resolution::SelfTypeAlias(i) => Some(*i),
            Resolution::Local(_) => None,
            Resolution::Error => None,
        }
    }

    pub fn def_kind(&self) -> Option<DefinitionKind> {
        match self {
            Resolution::Definition(_, k) => Some(*k),
            Resolution::FunctionSet(_) => Some(DefinitionKind::Function),
            Resolution::InterfaceSelfTypeAlias(_) => None,
            Resolution::SelfTypeAlias(_) => None,
            Resolution::Local(_) => None,
            Resolution::Error => None,
            Resolution::ConformanceSelfTypeAlias { .. } => None,
        }
    }

    pub fn is_error(&self) -> bool {
        match self {
            Resolution::Error => true,
            _ => false,
        }
    }

    pub fn description(&self) -> &'static str {
        match self {
            Resolution::Definition(_, k) => k.description(),
            Resolution::FunctionSet(_) => "function",
            Resolution::InterfaceSelfTypeAlias(_) => "self type",
            Resolution::ConformanceSelfTypeAlias { .. } => "self type",
            Resolution::SelfTypeAlias(_) => "self type",
            Resolution::Local(_) => "local variable",
            Resolution::Error => "unresolved symbol",
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum CtorOf {
    Struct,
    Variant,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum CtorKind {
    Fn,
    Const,
}

#[derive(Debug, Clone)]
pub struct PartialRes {
    base_res: Resolution,
    unresolved_segments: usize,
}

impl PartialRes {
    #[inline]
    pub fn new(base_res: Resolution) -> Self {
        PartialRes {
            base_res,
            unresolved_segments: 0,
        }
    }

    #[inline]
    pub fn with_unresolved_segments(base_res: Resolution, mut unresolved_segments: usize) -> Self {
        if matches!(base_res, Resolution::Error) {
            unresolved_segments = 0
        }
        PartialRes {
            base_res,
            unresolved_segments,
        }
    }

    #[inline]
    pub fn base_res(&self) -> Resolution {
        self.base_res.clone()
    }

    #[inline]
    pub fn unresolved_segments(&self) -> usize {
        self.unresolved_segments
    }

    #[inline]
    pub fn full_res(&self) -> Option<Resolution> {
        (self.unresolved_segments == 0).then_some(self.base_res.clone())
    }

    #[inline]
    pub fn expect_full_res(&self) -> Resolution {
        self.full_res().expect("unexpected unresolved segments")
    }
}
