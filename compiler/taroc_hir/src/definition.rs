use super::NodeID;
use index_vec::IndexVec;
use std::fmt::Display;

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

    pub fn is_local(&self, index: usize) -> bool {
        self.package_index == PackageIndex::from_usize(index)
    }

    pub fn package(&self) -> PackageIndex {
        self.package_index
    }
}

impl Display for DefinitionID {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "DefID({:?}, {:?})",
            self.package_index, self.definition_index
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DefinitionKind {
    Module,
    Struct,
    Enum,
    Function,
    Constructor,
    Operator,
    Variable,
    Constant,
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
    AssociatedType,
    EnumCase,
}

impl DefinitionKind {
    pub fn description(&self) -> &'static str {
        match self {
            DefinitionKind::Module => "module",
            DefinitionKind::Struct => "struct",
            DefinitionKind::Enum => "enum",
            DefinitionKind::Function => "function",
            DefinitionKind::Constructor => "constructor",
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
            DefinitionKind::AssociatedType => "associated type",
            DefinitionKind::Constant => "constant",
            DefinitionKind::Operator => "operator",
            DefinitionKind::EnumCase => "enum case",
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
    InterfaceSelfTypeAlias(DefinitionID),
    SelfTypeAlias(DefinitionID),
    Local(NodeID),
    Error,
}

impl Resolution {
    pub fn def_id(&self) -> Option<DefinitionID> {
        match self {
            Resolution::Definition(i, _) => Some(*i),
            Resolution::InterfaceSelfTypeAlias(i) => Some(*i),
            Resolution::SelfTypeAlias(i) => Some(*i),
            Resolution::Local(_) => None,
            Resolution::Error => None,
        }
    }

    pub fn def_kind(&self) -> Option<DefinitionKind> {
        match self {
            Resolution::Definition(_, k) => Some(*k),
            Resolution::InterfaceSelfTypeAlias(_) => None,
            Resolution::SelfTypeAlias(_) => None,
            Resolution::Local(_) => None,
            Resolution::Error => None,
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
            Resolution::InterfaceSelfTypeAlias(_) => "self type",
            Resolution::SelfTypeAlias(_) => "self type",
            Resolution::Local(_) => "local variable",
            Resolution::Error => "unresolved symbol",
        }
    }
}
