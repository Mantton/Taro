use super::NodeID;
use crate::VariantKind;
use index_vec::IndexVec;
use rustc_hash::FxHashSet;
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
    Constant,
    Interface,
    TypeAlias,
    Namespace,
    Bridged,
    Import,
    Export,
    Extension,
    Extern,
    TypeParameter,
    ConstParameter,
    Field,
    Variant,
    Ctor(CtorOf, CtorKind),
    StaticVariable,
    AssociatedType,
    AssociatedFunction,
    AssociatedConstant,
    AssociatedOperator,
}

impl DefinitionKind {
    pub fn description(&self) -> &'static str {
        match self {
            DefinitionKind::Module => "module",
            DefinitionKind::Struct => "struct",
            DefinitionKind::Enum => "enum",
            DefinitionKind::Function => "function",
            DefinitionKind::Interface => "interface",
            DefinitionKind::TypeAlias => "type alias",
            DefinitionKind::Namespace => "namespace",
            DefinitionKind::Bridged => "bridged namespace",
            DefinitionKind::Import => "import",
            DefinitionKind::Extension => "extension",
            DefinitionKind::Extern => "extern",
            DefinitionKind::TypeParameter => "type parameter",
            DefinitionKind::Field => "field",
            DefinitionKind::Variant => "variant",
            DefinitionKind::Export => "export",
            DefinitionKind::Constant => "constant",
            DefinitionKind::Ctor(..) => "constructor",
            DefinitionKind::StaticVariable => "static variable",
            DefinitionKind::AssociatedType => "associated type",
            DefinitionKind::AssociatedFunction => "associated function",
            DefinitionKind::AssociatedConstant => "associated constant",
            DefinitionKind::AssociatedOperator => "associated operator",
            DefinitionKind::ConstParameter => "const param",
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
    PrimaryType(PrimaryType),
    Definition(DefinitionID, DefinitionKind),
    InterfaceSelfTypeAlias(DefinitionID),
    SelfTypeAlias(SelfTypeAlias),
    SelfConstructor(DefinitionID),
    Local(NodeID),
    FunctionSet(FxHashSet<DefinitionID>),
    Error,
}

#[derive(Debug, Clone, Copy)]
pub enum SelfTypeAlias {
    Def(DefinitionID),
    Primary(PrimaryType),
}

impl Resolution {
    pub fn def_id(&self) -> Option<DefinitionID> {
        match self {
            Resolution::Definition(i, _) => Some(*i),
            Resolution::InterfaceSelfTypeAlias(i) => Some(*i),
            Resolution::SelfTypeAlias(_) => None,
            _ => None,
        }
    }

    pub fn def_kind(&self) -> Option<DefinitionKind> {
        match self {
            Resolution::Definition(_, k) => Some(*k),
            _ => None,
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
            Resolution::FunctionSet(..) => "function set",
            Resolution::PrimaryType(_) => "primary type",
            Resolution::SelfConstructor(_) => "self constructor",
        }
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CtorOf {
    /// This `DefKind::Ctor` is a synthesized constructor of a tuple or unit struct.
    Struct,
    /// This `DefKind::Ctor` is a synthesized constructor of a tuple or unit variant.
    Variant,
}

/// What kind of constructor something is.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CtorKind {
    /// Constructor function automatically created by a tuple struct/variant.
    Fn,
    /// Constructor constant automatically created by a unit struct/variant.
    Const,
}

impl CtorKind {
    pub fn from_variant(vdata: &VariantKind) -> Option<(CtorKind, NodeID)> {
        match *vdata {
            VariantKind::Tuple(node_id, _) => Some((CtorKind::Fn, node_id)),
            VariantKind::Unit(node_id) => Some((CtorKind::Const, node_id)),
            VariantKind::Struct(..) => None,
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum PrimaryType {
    Int(IntTy),
    UInt(UIntTy),
    Float(FloatTy),
    String,
    Bool,
    Rune,
}

impl PrimaryType {
    pub const ALL: [Self; 15] = [
        Self::Int(IntTy::I8),
        Self::Int(IntTy::I16),
        Self::Int(IntTy::I32),
        Self::Int(IntTy::I64),
        Self::Int(IntTy::ISize),
        Self::UInt(UIntTy::U8),
        Self::UInt(UIntTy::U16),
        Self::UInt(UIntTy::U32),
        Self::UInt(UIntTy::U64),
        Self::UInt(UIntTy::USize),
        Self::Float(FloatTy::F32),
        Self::Float(FloatTy::F64),
        Self::Bool,
        Self::Rune,
        Self::String,
    ];

    pub fn name_str(self) -> &'static str {
        match self {
            PrimaryType::Int(i) => i.name_str(),
            PrimaryType::UInt(u) => u.name_str(),
            PrimaryType::Float(f) => f.name_str(),
            PrimaryType::String => "string",
            PrimaryType::Bool => "bool",
            PrimaryType::Rune => "rune",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntTy {
    ISize,
    I8,
    I16,
    I32,
    I64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UIntTy {
    USize,
    U8,
    U16,
    U32,
    U64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FloatTy {
    F32,
    F64,
}
impl IntTy {
    pub fn name_str(&self) -> &'static str {
        match *self {
            IntTy::ISize => "isize",
            IntTy::I8 => "int8",
            IntTy::I16 => "int16",
            IntTy::I32 => "int32",
            IntTy::I64 => "int64",
        }
    }
}

impl UIntTy {
    pub fn name_str(&self) -> &'static str {
        match *self {
            UIntTy::USize => "usize",
            UIntTy::U8 => "uint8",
            UIntTy::U16 => "uint16",
            UIntTy::U32 => "uint32",
            UIntTy::U64 => "uint64",
        }
    }
}

impl FloatTy {
    pub fn name_str(self) -> &'static str {
        match self {
            FloatTy::F32 => "float",
            FloatTy::F64 => "double",
        }
    }
}

#[derive(Debug, Clone)]
pub struct PartialResolution {
    pub resolution: Resolution,
    pub unresolved_segments: usize,
}

impl PartialResolution {
    pub fn new(resolution: Resolution) -> Self {
        PartialResolution {
            resolution,
            unresolved_segments: 0,
        }
    }

    pub fn with_unresolved_segments(
        resolution: Resolution,
        mut unresolved_segments: usize,
    ) -> Self {
        if matches!(resolution, Resolution::Error) {
            unresolved_segments = 0
        }
        PartialResolution {
            resolution,
            unresolved_segments,
        }
    }

    #[inline]
    pub fn resolution(&self) -> Resolution {
        self.resolution.clone()
    }

    pub fn unresolved_segments(&self) -> usize {
        self.unresolved_segments
    }

    pub fn full_resolution(&self) -> Option<Resolution> {
        (self.unresolved_segments == 0).then_some(self.resolution.clone())
    }
}
