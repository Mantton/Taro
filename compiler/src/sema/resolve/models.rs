use crate::{
    ast::{self, Identifier, NodeID},
    span::{FileID, Span},
    utils::intern::Interned,
};
use ecow::EcoString;
use index_vec::define_index_type;
use indexmap::IndexSet;
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
    Implementation,
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
            DefinitionKind::Import => "import",
            DefinitionKind::Implementation => "implementation",
            DefinitionKind::TypeParameter => "type parameter",
            DefinitionKind::Field => "field",
            DefinitionKind::Variant => "variant",
            DefinitionKind::Export => "export",
            DefinitionKind::Constant => "constant",
            DefinitionKind::Ctor(..) => "constructor",
            DefinitionKind::AssociatedType => "associated type",
            DefinitionKind::AssociatedFunction => "associated function",
            DefinitionKind::AssociatedConstant => "associated constant",
            DefinitionKind::ConstParameter => "const parameter",
            DefinitionKind::ModuleVariable => "variable",
            DefinitionKind::AssociatedInitializer => "associated init",
            DefinitionKind::EnumVariant => "enum variant",
        }
    }
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

impl<'a> ScopeData<'a> {
    pub fn resolution(&self) -> Option<Resolution> {
        match self.kind {
            ScopeKind::Block(..) => None,
            ScopeKind::File(..) => None,
            ScopeKind::Definition(id, kind) => Some(Resolution::Definition(id, kind)),
        }
    }
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
    PrimaryType(PrimaryType),
    Definition(DefinitionID, DefinitionKind),
    SelfTypeAlias(DefinitionID),
    InterfaceSelfTypeParameter(DefinitionID),
    FunctionSet(Vec<DefinitionID>),
    LocalVariable(NodeID),
    SelfConstructor(DefinitionID),
}

impl Resolution {
    pub fn description(&self) -> &'static str {
        match self {
            Resolution::Definition(_, k) => k.description(),
            Resolution::InterfaceSelfTypeParameter(_) => "self type",
            Resolution::SelfTypeAlias(_) => "self type",
            Resolution::LocalVariable(_) => "local variable",
            Resolution::FunctionSet(..) => "function set",
            Resolution::PrimaryType(_) => "primary type",
            Resolution::SelfConstructor(_) => "self constructor",
        }
    }
}

pub type UsageEntry<'arena> = Interned<'arena, UsageEntryData<'arena>>;

#[derive(Debug, Clone)]
pub struct UsageEntryData<'a> {
    pub span: Span,
    pub module_path: Vec<Identifier>,
    pub kind: UsageKind,
    pub is_import: bool,
    pub scope: Scope<'a>,
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
    pub fn scope(&self) -> Option<Scope<'a>> {
        match self {
            ResolvedValue::Scope(scope) => Some(*scope),
            ResolvedValue::Resolution(_) => None,
        }
    }

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

#[derive(Debug, Clone)]
pub enum ResolutionError {
    NotAModule,
    NotAType,
    NotAnInterface,
    UnknownSymbol,
    AlreadyInScope(Span),
    AmbiguousUsage,
    InconsistentBindingMode(EcoString, Span),
    VariableNotBoundInPattern(BindingError),
    IdentifierBoundMoreThanOnceInParameterList,
    IdentifierBoundMoreThanOnceInSamePattern,
    UnknownMember,
}

#[derive(Debug, Clone)]
pub struct BindingError {
    pub name: EcoString,
    pub origin: IndexSet<Span>,
    pub target: IndexSet<Span>,
}

#[derive(Debug)]
pub enum ResolutionSource {
    Type,
    Interface,
    Expression,
    MatchPatternUnit,
    MatchPatternTupleStruct,
    MatchPatternStruct,
}

impl ResolutionSource {
    pub fn namespace(&self) -> ScopeNamespace {
        match self {
            ResolutionSource::Type
            | ResolutionSource::Interface
            | ResolutionSource::MatchPatternStruct => ScopeNamespace::Type,
            ResolutionSource::Expression => ScopeNamespace::Value,
            ResolutionSource::MatchPatternUnit => ScopeNamespace::Value,
            ResolutionSource::MatchPatternTupleStruct => ScopeNamespace::Value,
        }
    }

    pub fn is_allowed(&self, res: &Resolution) -> bool {
        match self {
            ResolutionSource::Type => {
                matches!(
                    res,
                    Resolution::Definition(
                        _,
                        DefinitionKind::Struct
                            | DefinitionKind::Enum
                            | DefinitionKind::Interface
                            | DefinitionKind::TypeParameter
                            | DefinitionKind::TypeAlias
                            | DefinitionKind::AssociatedType
                    ) | Resolution::SelfTypeAlias(..)
                        | Resolution::InterfaceSelfTypeParameter(..)
                        | Resolution::PrimaryType(..)
                )
            }
            ResolutionSource::Interface => {
                matches!(res, Resolution::Definition(_, DefinitionKind::Interface))
            }
            ResolutionSource::Expression => matches!(
                res,
                Resolution::Definition(
                    _,
                    DefinitionKind::Function
                        | DefinitionKind::Struct
                        | DefinitionKind::Variant
                        | DefinitionKind::ConstParameter
                        | DefinitionKind::Ctor(..)
                ) | Resolution::LocalVariable(..)
                    | Resolution::FunctionSet(..)
                    | Resolution::SelfConstructor(..)
            ),

            ResolutionSource::MatchPatternUnit => matches!(
                res,
                Resolution::Definition(_, DefinitionKind::Ctor(_, CtorKind::Constant))
            ),
            ResolutionSource::MatchPatternTupleStruct => matches!(
                res,
                Resolution::Definition(_, DefinitionKind::Ctor(_, CtorKind::Function))
            ),
            ResolutionSource::MatchPatternStruct => {
                matches!(res, Resolution::Definition(_, DefinitionKind::EnumVariant))
            }
        }
    }

    pub fn expected(&self) -> String {
        match self {
            ResolutionSource::Type => "type".into(),
            ResolutionSource::Interface => "interface".into(),
            ResolutionSource::Expression => "value".into(),
            ResolutionSource::MatchPatternUnit => "unit enum variant".into(),
            ResolutionSource::MatchPatternTupleStruct => "tuple enum variant".into(),
            ResolutionSource::MatchPatternStruct => "strict enum variant".into(),
        }
    }

    pub fn defer_to_type_checker(&self) -> bool {
        match self {
            ResolutionSource::Type => true,
            ResolutionSource::Interface => false,
            ResolutionSource::Expression => true,
            ResolutionSource::MatchPatternUnit => true,
            ResolutionSource::MatchPatternStruct => true,
            ResolutionSource::MatchPatternTupleStruct => true,
        }
    }
}

#[derive(Debug)]
pub enum PathResult<'arena> {
    Scope(Scope<'arena>),
    Resolution(ResolutionState),
    Failed {
        segment: Identifier,
        is_last_segment: bool,
        error: ResolutionError,
    },
}

#[derive(Debug, Clone)]
pub enum ResolutionState {
    Complete(Resolution),
    Partial {
        resolution: Resolution,
        unresolved_count: usize,
    },
}

#[derive(Clone, Copy)]
pub enum ImplicitScope {
    Packages,                // dependencies + self
    StdPrelude,              // std prelude
    BuiltinFunctionsPrelude, // builtin prelude (functions)
    BuiltinTypesPrelude,     // builtin prelude (types)
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
