use crate::{
    ast::{self, Identifier, NodeID},
    diagnostics::{Diagnostic, DiagnosticLevel},
    hir::StdType,
    sema::models::{FloatTy, IntTy, UIntTy},
    span::{FileID, Span, Symbol},
    utils::intern::Interned,
};
use indexmap::IndexSet;
use rustc_hash::FxHashMap;
use std::cell::{Cell, RefCell};

pub use crate::span::PackageIndex;
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
    AssociatedOperator,
    AssociatedType,
    VariantConstructor(VariantCtorKind),
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
            DefinitionKind::Extension => "extension",
            DefinitionKind::TypeParameter => "type parameter",
            DefinitionKind::Field => "field",
            DefinitionKind::Variant => "variant",
            DefinitionKind::Export => "export",
            DefinitionKind::Constant => "constant",
            DefinitionKind::VariantConstructor(..) => "constructor",
            DefinitionKind::AssociatedType => "associated type",
            DefinitionKind::AssociatedFunction => "associated function",
            DefinitionKind::AssociatedConstant => "associated constant",
            DefinitionKind::ConstParameter => "const parameter",
            DefinitionKind::ModuleVariable => "variable",
            DefinitionKind::AssociatedOperator => "associated operator",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VariantCtorKind {
    Function,
    Constant,
}

impl VariantCtorKind {
    pub fn from_variant(vdata: &ast::VariantKind) -> VariantCtorKind {
        match *vdata {
            ast::VariantKind::Tuple(..) => VariantCtorKind::Function,
            ast::VariantKind::Unit => VariantCtorKind::Constant,
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

    pub fn is_local_to_index(&self, local_index: PackageIndex) -> bool {
        self.package_index == local_index
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

pub type ScopeTable<'arena> = FxHashMap<Symbol, NameEntry<'arena>>;

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
pub enum Resolution<LocalNode = ast::NodeID> {
    PrimaryType(PrimaryType),
    Definition(DefinitionID, DefinitionKind),
    SelfTypeAlias(DefinitionID),
    InterfaceSelfTypeParameter(DefinitionID),
    FunctionSet(Vec<DefinitionID>),
    LocalVariable(LocalNode),
    SelfConstructor(DefinitionID),
    Foundation(StdType),
    Error,
}

impl<LocalNode> Resolution<LocalNode> {
    pub fn description(&self) -> &'static str {
        match self {
            Resolution::Definition(_, k) => k.description(),
            Resolution::InterfaceSelfTypeParameter(_) => "self type",
            Resolution::SelfTypeAlias(_) => "self type",
            Resolution::LocalVariable(_) => "local variable",
            Resolution::FunctionSet(..) => "function set",
            Resolution::PrimaryType(_) => "primary type",
            Resolution::SelfConstructor(_) => "self constructor",
            Resolution::Error => "error",
            Resolution::Foundation(_) => "std type",
        }
    }

    pub fn definition_id(&self) -> Option<DefinitionID> {
        match self {
            Resolution::Definition(id, _) => Some(*id),
            Resolution::SelfTypeAlias(id)
            | Resolution::InterfaceSelfTypeParameter(id)
            | Resolution::SelfConstructor(id) => Some(*id),
            _ => None,
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

#[derive(Debug, Clone, Copy)]
pub struct UsageBinding {
    pub node_id: NodeID,
    pub source: Identifier,
    pub target: Identifier,
}

pub struct LexicalScope<'a> {
    pub source: LexicalScopeSource<'a>,
    pub table: FxHashMap<Symbol, Resolution>,
}

pub enum LexicalScopeBinding<'arena> {
    Declaration(Holder<'arena>),
    Resolution(Resolution),
}

impl<'a> LexicalScope<'a> {
    pub fn new(source: LexicalScopeSource<'a>) -> LexicalScope<'a> {
        LexicalScope {
            source,
            table: Default::default(),
        }
    }

    pub fn define(&mut self, name: Symbol, resolution: Resolution) {
        self.table.insert(name, resolution);
    }
}

pub enum LexicalScopeSource<'a> {
    Plain,
    #[allow(unused)]
    Definition(DefinitionID),
    Scoped(Scope<'a>),
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
    Expectation {
        expectation: ResolutionSource,
        provided: Resolution,
        span: Span,
    },
    UnknownSymbol(Identifier),
    AlreadyInScope(Identifier),
    AmbiguousUsage(Identifier),
    VariableNotBoundInPattern(BindingError, Span),
    IdentifierBoundMoreThanOnceInParameterList(Identifier),
    IdentifierBoundMoreThanOnceInSamePattern(Identifier),
    UnknownMember(Identifier),
    SpecializationDisallowed(Option<Resolution>, Span),
}

impl ResolutionError {
    pub fn diag(&self) -> Diagnostic {
        match self {
            ResolutionError::Expectation {
                expectation,
                provided,
                span,
            } => Diagnostic::error(
                format!(
                    "expected {}, but found {}",
                    expectation.expected(),
                    provided.description(),
                ),
                Some(*span),
            ),

            ResolutionError::UnknownSymbol(ident) => Diagnostic::error(
                format!("unknown symbol `{}`", ident.symbol),
                Some(ident.span),
            ),

            ResolutionError::AlreadyInScope(ident) => Diagnostic::error(
                format!("`{}` is already in scope", ident.symbol),
                Some(ident.span),
            ),

            ResolutionError::AmbiguousUsage(ident) => Diagnostic::error(
                format!("ambiguous usage of `{}`", ident.symbol),
                Some(ident.span),
            ),

            ResolutionError::VariableNotBoundInPattern(binding_err, span) => {
                let mut base = Diagnostic::error(
                    format!("variable not bound in pattern: {}", binding_err.name),
                    Some(*span),
                );

                for &sp in binding_err.target.iter() {
                    let msg = format!("pattern does not bind variable '{}'", binding_err.name);
                    base.children
                        .push(Diagnostic::new(msg, Some(sp), DiagnosticLevel::Warn));
                }

                base
            }

            ResolutionError::IdentifierBoundMoreThanOnceInParameterList(ident) => {
                Diagnostic::error(
                    format!(
                        "identifier `{}` bound more than once in parameter list",
                        ident.symbol
                    ),
                    Some(ident.span),
                )
            }

            ResolutionError::IdentifierBoundMoreThanOnceInSamePattern(ident) => Diagnostic::error(
                format!(
                    "identifier `{}` bound more than once in the same pattern",
                    ident.symbol
                ),
                Some(ident.span),
            ),

            ResolutionError::UnknownMember(ident) => Diagnostic::error(
                format!("unknown member `{}`", ident.symbol),
                Some(ident.span),
            ),

            ResolutionError::SpecializationDisallowed(resolution, span) => Diagnostic::error(
                format!(
                    "specialization is disallowed for {}",
                    resolution
                        .as_ref()
                        .map(|r| r.description())
                        .unwrap_or_default(),
                ),
                Some(*span),
            ),
        }
    }
}

#[derive(Debug, Clone)]
pub struct BindingError {
    pub name: Symbol,
    pub origin: IndexSet<Span>,
    pub target: IndexSet<Span>,
}

#[derive(Debug, Clone, Copy)]
pub enum ResolutionSource {
    Type,
    TypeArgument,
    ExtensionTarget,
    Interface,
    Module,
    MatchPatternUnit,
    MatchPatternTupleStruct,
}

impl ResolutionSource {
    pub fn namespace(&self) -> ScopeNamespace {
        match self {
            ResolutionSource::Type
            | ResolutionSource::TypeArgument
            | ResolutionSource::ExtensionTarget
            | ResolutionSource::Interface => ScopeNamespace::Type,
            ResolutionSource::MatchPatternUnit => ScopeNamespace::Value,
            ResolutionSource::MatchPatternTupleStruct => ScopeNamespace::Value,
            ResolutionSource::Module => ScopeNamespace::Type,
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
                            | DefinitionKind::TypeParameter
                            | DefinitionKind::TypeAlias
                            | DefinitionKind::AssociatedType
                    ) | Resolution::SelfTypeAlias(..)
                        | Resolution::InterfaceSelfTypeParameter(..)
                        | Resolution::PrimaryType(..)
                )
            }
            ResolutionSource::TypeArgument => {
                matches!(
                    res,
                    Resolution::Definition(
                        _,
                        DefinitionKind::Struct
                            | DefinitionKind::Enum
                            | DefinitionKind::TypeParameter
                            | DefinitionKind::TypeAlias
                            | DefinitionKind::AssociatedType
                            | DefinitionKind::ConstParameter
                    ) | Resolution::SelfTypeAlias(..)
                        | Resolution::InterfaceSelfTypeParameter(..)
                        | Resolution::PrimaryType(..)
                )
            }
            ResolutionSource::ExtensionTarget => {
                matches!(
                    res,
                    Resolution::Definition(
                        _,
                        DefinitionKind::Struct
                            | DefinitionKind::Enum
                            | DefinitionKind::Interface
                            | DefinitionKind::TypeAlias
                    ) | Resolution::PrimaryType(..)
                )
            }
            ResolutionSource::Interface => {
                matches!(res, Resolution::Definition(_, DefinitionKind::Interface))
            }
            ResolutionSource::MatchPatternUnit => matches!(
                res,
                Resolution::Definition(
                    _,
                    DefinitionKind::VariantConstructor(VariantCtorKind::Constant)
                )
            ),
            ResolutionSource::MatchPatternTupleStruct => matches!(
                res,
                Resolution::Definition(
                    _,
                    DefinitionKind::VariantConstructor(VariantCtorKind::Function)
                )
            ),
            ResolutionSource::Module => matches!(
                res,
                Resolution::Definition(_, DefinitionKind::Module | DefinitionKind::Namespace)
            ),
        }
    }

    pub fn expected(&self) -> String {
        match self {
            ResolutionSource::Type => "type".into(),
            ResolutionSource::TypeArgument => "type or const argument".into(),
            ResolutionSource::ExtensionTarget => "type or interface".into(),
            ResolutionSource::Interface => "interface".into(),
            ResolutionSource::MatchPatternUnit => "unit enum variant".into(),
            ResolutionSource::MatchPatternTupleStruct => "tuple enum variant".into(),
            ResolutionSource::Module => "module or namespace".into(),
        }
    }

    pub fn defer_to_type_checker(&self) -> bool {
        match self {
            ResolutionSource::Type => true,
            ResolutionSource::TypeArgument => true,
            ResolutionSource::ExtensionTarget => true,
            ResolutionSource::Interface => false,
            ResolutionSource::MatchPatternUnit => true,
            ResolutionSource::MatchPatternTupleStruct => true,
            ResolutionSource::Module => false,
        }
    }
}

#[derive(Debug)]
pub enum PathResult<'arena> {
    Scope(Scope<'arena>),
    Resolution(ResolutionState),
    Failed { error: ResolutionError },
}

#[derive(Debug, Clone)]
pub enum ResolutionState {
    Complete(Resolution),
    Partial {
        resolution: Resolution,
        unresolved_count: usize,
    },
}

#[derive(Debug, Clone)]
pub enum ExpressionResolutionState {
    Resolved(Resolution),
    DeferredAssociatedType,
    DeferredAssociatedValue,
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

/// A stable "type constructor" key used for extension blocks.
///
/// This is computed directly from HIR types (not full semantic `Ty` lowering), so it can stay
/// resilient as the surface type syntax grows.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeHead {
    Primary(PrimaryType),
    /// A nominal type identity (struct/interface/enum/etc).
    Nominal(DefinitionID),
    Reference(ast::Mutability),
    Pointer(ast::Mutability),
    GcPtr,
    Tuple(u16),
    Array,
}

impl TypeHead {
    pub fn format(self, gcx: crate::compile::context::Gcx) -> String {
        match self {
            TypeHead::Primary(p) => p.name_str().into(),
            TypeHead::Nominal(id) => gcx.definition_ident(id).symbol.as_str().into(),
            TypeHead::Reference(m) => format!("&{}_", m.display_str()),
            TypeHead::Pointer(m) => format!("*{}_", m.display_str()),
            TypeHead::GcPtr => "GcPtr".into(),
            TypeHead::Tuple(n) => format!("({})", ",".repeat(n as usize)),
            TypeHead::Array => "[_]".into(),
        }
    }
}

pub struct ResolutionOutput<'arena> {
    pub resolutions: FxHashMap<NodeID, ResolutionState>,
    pub node_to_definition: FxHashMap<NodeID, DefinitionID>,
    pub definition_to_kind: FxHashMap<DefinitionID, DefinitionKind>,
    pub definition_to_parent: FxHashMap<DefinitionID, DefinitionID>,
    pub definition_to_ident: FxHashMap<DefinitionID, Identifier>,
    pub definition_to_visibility: FxHashMap<DefinitionID, Visibility>,
    pub definition_scope_mapping: FxHashMap<DefinitionID, Scope<'arena>>,
    pub expression_resolutions: FxHashMap<NodeID, ExpressionResolutionState>,
    pub root_scope: Scope<'arena>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Visibility {
    Public,
    Private(DefinitionID),
    FilePrivate(FileID),
}
