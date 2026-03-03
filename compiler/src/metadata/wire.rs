use crate::{
    PackageIndex, ast,
    compile::context::{GlobalContext, TypeDatabase},
    hir, mir,
    parse::IntegerTypeSuffix,
    sema::{
        models::{
            AdtDef, AdtKind, AliasDefinition, AliasKind, AssociatedTypeBinding,
            AssociatedTypeDefinition, CaptureKind, CapturedVar, ClosureCaptures, ClosureKind,
            ConformanceRecord, ConformanceRecordId, Const, ConstKind, ConstValue, Constraint,
            EnumDefinition, EnumVariant, EnumVariantField, EnumVariantKind, FloatTy,
            GenericArgument, GenericParameter, GenericParameterDefinition,
            GenericParameterDefinitionKind, Generics, InferTy, IntTy, InterfaceConstantRequirement,
            InterfaceDefinition, InterfaceMethodRequirement, InterfaceReference,
            InterfaceRequirements, LabeledFunctionParameter, LabeledFunctionSignature,
            PackageAliasTable, StructDefinition, StructField, SyntheticDefinition,
            SyntheticMethodKind, Ty, TyKind, UIntTy,
        },
        resolve::models::{
            DefinitionID, DefinitionIndex, DefinitionKind, ExpressionResolutionState, PrimaryType,
            Resolution, ResolutionOutput, ResolutionState, ScopeData, ScopeKind, TypeHead,
            UsageEntryData, UsageKind, VariantCtorKind, Visibility,
        },
        std_items::{StdItemEntry, StdItemRegistry},
        tycheck::derive::SyntheticMethodInfo,
    },
    span::{FileID, Identifier, Position, Span, Spanned, Symbol},
    specialize::{Instance, InstanceKind, VirtualInstance},
    utils::intern::Interned,
};
use ena::unify::UnifyKey;
use indexmap::IndexSet;
use rustc_hash::{FxBuildHasher, FxHashMap};
use serde::{Deserialize, Serialize};
use std::cell::Cell;

#[derive(Debug, Clone)]
pub struct WireDecodeError {
    message: String,
}

impl WireDecodeError {
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl std::fmt::Display for WireDecodeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.message.fmt(f)
    }
}

impl std::error::Error for WireDecodeError {}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FileMappingWire {
    pub old_file_id: u32,
    pub path: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MetadataPayloadWire {
    pub file_table: Vec<FileMappingWire>,
    pub semantic_payload: Option<Vec<u8>>,
    pub mir_payload: Option<Vec<u8>>,
    pub std_items: Option<StdItemRegistryWire>,
    pub synthetic_definitions: Vec<SyntheticDefinitionWire>,
    pub emitted_instances: Vec<InstanceWire>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SemanticPayloadWire {
    pub package_identifier: String,
    pub package_index: u32,
    pub symbol_table: SymbolTableWire,
    pub resolution: ResolutionOutputWire,
    pub type_db: TypeDatabaseWire,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct SymbolIdWire(pub u32);

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SymbolTableWire {
    pub symbols: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DefIdWire {
    pub package: u32,
    pub index: u32,
}

#[derive(Debug, Clone, Copy)]
pub struct FileRemap<'a> {
    pub old_to_new: &'a FxHashMap<u32, FileID>,
}

#[derive(Debug, Default)]
pub struct SymbolTableBuilder {
    symbols: IndexSet<String, FxBuildHasher>,
}

impl SymbolTableBuilder {
    pub fn intern_str(&mut self, symbol: &str) -> SymbolIdWire {
        if let Some((id, _)) = self.symbols.get_full(symbol) {
            return SymbolIdWire(id as u32);
        }
        let (id, _inserted) = self.symbols.insert_full(symbol.to_string());
        SymbolIdWire(id as u32)
    }

    pub fn intern_symbol(&mut self, symbol: Symbol) -> SymbolIdWire {
        self.intern_str(symbol.as_str())
    }

    pub fn finish(self) -> SymbolTableWire {
        SymbolTableWire {
            symbols: self.symbols.into_iter().collect(),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct SymbolTableRef<'a> {
    table: &'a SymbolTableWire,
    invalid_symbol_id: &'a Cell<Option<u32>>,
}

impl<'a> SymbolTableRef<'a> {
    pub fn new(table: &'a SymbolTableWire, invalid_symbol_id: &'a Cell<Option<u32>>) -> Self {
        Self {
            table,
            invalid_symbol_id,
        }
    }

    pub fn resolve_str(self, id: SymbolIdWire) -> &'a str {
        if let Some(value) = self.table.symbols.get(id.0 as usize).map(String::as_str) {
            return value;
        }

        if self.invalid_symbol_id.get().is_none() {
            self.invalid_symbol_id.set(Some(id.0));
        }

        "<invalid-symbol-id>"
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SpanWire {
    pub file: u32,
    pub start_line: u32,
    pub start_offset: u32,
    pub end_line: u32,
    pub end_offset: u32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct IdentifierWire {
    pub symbol: SymbolIdWire,
    pub span: SpanWire,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DefinitionKindWire {
    Module,
    Struct,
    Enum,
    Function,
    Constant,
    ModuleVariable,
    Interface,
    TypeAlias,
    Namespace,
    Impl,
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
    VariantConstructor(VariantCtorKindWire),
    OpaqueType,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum VariantCtorKindWire {
    Function,
    Constant,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum PrimaryTypeWire {
    Int(IntTyWire),
    UInt(UIntTyWire),
    Float(FloatTyWire),
    String,
    Bool,
    Rune,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ResolutionWire {
    PrimaryType(PrimaryTypeWire),
    Definition(DefIdWire, DefinitionKindWire),
    SelfTypeAlias(DefIdWire),
    InterfaceSelfTypeParameter(DefIdWire),
    FunctionSet(Vec<DefIdWire>),
    LocalVariable(u32),
    SelfConstructor(DefIdWire),
    StdItem(StdItemWire),
    Error,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ResolutionStateWire {
    Complete(ResolutionWire),
    Partial {
        resolution: ResolutionWire,
        unresolved_count: u32,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ExpressionResolutionStateWire {
    Resolved(ResolutionWire),
    DeferredAssociatedType,
    DeferredAssociatedValue,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum VisibilityWire {
    Public,
    Private(DefIdWire),
    FilePrivate(u32),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ScopeKindWire {
    Block(u32),
    File(u32),
    Definition(DefIdWire, DefinitionKindWire),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NameEntryWire {
    pub symbol: SymbolIdWire,
    pub ty: Option<ResolutionWire>,
    pub values: Vec<ResolutionWire>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ScopeWire {
    pub parent: Option<u32>,
    pub kind: ScopeKindWire,
    pub entries: Vec<NameEntryWire>,
    pub glob_imports: Vec<GlobUsageWire>,
    pub glob_exports: Vec<GlobUsageWire>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GlobUsageWire {
    pub id: u32,
    pub span: SpanWire,
    pub module_scope: Option<u32>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResolutionOutputWire {
    pub resolutions: Vec<(u32, ResolutionStateWire)>,
    pub node_to_definition: Vec<(u32, DefIdWire)>,
    pub definition_to_kind: Vec<(DefIdWire, DefinitionKindWire)>,
    pub definition_to_parent: Vec<(DefIdWire, DefIdWire)>,
    pub definition_to_ident: Vec<(DefIdWire, IdentifierWire)>,
    pub definition_to_visibility: Vec<(DefIdWire, VisibilityWire)>,
    pub file_scope_mapping: Vec<(u32, u32)>,
    pub definition_scope_mapping: Vec<(DefIdWire, u32)>,
    pub expression_resolutions: Vec<(u32, ExpressionResolutionStateWire)>,
    pub scopes: Vec<ScopeWire>,
    pub root_scope: u32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TypeDatabaseWire {
    pub def_to_ty: Vec<(DefIdWire, TyWire)>,
    pub def_to_const: Vec<(DefIdWire, ConstWire)>,
    pub def_to_fn_sig: Vec<(DefIdWire, LabeledFunctionSignatureWire)>,
    pub def_to_struct_def: Vec<(DefIdWire, StructDefinitionWire)>,
    pub def_to_enum_def: Vec<(DefIdWire, EnumDefinitionWire)>,
    pub def_to_constraints: Vec<(DefIdWire, Vec<ConstraintSpannedWire>)>,
    pub def_to_canon_constraints: Vec<(DefIdWire, Vec<ConstraintSpannedWire>)>,
    pub impl_to_type_head: Vec<(DefIdWire, TypeHeadWire)>,
    pub impl_to_target_ty: Vec<(DefIdWire, TyWire)>,
    pub type_head_to_impls: Vec<(TypeHeadWire, Vec<DefIdWire>)>,
    pub type_head_to_members: Vec<(TypeHeadWire, TypeMemberIndexWire)>,
    pub def_to_generics: Vec<(DefIdWire, GenericsWire)>,
    pub generic_type_defaults: Vec<(DefIdWire, TyWire)>,
    pub generic_const_param_tys: Vec<(DefIdWire, TyWire)>,
    pub generic_const_defaults: Vec<(DefIdWire, ConstWire)>,
    pub def_to_attributes: Vec<(DefIdWire, Vec<AttributeWire>)>,
    pub def_to_iface_def: Vec<(DefIdWire, InterfaceDefinitionWire)>,
    pub interface_to_supers: Vec<(DefIdWire, Vec<DefIdWire>)>,
    pub conformance_records: Vec<(ConformanceRecordIdWire, ConformanceRecordWire)>,
    pub conformance_by_interface_head:
        Vec<((DefIdWire, TypeHeadWire), Vec<ConformanceRecordIdWire>)>,
    pub conformance_by_interface: Vec<(DefIdWire, Vec<ConformanceRecordIdWire>)>,
    pub conformance_by_head: Vec<(TypeHeadWire, Vec<ConformanceRecordIdWire>)>,
    pub conformance_by_extension: Vec<(DefIdWire, Vec<ConformanceRecordIdWire>)>,
    pub next_conformance_record_index: u32,
    pub interface_requirements: Vec<(DefIdWire, InterfaceRequirementsWire)>,
    pub alias_table: PackageAliasTableWire,
    pub resolved_aliases: Vec<(DefIdWire, TyWire)>,
    pub def_to_escape_summary: Vec<(DefIdWire, EscapeSummaryWire)>,
    pub closure_captures: Vec<(DefIdWire, ClosureCapturesWire)>,
    pub synthetic_methods: Vec<((TypeHeadWire, DefIdWire), SyntheticMethodInfoWire)>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConstraintSpannedWire {
    pub value: ConstraintWire,
    pub span: SpanWire,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ConstraintWire {
    TypeEquality(TyWire, TyWire),
    Bound {
        ty: TyWire,
        interface: InterfaceReferenceWire,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TyWire {
    pub kind: TyKindWire,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TyKindWire {
    Array {
        element: Box<TyWire>,
        len: Box<ConstWire>,
    },
    Bool,
    Rune,
    String,
    Int(IntTyWire),
    UInt(UIntTyWire),
    Float(FloatTyWire),
    Adt(AdtDefWire, Vec<GenericArgumentWire>),
    Pointer(Box<TyWire>, MutabilityWire),
    Reference(Box<TyWire>, MutabilityWire),
    Tuple(Vec<TyWire>),
    FnPointer {
        inputs: Vec<TyWire>,
        output: Box<TyWire>,
    },
    BoxedExistential {
        interfaces: Vec<InterfaceReferenceWire>,
    },
    Alias {
        kind: AliasKindWire,
        def_id: DefIdWire,
        args: Vec<GenericArgumentWire>,
    },
    Infer(InferTyWire),
    Parameter(GenericParameterWire),
    Closure {
        closure_def_id: DefIdWire,
        captured_generics: Vec<GenericArgumentWire>,
        inputs: Vec<TyWire>,
        output: Box<TyWire>,
        kind: ClosureKindWire,
    },
    Opaque(DefIdWire),
    Error,
    Never,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum MutabilityWire {
    Mutable,
    Immutable,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum IntTyWire {
    ISize,
    I8,
    I16,
    I32,
    I64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum UIntTyWire {
    USize,
    U8,
    U16,
    U32,
    U64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum FloatTyWire {
    F32,
    F64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AdtDefWire {
    pub kind: AdtKindWire,
    pub id: DefIdWire,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AdtKindWire {
    Struct,
    Enum,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AliasKindWire {
    Inherent,
    Weak,
    Projection,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum InferTyWire {
    TyVar(u32),
    IntVar(u32),
    FloatVar(u32),
    NilVar(u32),
    FreshTy(u32),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GenericParameterWire {
    pub index: u32,
    pub name: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConstWire {
    pub ty: TyWire,
    pub kind: ConstKindWire,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ConstKindWire {
    Value(ConstValueWire),
    Param(GenericParameterWire),
    Infer(u32),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ConstValueWire {
    Integer(i128),
    Bool(bool),
    Rune(char),
    String(String),
    Float(f64),
    Unit,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum GenericArgumentWire {
    Type(TyWire),
    Const(ConstWire),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StructFieldWire {
    pub name: SymbolIdWire,
    pub ty: TyWire,
    pub mutability: MutabilityWire,
    pub def_id: DefIdWire,
    pub visibility: VisibilityWire,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StructDefinitionWire {
    pub adt_def: AdtDefWire,
    pub fields: Vec<StructFieldWire>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EnumVariantFieldWire {
    pub label: Option<SymbolIdWire>,
    pub ty: TyWire,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum EnumVariantKindWire {
    Unit,
    Tuple(Vec<EnumVariantFieldWire>),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EnumVariantWire {
    pub name: SymbolIdWire,
    pub def_id: DefIdWire,
    pub ctor_def_id: DefIdWire,
    pub kind: EnumVariantKindWire,
    pub discriminant: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EnumDefinitionWire {
    pub adt_def: AdtDefWire,
    pub variants: Vec<EnumVariantWire>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LabeledFunctionSignatureWire {
    pub inputs: Vec<LabeledFunctionParameterWire>,
    pub output: TyWire,
    pub is_variadic: bool,
    pub abi: Option<AbiWire>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LabeledFunctionParameterWire {
    pub label: Option<String>,
    pub name: String,
    pub ty: TyWire,
    pub default_provider: Option<DefIdWire>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AbiWire {
    C,
    Runtime,
    Intrinsic,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GenericsWire {
    pub parameters: Vec<GenericParameterDefinitionWire>,
    pub has_self: bool,
    pub parent: Option<DefIdWire>,
    pub parent_count: u32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GenericParameterDefinitionWire {
    pub name: String,
    pub id: DefIdWire,
    pub index: u32,
    pub kind: GenericParameterDefinitionKindWire,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum GenericParameterDefinitionKindWire {
    Type { has_default: bool },
    Const { has_default: bool },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InterfaceDefinitionWire {
    pub id: DefIdWire,
    pub superfaces: Vec<InterfaceReferenceSpannedWire>,
    pub assoc_types: Vec<(SymbolIdWire, DefIdWire)>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InterfaceReferenceSpannedWire {
    pub value: InterfaceReferenceWire,
    pub span: SpanWire,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InterfaceRequirementsWire {
    pub methods: Vec<InterfaceMethodRequirementWire>,
    pub types: Vec<AssociatedTypeDefinitionWire>,
    pub constants: Vec<InterfaceConstantRequirementWire>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InterfaceMethodRequirementWire {
    pub id: DefIdWire,
    pub name: SymbolIdWire,
    pub signature: LabeledFunctionSignatureWire,
    pub has_self: bool,
    pub is_required: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InterfaceConstantRequirementWire {
    pub id: DefIdWire,
    pub name: SymbolIdWire,
    pub ty: TyWire,
    pub default: Option<ConstWire>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InterfaceReferenceWire {
    pub id: DefIdWire,
    pub arguments: Vec<GenericArgumentWire>,
    pub bindings: Vec<AssociatedTypeBindingWire>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AssociatedTypeBindingWire {
    pub name: String,
    pub ty: TyWire,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AssociatedTypeDefinitionWire {
    pub id: DefIdWire,
    pub name: SymbolIdWire,
    pub default_type: Option<TyWire>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConformanceRecordWire {
    pub target: TypeHeadWire,
    pub interface: InterfaceReferenceWire,
    pub extension: DefIdWire,
    pub location: SpanWire,
    pub is_conditional: bool,
    pub is_inline: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConformanceRecordIdWire {
    pub package: u32,
    pub index: u32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TypeHeadWire {
    Primary(PrimaryTypeWire),
    Nominal(DefIdWire),
    Closure(DefIdWire),
    Reference(MutabilityWire),
    Pointer(MutabilityWire),
    Tuple(u16),
    Array,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TypeMemberIndexWire {
    pub inherent_static: Vec<(SymbolIdWire, MemberSetWire)>,
    pub inherent_instance: Vec<(SymbolIdWire, MemberSetWire)>,
    pub trait_methods: Vec<((DefIdWire, SymbolIdWire), MemberSetWire)>,
    pub trait_methods_by_name: Vec<(SymbolIdWire, Vec<DefIdWire>)>,
    pub operators: Vec<(OperatorKindWire, MemberSetWire)>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MemberSetWire {
    pub members: Vec<DefIdWire>,
    pub fingerprints: Vec<(u64, DefIdWire)>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum OperatorKindWire {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Eq,
    Ne,
    Gt,
    Lt,
    Ge,
    Le,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    BitNot,
    Neg,
    Not,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PackageAliasTableWire {
    pub aliases: Vec<(DefIdWire, AliasDefinitionWire)>,
    pub by_type: Vec<(TypeHeadWire, AliasBucketWire)>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AliasBucketWire {
    pub aliases: Vec<(SymbolIdWire, Vec<(DefIdWire, SpanWire)>)>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AliasDefinitionWire {
    pub id: DefIdWire,
    pub name: SymbolIdWire,
    pub kind: AliasKindWire,
    pub span: SpanWire,
    pub extension_id: Option<DefIdWire>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EscapeSummaryWire {
    pub params: Vec<ParamEscapeInfoWire>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ParamEscapeInfoWire {
    pub leaks_to_heap: bool,
    pub flows_to_return: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ClosureCapturesWire {
    pub captures: Vec<CapturedVarWire>,
    pub kind: ClosureKindWire,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CapturedVarWire {
    pub source_id: u32,
    pub name: SymbolIdWire,
    pub ty: TyWire,
    pub capture_kind: CaptureKindWire,
    pub field_index: u32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum CaptureKindWire {
    ByCopy,
    ByRef { mutable: bool },
    ByMove,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ClosureKindWire {
    Fn,
    FnMut,
    FnOnce,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SyntheticMethodInfoWire {
    pub kind: SyntheticMethodKindWire,
    pub self_ty: TyWire,
    pub interface_id: DefIdWire,
    pub interface_args: Vec<GenericArgumentWire>,
    pub interface_bindings: Vec<AssociatedTypeBindingWire>,
    pub method_id: DefIdWire,
    pub method_name: SymbolIdWire,
    pub syn_id: Option<DefIdWire>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SyntheticMethodKindWire {
    CopyClone,
    MemberwiseClone,
    MemberwiseHash,
    MemberwiseEquality,
    ClosureCall,
    ClosureCallMut,
    ClosureCallOnce,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AttributeWire {
    pub identifier: IdentifierWire,
    pub args: Option<AttributeArgsWire>,
    pub span: SpanWire,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AttributeArgsWire {
    pub items: Vec<AttributeArgWire>,
    pub span: SpanWire,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AttributeArgWire {
    KeyValue {
        key: IdentifierWire,
        value: LiteralWire,
        span: SpanWire,
    },
    Flag {
        key: IdentifierWire,
        span: SpanWire,
    },
    Literal {
        value: LiteralWire,
        span: SpanWire,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum LiteralWire {
    Bool(bool),
    Rune(char),
    String(String),
    Integer {
        value: u64,
        suffix: Option<IntegerTypeSuffixWire>,
    },
    Float(f64),
    Nil,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum IntegerTypeSuffixWire {
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StdItemRegistryWire {
    pub entries: Vec<(StdItemWire, StdItemEntryWire)>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StdItemEntryWire {
    pub def_id: DefIdWire,
    pub def_kind: DefinitionKindWire,
    pub span: SpanWire,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum StdItemWire {
    Optional,
    List,
    Set,
    Dictionary,
    Range,
    ClosedRange,
    Copy,
    Clone,
    Hashable,
    Equatable,
    Iterator,
    Iterable,
    Fn,
    FnMut,
    FnOnce,
    Tuple,
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Neg,
    Not,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    BitNot,
    PartialEq,
    PartialOrd,
    OptionalSomeVariant,
    OptionalSomeCtor,
    OptionalNoneVariant,
    OptionalNoneCtor,
    Make,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SyntheticDefinitionWire {
    pub id: DefIdWire,
    pub name: String,
    pub generics: GenericsWire,
    pub signature: LabeledFunctionSignatureWire,
    pub span: SpanWire,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InstanceWire {
    pub kind: InstanceKindWire,
    pub args: Vec<GenericArgumentWire>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum InstanceKindWire {
    Item(DefIdWire),
    Virtual(VirtualInstanceWire),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VirtualInstanceWire {
    pub method_id: DefIdWire,
    pub method_interface: DefIdWire,
    pub slot: u32,
    pub table_index: u32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MirPackageWire {
    pub functions: Vec<(DefIdWire, BodyWire)>,
    pub entry: Option<DefIdWire>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BodyWire {
    pub owner: DefIdWire,
    pub locals: Vec<LocalDeclWire>,
    pub basic_blocks: Vec<BasicBlockDataWire>,
    pub start_block: u32,
    pub return_local: u32,
    pub escape_locals: Vec<bool>,
    pub phase: MirPhaseWire,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LocalDeclWire {
    pub ty: TyWire,
    pub kind: LocalKindWire,
    pub mutable: bool,
    pub name: Option<String>,
    pub span: SpanWire,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum LocalKindWire {
    Param,
    User,
    Temp,
    Return,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BasicBlockDataWire {
    pub note: Option<String>,
    pub statements: Vec<StatementWire>,
    pub terminator: Option<TerminatorWire>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StatementWire {
    pub kind: StatementKindWire,
    pub span: SpanWire,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum StatementKindWire {
    Assign(PlaceWire, RvalueWire),
    GcSafepoint,
    Nop,
    SetDiscriminant {
        place: PlaceWire,
        variant_index: u32,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TerminatorWire {
    pub kind: TerminatorKindWire,
    pub span: SpanWire,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TerminatorKindWire {
    Goto {
        target: u32,
    },
    UnresolvedGoto,
    SwitchInt {
        discr: OperandWire,
        targets: Vec<(u128, u32)>,
        otherwise: u32,
    },
    Return,
    ResumeUnwind,
    Unreachable,
    Call {
        func: OperandWire,
        args: Vec<OperandWire>,
        destination: PlaceWire,
        target: u32,
        unwind: CallUnwindActionWire,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum CallUnwindActionWire {
    Cleanup(u32),
    Terminate,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PlaceWire {
    pub local: u32,
    pub projection: Vec<PlaceElemWire>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum PlaceElemWire {
    Deref,
    Field(u32, TyWire),
    VariantDowncast { name: String, index: u32 },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum OperandWire {
    Copy(PlaceWire),
    Move(PlaceWire),
    Constant(ConstantWire),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConstantWire {
    pub ty: TyWire,
    pub value: ConstantKindWire,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ConstantKindWire {
    Bool(bool),
    Rune(char),
    String(String),
    Integer(u64),
    Float(f64),
    Unit,
    Function(DefIdWire, Vec<GenericArgumentWire>, TyWire),
    ConstParam(GenericParameterWire),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RvalueWire {
    Use(OperandWire),
    UnaryOp {
        op: UnaryOperatorWire,
        operand: OperandWire,
    },
    BinaryOp {
        op: BinaryOperatorWire,
        lhs: OperandWire,
        rhs: OperandWire,
    },
    Cast {
        operand: OperandWire,
        ty: TyWire,
        kind: CastKindWire,
    },
    Ref {
        mutable: bool,
        place: PlaceWire,
    },
    Discriminant {
        place: PlaceWire,
    },
    Alloc {
        ty: TyWire,
    },
    Aggregate {
        kind: AggregateKindWire,
        fields: Vec<OperandWire>,
    },
    Repeat {
        operand: OperandWire,
        count: u32,
        element: TyWire,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum CastKindWire {
    Numeric,
    BoxExistential,
    ExistentialUpcast,
    ExistentialTypeIs { target: TyWire },
    ExistentialTryCast { target: TyWire },
    Pointer,
    ClosureToFnPointer,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AggregateKindWire {
    Tuple,
    Adt {
        def_id: DefIdWire,
        variant_index: Option<u32>,
        generic_args: Vec<GenericArgumentWire>,
    },
    Array {
        len: u32,
        element: TyWire,
    },
    Closure {
        def_id: DefIdWire,
        captured_generics: Vec<GenericArgumentWire>,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum UnaryOperatorWire {
    LogicalNot,
    Negate,
    BitwiseNot,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum BinaryOperatorWire {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    BitAnd,
    BitOr,
    BitXor,
    BitShl,
    BitShr,
    Eql,
    Lt,
    Gt,
    Leq,
    Geq,
    Neq,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum MirPhaseWire {
    Built,
    CfgClean,
    Lowered,
}

pub fn file_table_from_dcx(gcx: GlobalContext<'_>) -> Vec<FileMappingWire> {
    gcx.dcx
        .all_file_mappings()
        .into_iter()
        .map(|(id, path)| FileMappingWire {
            old_file_id: id.raw(),
            path: path.to_string_lossy().into_owned(),
        })
        .collect()
}

pub fn build_file_remap(
    gcx: GlobalContext<'_>,
    file_table: &[FileMappingWire],
) -> FxHashMap<u32, FileID> {
    let mut map = FxHashMap::default();
    for entry in file_table {
        let new_id = gcx
            .dcx
            .add_file_mapping(std::path::PathBuf::from(&entry.path));
        map.insert(entry.old_file_id, new_id);
    }
    map
}

#[inline]
pub fn def_to_wire(id: DefinitionID) -> DefIdWire {
    DefIdWire {
        package: id.package().raw(),
        index: id.index().index() as u32,
    }
}

#[inline]
pub fn def_from_wire(w: &DefIdWire) -> DefinitionID {
    DefinitionID::new(
        PackageIndex::new(w.package as usize),
        DefinitionIndex::from_raw(w.index),
    )
}

#[inline]
pub fn span_to_wire(span: Span) -> SpanWire {
    SpanWire {
        file: span.file.raw(),
        start_line: span.start.line as u32,
        start_offset: span.start.offset as u32,
        end_line: span.end.line as u32,
        end_offset: span.end.offset as u32,
    }
}

#[inline]
pub fn span_from_wire(w: &SpanWire, remap: FileRemap<'_>) -> Span {
    let file = remap
        .old_to_new
        .get(&w.file)
        .copied()
        .unwrap_or_else(|| FileID::from_raw(0));
    Span {
        file,
        start: Position {
            line: w.start_line as usize,
            offset: w.start_offset as usize,
        },
        end: Position {
            line: w.end_line as usize,
            offset: w.end_offset as usize,
        },
    }
}

#[inline]
pub fn identifier_to_wire(id: Identifier, symbols: &mut SymbolTableBuilder) -> IdentifierWire {
    IdentifierWire {
        symbol: symbols.intern_symbol(id.symbol),
        span: span_to_wire(id.span),
    }
}

#[inline]
pub fn identifier_from_wire(
    w: &IdentifierWire,
    remap: FileRemap<'_>,
    symbols: SymbolTableRef<'_>,
) -> Identifier {
    Identifier {
        symbol: Symbol::new(symbols.resolve_str(w.symbol)),
        span: span_from_wire(&w.span, remap),
    }
}

#[inline]
pub fn mutability_to_wire(v: hir::Mutability) -> MutabilityWire {
    match v {
        hir::Mutability::Mutable => MutabilityWire::Mutable,
        hir::Mutability::Immutable => MutabilityWire::Immutable,
    }
}

#[inline]
pub fn mutability_from_wire(v: &MutabilityWire) -> hir::Mutability {
    match v {
        MutabilityWire::Mutable => hir::Mutability::Mutable,
        MutabilityWire::Immutable => hir::Mutability::Immutable,
    }
}

#[inline]
pub fn int_ty_to_wire(v: IntTy) -> IntTyWire {
    match v {
        IntTy::ISize => IntTyWire::ISize,
        IntTy::I8 => IntTyWire::I8,
        IntTy::I16 => IntTyWire::I16,
        IntTy::I32 => IntTyWire::I32,
        IntTy::I64 => IntTyWire::I64,
    }
}

#[inline]
pub fn int_ty_from_wire(v: &IntTyWire) -> IntTy {
    match v {
        IntTyWire::ISize => IntTy::ISize,
        IntTyWire::I8 => IntTy::I8,
        IntTyWire::I16 => IntTy::I16,
        IntTyWire::I32 => IntTy::I32,
        IntTyWire::I64 => IntTy::I64,
    }
}

#[inline]
pub fn uint_ty_to_wire(v: UIntTy) -> UIntTyWire {
    match v {
        UIntTy::USize => UIntTyWire::USize,
        UIntTy::U8 => UIntTyWire::U8,
        UIntTy::U16 => UIntTyWire::U16,
        UIntTy::U32 => UIntTyWire::U32,
        UIntTy::U64 => UIntTyWire::U64,
    }
}

#[inline]
pub fn uint_ty_from_wire(v: &UIntTyWire) -> UIntTy {
    match v {
        UIntTyWire::USize => UIntTy::USize,
        UIntTyWire::U8 => UIntTy::U8,
        UIntTyWire::U16 => UIntTy::U16,
        UIntTyWire::U32 => UIntTy::U32,
        UIntTyWire::U64 => UIntTy::U64,
    }
}

#[inline]
pub fn float_ty_to_wire(v: FloatTy) -> FloatTyWire {
    match v {
        FloatTy::F32 => FloatTyWire::F32,
        FloatTy::F64 => FloatTyWire::F64,
    }
}

#[inline]
pub fn float_ty_from_wire(v: &FloatTyWire) -> FloatTy {
    match v {
        FloatTyWire::F32 => FloatTy::F32,
        FloatTyWire::F64 => FloatTy::F64,
    }
}

#[inline]
pub fn primary_type_to_wire(v: PrimaryType) -> PrimaryTypeWire {
    match v {
        PrimaryType::Int(v) => PrimaryTypeWire::Int(int_ty_to_wire(v)),
        PrimaryType::UInt(v) => PrimaryTypeWire::UInt(uint_ty_to_wire(v)),
        PrimaryType::Float(v) => PrimaryTypeWire::Float(float_ty_to_wire(v)),
        PrimaryType::String => PrimaryTypeWire::String,
        PrimaryType::Bool => PrimaryTypeWire::Bool,
        PrimaryType::Rune => PrimaryTypeWire::Rune,
    }
}

#[inline]
pub fn primary_type_from_wire(v: &PrimaryTypeWire) -> PrimaryType {
    match v {
        PrimaryTypeWire::Int(v) => PrimaryType::Int(int_ty_from_wire(v)),
        PrimaryTypeWire::UInt(v) => PrimaryType::UInt(uint_ty_from_wire(v)),
        PrimaryTypeWire::Float(v) => PrimaryType::Float(float_ty_from_wire(v)),
        PrimaryTypeWire::String => PrimaryType::String,
        PrimaryTypeWire::Bool => PrimaryType::Bool,
        PrimaryTypeWire::Rune => PrimaryType::Rune,
    }
}

#[inline]
pub fn variant_ctor_kind_to_wire(v: VariantCtorKind) -> VariantCtorKindWire {
    match v {
        VariantCtorKind::Function => VariantCtorKindWire::Function,
        VariantCtorKind::Constant => VariantCtorKindWire::Constant,
    }
}

#[inline]
pub fn variant_ctor_kind_from_wire(v: &VariantCtorKindWire) -> VariantCtorKind {
    match v {
        VariantCtorKindWire::Function => VariantCtorKind::Function,
        VariantCtorKindWire::Constant => VariantCtorKind::Constant,
    }
}

#[inline]
pub fn definition_kind_to_wire(v: DefinitionKind) -> DefinitionKindWire {
    match v {
        DefinitionKind::Module => DefinitionKindWire::Module,
        DefinitionKind::Struct => DefinitionKindWire::Struct,
        DefinitionKind::Enum => DefinitionKindWire::Enum,
        DefinitionKind::Function => DefinitionKindWire::Function,
        DefinitionKind::Constant => DefinitionKindWire::Constant,
        DefinitionKind::ModuleVariable => DefinitionKindWire::ModuleVariable,
        DefinitionKind::Interface => DefinitionKindWire::Interface,
        DefinitionKind::TypeAlias => DefinitionKindWire::TypeAlias,
        DefinitionKind::Namespace => DefinitionKindWire::Namespace,
        DefinitionKind::Impl => DefinitionKindWire::Impl,
        DefinitionKind::Import => DefinitionKindWire::Import,
        DefinitionKind::Export => DefinitionKindWire::Export,
        DefinitionKind::TypeParameter => DefinitionKindWire::TypeParameter,
        DefinitionKind::ConstParameter => DefinitionKindWire::ConstParameter,
        DefinitionKind::Field => DefinitionKindWire::Field,
        DefinitionKind::Variant => DefinitionKindWire::Variant,
        DefinitionKind::AssociatedFunction => DefinitionKindWire::AssociatedFunction,
        DefinitionKind::AssociatedConstant => DefinitionKindWire::AssociatedConstant,
        DefinitionKind::AssociatedOperator => DefinitionKindWire::AssociatedOperator,
        DefinitionKind::AssociatedType => DefinitionKindWire::AssociatedType,
        DefinitionKind::VariantConstructor(v) => {
            DefinitionKindWire::VariantConstructor(variant_ctor_kind_to_wire(v))
        }
        DefinitionKind::OpaqueType => DefinitionKindWire::OpaqueType,
    }
}

#[inline]
pub fn definition_kind_from_wire(v: &DefinitionKindWire) -> DefinitionKind {
    match v {
        DefinitionKindWire::Module => DefinitionKind::Module,
        DefinitionKindWire::Struct => DefinitionKind::Struct,
        DefinitionKindWire::Enum => DefinitionKind::Enum,
        DefinitionKindWire::Function => DefinitionKind::Function,
        DefinitionKindWire::Constant => DefinitionKind::Constant,
        DefinitionKindWire::ModuleVariable => DefinitionKind::ModuleVariable,
        DefinitionKindWire::Interface => DefinitionKind::Interface,
        DefinitionKindWire::TypeAlias => DefinitionKind::TypeAlias,
        DefinitionKindWire::Namespace => DefinitionKind::Namespace,
        DefinitionKindWire::Impl => DefinitionKind::Impl,
        DefinitionKindWire::Import => DefinitionKind::Import,
        DefinitionKindWire::Export => DefinitionKind::Export,
        DefinitionKindWire::TypeParameter => DefinitionKind::TypeParameter,
        DefinitionKindWire::ConstParameter => DefinitionKind::ConstParameter,
        DefinitionKindWire::Field => DefinitionKind::Field,
        DefinitionKindWire::Variant => DefinitionKind::Variant,
        DefinitionKindWire::AssociatedFunction => DefinitionKind::AssociatedFunction,
        DefinitionKindWire::AssociatedConstant => DefinitionKind::AssociatedConstant,
        DefinitionKindWire::AssociatedOperator => DefinitionKind::AssociatedOperator,
        DefinitionKindWire::AssociatedType => DefinitionKind::AssociatedType,
        DefinitionKindWire::VariantConstructor(v) => {
            DefinitionKind::VariantConstructor(variant_ctor_kind_from_wire(v))
        }
        DefinitionKindWire::OpaqueType => DefinitionKind::OpaqueType,
    }
}

#[inline]
pub fn std_item_to_wire(v: hir::StdItem) -> StdItemWire {
    match v {
        hir::StdItem::Optional => StdItemWire::Optional,
        hir::StdItem::List => StdItemWire::List,
        hir::StdItem::Set => StdItemWire::Set,
        hir::StdItem::Dictionary => StdItemWire::Dictionary,
        hir::StdItem::Range => StdItemWire::Range,
        hir::StdItem::ClosedRange => StdItemWire::ClosedRange,
        hir::StdItem::Copy => StdItemWire::Copy,
        hir::StdItem::Clone => StdItemWire::Clone,
        hir::StdItem::Hashable => StdItemWire::Hashable,
        hir::StdItem::Equatable => StdItemWire::Equatable,
        hir::StdItem::Iterator => StdItemWire::Iterator,
        hir::StdItem::Iterable => StdItemWire::Iterable,
        hir::StdItem::Fn => StdItemWire::Fn,
        hir::StdItem::FnMut => StdItemWire::FnMut,
        hir::StdItem::FnOnce => StdItemWire::FnOnce,
        hir::StdItem::Tuple => StdItemWire::Tuple,
        hir::StdItem::Add => StdItemWire::Add,
        hir::StdItem::Sub => StdItemWire::Sub,
        hir::StdItem::Mul => StdItemWire::Mul,
        hir::StdItem::Div => StdItemWire::Div,
        hir::StdItem::Rem => StdItemWire::Rem,
        hir::StdItem::Neg => StdItemWire::Neg,
        hir::StdItem::Not => StdItemWire::Not,
        hir::StdItem::BitAnd => StdItemWire::BitAnd,
        hir::StdItem::BitOr => StdItemWire::BitOr,
        hir::StdItem::BitXor => StdItemWire::BitXor,
        hir::StdItem::Shl => StdItemWire::Shl,
        hir::StdItem::Shr => StdItemWire::Shr,
        hir::StdItem::BitNot => StdItemWire::BitNot,
        hir::StdItem::PartialEq => StdItemWire::PartialEq,
        hir::StdItem::PartialOrd => StdItemWire::PartialOrd,
        hir::StdItem::OptionalSomeVariant => StdItemWire::OptionalSomeVariant,
        hir::StdItem::OptionalSomeCtor => StdItemWire::OptionalSomeCtor,
        hir::StdItem::OptionalNoneVariant => StdItemWire::OptionalNoneVariant,
        hir::StdItem::OptionalNoneCtor => StdItemWire::OptionalNoneCtor,
        hir::StdItem::Make => StdItemWire::Make,
    }
}

#[inline]
pub fn std_item_from_wire(v: &StdItemWire) -> hir::StdItem {
    match v {
        StdItemWire::Optional => hir::StdItem::Optional,
        StdItemWire::List => hir::StdItem::List,
        StdItemWire::Set => hir::StdItem::Set,
        StdItemWire::Dictionary => hir::StdItem::Dictionary,
        StdItemWire::Range => hir::StdItem::Range,
        StdItemWire::ClosedRange => hir::StdItem::ClosedRange,
        StdItemWire::Copy => hir::StdItem::Copy,
        StdItemWire::Clone => hir::StdItem::Clone,
        StdItemWire::Hashable => hir::StdItem::Hashable,
        StdItemWire::Equatable => hir::StdItem::Equatable,
        StdItemWire::Iterator => hir::StdItem::Iterator,
        StdItemWire::Iterable => hir::StdItem::Iterable,
        StdItemWire::Fn => hir::StdItem::Fn,
        StdItemWire::FnMut => hir::StdItem::FnMut,
        StdItemWire::FnOnce => hir::StdItem::FnOnce,
        StdItemWire::Tuple => hir::StdItem::Tuple,
        StdItemWire::Add => hir::StdItem::Add,
        StdItemWire::Sub => hir::StdItem::Sub,
        StdItemWire::Mul => hir::StdItem::Mul,
        StdItemWire::Div => hir::StdItem::Div,
        StdItemWire::Rem => hir::StdItem::Rem,
        StdItemWire::Neg => hir::StdItem::Neg,
        StdItemWire::Not => hir::StdItem::Not,
        StdItemWire::BitAnd => hir::StdItem::BitAnd,
        StdItemWire::BitOr => hir::StdItem::BitOr,
        StdItemWire::BitXor => hir::StdItem::BitXor,
        StdItemWire::Shl => hir::StdItem::Shl,
        StdItemWire::Shr => hir::StdItem::Shr,
        StdItemWire::BitNot => hir::StdItem::BitNot,
        StdItemWire::PartialEq => hir::StdItem::PartialEq,
        StdItemWire::PartialOrd => hir::StdItem::PartialOrd,
        StdItemWire::OptionalSomeVariant => hir::StdItem::OptionalSomeVariant,
        StdItemWire::OptionalSomeCtor => hir::StdItem::OptionalSomeCtor,
        StdItemWire::OptionalNoneVariant => hir::StdItem::OptionalNoneVariant,
        StdItemWire::OptionalNoneCtor => hir::StdItem::OptionalNoneCtor,
        StdItemWire::Make => hir::StdItem::Make,
    }
}

#[inline]
pub fn abi_to_wire(v: hir::Abi) -> AbiWire {
    match v {
        hir::Abi::C => AbiWire::C,
        hir::Abi::Runtime => AbiWire::Runtime,
        hir::Abi::Intrinsic => AbiWire::Intrinsic,
    }
}

#[inline]
pub fn abi_from_wire(v: &AbiWire) -> hir::Abi {
    match v {
        AbiWire::C => hir::Abi::C,
        AbiWire::Runtime => hir::Abi::Runtime,
        AbiWire::Intrinsic => hir::Abi::Intrinsic,
    }
}

#[inline]
pub fn int_suffix_to_wire(v: IntegerTypeSuffix) -> IntegerTypeSuffixWire {
    match v {
        IntegerTypeSuffix::I8 => IntegerTypeSuffixWire::I8,
        IntegerTypeSuffix::I16 => IntegerTypeSuffixWire::I16,
        IntegerTypeSuffix::I32 => IntegerTypeSuffixWire::I32,
        IntegerTypeSuffix::I64 => IntegerTypeSuffixWire::I64,
        IntegerTypeSuffix::U8 => IntegerTypeSuffixWire::U8,
        IntegerTypeSuffix::U16 => IntegerTypeSuffixWire::U16,
        IntegerTypeSuffix::U32 => IntegerTypeSuffixWire::U32,
        IntegerTypeSuffix::U64 => IntegerTypeSuffixWire::U64,
    }
}

#[inline]
pub fn int_suffix_from_wire(v: &IntegerTypeSuffixWire) -> IntegerTypeSuffix {
    match v {
        IntegerTypeSuffixWire::I8 => IntegerTypeSuffix::I8,
        IntegerTypeSuffixWire::I16 => IntegerTypeSuffix::I16,
        IntegerTypeSuffixWire::I32 => IntegerTypeSuffix::I32,
        IntegerTypeSuffixWire::I64 => IntegerTypeSuffix::I64,
        IntegerTypeSuffixWire::U8 => IntegerTypeSuffix::U8,
        IntegerTypeSuffixWire::U16 => IntegerTypeSuffix::U16,
        IntegerTypeSuffixWire::U32 => IntegerTypeSuffix::U32,
        IntegerTypeSuffixWire::U64 => IntegerTypeSuffix::U64,
    }
}

#[inline]
pub fn operator_kind_to_wire(v: hir::OperatorKind) -> OperatorKindWire {
    match v {
        hir::OperatorKind::Add | hir::OperatorKind::AddAssign => OperatorKindWire::Add,
        hir::OperatorKind::Sub | hir::OperatorKind::SubAssign => OperatorKindWire::Sub,
        hir::OperatorKind::Mul | hir::OperatorKind::MulAssign => OperatorKindWire::Mul,
        hir::OperatorKind::Div | hir::OperatorKind::DivAssign => OperatorKindWire::Div,
        hir::OperatorKind::Rem | hir::OperatorKind::RemAssign => OperatorKindWire::Rem,
        hir::OperatorKind::Eq => OperatorKindWire::Eq,
        hir::OperatorKind::Neq => OperatorKindWire::Ne,
        hir::OperatorKind::Gt => OperatorKindWire::Gt,
        hir::OperatorKind::Lt => OperatorKindWire::Lt,
        hir::OperatorKind::Geq => OperatorKindWire::Ge,
        hir::OperatorKind::Leq => OperatorKindWire::Le,
        hir::OperatorKind::BitAnd | hir::OperatorKind::BitAndAssign => OperatorKindWire::BitAnd,
        hir::OperatorKind::BitOr | hir::OperatorKind::BitOrAssign => OperatorKindWire::BitOr,
        hir::OperatorKind::BitXor | hir::OperatorKind::BitXorAssign => OperatorKindWire::BitXor,
        hir::OperatorKind::BitShl | hir::OperatorKind::BitShlAssign => OperatorKindWire::Shl,
        hir::OperatorKind::BitShr | hir::OperatorKind::BitShrAssign => OperatorKindWire::Shr,
        hir::OperatorKind::BitwiseNot => OperatorKindWire::BitNot,
        hir::OperatorKind::Neg => OperatorKindWire::Neg,
        hir::OperatorKind::Not => OperatorKindWire::Not,
        hir::OperatorKind::BoolAnd => OperatorKindWire::BitAnd,
        hir::OperatorKind::BoolOr => OperatorKindWire::BitOr,
    }
}

#[inline]
pub fn operator_kind_from_wire(v: &OperatorKindWire) -> hir::OperatorKind {
    match v {
        OperatorKindWire::Add => hir::OperatorKind::Add,
        OperatorKindWire::Sub => hir::OperatorKind::Sub,
        OperatorKindWire::Mul => hir::OperatorKind::Mul,
        OperatorKindWire::Div => hir::OperatorKind::Div,
        OperatorKindWire::Rem => hir::OperatorKind::Rem,
        OperatorKindWire::Eq => hir::OperatorKind::Eq,
        OperatorKindWire::Ne => hir::OperatorKind::Neq,
        OperatorKindWire::Gt => hir::OperatorKind::Gt,
        OperatorKindWire::Lt => hir::OperatorKind::Lt,
        OperatorKindWire::Ge => hir::OperatorKind::Geq,
        OperatorKindWire::Le => hir::OperatorKind::Leq,
        OperatorKindWire::BitAnd => hir::OperatorKind::BitAnd,
        OperatorKindWire::BitOr => hir::OperatorKind::BitOr,
        OperatorKindWire::BitXor => hir::OperatorKind::BitXor,
        OperatorKindWire::Shl => hir::OperatorKind::BitShl,
        OperatorKindWire::Shr => hir::OperatorKind::BitShr,
        OperatorKindWire::BitNot => hir::OperatorKind::BitwiseNot,
        OperatorKindWire::Neg => hir::OperatorKind::Neg,
        OperatorKindWire::Not => hir::OperatorKind::Not,
    }
}

#[inline]
pub fn literal_to_wire(v: &hir::Literal) -> LiteralWire {
    match v {
        hir::Literal::Bool(v) => LiteralWire::Bool(*v),
        hir::Literal::Rune(v) => LiteralWire::Rune(*v),
        hir::Literal::String(v) => LiteralWire::String(v.as_str().to_string()),
        hir::Literal::Integer { value, suffix } => LiteralWire::Integer {
            value: *value,
            suffix: suffix.as_ref().map(|v| int_suffix_to_wire(*v)),
        },
        hir::Literal::Float(v) => LiteralWire::Float(*v),
        hir::Literal::Nil => LiteralWire::Nil,
    }
}

#[inline]
pub fn literal_from_wire(v: &LiteralWire) -> hir::Literal {
    match v {
        LiteralWire::Bool(v) => hir::Literal::Bool(*v),
        LiteralWire::Rune(v) => hir::Literal::Rune(*v),
        LiteralWire::String(v) => hir::Literal::String(Symbol::new(v)),
        LiteralWire::Integer { value, suffix } => hir::Literal::Integer {
            value: *value,
            suffix: suffix.as_ref().map(int_suffix_from_wire),
        },
        LiteralWire::Float(v) => hir::Literal::Float(*v),
        LiteralWire::Nil => hir::Literal::Nil,
    }
}

#[inline]
pub fn attribute_arg_to_wire(
    arg: &hir::AttributeArg,
    symbols: &mut SymbolTableBuilder,
) -> AttributeArgWire {
    match arg {
        hir::AttributeArg::KeyValue { key, value, span } => AttributeArgWire::KeyValue {
            key: identifier_to_wire(*key, symbols),
            value: literal_to_wire(value),
            span: span_to_wire(*span),
        },
        hir::AttributeArg::Flag { key, span } => AttributeArgWire::Flag {
            key: identifier_to_wire(*key, symbols),
            span: span_to_wire(*span),
        },
        hir::AttributeArg::Literal { value, span } => AttributeArgWire::Literal {
            value: literal_to_wire(value),
            span: span_to_wire(*span),
        },
    }
}

#[inline]
pub fn attribute_arg_from_wire(
    arg: &AttributeArgWire,
    remap: FileRemap<'_>,
    symbols: SymbolTableRef<'_>,
) -> hir::AttributeArg {
    match arg {
        AttributeArgWire::KeyValue { key, value, span } => hir::AttributeArg::KeyValue {
            key: identifier_from_wire(key, remap, symbols),
            value: literal_from_wire(value),
            span: span_from_wire(span, remap),
        },
        AttributeArgWire::Flag { key, span } => hir::AttributeArg::Flag {
            key: identifier_from_wire(key, remap, symbols),
            span: span_from_wire(span, remap),
        },
        AttributeArgWire::Literal { value, span } => hir::AttributeArg::Literal {
            value: literal_from_wire(value),
            span: span_from_wire(span, remap),
        },
    }
}

#[inline]
pub fn attribute_to_wire(attr: &hir::Attribute, symbols: &mut SymbolTableBuilder) -> AttributeWire {
    AttributeWire {
        identifier: identifier_to_wire(attr.identifier, symbols),
        args: attr.args.as_ref().map(|args| AttributeArgsWire {
            items: args
                .items
                .iter()
                .map(|arg| attribute_arg_to_wire(arg, symbols))
                .collect(),
            span: span_to_wire(args.span),
        }),
        span: span_to_wire(attr.span),
    }
}

#[inline]
pub fn attribute_from_wire(
    attr: &AttributeWire,
    remap: FileRemap<'_>,
    symbols: SymbolTableRef<'_>,
) -> hir::Attribute {
    hir::Attribute {
        identifier: identifier_from_wire(&attr.identifier, remap, symbols),
        args: attr.args.as_ref().map(|args| hir::AttributeArgs {
            items: args
                .items
                .iter()
                .map(|arg| attribute_arg_from_wire(arg, remap, symbols))
                .collect(),
            span: span_from_wire(&args.span, remap),
        }),
        span: span_from_wire(&attr.span, remap),
    }
}

#[inline]
pub fn generic_param_to_wire(param: GenericParameter) -> GenericParameterWire {
    GenericParameterWire {
        index: param.index as u32,
        name: param.name.as_str().to_string(),
    }
}

#[inline]
pub fn generic_param_from_wire(param: &GenericParameterWire) -> GenericParameter {
    GenericParameter {
        index: param.index as usize,
        name: Symbol::new(&param.name),
    }
}

#[inline]
pub fn const_value_to_wire(v: ConstValue) -> ConstValueWire {
    match v {
        ConstValue::Integer(v) => ConstValueWire::Integer(v),
        ConstValue::Bool(v) => ConstValueWire::Bool(v),
        ConstValue::Rune(v) => ConstValueWire::Rune(v),
        ConstValue::String(v) => ConstValueWire::String(v.as_str().to_string()),
        ConstValue::Float(v) => ConstValueWire::Float(v),
        ConstValue::Unit => ConstValueWire::Unit,
    }
}

#[inline]
pub fn const_value_from_wire(v: &ConstValueWire) -> ConstValue {
    match v {
        ConstValueWire::Integer(v) => ConstValue::Integer(*v),
        ConstValueWire::Bool(v) => ConstValue::Bool(*v),
        ConstValueWire::Rune(v) => ConstValue::Rune(*v),
        ConstValueWire::String(v) => ConstValue::String(Symbol::new(v)),
        ConstValueWire::Float(v) => ConstValue::Float(*v),
        ConstValueWire::Unit => ConstValue::Unit,
    }
}

#[inline]
pub fn infer_ty_to_wire(v: InferTy) -> InferTyWire {
    match v {
        InferTy::TyVar(v) => InferTyWire::TyVar(v.index() as u32),
        InferTy::IntVar(v) => InferTyWire::IntVar(v.index() as u32),
        InferTy::FloatVar(v) => InferTyWire::FloatVar(v.index() as u32),
        InferTy::NilVar(v) => InferTyWire::NilVar(v.index() as u32),
        InferTy::FreshTy(v) => InferTyWire::FreshTy(v),
    }
}

#[inline]
pub fn infer_ty_from_wire(v: &InferTyWire) -> InferTy {
    match v {
        InferTyWire::TyVar(v) => InferTy::TyVar(crate::sema::models::TyVarID::from_raw(*v)),
        InferTyWire::IntVar(v) => {
            InferTy::IntVar(crate::sema::tycheck::infer::keys::IntVarID::from_index(*v))
        }
        InferTyWire::FloatVar(v) => InferTy::FloatVar(
            crate::sema::tycheck::infer::keys::FloatVarID::from_index(*v),
        ),
        InferTyWire::NilVar(v) => {
            InferTy::NilVar(crate::sema::tycheck::infer::keys::NilVarID::from_index(*v))
        }
        InferTyWire::FreshTy(v) => InferTy::FreshTy(*v),
    }
}

#[inline]
pub fn alias_kind_to_wire(v: AliasKind) -> AliasKindWire {
    match v {
        AliasKind::Inherent => AliasKindWire::Inherent,
        AliasKind::Weak => AliasKindWire::Weak,
        AliasKind::Projection => AliasKindWire::Projection,
    }
}

#[inline]
pub fn alias_kind_from_wire(v: &AliasKindWire) -> AliasKind {
    match v {
        AliasKindWire::Inherent => AliasKind::Inherent,
        AliasKindWire::Weak => AliasKind::Weak,
        AliasKindWire::Projection => AliasKind::Projection,
    }
}

#[inline]
pub fn closure_kind_to_wire(v: ClosureKind) -> ClosureKindWire {
    match v {
        ClosureKind::Fn => ClosureKindWire::Fn,
        ClosureKind::FnMut => ClosureKindWire::FnMut,
        ClosureKind::FnOnce => ClosureKindWire::FnOnce,
    }
}

#[inline]
pub fn closure_kind_from_wire(v: &ClosureKindWire) -> ClosureKind {
    match v {
        ClosureKindWire::Fn => ClosureKind::Fn,
        ClosureKindWire::FnMut => ClosureKind::FnMut,
        ClosureKindWire::FnOnce => ClosureKind::FnOnce,
    }
}

#[inline]
pub fn capture_kind_to_wire(v: CaptureKind) -> CaptureKindWire {
    match v {
        CaptureKind::ByCopy => CaptureKindWire::ByCopy,
        CaptureKind::ByRef { mutable } => CaptureKindWire::ByRef { mutable },
        CaptureKind::ByMove => CaptureKindWire::ByMove,
    }
}

#[inline]
pub fn capture_kind_from_wire(v: &CaptureKindWire) -> CaptureKind {
    match v {
        CaptureKindWire::ByCopy => CaptureKind::ByCopy,
        CaptureKindWire::ByRef { mutable } => CaptureKind::ByRef { mutable: *mutable },
        CaptureKindWire::ByMove => CaptureKind::ByMove,
    }
}

#[inline]
pub fn adt_def_to_wire(v: AdtDef) -> AdtDefWire {
    AdtDefWire {
        kind: match v.kind {
            AdtKind::Struct => AdtKindWire::Struct,
            AdtKind::Enum => AdtKindWire::Enum,
        },
        id: def_to_wire(v.id),
    }
}

#[inline]
pub fn adt_def_from_wire(v: &AdtDefWire) -> AdtDef {
    AdtDef {
        kind: match v.kind {
            AdtKindWire::Struct => AdtKind::Struct,
            AdtKindWire::Enum => AdtKind::Enum,
        },
        id: def_from_wire(&v.id),
    }
}

pub fn generic_arg_to_wire(v: GenericArgument<'_>) -> GenericArgumentWire {
    match v {
        GenericArgument::Type(v) => GenericArgumentWire::Type(ty_to_wire(v)),
        GenericArgument::Const(v) => GenericArgumentWire::Const(const_to_wire(v)),
    }
}

pub fn generic_arg_from_wire<'a>(
    gcx: GlobalContext<'a>,
    v: &GenericArgumentWire,
) -> GenericArgument<'a> {
    match v {
        GenericArgumentWire::Type(v) => GenericArgument::Type(ty_from_wire(gcx, v)),
        GenericArgumentWire::Const(v) => GenericArgument::Const(const_from_wire(gcx, v)),
    }
}

pub fn interface_reference_to_wire(v: InterfaceReference<'_>) -> InterfaceReferenceWire {
    InterfaceReferenceWire {
        id: def_to_wire(v.id),
        arguments: v
            .arguments
            .iter()
            .copied()
            .map(generic_arg_to_wire)
            .collect(),
        bindings: v
            .bindings
            .iter()
            .map(|b| AssociatedTypeBindingWire {
                name: b.name.as_str().to_string(),
                ty: ty_to_wire(b.ty),
            })
            .collect(),
    }
}

pub fn interface_reference_from_wire<'a>(
    gcx: GlobalContext<'a>,
    v: &InterfaceReferenceWire,
) -> InterfaceReference<'a> {
    let arguments: Vec<_> = v
        .arguments
        .iter()
        .map(|arg| generic_arg_from_wire(gcx, arg))
        .collect();
    let bindings: Vec<_> = v
        .bindings
        .iter()
        .map(|binding| AssociatedTypeBinding {
            name: Symbol::new(&binding.name),
            ty: ty_from_wire(gcx, &binding.ty),
        })
        .collect();

    InterfaceReference {
        id: def_from_wire(&v.id),
        arguments: gcx.store.interners.intern_generic_args(arguments),
        bindings: gcx.store.arenas.global.alloc_slice_copy(&bindings),
    }
}

pub fn const_to_wire(v: Const<'_>) -> ConstWire {
    ConstWire {
        ty: ty_to_wire(v.ty),
        kind: match v.kind {
            ConstKind::Value(v) => ConstKindWire::Value(const_value_to_wire(v)),
            ConstKind::Param(v) => ConstKindWire::Param(generic_param_to_wire(v)),
            ConstKind::Infer(v) => ConstKindWire::Infer(v.index() as u32),
        },
    }
}

pub fn const_from_wire<'a>(gcx: GlobalContext<'a>, v: &ConstWire) -> Const<'a> {
    Const {
        ty: ty_from_wire(gcx, &v.ty),
        kind: match &v.kind {
            ConstKindWire::Value(v) => ConstKind::Value(const_value_from_wire(v)),
            ConstKindWire::Param(v) => ConstKind::Param(generic_param_from_wire(v)),
            ConstKindWire::Infer(v) => {
                ConstKind::Infer(crate::sema::models::ConstVarID::from_raw(*v))
            }
        },
    }
}

pub fn ty_to_wire(v: Ty<'_>) -> TyWire {
    TyWire {
        kind: match v.kind() {
            TyKind::Array { element, len } => TyKindWire::Array {
                element: Box::new(ty_to_wire(element)),
                len: Box::new(const_to_wire(len)),
            },
            TyKind::Bool => TyKindWire::Bool,
            TyKind::Rune => TyKindWire::Rune,
            TyKind::String => TyKindWire::String,
            TyKind::Int(v) => TyKindWire::Int(int_ty_to_wire(v)),
            TyKind::UInt(v) => TyKindWire::UInt(uint_ty_to_wire(v)),
            TyKind::Float(v) => TyKindWire::Float(float_ty_to_wire(v)),
            TyKind::Adt(def, args) => TyKindWire::Adt(
                adt_def_to_wire(def),
                args.iter().copied().map(generic_arg_to_wire).collect(),
            ),
            TyKind::Pointer(ty, m) => {
                TyKindWire::Pointer(Box::new(ty_to_wire(ty)), mutability_to_wire(m))
            }
            TyKind::Reference(ty, m) => {
                TyKindWire::Reference(Box::new(ty_to_wire(ty)), mutability_to_wire(m))
            }
            TyKind::Tuple(items) => {
                TyKindWire::Tuple(items.iter().copied().map(ty_to_wire).collect())
            }
            TyKind::FnPointer { inputs, output } => TyKindWire::FnPointer {
                inputs: inputs.iter().copied().map(ty_to_wire).collect(),
                output: Box::new(ty_to_wire(output)),
            },
            TyKind::BoxedExistential { interfaces } => TyKindWire::BoxedExistential {
                interfaces: interfaces
                    .iter()
                    .copied()
                    .map(interface_reference_to_wire)
                    .collect(),
            },
            TyKind::Alias { kind, def_id, args } => TyKindWire::Alias {
                kind: alias_kind_to_wire(kind),
                def_id: def_to_wire(def_id),
                args: args.iter().copied().map(generic_arg_to_wire).collect(),
            },
            TyKind::Infer(v) => TyKindWire::Infer(infer_ty_to_wire(v)),
            TyKind::Parameter(v) => TyKindWire::Parameter(generic_param_to_wire(v)),
            TyKind::Closure {
                closure_def_id,
                captured_generics,
                inputs,
                output,
                kind,
            } => TyKindWire::Closure {
                closure_def_id: def_to_wire(closure_def_id),
                captured_generics: captured_generics
                    .iter()
                    .copied()
                    .map(generic_arg_to_wire)
                    .collect(),
                inputs: inputs.iter().copied().map(ty_to_wire).collect(),
                output: Box::new(ty_to_wire(output)),
                kind: closure_kind_to_wire(kind),
            },
            TyKind::Opaque(v) => TyKindWire::Opaque(def_to_wire(v)),
            TyKind::Error => TyKindWire::Error,
            TyKind::Never => TyKindWire::Never,
        },
    }
}

pub fn ty_from_wire<'a>(gcx: GlobalContext<'a>, v: &TyWire) -> Ty<'a> {
    let kind = match &v.kind {
        TyKindWire::Array { element, len } => TyKind::Array {
            element: ty_from_wire(gcx, element),
            len: const_from_wire(gcx, len),
        },
        TyKindWire::Bool => TyKind::Bool,
        TyKindWire::Rune => TyKind::Rune,
        TyKindWire::String => TyKind::String,
        TyKindWire::Int(v) => TyKind::Int(int_ty_from_wire(v)),
        TyKindWire::UInt(v) => TyKind::UInt(uint_ty_from_wire(v)),
        TyKindWire::Float(v) => TyKind::Float(float_ty_from_wire(v)),
        TyKindWire::Adt(def, args) => {
            let args: Vec<_> = args
                .iter()
                .map(|arg| generic_arg_from_wire(gcx, arg))
                .collect();
            TyKind::Adt(
                adt_def_from_wire(def),
                gcx.store.interners.intern_generic_args(args),
            )
        }
        TyKindWire::Pointer(ty, m) => {
            TyKind::Pointer(ty_from_wire(gcx, ty), mutability_from_wire(m))
        }
        TyKindWire::Reference(ty, m) => {
            TyKind::Reference(ty_from_wire(gcx, ty), mutability_from_wire(m))
        }
        TyKindWire::Tuple(items) => {
            let items: Vec<_> = items.iter().map(|item| ty_from_wire(gcx, item)).collect();
            TyKind::Tuple(gcx.store.interners.intern_ty_list(items))
        }
        TyKindWire::FnPointer { inputs, output } => {
            let inputs: Vec<_> = inputs.iter().map(|item| ty_from_wire(gcx, item)).collect();
            TyKind::FnPointer {
                inputs: gcx.store.interners.intern_ty_list(inputs),
                output: ty_from_wire(gcx, output),
            }
        }
        TyKindWire::BoxedExistential { interfaces } => {
            let interfaces: Vec<_> = interfaces
                .iter()
                .map(|iface| interface_reference_from_wire(gcx, iface))
                .collect();
            TyKind::BoxedExistential {
                interfaces: gcx.store.arenas.global.alloc_slice_copy(&interfaces),
            }
        }
        TyKindWire::Alias { kind, def_id, args } => {
            let args: Vec<_> = args
                .iter()
                .map(|arg| generic_arg_from_wire(gcx, arg))
                .collect();
            TyKind::Alias {
                kind: alias_kind_from_wire(kind),
                def_id: def_from_wire(def_id),
                args: gcx.store.interners.intern_generic_args(args),
            }
        }
        TyKindWire::Infer(v) => TyKind::Infer(infer_ty_from_wire(v)),
        TyKindWire::Parameter(v) => TyKind::Parameter(generic_param_from_wire(v)),
        TyKindWire::Closure {
            closure_def_id,
            captured_generics,
            inputs,
            output,
            kind,
        } => {
            let captured_generics: Vec<_> = captured_generics
                .iter()
                .map(|arg| generic_arg_from_wire(gcx, arg))
                .collect();
            let inputs: Vec<_> = inputs.iter().map(|item| ty_from_wire(gcx, item)).collect();
            TyKind::Closure {
                closure_def_id: def_from_wire(closure_def_id),
                captured_generics: gcx.store.interners.intern_generic_args(captured_generics),
                inputs: gcx.store.interners.intern_ty_list(inputs),
                output: ty_from_wire(gcx, output),
                kind: closure_kind_from_wire(kind),
            }
        }
        TyKindWire::Opaque(v) => TyKind::Opaque(def_from_wire(v)),
        TyKindWire::Error => TyKind::Error,
        TyKindWire::Never => TyKind::Never,
    };
    Ty::new(kind, gcx)
}

#[inline]
pub fn node_to_wire(id: ast::NodeID) -> u32 {
    id.index() as u32
}

#[inline]
pub fn node_from_wire(id: u32) -> ast::NodeID {
    ast::NodeID::from_raw(id)
}

#[inline]
pub fn hir_node_to_wire(id: hir::NodeID) -> u32 {
    id.index() as u32
}

#[inline]
pub fn hir_node_from_wire(id: u32) -> hir::NodeID {
    hir::NodeID::from_raw(id)
}

pub fn resolution_to_wire(v: &Resolution) -> ResolutionWire {
    match v {
        Resolution::PrimaryType(v) => ResolutionWire::PrimaryType(primary_type_to_wire(*v)),
        Resolution::Definition(id, kind) => {
            ResolutionWire::Definition(def_to_wire(*id), definition_kind_to_wire(*kind))
        }
        Resolution::SelfTypeAlias(id) => ResolutionWire::SelfTypeAlias(def_to_wire(*id)),
        Resolution::InterfaceSelfTypeParameter(id) => {
            ResolutionWire::InterfaceSelfTypeParameter(def_to_wire(*id))
        }
        Resolution::FunctionSet(set) => {
            ResolutionWire::FunctionSet(set.iter().copied().map(def_to_wire).collect())
        }
        Resolution::LocalVariable(id) => ResolutionWire::LocalVariable(node_to_wire(*id)),
        Resolution::SelfConstructor(id) => ResolutionWire::SelfConstructor(def_to_wire(*id)),
        Resolution::StdItem(item) => ResolutionWire::StdItem(std_item_to_wire(*item)),
        Resolution::Error => ResolutionWire::Error,
    }
}

pub fn resolution_from_wire(v: &ResolutionWire) -> Resolution {
    match v {
        ResolutionWire::PrimaryType(v) => Resolution::PrimaryType(primary_type_from_wire(v)),
        ResolutionWire::Definition(id, kind) => {
            Resolution::Definition(def_from_wire(id), definition_kind_from_wire(kind))
        }
        ResolutionWire::SelfTypeAlias(id) => Resolution::SelfTypeAlias(def_from_wire(id)),
        ResolutionWire::InterfaceSelfTypeParameter(id) => {
            Resolution::InterfaceSelfTypeParameter(def_from_wire(id))
        }
        ResolutionWire::FunctionSet(ids) => {
            Resolution::FunctionSet(ids.iter().map(def_from_wire).collect())
        }
        ResolutionWire::LocalVariable(id) => Resolution::LocalVariable(node_from_wire(*id)),
        ResolutionWire::SelfConstructor(id) => Resolution::SelfConstructor(def_from_wire(id)),
        ResolutionWire::StdItem(item) => Resolution::StdItem(std_item_from_wire(item)),
        ResolutionWire::Error => Resolution::Error,
    }
}

pub fn resolution_state_to_wire(v: &ResolutionState) -> ResolutionStateWire {
    match v {
        ResolutionState::Complete(v) => ResolutionStateWire::Complete(resolution_to_wire(v)),
        ResolutionState::Partial {
            resolution,
            unresolved_count,
        } => ResolutionStateWire::Partial {
            resolution: resolution_to_wire(resolution),
            unresolved_count: *unresolved_count as u32,
        },
    }
}

pub fn resolution_state_from_wire(v: &ResolutionStateWire) -> ResolutionState {
    match v {
        ResolutionStateWire::Complete(v) => ResolutionState::Complete(resolution_from_wire(v)),
        ResolutionStateWire::Partial {
            resolution,
            unresolved_count,
        } => ResolutionState::Partial {
            resolution: resolution_from_wire(resolution),
            unresolved_count: *unresolved_count as usize,
        },
    }
}

pub fn expression_resolution_state_to_wire(
    v: &ExpressionResolutionState,
) -> ExpressionResolutionStateWire {
    match v {
        ExpressionResolutionState::Resolved(v) => {
            ExpressionResolutionStateWire::Resolved(resolution_to_wire(v))
        }
        ExpressionResolutionState::DeferredAssociatedType => {
            ExpressionResolutionStateWire::DeferredAssociatedType
        }
        ExpressionResolutionState::DeferredAssociatedValue => {
            ExpressionResolutionStateWire::DeferredAssociatedValue
        }
    }
}

pub fn expression_resolution_state_from_wire(
    v: &ExpressionResolutionStateWire,
) -> ExpressionResolutionState {
    match v {
        ExpressionResolutionStateWire::Resolved(v) => {
            ExpressionResolutionState::Resolved(resolution_from_wire(v))
        }
        ExpressionResolutionStateWire::DeferredAssociatedType => {
            ExpressionResolutionState::DeferredAssociatedType
        }
        ExpressionResolutionStateWire::DeferredAssociatedValue => {
            ExpressionResolutionState::DeferredAssociatedValue
        }
    }
}

pub fn visibility_to_wire(v: Visibility) -> VisibilityWire {
    match v {
        Visibility::Public => VisibilityWire::Public,
        Visibility::Private(v) => VisibilityWire::Private(def_to_wire(v)),
        Visibility::FilePrivate(v) => VisibilityWire::FilePrivate(v.raw()),
    }
}

pub fn visibility_from_wire(v: &VisibilityWire, remap: FileRemap<'_>) -> Visibility {
    match v {
        VisibilityWire::Public => Visibility::Public,
        VisibilityWire::Private(v) => Visibility::Private(def_from_wire(v)),
        VisibilityWire::FilePrivate(v) => Visibility::FilePrivate(
            remap
                .old_to_new
                .get(v)
                .copied()
                .unwrap_or_else(|| FileID::from_raw(0)),
        ),
    }
}

pub fn scope_kind_to_wire(v: ScopeKind) -> ScopeKindWire {
    match v {
        ScopeKind::Block(v) => ScopeKindWire::Block(node_to_wire(v)),
        ScopeKind::File(v) => ScopeKindWire::File(v.raw()),
        ScopeKind::Definition(id, kind) => {
            ScopeKindWire::Definition(def_to_wire(id), definition_kind_to_wire(kind))
        }
    }
}

pub fn scope_kind_from_wire(v: &ScopeKindWire, remap: FileRemap<'_>) -> ScopeKind {
    match v {
        ScopeKindWire::Block(v) => ScopeKind::Block(node_from_wire(*v)),
        ScopeKindWire::File(v) => ScopeKind::File(
            remap
                .old_to_new
                .get(v)
                .copied()
                .unwrap_or_else(|| FileID::from_raw(0)),
        ),
        ScopeKindWire::Definition(id, kind) => {
            ScopeKind::Definition(def_from_wire(id), definition_kind_from_wire(kind))
        }
    }
}

#[inline]
pub fn type_head_to_wire(v: TypeHead) -> TypeHeadWire {
    match v {
        TypeHead::Primary(v) => TypeHeadWire::Primary(primary_type_to_wire(v)),
        TypeHead::Nominal(v) => TypeHeadWire::Nominal(def_to_wire(v)),
        TypeHead::Closure(v) => TypeHeadWire::Closure(def_to_wire(v)),
        TypeHead::Reference(v) => TypeHeadWire::Reference(mutability_to_wire(v)),
        TypeHead::Pointer(v) => TypeHeadWire::Pointer(mutability_to_wire(v)),
        TypeHead::Tuple(v) => TypeHeadWire::Tuple(v),
        TypeHead::Array => TypeHeadWire::Array,
    }
}

#[inline]
pub fn type_head_from_wire(v: &TypeHeadWire) -> TypeHead {
    match v {
        TypeHeadWire::Primary(v) => TypeHead::Primary(primary_type_from_wire(v)),
        TypeHeadWire::Nominal(v) => TypeHead::Nominal(def_from_wire(v)),
        TypeHeadWire::Closure(v) => TypeHead::Closure(def_from_wire(v)),
        TypeHeadWire::Reference(v) => TypeHead::Reference(mutability_from_wire(v)),
        TypeHeadWire::Pointer(v) => TypeHead::Pointer(mutability_from_wire(v)),
        TypeHeadWire::Tuple(v) => TypeHead::Tuple(*v),
        TypeHeadWire::Array => TypeHead::Array,
    }
}

pub fn constraint_to_wire(v: &Constraint<'_>) -> ConstraintWire {
    match v {
        Constraint::TypeEquality(lhs, rhs) => {
            ConstraintWire::TypeEquality(ty_to_wire(*lhs), ty_to_wire(*rhs))
        }
        Constraint::Bound { ty, interface } => ConstraintWire::Bound {
            ty: ty_to_wire(*ty),
            interface: interface_reference_to_wire(*interface),
        },
    }
}

pub fn constraint_from_wire<'a>(gcx: GlobalContext<'a>, v: &ConstraintWire) -> Constraint<'a> {
    match v {
        ConstraintWire::TypeEquality(lhs, rhs) => {
            Constraint::TypeEquality(ty_from_wire(gcx, lhs), ty_from_wire(gcx, rhs))
        }
        ConstraintWire::Bound { ty, interface } => Constraint::Bound {
            ty: ty_from_wire(gcx, ty),
            interface: interface_reference_from_wire(gcx, interface),
        },
    }
}

#[inline]
fn dummy_hir_type(span: Span) -> Box<hir::Type> {
    Box::new(hir::Type {
        id: hir::NodeID::from_raw(u32::MAX - 1),
        span,
        kind: hir::TypeKind::Infer,
    })
}

#[inline]
fn dummy_hir_anon_const(span: Span) -> hir::AnonConst {
    let expr = hir::Expression {
        id: hir::NodeID::from_raw(u32::MAX - 2),
        kind: hir::ExpressionKind::Literal(hir::Literal::Nil),
        span,
    };
    hir::AnonConst {
        value: Box::new(expr),
    }
}

pub fn fn_param_to_wire(v: &LabeledFunctionParameter<'_>) -> LabeledFunctionParameterWire {
    LabeledFunctionParameterWire {
        label: v.label.map(|v| v.as_str().to_string()),
        name: v.name.as_str().to_string(),
        ty: ty_to_wire(v.ty),
        default_provider: v.default_provider.map(def_to_wire),
    }
}

pub fn fn_param_from_wire<'a>(
    gcx: GlobalContext<'a>,
    v: &LabeledFunctionParameterWire,
) -> LabeledFunctionParameter<'a> {
    LabeledFunctionParameter {
        label: v.label.as_ref().map(|v| Symbol::new(v)),
        name: Symbol::new(&v.name),
        ty: ty_from_wire(gcx, &v.ty),
        default_provider: v.default_provider.as_ref().map(def_from_wire),
    }
}

pub fn signature_to_wire(v: &LabeledFunctionSignature<'_>) -> LabeledFunctionSignatureWire {
    LabeledFunctionSignatureWire {
        inputs: v.inputs.iter().map(fn_param_to_wire).collect(),
        output: ty_to_wire(v.output),
        is_variadic: v.is_variadic,
        abi: v.abi.map(abi_to_wire),
    }
}

pub fn signature_from_wire<'a>(
    gcx: GlobalContext<'a>,
    v: &LabeledFunctionSignatureWire,
) -> LabeledFunctionSignature<'a> {
    LabeledFunctionSignature {
        inputs: v
            .inputs
            .iter()
            .map(|v| fn_param_from_wire(gcx, v))
            .collect(),
        output: ty_from_wire(gcx, &v.output),
        is_variadic: v.is_variadic,
        abi: v.abi.as_ref().map(abi_from_wire),
    }
}

pub fn generics_to_wire(v: &Generics) -> GenericsWire {
    GenericsWire {
        parameters: v
            .parameters
            .iter()
            .map(|param| GenericParameterDefinitionWire {
                name: param.name.as_str().to_string(),
                id: def_to_wire(param.id),
                index: param.index as u32,
                kind: match &param.kind {
                    GenericParameterDefinitionKind::Type { default } => {
                        GenericParameterDefinitionKindWire::Type {
                            has_default: default.is_some(),
                        }
                    }
                    GenericParameterDefinitionKind::Const { default, .. } => {
                        GenericParameterDefinitionKindWire::Const {
                            has_default: default.is_some(),
                        }
                    }
                },
            })
            .collect(),
        has_self: v.has_self,
        parent: v.parent.map(def_to_wire),
        parent_count: v.parent_count as u32,
    }
}

pub fn generics_from_wire(v: &GenericsWire, placeholder_span: Span) -> Generics {
    Generics {
        parameters: v
            .parameters
            .iter()
            .map(|param| GenericParameterDefinition {
                name: Symbol::new(&param.name),
                id: def_from_wire(&param.id),
                index: param.index as usize,
                kind: match param.kind {
                    GenericParameterDefinitionKindWire::Type { has_default } => {
                        GenericParameterDefinitionKind::Type {
                            default: has_default.then(|| dummy_hir_type(placeholder_span)),
                        }
                    }
                    GenericParameterDefinitionKindWire::Const { has_default } => {
                        GenericParameterDefinitionKind::Const {
                            ty: dummy_hir_type(placeholder_span),
                            default: has_default.then(|| dummy_hir_anon_const(placeholder_span)),
                        }
                    }
                },
            })
            .collect(),
        has_self: v.has_self,
        parent: v.parent.as_ref().map(def_from_wire),
        parent_count: v.parent_count as usize,
    }
}

pub fn struct_definition_to_wire(
    v: &StructDefinition<'_>,
    symbols: &mut SymbolTableBuilder,
) -> StructDefinitionWire {
    StructDefinitionWire {
        adt_def: adt_def_to_wire(v.adt_def),
        fields: v
            .fields
            .iter()
            .map(|field| StructFieldWire {
                name: symbols.intern_symbol(field.name),
                ty: ty_to_wire(field.ty),
                mutability: mutability_to_wire(field.mutability),
                def_id: def_to_wire(field.def_id),
                visibility: visibility_to_wire(field.visibility),
            })
            .collect(),
    }
}

pub fn struct_definition_from_wire<'a>(
    gcx: GlobalContext<'a>,
    v: &StructDefinitionWire,
    remap: FileRemap<'_>,
    symbols: SymbolTableRef<'_>,
) -> StructDefinition<'a> {
    let fields: Vec<_> = v
        .fields
        .iter()
        .map(|field| StructField {
            name: Symbol::new(symbols.resolve_str(field.name)),
            ty: ty_from_wire(gcx, &field.ty),
            mutability: mutability_from_wire(&field.mutability),
            def_id: def_from_wire(&field.def_id),
            visibility: visibility_from_wire(&field.visibility, remap),
        })
        .collect();
    StructDefinition {
        adt_def: adt_def_from_wire(&v.adt_def),
        fields: gcx.store.arenas.global.alloc_slice_copy(&fields),
    }
}

pub fn enum_definition_to_wire(
    v: &EnumDefinition<'_>,
    symbols: &mut SymbolTableBuilder,
) -> EnumDefinitionWire {
    EnumDefinitionWire {
        adt_def: adt_def_to_wire(v.adt_def),
        variants: v
            .variants
            .iter()
            .map(|variant| EnumVariantWire {
                name: symbols.intern_symbol(variant.name),
                def_id: def_to_wire(variant.def_id),
                ctor_def_id: def_to_wire(variant.ctor_def_id),
                kind: match variant.kind {
                    EnumVariantKind::Unit => EnumVariantKindWire::Unit,
                    EnumVariantKind::Tuple(fields) => EnumVariantKindWire::Tuple(
                        fields
                            .iter()
                            .map(|field| EnumVariantFieldWire {
                                label: field.label.map(|v| symbols.intern_symbol(v)),
                                ty: ty_to_wire(field.ty),
                            })
                            .collect(),
                    ),
                },
                discriminant: variant.discriminant,
            })
            .collect(),
    }
}

pub fn enum_definition_from_wire<'a>(
    gcx: GlobalContext<'a>,
    v: &EnumDefinitionWire,
    symbols: SymbolTableRef<'_>,
) -> EnumDefinition<'a> {
    let variants: Vec<_> = v
        .variants
        .iter()
        .map(|variant| {
            let kind = match &variant.kind {
                EnumVariantKindWire::Unit => EnumVariantKind::Unit,
                EnumVariantKindWire::Tuple(fields) => {
                    let fields: Vec<_> = fields
                        .iter()
                        .map(|field| EnumVariantField {
                            label: field.label.map(|v| Symbol::new(symbols.resolve_str(v))),
                            ty: ty_from_wire(gcx, &field.ty),
                        })
                        .collect();
                    EnumVariantKind::Tuple(gcx.store.arenas.global.alloc_slice_copy(&fields))
                }
            };
            EnumVariant {
                name: Symbol::new(symbols.resolve_str(variant.name)),
                def_id: def_from_wire(&variant.def_id),
                ctor_def_id: def_from_wire(&variant.ctor_def_id),
                kind,
                discriminant: variant.discriminant,
            }
        })
        .collect();
    EnumDefinition {
        adt_def: adt_def_from_wire(&v.adt_def),
        variants: gcx.store.arenas.global.alloc_slice_copy(&variants),
    }
}

pub fn interface_def_to_wire(
    v: &InterfaceDefinition<'_>,
    symbols: &mut SymbolTableBuilder,
) -> InterfaceDefinitionWire {
    InterfaceDefinitionWire {
        id: def_to_wire(v.id),
        superfaces: v
            .superfaces
            .iter()
            .map(|sup| InterfaceReferenceSpannedWire {
                value: interface_reference_to_wire(sup.value),
                span: span_to_wire(sup.span),
            })
            .collect(),
        assoc_types: v
            .assoc_types
            .iter()
            .map(|(name, id)| (symbols.intern_symbol(*name), def_to_wire(*id)))
            .collect(),
    }
}

pub fn interface_def_from_wire<'a>(
    gcx: GlobalContext<'a>,
    v: &InterfaceDefinitionWire,
    remap: FileRemap<'_>,
    symbols: SymbolTableRef<'_>,
) -> InterfaceDefinition<'a> {
    InterfaceDefinition {
        id: def_from_wire(&v.id),
        superfaces: v
            .superfaces
            .iter()
            .map(|sup| Spanned {
                value: interface_reference_from_wire(gcx, &sup.value),
                span: span_from_wire(&sup.span, remap),
            })
            .collect(),
        assoc_types: v
            .assoc_types
            .iter()
            .map(|(name, id)| (Symbol::new(symbols.resolve_str(*name)), def_from_wire(id)))
            .collect(),
    }
}

pub fn interface_requirements_to_wire(
    v: &InterfaceRequirements<'_>,
    symbols: &mut SymbolTableBuilder,
) -> InterfaceRequirementsWire {
    InterfaceRequirementsWire {
        methods: v
            .methods
            .iter()
            .map(|method| InterfaceMethodRequirementWire {
                id: def_to_wire(method.id),
                name: symbols.intern_symbol(method.name),
                signature: signature_to_wire(method.signature),
                has_self: method.has_self,
                is_required: method.is_required,
            })
            .collect(),
        types: v
            .types
            .iter()
            .map(|ty| AssociatedTypeDefinitionWire {
                id: def_to_wire(ty.id),
                name: symbols.intern_symbol(ty.name),
                default_type: ty.default_type.map(ty_to_wire),
            })
            .collect(),
        constants: v
            .constants
            .iter()
            .map(|constant| InterfaceConstantRequirementWire {
                id: def_to_wire(constant.id),
                name: symbols.intern_symbol(constant.name),
                ty: ty_to_wire(constant.ty),
                default: constant.default.map(const_to_wire),
            })
            .collect(),
    }
}

pub fn interface_requirements_from_wire<'a>(
    gcx: GlobalContext<'a>,
    v: &InterfaceRequirementsWire,
    symbols: SymbolTableRef<'_>,
) -> InterfaceRequirements<'a> {
    InterfaceRequirements {
        methods: v
            .methods
            .iter()
            .map(|method| {
                let signature = gcx
                    .store
                    .arenas
                    .function_signatures
                    .alloc(signature_from_wire(gcx, &method.signature));
                InterfaceMethodRequirement {
                    id: def_from_wire(&method.id),
                    name: Symbol::new(symbols.resolve_str(method.name)),
                    signature,
                    has_self: method.has_self,
                    is_required: method.is_required,
                }
            })
            .collect(),
        types: v
            .types
            .iter()
            .map(|ty| AssociatedTypeDefinition {
                id: def_from_wire(&ty.id),
                name: Symbol::new(symbols.resolve_str(ty.name)),
                default_type: ty.default_type.as_ref().map(|ty| ty_from_wire(gcx, ty)),
            })
            .collect(),
        constants: v
            .constants
            .iter()
            .map(|constant| InterfaceConstantRequirement {
                id: def_from_wire(&constant.id),
                name: Symbol::new(symbols.resolve_str(constant.name)),
                ty: ty_from_wire(gcx, &constant.ty),
                default: constant.default.as_ref().map(|v| const_from_wire(gcx, v)),
            })
            .collect(),
    }
}

pub fn conformance_id_to_wire(v: ConformanceRecordId) -> ConformanceRecordIdWire {
    ConformanceRecordIdWire {
        package: v.package.raw(),
        index: v.index,
    }
}

pub fn conformance_id_from_wire(v: &ConformanceRecordIdWire) -> ConformanceRecordId {
    ConformanceRecordId::new(PackageIndex::new(v.package as usize), v.index)
}

pub fn conformance_record_to_wire(v: ConformanceRecord<'_>) -> ConformanceRecordWire {
    ConformanceRecordWire {
        target: type_head_to_wire(v.target),
        interface: interface_reference_to_wire(v.interface),
        extension: def_to_wire(v.extension),
        location: span_to_wire(v.location),
        is_conditional: v.is_conditional,
        is_inline: v.is_inline,
    }
}

pub fn conformance_record_from_wire<'a>(
    gcx: GlobalContext<'a>,
    v: &ConformanceRecordWire,
    remap: FileRemap<'_>,
) -> ConformanceRecord<'a> {
    ConformanceRecord {
        target: type_head_from_wire(&v.target),
        interface: interface_reference_from_wire(gcx, &v.interface),
        extension: def_from_wire(&v.extension),
        location: span_from_wire(&v.location, remap),
        is_conditional: v.is_conditional,
        is_inline: v.is_inline,
    }
}

pub fn member_set_to_wire(v: &crate::compile::context::MemberSet) -> MemberSetWire {
    MemberSetWire {
        members: v.members.iter().copied().map(def_to_wire).collect(),
        fingerprints: v
            .fingerprints
            .iter()
            .map(|(fp, id)| (*fp, def_to_wire(*id)))
            .collect(),
    }
}

pub fn member_set_from_wire(v: &MemberSetWire) -> crate::compile::context::MemberSet {
    crate::compile::context::MemberSet {
        members: v.members.iter().map(def_from_wire).collect(),
        fingerprints: v
            .fingerprints
            .iter()
            .map(|(fp, id)| (*fp, def_from_wire(id)))
            .collect(),
    }
}

pub fn type_member_index_to_wire(
    v: &crate::compile::context::TypeMemberIndex,
    symbols: &mut SymbolTableBuilder,
) -> TypeMemberIndexWire {
    TypeMemberIndexWire {
        inherent_static: v
            .inherent_static
            .iter()
            .map(|(name, set)| (symbols.intern_symbol(*name), member_set_to_wire(set)))
            .collect(),
        inherent_instance: v
            .inherent_instance
            .iter()
            .map(|(name, set)| (symbols.intern_symbol(*name), member_set_to_wire(set)))
            .collect(),
        trait_methods: v
            .trait_methods
            .iter()
            .map(|((iface, name), set)| {
                (
                    (def_to_wire(*iface), symbols.intern_symbol(*name)),
                    member_set_to_wire(set),
                )
            })
            .collect(),
        trait_methods_by_name: v
            .trait_methods_by_name
            .iter()
            .map(|(name, ids)| {
                (
                    symbols.intern_symbol(*name),
                    ids.iter().copied().map(def_to_wire).collect(),
                )
            })
            .collect(),
        operators: v
            .operators
            .iter()
            .map(|(op, set)| (operator_kind_to_wire(*op), member_set_to_wire(set)))
            .collect(),
    }
}

pub fn type_member_index_from_wire(
    v: &TypeMemberIndexWire,
    symbols: SymbolTableRef<'_>,
) -> crate::compile::context::TypeMemberIndex {
    crate::compile::context::TypeMemberIndex {
        inherent_static: v
            .inherent_static
            .iter()
            .map(|(name, set)| {
                (
                    Symbol::new(symbols.resolve_str(*name)),
                    member_set_from_wire(set),
                )
            })
            .collect(),
        inherent_instance: v
            .inherent_instance
            .iter()
            .map(|(name, set)| {
                (
                    Symbol::new(symbols.resolve_str(*name)),
                    member_set_from_wire(set),
                )
            })
            .collect(),
        trait_methods: v
            .trait_methods
            .iter()
            .map(|((iface, name), set)| {
                (
                    (
                        def_from_wire(iface),
                        Symbol::new(symbols.resolve_str(*name)),
                    ),
                    member_set_from_wire(set),
                )
            })
            .collect(),
        trait_methods_by_name: v
            .trait_methods_by_name
            .iter()
            .map(|(name, ids)| {
                (
                    Symbol::new(symbols.resolve_str(*name)),
                    ids.iter().map(def_from_wire).collect::<Vec<_>>(),
                )
            })
            .collect(),
        operators: v
            .operators
            .iter()
            .map(|(op, set)| (operator_kind_from_wire(op), member_set_from_wire(set)))
            .collect(),
    }
}

pub fn alias_table_to_wire(
    v: &PackageAliasTable,
    symbols: &mut SymbolTableBuilder,
) -> PackageAliasTableWire {
    PackageAliasTableWire {
        aliases: v
            .aliases
            .iter()
            .map(|(id, alias)| {
                (
                    def_to_wire(*id),
                    AliasDefinitionWire {
                        id: def_to_wire(alias.id),
                        name: symbols.intern_symbol(alias.name),
                        kind: alias_kind_to_wire(alias.kind),
                        span: span_to_wire(alias.span),
                        extension_id: alias.extension_id.map(def_to_wire),
                    },
                )
            })
            .collect(),
        by_type: v
            .by_type
            .iter()
            .map(|(head, bucket)| {
                (
                    type_head_to_wire(*head),
                    AliasBucketWire {
                        aliases: bucket
                            .aliases
                            .iter()
                            .map(|(name, entries)| {
                                (
                                    symbols.intern_symbol(*name),
                                    entries
                                        .iter()
                                        .map(|(id, span)| (def_to_wire(*id), span_to_wire(*span)))
                                        .collect(),
                                )
                            })
                            .collect(),
                    },
                )
            })
            .collect(),
    }
}

pub fn alias_table_from_wire(
    v: &PackageAliasTableWire,
    remap: FileRemap<'_>,
    placeholder_span: Span,
    symbols: SymbolTableRef<'_>,
) -> PackageAliasTable {
    PackageAliasTable {
        aliases: v
            .aliases
            .iter()
            .map(|(id, alias)| {
                (
                    def_from_wire(id),
                    AliasDefinition {
                        id: def_from_wire(&alias.id),
                        name: Symbol::new(symbols.resolve_str(alias.name)),
                        kind: alias_kind_from_wire(&alias.kind),
                        span: span_from_wire(&alias.span, remap),
                        ast_ty: dummy_hir_type(placeholder_span),
                        extension_id: alias.extension_id.as_ref().map(def_from_wire),
                    },
                )
            })
            .collect(),
        by_type: v
            .by_type
            .iter()
            .map(|(head, bucket)| {
                (
                    type_head_from_wire(head),
                    crate::sema::models::AliasBucket {
                        aliases: bucket
                            .aliases
                            .iter()
                            .map(|(name, entries)| {
                                (
                                    Symbol::new(symbols.resolve_str(*name)),
                                    entries
                                        .iter()
                                        .map(|(id, span)| {
                                            (def_from_wire(id), span_from_wire(span, remap))
                                        })
                                        .collect(),
                                )
                            })
                            .collect(),
                    },
                )
            })
            .collect(),
    }
}

pub fn escape_summary_to_wire(v: &mir::EscapeSummary) -> EscapeSummaryWire {
    EscapeSummaryWire {
        params: v
            .params
            .iter()
            .map(|param| ParamEscapeInfoWire {
                leaks_to_heap: param.leaks_to_heap,
                flows_to_return: param.flows_to_return,
            })
            .collect(),
    }
}

pub fn escape_summary_from_wire(v: &EscapeSummaryWire) -> mir::EscapeSummary {
    mir::EscapeSummary {
        params: v
            .params
            .iter()
            .map(|param| mir::ParamEscapeInfo {
                leaks_to_heap: param.leaks_to_heap,
                flows_to_return: param.flows_to_return,
            })
            .collect(),
    }
}

pub fn closure_captures_to_wire(
    v: &ClosureCaptures<'_>,
    symbols: &mut SymbolTableBuilder,
) -> ClosureCapturesWire {
    ClosureCapturesWire {
        captures: v
            .captures
            .iter()
            .map(|capture| CapturedVarWire {
                source_id: hir_node_to_wire(capture.source_id),
                name: symbols.intern_symbol(capture.name),
                ty: ty_to_wire(capture.ty),
                capture_kind: capture_kind_to_wire(capture.capture_kind),
                field_index: capture.field_index.index() as u32,
            })
            .collect(),
        kind: closure_kind_to_wire(v.kind),
    }
}

pub fn closure_captures_from_wire<'a>(
    gcx: GlobalContext<'a>,
    v: &ClosureCapturesWire,
    symbols: SymbolTableRef<'_>,
) -> ClosureCaptures<'a> {
    ClosureCaptures {
        captures: v
            .captures
            .iter()
            .map(|capture| CapturedVar {
                source_id: hir_node_from_wire(capture.source_id),
                name: Symbol::new(symbols.resolve_str(capture.name)),
                ty: ty_from_wire(gcx, &capture.ty),
                capture_kind: capture_kind_from_wire(&capture.capture_kind),
                field_index: crate::thir::FieldIndex::from_raw(capture.field_index),
            })
            .collect(),
        kind: closure_kind_from_wire(&v.kind),
    }
}

pub fn synthetic_method_info_to_wire(
    v: &SyntheticMethodInfo<'_>,
    symbols: &mut SymbolTableBuilder,
) -> SyntheticMethodInfoWire {
    SyntheticMethodInfoWire {
        kind: match v.kind {
            SyntheticMethodKind::CopyClone => SyntheticMethodKindWire::CopyClone,
            SyntheticMethodKind::MemberwiseClone => SyntheticMethodKindWire::MemberwiseClone,
            SyntheticMethodKind::MemberwiseHash => SyntheticMethodKindWire::MemberwiseHash,
            SyntheticMethodKind::MemberwiseEquality => SyntheticMethodKindWire::MemberwiseEquality,
            SyntheticMethodKind::ClosureCall => SyntheticMethodKindWire::ClosureCall,
            SyntheticMethodKind::ClosureCallMut => SyntheticMethodKindWire::ClosureCallMut,
            SyntheticMethodKind::ClosureCallOnce => SyntheticMethodKindWire::ClosureCallOnce,
        },
        self_ty: ty_to_wire(v.self_ty),
        interface_id: def_to_wire(v.interface_id),
        interface_args: v
            .interface_args
            .iter()
            .copied()
            .map(generic_arg_to_wire)
            .collect(),
        interface_bindings: v
            .interface_bindings
            .iter()
            .map(|binding| AssociatedTypeBindingWire {
                name: binding.name.as_str().to_string(),
                ty: ty_to_wire(binding.ty),
            })
            .collect(),
        method_id: def_to_wire(v.method_id),
        method_name: symbols.intern_symbol(v.method_name),
        syn_id: v.syn_id.map(def_to_wire),
    }
}

pub fn synthetic_method_info_from_wire<'a>(
    gcx: GlobalContext<'a>,
    v: &SyntheticMethodInfoWire,
    symbols: SymbolTableRef<'_>,
) -> SyntheticMethodInfo<'a> {
    let interface_args: Vec<_> = v
        .interface_args
        .iter()
        .map(|arg| generic_arg_from_wire(gcx, arg))
        .collect();
    let interface_bindings: Vec<_> = v
        .interface_bindings
        .iter()
        .map(|binding| AssociatedTypeBinding {
            name: Symbol::new(&binding.name),
            ty: ty_from_wire(gcx, &binding.ty),
        })
        .collect();

    SyntheticMethodInfo {
        kind: match v.kind {
            SyntheticMethodKindWire::CopyClone => SyntheticMethodKind::CopyClone,
            SyntheticMethodKindWire::MemberwiseClone => SyntheticMethodKind::MemberwiseClone,
            SyntheticMethodKindWire::MemberwiseHash => SyntheticMethodKind::MemberwiseHash,
            SyntheticMethodKindWire::MemberwiseEquality => SyntheticMethodKind::MemberwiseEquality,
            SyntheticMethodKindWire::ClosureCall => SyntheticMethodKind::ClosureCall,
            SyntheticMethodKindWire::ClosureCallMut => SyntheticMethodKind::ClosureCallMut,
            SyntheticMethodKindWire::ClosureCallOnce => SyntheticMethodKind::ClosureCallOnce,
        },
        self_ty: ty_from_wire(gcx, &v.self_ty),
        interface_id: def_from_wire(&v.interface_id),
        interface_args: gcx.store.interners.intern_generic_args(interface_args),
        interface_bindings: gcx
            .store
            .arenas
            .global
            .alloc_slice_copy(&interface_bindings),
        method_id: def_from_wire(&v.method_id),
        method_name: Symbol::new(symbols.resolve_str(v.method_name)),
        syn_id: v.syn_id.as_ref().map(def_from_wire),
    }
}

pub fn instance_to_wire(v: Instance<'_>) -> InstanceWire {
    InstanceWire {
        kind: match v.kind {
            InstanceKind::Item(id) => InstanceKindWire::Item(def_to_wire(id)),
            InstanceKind::Virtual(virtual_call) => InstanceKindWire::Virtual(VirtualInstanceWire {
                method_id: def_to_wire(virtual_call.method_id),
                method_interface: def_to_wire(virtual_call.method_interface),
                slot: virtual_call.slot as u32,
                table_index: virtual_call.table_index as u32,
            }),
        },
        args: v.args.iter().copied().map(generic_arg_to_wire).collect(),
    }
}

pub fn instance_from_wire<'a>(gcx: GlobalContext<'a>, v: &InstanceWire) -> Instance<'a> {
    let args: Vec<_> = v
        .args
        .iter()
        .map(|arg| generic_arg_from_wire(gcx, arg))
        .collect();
    let kind = match &v.kind {
        InstanceKindWire::Item(id) => InstanceKind::Item(def_from_wire(id)),
        InstanceKindWire::Virtual(virtual_call) => InstanceKind::Virtual(VirtualInstance {
            method_id: def_from_wire(&virtual_call.method_id),
            method_interface: def_from_wire(&virtual_call.method_interface),
            slot: virtual_call.slot as usize,
            table_index: virtual_call.table_index as usize,
        }),
    };
    Instance {
        kind,
        args: gcx.store.interners.intern_generic_args(args),
    }
}

pub fn std_registry_to_wire(registry: &StdItemRegistry) -> StdItemRegistryWire {
    StdItemRegistryWire {
        entries: registry
            .entries()
            .map(|(item, entry)| {
                (
                    std_item_to_wire(item),
                    StdItemEntryWire {
                        def_id: def_to_wire(entry.def_id),
                        def_kind: definition_kind_to_wire(entry.def_kind),
                        span: span_to_wire(entry.span),
                    },
                )
            })
            .collect(),
    }
}

pub fn std_registry_from_wire(wire: &StdItemRegistryWire, remap: FileRemap<'_>) -> StdItemRegistry {
    let entries: Vec<_> = wire
        .entries
        .iter()
        .map(|(item, entry)| {
            (
                std_item_from_wire(item),
                StdItemEntry {
                    def_id: def_from_wire(&entry.def_id),
                    def_kind: definition_kind_from_wire(&entry.def_kind),
                    span: span_from_wire(&entry.span, remap),
                },
            )
        })
        .collect();
    StdItemRegistry::from_entries(entries)
}

pub fn synthetic_definition_to_wire(
    id: DefinitionID,
    v: &SyntheticDefinition<'_>,
) -> SyntheticDefinitionWire {
    SyntheticDefinitionWire {
        id: def_to_wire(id),
        name: v.name.as_str().to_string(),
        generics: generics_to_wire(v.generics),
        signature: signature_to_wire(v.signature),
        span: span_to_wire(v.span),
    }
}

pub fn synthetic_definition_from_wire<'a>(
    gcx: GlobalContext<'a>,
    v: &SyntheticDefinitionWire,
    remap: FileRemap<'_>,
) -> (DefinitionID, SyntheticDefinition<'a>) {
    let placeholder_file = remap
        .old_to_new
        .values()
        .copied()
        .next()
        .unwrap_or_else(|| FileID::from_raw(0));
    let placeholder_span = Span::empty(placeholder_file);
    let generics: &'a Generics = gcx
        .store
        .arenas
        .generics
        .alloc(generics_from_wire(&v.generics, placeholder_span));
    let signature: &'a LabeledFunctionSignature<'a> = gcx
        .store
        .arenas
        .function_signatures
        .alloc(signature_from_wire(gcx, &v.signature));

    (
        def_from_wire(&v.id),
        SyntheticDefinition {
            name: Symbol::new(&v.name),
            generics,
            signature,
            span: span_from_wire(&v.span, remap),
        },
    )
}

#[inline]
pub fn local_kind_to_wire(v: mir::LocalKind) -> LocalKindWire {
    match v {
        mir::LocalKind::Param => LocalKindWire::Param,
        mir::LocalKind::User => LocalKindWire::User,
        mir::LocalKind::Temp => LocalKindWire::Temp,
        mir::LocalKind::Return => LocalKindWire::Return,
    }
}

#[inline]
pub fn local_kind_from_wire(v: &LocalKindWire) -> mir::LocalKind {
    match v {
        LocalKindWire::Param => mir::LocalKind::Param,
        LocalKindWire::User => mir::LocalKind::User,
        LocalKindWire::Temp => mir::LocalKind::Temp,
        LocalKindWire::Return => mir::LocalKind::Return,
    }
}

#[inline]
pub fn mir_phase_to_wire(v: mir::MirPhase) -> MirPhaseWire {
    match v {
        mir::MirPhase::Built => MirPhaseWire::Built,
        mir::MirPhase::CfgClean => MirPhaseWire::CfgClean,
        mir::MirPhase::Lowered => MirPhaseWire::Lowered,
    }
}

#[inline]
pub fn mir_phase_from_wire(v: &MirPhaseWire) -> mir::MirPhase {
    match v {
        MirPhaseWire::Built => mir::MirPhase::Built,
        MirPhaseWire::CfgClean => mir::MirPhase::CfgClean,
        MirPhaseWire::Lowered => mir::MirPhase::Lowered,
    }
}

#[inline]
pub fn unary_op_to_wire(v: mir::UnaryOperator) -> UnaryOperatorWire {
    match v {
        mir::UnaryOperator::LogicalNot => UnaryOperatorWire::LogicalNot,
        mir::UnaryOperator::Negate => UnaryOperatorWire::Negate,
        mir::UnaryOperator::BitwiseNot => UnaryOperatorWire::BitwiseNot,
    }
}

#[inline]
pub fn unary_op_from_wire(v: &UnaryOperatorWire) -> mir::UnaryOperator {
    match v {
        UnaryOperatorWire::LogicalNot => mir::UnaryOperator::LogicalNot,
        UnaryOperatorWire::Negate => mir::UnaryOperator::Negate,
        UnaryOperatorWire::BitwiseNot => mir::UnaryOperator::BitwiseNot,
    }
}

#[inline]
pub fn binary_op_to_wire(v: mir::BinaryOperator) -> BinaryOperatorWire {
    match v {
        mir::BinaryOperator::Add => BinaryOperatorWire::Add,
        mir::BinaryOperator::Sub => BinaryOperatorWire::Sub,
        mir::BinaryOperator::Mul => BinaryOperatorWire::Mul,
        mir::BinaryOperator::Div => BinaryOperatorWire::Div,
        mir::BinaryOperator::Rem => BinaryOperatorWire::Rem,
        mir::BinaryOperator::BitAnd => BinaryOperatorWire::BitAnd,
        mir::BinaryOperator::BitOr => BinaryOperatorWire::BitOr,
        mir::BinaryOperator::BitXor => BinaryOperatorWire::BitXor,
        mir::BinaryOperator::BitShl => BinaryOperatorWire::BitShl,
        mir::BinaryOperator::BitShr => BinaryOperatorWire::BitShr,
        mir::BinaryOperator::Eql => BinaryOperatorWire::Eql,
        mir::BinaryOperator::Lt => BinaryOperatorWire::Lt,
        mir::BinaryOperator::Gt => BinaryOperatorWire::Gt,
        mir::BinaryOperator::Leq => BinaryOperatorWire::Leq,
        mir::BinaryOperator::Geq => BinaryOperatorWire::Geq,
        mir::BinaryOperator::Neq => BinaryOperatorWire::Neq,
    }
}

#[inline]
pub fn binary_op_from_wire(v: &BinaryOperatorWire) -> mir::BinaryOperator {
    match v {
        BinaryOperatorWire::Add => mir::BinaryOperator::Add,
        BinaryOperatorWire::Sub => mir::BinaryOperator::Sub,
        BinaryOperatorWire::Mul => mir::BinaryOperator::Mul,
        BinaryOperatorWire::Div => mir::BinaryOperator::Div,
        BinaryOperatorWire::Rem => mir::BinaryOperator::Rem,
        BinaryOperatorWire::BitAnd => mir::BinaryOperator::BitAnd,
        BinaryOperatorWire::BitOr => mir::BinaryOperator::BitOr,
        BinaryOperatorWire::BitXor => mir::BinaryOperator::BitXor,
        BinaryOperatorWire::BitShl => mir::BinaryOperator::BitShl,
        BinaryOperatorWire::BitShr => mir::BinaryOperator::BitShr,
        BinaryOperatorWire::Eql => mir::BinaryOperator::Eql,
        BinaryOperatorWire::Lt => mir::BinaryOperator::Lt,
        BinaryOperatorWire::Gt => mir::BinaryOperator::Gt,
        BinaryOperatorWire::Leq => mir::BinaryOperator::Leq,
        BinaryOperatorWire::Geq => mir::BinaryOperator::Geq,
        BinaryOperatorWire::Neq => mir::BinaryOperator::Neq,
    }
}

pub fn place_to_wire(v: &mir::Place<'_>) -> PlaceWire {
    PlaceWire {
        local: v.local.index() as u32,
        projection: v
            .projection
            .iter()
            .map(|elem| match elem {
                mir::PlaceElem::Deref => PlaceElemWire::Deref,
                mir::PlaceElem::Field(index, ty) => {
                    PlaceElemWire::Field(index.index() as u32, ty_to_wire(*ty))
                }
                mir::PlaceElem::VariantDowncast { name, index } => PlaceElemWire::VariantDowncast {
                    name: name.as_str().to_string(),
                    index: index.index() as u32,
                },
            })
            .collect(),
    }
}

pub fn place_from_wire<'a>(gcx: GlobalContext<'a>, v: &PlaceWire) -> mir::Place<'a> {
    mir::Place {
        local: mir::LocalId::from_raw(v.local),
        projection: v
            .projection
            .iter()
            .map(|elem| match elem {
                PlaceElemWire::Deref => mir::PlaceElem::Deref,
                PlaceElemWire::Field(index, ty) => mir::PlaceElem::Field(
                    crate::thir::FieldIndex::from_raw(*index),
                    ty_from_wire(gcx, ty),
                ),
                PlaceElemWire::VariantDowncast { name, index } => mir::PlaceElem::VariantDowncast {
                    name: Symbol::new(name),
                    index: crate::thir::VariantIndex::from_raw(*index),
                },
            })
            .collect(),
    }
}

pub fn mir_constant_to_wire(v: &mir::Constant<'_>) -> ConstantWire {
    ConstantWire {
        ty: ty_to_wire(v.ty),
        value: match &v.value {
            mir::ConstantKind::Bool(v) => ConstantKindWire::Bool(*v),
            mir::ConstantKind::Rune(v) => ConstantKindWire::Rune(*v),
            mir::ConstantKind::String(v) => ConstantKindWire::String(v.as_str().to_string()),
            mir::ConstantKind::Integer(v) => ConstantKindWire::Integer(*v),
            mir::ConstantKind::Float(v) => ConstantKindWire::Float(*v),
            mir::ConstantKind::Unit => ConstantKindWire::Unit,
            mir::ConstantKind::Function(id, args, ty) => ConstantKindWire::Function(
                def_to_wire(*id),
                args.iter().copied().map(generic_arg_to_wire).collect(),
                ty_to_wire(*ty),
            ),
            mir::ConstantKind::ConstParam(param) => {
                ConstantKindWire::ConstParam(generic_param_to_wire(*param))
            }
        },
    }
}

pub fn mir_constant_from_wire<'a>(gcx: GlobalContext<'a>, v: &ConstantWire) -> mir::Constant<'a> {
    mir::Constant {
        ty: ty_from_wire(gcx, &v.ty),
        value: match &v.value {
            ConstantKindWire::Bool(v) => mir::ConstantKind::Bool(*v),
            ConstantKindWire::Rune(v) => mir::ConstantKind::Rune(*v),
            ConstantKindWire::String(v) => mir::ConstantKind::String(Symbol::new(v)),
            ConstantKindWire::Integer(v) => mir::ConstantKind::Integer(*v),
            ConstantKindWire::Float(v) => mir::ConstantKind::Float(*v),
            ConstantKindWire::Unit => mir::ConstantKind::Unit,
            ConstantKindWire::Function(id, args, ty) => {
                let args: Vec<_> = args
                    .iter()
                    .map(|arg| generic_arg_from_wire(gcx, arg))
                    .collect();
                mir::ConstantKind::Function(
                    def_from_wire(id),
                    gcx.store.interners.intern_generic_args(args),
                    ty_from_wire(gcx, ty),
                )
            }
            ConstantKindWire::ConstParam(param) => {
                mir::ConstantKind::ConstParam(generic_param_from_wire(param))
            }
        },
    }
}

pub fn operand_to_wire(v: &mir::Operand<'_>) -> OperandWire {
    match v {
        mir::Operand::Copy(v) => OperandWire::Copy(place_to_wire(v)),
        mir::Operand::Move(v) => OperandWire::Move(place_to_wire(v)),
        mir::Operand::Constant(v) => OperandWire::Constant(mir_constant_to_wire(v)),
    }
}

pub fn operand_from_wire<'a>(gcx: GlobalContext<'a>, v: &OperandWire) -> mir::Operand<'a> {
    match v {
        OperandWire::Copy(v) => mir::Operand::Copy(place_from_wire(gcx, v)),
        OperandWire::Move(v) => mir::Operand::Move(place_from_wire(gcx, v)),
        OperandWire::Constant(v) => mir::Operand::Constant(mir_constant_from_wire(gcx, v)),
    }
}

pub fn cast_kind_to_wire(v: &mir::CastKind<'_>) -> CastKindWire {
    match v {
        mir::CastKind::Numeric => CastKindWire::Numeric,
        mir::CastKind::BoxExistential => CastKindWire::BoxExistential,
        mir::CastKind::ExistentialUpcast => CastKindWire::ExistentialUpcast,
        mir::CastKind::ExistentialTypeIs { target } => CastKindWire::ExistentialTypeIs {
            target: ty_to_wire(*target),
        },
        mir::CastKind::ExistentialTryCast { target } => CastKindWire::ExistentialTryCast {
            target: ty_to_wire(*target),
        },
        mir::CastKind::Pointer => CastKindWire::Pointer,
        mir::CastKind::ClosureToFnPointer => CastKindWire::ClosureToFnPointer,
    }
}

pub fn cast_kind_from_wire<'a>(gcx: GlobalContext<'a>, v: &CastKindWire) -> mir::CastKind<'a> {
    match v {
        CastKindWire::Numeric => mir::CastKind::Numeric,
        CastKindWire::BoxExistential => mir::CastKind::BoxExistential,
        CastKindWire::ExistentialUpcast => mir::CastKind::ExistentialUpcast,
        CastKindWire::ExistentialTypeIs { target } => mir::CastKind::ExistentialTypeIs {
            target: ty_from_wire(gcx, target),
        },
        CastKindWire::ExistentialTryCast { target } => mir::CastKind::ExistentialTryCast {
            target: ty_from_wire(gcx, target),
        },
        CastKindWire::Pointer => mir::CastKind::Pointer,
        CastKindWire::ClosureToFnPointer => mir::CastKind::ClosureToFnPointer,
    }
}

pub fn aggregate_kind_to_wire(v: &mir::AggregateKind<'_>) -> AggregateKindWire {
    match v {
        mir::AggregateKind::Tuple => AggregateKindWire::Tuple,
        mir::AggregateKind::Adt {
            def_id,
            variant_index,
            generic_args,
        } => AggregateKindWire::Adt {
            def_id: def_to_wire(*def_id),
            variant_index: variant_index.map(|v| v.index() as u32),
            generic_args: generic_args
                .iter()
                .copied()
                .map(generic_arg_to_wire)
                .collect(),
        },
        mir::AggregateKind::Array { len, element } => AggregateKindWire::Array {
            len: *len as u32,
            element: ty_to_wire(*element),
        },
        mir::AggregateKind::Closure {
            def_id,
            captured_generics,
        } => AggregateKindWire::Closure {
            def_id: def_to_wire(*def_id),
            captured_generics: captured_generics
                .iter()
                .copied()
                .map(generic_arg_to_wire)
                .collect(),
        },
    }
}

pub fn aggregate_kind_from_wire<'a>(
    gcx: GlobalContext<'a>,
    v: &AggregateKindWire,
) -> mir::AggregateKind<'a> {
    match v {
        AggregateKindWire::Tuple => mir::AggregateKind::Tuple,
        AggregateKindWire::Adt {
            def_id,
            variant_index,
            generic_args,
        } => {
            let generic_args: Vec<_> = generic_args
                .iter()
                .map(|arg| generic_arg_from_wire(gcx, arg))
                .collect();
            mir::AggregateKind::Adt {
                def_id: def_from_wire(def_id),
                variant_index: variant_index.map(|v| crate::thir::VariantIndex::from_raw(v)),
                generic_args: gcx.store.interners.intern_generic_args(generic_args),
            }
        }
        AggregateKindWire::Array { len, element } => mir::AggregateKind::Array {
            len: *len as usize,
            element: ty_from_wire(gcx, element),
        },
        AggregateKindWire::Closure {
            def_id,
            captured_generics,
        } => {
            let captured_generics: Vec<_> = captured_generics
                .iter()
                .map(|arg| generic_arg_from_wire(gcx, arg))
                .collect();
            mir::AggregateKind::Closure {
                def_id: def_from_wire(def_id),
                captured_generics: gcx.store.interners.intern_generic_args(captured_generics),
            }
        }
    }
}

pub fn rvalue_to_wire(v: &mir::Rvalue<'_>) -> RvalueWire {
    match v {
        mir::Rvalue::Use(v) => RvalueWire::Use(operand_to_wire(v)),
        mir::Rvalue::UnaryOp { op, operand } => RvalueWire::UnaryOp {
            op: unary_op_to_wire(*op),
            operand: operand_to_wire(operand),
        },
        mir::Rvalue::BinaryOp { op, lhs, rhs } => RvalueWire::BinaryOp {
            op: binary_op_to_wire(*op),
            lhs: operand_to_wire(lhs),
            rhs: operand_to_wire(rhs),
        },
        mir::Rvalue::Cast { operand, ty, kind } => RvalueWire::Cast {
            operand: operand_to_wire(operand),
            ty: ty_to_wire(*ty),
            kind: cast_kind_to_wire(kind),
        },
        mir::Rvalue::Ref { mutable, place } => RvalueWire::Ref {
            mutable: *mutable,
            place: place_to_wire(place),
        },
        mir::Rvalue::Discriminant { place } => RvalueWire::Discriminant {
            place: place_to_wire(place),
        },
        mir::Rvalue::Alloc { ty } => RvalueWire::Alloc {
            ty: ty_to_wire(*ty),
        },
        mir::Rvalue::Aggregate { kind, fields } => RvalueWire::Aggregate {
            kind: aggregate_kind_to_wire(kind),
            fields: fields.iter().map(operand_to_wire).collect(),
        },
        mir::Rvalue::Repeat {
            operand,
            count,
            element,
        } => RvalueWire::Repeat {
            operand: operand_to_wire(operand),
            count: *count as u32,
            element: ty_to_wire(*element),
        },
    }
}

pub fn rvalue_from_wire<'a>(gcx: GlobalContext<'a>, v: &RvalueWire) -> mir::Rvalue<'a> {
    match v {
        RvalueWire::Use(v) => mir::Rvalue::Use(operand_from_wire(gcx, v)),
        RvalueWire::UnaryOp { op, operand } => mir::Rvalue::UnaryOp {
            op: unary_op_from_wire(op),
            operand: operand_from_wire(gcx, operand),
        },
        RvalueWire::BinaryOp { op, lhs, rhs } => mir::Rvalue::BinaryOp {
            op: binary_op_from_wire(op),
            lhs: operand_from_wire(gcx, lhs),
            rhs: operand_from_wire(gcx, rhs),
        },
        RvalueWire::Cast { operand, ty, kind } => mir::Rvalue::Cast {
            operand: operand_from_wire(gcx, operand),
            ty: ty_from_wire(gcx, ty),
            kind: cast_kind_from_wire(gcx, kind),
        },
        RvalueWire::Ref { mutable, place } => mir::Rvalue::Ref {
            mutable: *mutable,
            place: place_from_wire(gcx, place),
        },
        RvalueWire::Discriminant { place } => mir::Rvalue::Discriminant {
            place: place_from_wire(gcx, place),
        },
        RvalueWire::Alloc { ty } => mir::Rvalue::Alloc {
            ty: ty_from_wire(gcx, ty),
        },
        RvalueWire::Aggregate { kind, fields } => {
            let fields: Vec<_> = fields
                .iter()
                .map(|field| operand_from_wire(gcx, field))
                .collect();
            mir::Rvalue::Aggregate {
                kind: aggregate_kind_from_wire(gcx, kind),
                fields: fields.into_iter().collect(),
            }
        }
        RvalueWire::Repeat {
            operand,
            count,
            element,
        } => mir::Rvalue::Repeat {
            operand: operand_from_wire(gcx, operand),
            count: *count as usize,
            element: ty_from_wire(gcx, element),
        },
    }
}

pub fn statement_to_wire(v: &mir::Statement<'_>) -> StatementWire {
    StatementWire {
        kind: match &v.kind {
            mir::StatementKind::Assign(place, rvalue) => {
                StatementKindWire::Assign(place_to_wire(place), rvalue_to_wire(rvalue))
            }
            mir::StatementKind::GcSafepoint => StatementKindWire::GcSafepoint,
            mir::StatementKind::Nop => StatementKindWire::Nop,
            mir::StatementKind::SetDiscriminant {
                place,
                variant_index,
            } => StatementKindWire::SetDiscriminant {
                place: place_to_wire(place),
                variant_index: variant_index.index() as u32,
            },
        },
        span: span_to_wire(v.span),
    }
}

pub fn statement_from_wire<'a>(
    gcx: GlobalContext<'a>,
    v: &StatementWire,
    remap: FileRemap<'_>,
) -> mir::Statement<'a> {
    mir::Statement {
        kind: match &v.kind {
            StatementKindWire::Assign(place, rvalue) => mir::StatementKind::Assign(
                place_from_wire(gcx, place),
                rvalue_from_wire(gcx, rvalue),
            ),
            StatementKindWire::GcSafepoint => mir::StatementKind::GcSafepoint,
            StatementKindWire::Nop => mir::StatementKind::Nop,
            StatementKindWire::SetDiscriminant {
                place,
                variant_index,
            } => mir::StatementKind::SetDiscriminant {
                place: place_from_wire(gcx, place),
                variant_index: crate::thir::VariantIndex::from_raw(*variant_index),
            },
        },
        span: span_from_wire(&v.span, remap),
    }
}

#[inline]
pub fn unwind_to_wire(v: mir::CallUnwindAction) -> CallUnwindActionWire {
    match v {
        mir::CallUnwindAction::Cleanup(v) => CallUnwindActionWire::Cleanup(v.index() as u32),
        mir::CallUnwindAction::Terminate => CallUnwindActionWire::Terminate,
    }
}

#[inline]
pub fn unwind_from_wire(v: &CallUnwindActionWire) -> mir::CallUnwindAction {
    match v {
        CallUnwindActionWire::Cleanup(v) => {
            mir::CallUnwindAction::Cleanup(mir::BasicBlockId::from_raw(*v))
        }
        CallUnwindActionWire::Terminate => mir::CallUnwindAction::Terminate,
    }
}

pub fn terminator_to_wire(v: &mir::Terminator<'_>) -> TerminatorWire {
    TerminatorWire {
        kind: match &v.kind {
            mir::TerminatorKind::Goto { target } => TerminatorKindWire::Goto {
                target: target.index() as u32,
            },
            mir::TerminatorKind::UnresolvedGoto => TerminatorKindWire::UnresolvedGoto,
            mir::TerminatorKind::SwitchInt {
                discr,
                targets,
                otherwise,
            } => TerminatorKindWire::SwitchInt {
                discr: operand_to_wire(discr),
                targets: targets
                    .iter()
                    .map(|(value, target)| (*value, target.index() as u32))
                    .collect(),
                otherwise: otherwise.index() as u32,
            },
            mir::TerminatorKind::Return => TerminatorKindWire::Return,
            mir::TerminatorKind::ResumeUnwind => TerminatorKindWire::ResumeUnwind,
            mir::TerminatorKind::Unreachable => TerminatorKindWire::Unreachable,
            mir::TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                unwind,
            } => TerminatorKindWire::Call {
                func: operand_to_wire(func),
                args: args.iter().map(operand_to_wire).collect(),
                destination: place_to_wire(destination),
                target: target.index() as u32,
                unwind: unwind_to_wire(*unwind),
            },
        },
        span: span_to_wire(v.span),
    }
}

pub fn terminator_from_wire<'a>(
    gcx: GlobalContext<'a>,
    v: &TerminatorWire,
    remap: FileRemap<'_>,
) -> mir::Terminator<'a> {
    mir::Terminator {
        kind: match &v.kind {
            TerminatorKindWire::Goto { target } => mir::TerminatorKind::Goto {
                target: mir::BasicBlockId::from_raw(*target),
            },
            TerminatorKindWire::UnresolvedGoto => mir::TerminatorKind::UnresolvedGoto,
            TerminatorKindWire::SwitchInt {
                discr,
                targets,
                otherwise,
            } => mir::TerminatorKind::SwitchInt {
                discr: operand_from_wire(gcx, discr),
                targets: targets
                    .iter()
                    .map(|(value, target)| (*value, mir::BasicBlockId::from_raw(*target)))
                    .collect(),
                otherwise: mir::BasicBlockId::from_raw(*otherwise),
            },
            TerminatorKindWire::Return => mir::TerminatorKind::Return,
            TerminatorKindWire::ResumeUnwind => mir::TerminatorKind::ResumeUnwind,
            TerminatorKindWire::Unreachable => mir::TerminatorKind::Unreachable,
            TerminatorKindWire::Call {
                func,
                args,
                destination,
                target,
                unwind,
            } => mir::TerminatorKind::Call {
                func: operand_from_wire(gcx, func),
                args: args.iter().map(|arg| operand_from_wire(gcx, arg)).collect(),
                destination: place_from_wire(gcx, destination),
                target: mir::BasicBlockId::from_raw(*target),
                unwind: unwind_from_wire(unwind),
            },
        },
        span: span_from_wire(&v.span, remap),
    }
}

pub fn mir_body_to_wire(v: &mir::Body<'_>) -> BodyWire {
    BodyWire {
        owner: def_to_wire(v.owner),
        locals: v
            .locals
            .iter()
            .map(|local| LocalDeclWire {
                ty: ty_to_wire(local.ty),
                kind: local_kind_to_wire(local.kind),
                mutable: local.mutable,
                name: local.name.map(|v| v.as_str().to_string()),
                span: span_to_wire(local.span),
            })
            .collect(),
        basic_blocks: v
            .basic_blocks
            .iter()
            .map(|block| BasicBlockDataWire {
                note: block.note.clone(),
                statements: block.statements.iter().map(statement_to_wire).collect(),
                terminator: block.terminator.as_ref().map(terminator_to_wire),
            })
            .collect(),
        start_block: v.start_block.index() as u32,
        return_local: v.return_local.index() as u32,
        escape_locals: v.escape_locals.clone(),
        phase: mir_phase_to_wire(v.phase),
    }
}

pub fn mir_body_from_wire<'a>(
    gcx: GlobalContext<'a>,
    v: &BodyWire,
    remap: FileRemap<'_>,
) -> mir::Body<'a> {
    mir::Body {
        owner: def_from_wire(&v.owner),
        locals: v
            .locals
            .iter()
            .map(|local| mir::LocalDecl {
                ty: ty_from_wire(gcx, &local.ty),
                kind: local_kind_from_wire(&local.kind),
                mutable: local.mutable,
                name: local.name.as_ref().map(|v| Symbol::new(v)),
                span: span_from_wire(&local.span, remap),
            })
            .collect(),
        basic_blocks: v
            .basic_blocks
            .iter()
            .map(|block| mir::BasicBlockData {
                note: block.note.clone(),
                statements: block
                    .statements
                    .iter()
                    .map(|statement| statement_from_wire(gcx, statement, remap))
                    .collect(),
                terminator: block
                    .terminator
                    .as_ref()
                    .map(|terminator| terminator_from_wire(gcx, terminator, remap)),
            })
            .collect(),
        start_block: mir::BasicBlockId::from_raw(v.start_block),
        return_local: mir::LocalId::from_raw(v.return_local),
        escape_locals: v.escape_locals.clone(),
        phase: mir_phase_from_wire(&v.phase),
    }
}

pub fn mir_package_to_wire(v: &mir::MirPackage<'_>) -> MirPackageWire {
    mir_package_to_wire_filtered(v, |_, _| true)
}

pub fn mir_package_to_wire_filtered(
    v: &mir::MirPackage<'_>,
    mut include: impl FnMut(DefinitionID, &mir::Body<'_>) -> bool,
) -> MirPackageWire {
    let entry_id = v.entry;
    let mut entry_retained = false;
    let functions: Vec<_> = v
        .functions
        .iter()
        .filter_map(|(id, body)| {
            if include(*id, body) {
                if Some(*id) == entry_id {
                    entry_retained = true;
                }
                Some((def_to_wire(*id), mir_body_to_wire(body)))
            } else {
                None
            }
        })
        .collect();
    let entry = if entry_retained {
        entry_id.map(def_to_wire)
    } else {
        None
    };

    MirPackageWire { functions, entry }
}

pub fn mir_package_from_wire<'a>(
    gcx: GlobalContext<'a>,
    v: &MirPackageWire,
    remap: FileRemap<'_>,
) -> mir::MirPackage<'a> {
    mir::MirPackage {
        functions: v
            .functions
            .iter()
            .map(|(id, body)| {
                let body = mir_body_from_wire(gcx, body, remap);
                let body: &'a mir::Body<'a> = gcx.store.arenas.mir_bodies.alloc(body);
                (def_from_wire(id), body)
            })
            .collect(),
        entry: v.entry.as_ref().map(def_from_wire),
    }
}

fn scope_ptr(scope: crate::sema::resolve::models::Scope<'_>) -> usize {
    scope.0 as *const ScopeData<'_> as usize
}

fn scope_entry_resolution(entry: crate::sema::resolve::models::ScopeEntry<'_>) -> Resolution {
    match &entry.kind {
        crate::sema::resolve::models::ScopeEntryKind::Resolution(resolution) => resolution.clone(),
        crate::sema::resolve::models::ScopeEntryKind::Usage { used_entry, .. } => {
            used_entry.resolution()
        }
    }
}

pub fn resolution_output_to_wire(
    output: &ResolutionOutput<'_>,
    symbols: &mut SymbolTableBuilder,
) -> ResolutionOutputWire {
    fn push_scope<'a>(
        scope: crate::sema::resolve::models::Scope<'a>,
        scope_to_id: &mut FxHashMap<usize, u32>,
        scopes: &mut Vec<crate::sema::resolve::models::Scope<'a>>,
        queue: &mut std::collections::VecDeque<crate::sema::resolve::models::Scope<'a>>,
    ) {
        let ptr = scope_ptr(scope);
        if scope_to_id.contains_key(&ptr) {
            return;
        }
        let id = scopes.len() as u32;
        scope_to_id.insert(ptr, id);
        scopes.push(scope);
        queue.push_back(scope);
    }

    let mut scopes = Vec::new();
    let mut scope_to_id: FxHashMap<usize, u32> = FxHashMap::default();
    let mut queue = std::collections::VecDeque::new();

    push_scope(output.root_scope, &mut scope_to_id, &mut scopes, &mut queue);
    for scope in output.file_scope_mapping.values().copied() {
        push_scope(scope, &mut scope_to_id, &mut scopes, &mut queue);
    }
    for scope in output.definition_scope_mapping.values().copied() {
        push_scope(scope, &mut scope_to_id, &mut scopes, &mut queue);
    }

    while let Some(scope) = queue.pop_front() {
        if let Some(parent) = scope.parent {
            push_scope(parent, &mut scope_to_id, &mut scopes, &mut queue);
        }

        for usage in scope.glob_imports.borrow().iter() {
            if let Some(module_scope) = usage.module_scope.get() {
                push_scope(module_scope, &mut scope_to_id, &mut scopes, &mut queue);
            }
        }
        for usage in scope.glob_exports.borrow().iter() {
            if let Some(module_scope) = usage.module_scope.get() {
                push_scope(module_scope, &mut scope_to_id, &mut scopes, &mut queue);
            }
        }

        let table = scope.table.borrow();
        for entry in table.values() {
            if let Some(entry) = entry.ty {
                if let crate::sema::resolve::models::ScopeEntryKind::Usage {
                    used_scope,
                    user,
                    ..
                } = &entry.kind
                {
                    push_scope(*used_scope, &mut scope_to_id, &mut scopes, &mut queue);
                    if let Some(module_scope) = user.module_scope.get() {
                        push_scope(module_scope, &mut scope_to_id, &mut scopes, &mut queue);
                    }
                }
            }

            for entry in &entry.values {
                if let crate::sema::resolve::models::ScopeEntryKind::Usage {
                    used_scope,
                    user,
                    ..
                } = &entry.kind
                {
                    push_scope(*used_scope, &mut scope_to_id, &mut scopes, &mut queue);
                    if let Some(module_scope) = user.module_scope.get() {
                        push_scope(module_scope, &mut scope_to_id, &mut scopes, &mut queue);
                    }
                }
            }
        }
    }

    let mut scope_wires = Vec::with_capacity(scopes.len());
    for scope in &scopes {
        let mut glob_imports: Vec<_> = scope
            .glob_imports
            .borrow()
            .iter()
            .map(|usage| GlobUsageWire {
                id: match usage.kind {
                    UsageKind::Glob { id } => node_to_wire(id),
                    UsageKind::Single(_) => u32::MAX,
                },
                span: span_to_wire(usage.span),
                module_scope: usage
                    .module_scope
                    .get()
                    .map(|module_scope| scope_to_id[&scope_ptr(module_scope)]),
            })
            .collect();
        glob_imports.sort_by_key(|usage| (usage.module_scope.unwrap_or(u32::MAX), usage.id));

        let mut glob_exports: Vec<_> = scope
            .glob_exports
            .borrow()
            .iter()
            .map(|usage| GlobUsageWire {
                id: match usage.kind {
                    UsageKind::Glob { id } => node_to_wire(id),
                    UsageKind::Single(_) => u32::MAX,
                },
                span: span_to_wire(usage.span),
                module_scope: usage
                    .module_scope
                    .get()
                    .map(|module_scope| scope_to_id[&scope_ptr(module_scope)]),
            })
            .collect();
        glob_exports.sort_by_key(|usage| (usage.module_scope.unwrap_or(u32::MAX), usage.id));

        let mut entries: Vec<_> = scope
            .table
            .borrow()
            .iter()
            .map(|(symbol, entry)| {
                (
                    symbol.as_str().to_string(),
                    entry
                        .ty
                        .map(|entry| resolution_to_wire(&scope_entry_resolution(entry))),
                    entry
                        .values
                        .iter()
                        .map(|entry| resolution_to_wire(&scope_entry_resolution(*entry)))
                        .collect::<Vec<_>>(),
                )
            })
            .collect();
        entries.sort_by(|a, b| a.0.cmp(&b.0));
        let entries = entries
            .into_iter()
            .map(|(symbol, ty, values)| NameEntryWire {
                symbol: symbols.intern_str(&symbol),
                ty,
                values,
            })
            .collect();

        let parent = scope.parent.map(|parent| scope_to_id[&scope_ptr(parent)]);
        scope_wires.push(ScopeWire {
            parent,
            kind: scope_kind_to_wire(scope.kind),
            entries,
            glob_imports,
            glob_exports,
        });
    }

    let mut resolutions: Vec<_> = output
        .resolutions
        .iter()
        .map(|(node, resolution)| (node_to_wire(*node), resolution_state_to_wire(resolution)))
        .collect();
    resolutions.sort_by_key(|(node, _)| *node);

    let mut node_to_definition: Vec<_> = output
        .node_to_definition
        .iter()
        .map(|(node, def)| (node_to_wire(*node), def_to_wire(*def)))
        .collect();
    node_to_definition.sort_by_key(|(node, _)| *node);

    let mut definition_to_kind: Vec<_> = output
        .definition_to_kind
        .iter()
        .map(|(def, kind)| (def_to_wire(*def), definition_kind_to_wire(*kind)))
        .collect();
    definition_to_kind.sort_by_key(|(def, _)| (def.package, def.index));

    let mut definition_to_parent: Vec<_> = output
        .definition_to_parent
        .iter()
        .map(|(def, parent)| (def_to_wire(*def), def_to_wire(*parent)))
        .collect();
    definition_to_parent.sort_by_key(|(def, _)| (def.package, def.index));

    let mut definition_to_ident: Vec<_> = output
        .definition_to_ident
        .iter()
        .map(|(def, ident)| (def_to_wire(*def), identifier_to_wire(*ident, symbols)))
        .collect();
    definition_to_ident.sort_by_key(|(def, _)| (def.package, def.index));

    let mut definition_to_visibility: Vec<_> = output
        .definition_to_visibility
        .iter()
        .map(|(def, vis)| (def_to_wire(*def), visibility_to_wire(*vis)))
        .collect();
    definition_to_visibility.sort_by_key(|(def, _)| (def.package, def.index));

    let mut file_scope_mapping: Vec<_> = output
        .file_scope_mapping
        .iter()
        .map(|(file, scope)| (file.raw(), scope_to_id[&scope_ptr(*scope)]))
        .collect();
    file_scope_mapping.sort_by_key(|(file, _)| *file);

    let mut definition_scope_mapping: Vec<_> = output
        .definition_scope_mapping
        .iter()
        .map(|(def, scope)| (def_to_wire(*def), scope_to_id[&scope_ptr(*scope)]))
        .collect();
    definition_scope_mapping.sort_by_key(|(def, _)| (def.package, def.index));

    let mut expression_resolutions: Vec<_> = output
        .expression_resolutions
        .iter()
        .map(|(node, state)| {
            (
                node_to_wire(*node),
                expression_resolution_state_to_wire(state),
            )
        })
        .collect();
    expression_resolutions.sort_by_key(|(node, _)| *node);

    ResolutionOutputWire {
        resolutions,
        node_to_definition,
        definition_to_kind,
        definition_to_parent,
        definition_to_ident,
        definition_to_visibility,
        file_scope_mapping,
        definition_scope_mapping,
        expression_resolutions,
        scopes: scope_wires,
        root_scope: scope_to_id[&scope_ptr(output.root_scope)],
    }
}

fn validate_scope_graph_for_hydration(wire: &ResolutionOutputWire) -> Result<(), WireDecodeError> {
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum VisitState {
        Unvisited,
        Visiting,
        Visited,
    }

    fn scope_idx(
        scope_id: u32,
        scope_count: usize,
        context: &str,
    ) -> Result<usize, WireDecodeError> {
        let idx = scope_id as usize;
        if idx >= scope_count {
            return Err(WireDecodeError::new(format!(
                "{context}: invalid scope index {scope_id} (scope count = {scope_count})",
            )));
        }
        Ok(idx)
    }

    fn visit_scope(
        idx: usize,
        wire: &ResolutionOutputWire,
        states: &mut [VisitState],
    ) -> Result<(), WireDecodeError> {
        match states[idx] {
            VisitState::Visited => return Ok(()),
            VisitState::Visiting => {
                return Err(WireDecodeError::new(format!(
                    "cycle detected while validating scope graph at index {}",
                    idx
                )));
            }
            VisitState::Unvisited => {}
        }

        states[idx] = VisitState::Visiting;
        if let Some(parent) = wire.scopes[idx].parent {
            let parent_idx = scope_idx(parent, wire.scopes.len(), "scope parent")?;
            visit_scope(parent_idx, wire, states)?;
        }
        states[idx] = VisitState::Visited;
        Ok(())
    }

    let mut states = vec![VisitState::Unvisited; wire.scopes.len()];
    for idx in 0..wire.scopes.len() {
        visit_scope(idx, wire, &mut states)?;
    }
    let _ = scope_idx(wire.root_scope, wire.scopes.len(), "root scope")?;
    Ok(())
}

pub fn resolution_output_from_wire<'a>(
    gcx: GlobalContext<'a>,
    wire: &ResolutionOutputWire,
    remap: FileRemap<'_>,
    symbols: SymbolTableRef<'_>,
) -> Result<ResolutionOutput<'a>, WireDecodeError> {
    validate_scope_graph_for_hydration(wire)?;

    #[derive(Clone, Copy, PartialEq, Eq)]
    enum ScopeBuildState {
        Unvisited,
        Visiting,
        Built,
    }

    fn scope_idx(
        scope_id: u32,
        scope_count: usize,
        context: &str,
    ) -> Result<usize, WireDecodeError> {
        let idx = scope_id as usize;
        if idx >= scope_count {
            return Err(WireDecodeError::new(format!(
                "{context}: invalid scope index {scope_id} (scope count = {scope_count})",
            )));
        }
        Ok(idx)
    }

    fn scope_by_id<'a>(
        built: &[Option<crate::sema::resolve::models::Scope<'a>>],
        scope_id: u32,
        context: &str,
    ) -> Result<crate::sema::resolve::models::Scope<'a>, WireDecodeError> {
        let idx = scope_idx(scope_id, built.len(), context)?;
        built[idx].ok_or_else(|| {
            WireDecodeError::new(format!(
                "{context}: scope index {scope_id} was not built during hydration",
            ))
        })
    }

    fn build_scope<'a>(
        idx: usize,
        wires: &[ScopeWire],
        built: &mut [Option<crate::sema::resolve::models::Scope<'a>>],
        states: &mut [ScopeBuildState],
        gcx: GlobalContext<'a>,
        remap: FileRemap<'_>,
    ) -> Result<crate::sema::resolve::models::Scope<'a>, WireDecodeError> {
        match states[idx] {
            ScopeBuildState::Built => {
                return built[idx].ok_or_else(|| {
                    WireDecodeError::new(format!(
                        "scope index {} marked built but missing value",
                        idx
                    ))
                });
            }
            ScopeBuildState::Visiting => {
                return Err(WireDecodeError::new(format!(
                    "cycle detected while hydrating scopes at index {}",
                    idx
                )));
            }
            ScopeBuildState::Unvisited => {}
        }

        states[idx] = ScopeBuildState::Visiting;
        let scope_wire = wires.get(idx).ok_or_else(|| {
            WireDecodeError::new(format!(
                "scope index {} out of bounds (scope count = {})",
                idx,
                wires.len()
            ))
        })?;
        let parent = match scope_wire.parent {
            Some(parent_id) => {
                let parent_idx = scope_idx(parent_id, wires.len(), "scope parent")?;
                Some(build_scope(parent_idx, wires, built, states, gcx, remap)?)
            }
            None => None,
        };
        let kind = scope_kind_from_wire(&scope_wire.kind, remap);
        let scope =
            Interned::new_unchecked(gcx.store.arenas.scopes.alloc(ScopeData::new(kind, parent)));
        built[idx] = Some(scope);
        states[idx] = ScopeBuildState::Built;
        Ok(scope)
    }

    let fallback_file = remap
        .old_to_new
        .values()
        .copied()
        .next()
        .unwrap_or_else(|| FileID::from_raw(0));

    let mut definition_to_ident = FxHashMap::default();
    for (def, ident) in &wire.definition_to_ident {
        definition_to_ident.insert(
            def_from_wire(def),
            identifier_from_wire(ident, remap, symbols),
        );
    }

    let mut built_scopes = vec![None; wire.scopes.len()];
    let mut build_states = vec![ScopeBuildState::Unvisited; wire.scopes.len()];
    for idx in 0..wire.scopes.len() {
        let _ = build_scope(
            idx,
            &wire.scopes,
            &mut built_scopes,
            &mut build_states,
            gcx,
            remap,
        )?;
    }

    for (idx, scope_wire) in wire.scopes.iter().enumerate() {
        let scope = built_scopes[idx].ok_or_else(|| {
            WireDecodeError::new(format!(
                "scope index {} missing after scope-build pass",
                idx
            ))
        })?;
        let default_file = match scope.kind {
            ScopeKind::File(file) => file,
            ScopeKind::Definition(def, _) => definition_to_ident
                .get(&def)
                .map(|ident| ident.span.file)
                .unwrap_or(fallback_file),
            ScopeKind::Block(_) => fallback_file,
        };
        let mut table = scope.table.borrow_mut();
        for entry in &scope_wire.entries {
            let mut name_entry = crate::sema::resolve::models::NameEntry::default();
            if let Some(ty) = &entry.ty {
                let resolution = resolution_from_wire(ty);
                let scope_entry = Interned::new_unchecked(gcx.store.arenas.scope_entries.alloc(
                    crate::sema::resolve::models::ScopeEntryData {
                        kind: crate::sema::resolve::models::ScopeEntryKind::Resolution(resolution),
                        span: Span::empty(default_file),
                    },
                ));
                name_entry.ty = Some(scope_entry);
            }
            for value in &entry.values {
                let resolution = resolution_from_wire(value);
                let scope_entry = Interned::new_unchecked(gcx.store.arenas.scope_entries.alloc(
                    crate::sema::resolve::models::ScopeEntryData {
                        kind: crate::sema::resolve::models::ScopeEntryKind::Resolution(resolution),
                        span: Span::empty(default_file),
                    },
                ));
                name_entry.values.push(scope_entry);
            }
            table.insert(Symbol::new(symbols.resolve_str(entry.symbol)), name_entry);
        }

        let mut glob_imports = scope.glob_imports.borrow_mut();
        for usage in &scope_wire.glob_imports {
            let module_scope = match usage.module_scope {
                Some(scope_id) => Some(scope_by_id(
                    &built_scopes,
                    scope_id,
                    "glob import module scope",
                )?),
                None => None,
            };
            let usage = UsageEntryData {
                span: span_from_wire(&usage.span, remap),
                module_path: Vec::new(),
                kind: UsageKind::Glob {
                    id: node_from_wire(usage.id),
                },
                is_import: true,
                scope,
                module_scope: std::cell::Cell::new(module_scope),
            };
            let usage = Interned::new_unchecked(gcx.store.arenas.usage_entries.alloc(usage));
            glob_imports.push(usage);
        }

        let mut glob_exports = scope.glob_exports.borrow_mut();
        for usage in &scope_wire.glob_exports {
            let module_scope = match usage.module_scope {
                Some(scope_id) => Some(scope_by_id(
                    &built_scopes,
                    scope_id,
                    "glob export module scope",
                )?),
                None => None,
            };
            let usage = UsageEntryData {
                span: span_from_wire(&usage.span, remap),
                module_path: Vec::new(),
                kind: UsageKind::Glob {
                    id: node_from_wire(usage.id),
                },
                is_import: false,
                scope,
                module_scope: std::cell::Cell::new(module_scope),
            };
            let usage = Interned::new_unchecked(gcx.store.arenas.usage_entries.alloc(usage));
            glob_exports.push(usage);
        }
    }

    let root_scope = scope_by_id(&built_scopes, wire.root_scope, "root scope")?;
    Ok(ResolutionOutput {
        resolutions: wire
            .resolutions
            .iter()
            .map(|(node, state)| (node_from_wire(*node), resolution_state_from_wire(state)))
            .collect(),
        node_to_definition: wire
            .node_to_definition
            .iter()
            .map(|(node, def)| (node_from_wire(*node), def_from_wire(def)))
            .collect(),
        definition_to_kind: wire
            .definition_to_kind
            .iter()
            .map(|(def, kind)| (def_from_wire(def), definition_kind_from_wire(kind)))
            .collect(),
        definition_to_parent: wire
            .definition_to_parent
            .iter()
            .map(|(def, parent)| (def_from_wire(def), def_from_wire(parent)))
            .collect(),
        definition_to_ident,
        definition_to_visibility: wire
            .definition_to_visibility
            .iter()
            .map(|(def, vis)| (def_from_wire(def), visibility_from_wire(vis, remap)))
            .collect(),
        file_scope_mapping: wire
            .file_scope_mapping
            .iter()
            .filter_map(|(file, scope)| {
                let file = remap.old_to_new.get(file).copied()?;
                let scope = built_scopes.get(*scope as usize).and_then(|scope| *scope)?;
                Some((file, scope))
            })
            .collect(),
        definition_scope_mapping: wire
            .definition_scope_mapping
            .iter()
            .filter_map(|(def, scope)| {
                let scope = built_scopes.get(*scope as usize).and_then(|scope| *scope)?;
                Some((def_from_wire(def), scope))
            })
            .collect(),
        expression_resolutions: wire
            .expression_resolutions
            .iter()
            .map(|(node, state)| {
                (
                    node_from_wire(*node),
                    expression_resolution_state_from_wire(state),
                )
            })
            .collect(),
        root_scope,
    })
}

pub fn type_database_to_wire(
    db: &TypeDatabase<'_>,
    symbols: &mut SymbolTableBuilder,
) -> TypeDatabaseWire {
    TypeDatabaseWire {
        def_to_ty: db
            .def_to_ty
            .iter()
            .map(|(def, ty)| (def_to_wire(*def), ty_to_wire(*ty)))
            .collect(),
        def_to_const: db
            .def_to_const
            .iter()
            .map(|(def, value)| (def_to_wire(*def), const_to_wire(*value)))
            .collect(),
        def_to_fn_sig: db
            .def_to_fn_sig
            .iter()
            .map(|(def, sig)| (def_to_wire(*def), signature_to_wire(sig)))
            .collect(),
        def_to_struct_def: db
            .def_to_struct_def
            .iter()
            .map(|(def, st)| (def_to_wire(*def), struct_definition_to_wire(st, symbols)))
            .collect(),
        def_to_enum_def: db
            .def_to_enum_def
            .iter()
            .map(|(def, en)| (def_to_wire(*def), enum_definition_to_wire(en, symbols)))
            .collect(),
        def_to_constraints: db
            .def_to_constraints
            .iter()
            .map(|(def, constraints)| {
                (
                    def_to_wire(*def),
                    constraints
                        .iter()
                        .map(|constraint| ConstraintSpannedWire {
                            value: constraint_to_wire(&constraint.value),
                            span: span_to_wire(constraint.span),
                        })
                        .collect(),
                )
            })
            .collect(),
        def_to_canon_constraints: db
            .def_to_canon_constraints
            .iter()
            .map(|(def, constraints)| {
                (
                    def_to_wire(*def),
                    constraints
                        .iter()
                        .map(|constraint| ConstraintSpannedWire {
                            value: constraint_to_wire(&constraint.value),
                            span: span_to_wire(constraint.span),
                        })
                        .collect(),
                )
            })
            .collect(),
        impl_to_type_head: db
            .impl_to_type_head
            .iter()
            .map(|(def, head)| (def_to_wire(*def), type_head_to_wire(*head)))
            .collect(),
        impl_to_target_ty: db
            .impl_to_target_ty
            .iter()
            .map(|(def, ty)| (def_to_wire(*def), ty_to_wire(*ty)))
            .collect(),
        type_head_to_impls: db
            .type_head_to_impls
            .iter()
            .map(|(head, ids)| {
                (
                    type_head_to_wire(*head),
                    ids.iter().copied().map(def_to_wire).collect(),
                )
            })
            .collect(),
        type_head_to_members: db
            .type_head_to_members
            .iter()
            .map(|(head, members)| {
                (
                    type_head_to_wire(*head),
                    type_member_index_to_wire(members, symbols),
                )
            })
            .collect(),
        def_to_generics: db
            .def_to_generics
            .iter()
            .map(|(def, generics)| (def_to_wire(*def), generics_to_wire(generics)))
            .collect(),
        generic_type_defaults: db
            .generic_type_defaults
            .iter()
            .map(|(def, ty)| (def_to_wire(*def), ty_to_wire(*ty)))
            .collect(),
        generic_const_param_tys: db
            .generic_const_param_tys
            .iter()
            .map(|(def, ty)| (def_to_wire(*def), ty_to_wire(*ty)))
            .collect(),
        generic_const_defaults: db
            .generic_const_defaults
            .iter()
            .map(|(def, value)| (def_to_wire(*def), const_to_wire(*value)))
            .collect(),
        def_to_attributes: db
            .def_to_attributes
            .iter()
            .map(|(def, attrs)| {
                (
                    def_to_wire(*def),
                    attrs
                        .iter()
                        .map(|attr| attribute_to_wire(attr, symbols))
                        .collect::<Vec<_>>(),
                )
            })
            .collect(),
        def_to_iface_def: db
            .def_to_iface_def
            .iter()
            .map(|(def, iface)| (def_to_wire(*def), interface_def_to_wire(iface, symbols)))
            .collect(),
        interface_to_supers: db
            .interface_to_supers
            .iter()
            .map(|(def, supers)| {
                (
                    def_to_wire(*def),
                    supers.iter().copied().map(def_to_wire).collect(),
                )
            })
            .collect(),
        conformance_records: db
            .conformance_records
            .iter()
            .map(|(id, record)| {
                (
                    conformance_id_to_wire(*id),
                    conformance_record_to_wire(*record),
                )
            })
            .collect(),
        conformance_by_interface_head: db
            .conformance_by_interface_head
            .iter()
            .map(|((iface, head), ids)| {
                (
                    (def_to_wire(*iface), type_head_to_wire(*head)),
                    ids.iter().copied().map(conformance_id_to_wire).collect(),
                )
            })
            .collect(),
        conformance_by_interface: db
            .conformance_by_interface
            .iter()
            .map(|(iface, ids)| {
                (
                    def_to_wire(*iface),
                    ids.iter().copied().map(conformance_id_to_wire).collect(),
                )
            })
            .collect(),
        conformance_by_head: db
            .conformance_by_head
            .iter()
            .map(|(head, ids)| {
                (
                    type_head_to_wire(*head),
                    ids.iter().copied().map(conformance_id_to_wire).collect(),
                )
            })
            .collect(),
        conformance_by_extension: db
            .conformance_by_extension
            .iter()
            .map(|(ext, ids)| {
                (
                    def_to_wire(*ext),
                    ids.iter().copied().map(conformance_id_to_wire).collect(),
                )
            })
            .collect(),
        next_conformance_record_index: db.next_conformance_record_index,
        interface_requirements: db
            .interface_requirements
            .iter()
            .map(|(def, reqs)| {
                (
                    def_to_wire(*def),
                    interface_requirements_to_wire(reqs, symbols),
                )
            })
            .collect(),
        alias_table: alias_table_to_wire(&db.alias_table, symbols),
        resolved_aliases: db
            .resolved_aliases
            .iter()
            .map(|(def, ty)| (def_to_wire(*def), ty_to_wire(*ty)))
            .collect(),
        def_to_escape_summary: db
            .def_to_escape_summary
            .iter()
            .map(|(def, summary)| (def_to_wire(*def), escape_summary_to_wire(summary)))
            .collect(),
        closure_captures: db
            .closure_captures
            .iter()
            .map(|(def, captures)| {
                (
                    def_to_wire(*def),
                    closure_captures_to_wire(captures, symbols),
                )
            })
            .collect(),
        synthetic_methods: db
            .synthetic_methods
            .iter()
            .map(|((head, method_id), info)| {
                (
                    (type_head_to_wire(*head), def_to_wire(*method_id)),
                    synthetic_method_info_to_wire(info, symbols),
                )
            })
            .collect(),
    }
}

pub fn type_database_from_wire<'a>(
    gcx: GlobalContext<'a>,
    wire: &TypeDatabaseWire,
    remap: FileRemap<'_>,
    symbols: SymbolTableRef<'_>,
) -> TypeDatabase<'a> {
    let placeholder_file = remap
        .old_to_new
        .values()
        .copied()
        .next()
        .unwrap_or_else(|| FileID::from_raw(0));
    let placeholder_span = Span::empty(placeholder_file);

    TypeDatabase {
        def_to_ty: wire
            .def_to_ty
            .iter()
            .map(|(def, ty)| (def_from_wire(def), ty_from_wire(gcx, ty)))
            .collect(),
        def_to_const: wire
            .def_to_const
            .iter()
            .map(|(def, value)| (def_from_wire(def), const_from_wire(gcx, value)))
            .collect(),
        def_to_fn_sig: wire
            .def_to_fn_sig
            .iter()
            .map(|(def, sig)| {
                let sig: &'a LabeledFunctionSignature<'a> = gcx
                    .store
                    .arenas
                    .function_signatures
                    .alloc(signature_from_wire(gcx, sig));
                (def_from_wire(def), sig)
            })
            .collect(),
        def_to_struct_def: wire
            .def_to_struct_def
            .iter()
            .map(|(def, st)| {
                let st: &'a StructDefinition<'a> = gcx
                    .store
                    .arenas
                    .struct_definitions
                    .alloc(struct_definition_from_wire(gcx, st, remap, symbols));
                (def_from_wire(def), st)
            })
            .collect(),
        def_to_enum_def: wire
            .def_to_enum_def
            .iter()
            .map(|(def, en)| {
                let en: &'a EnumDefinition<'a> = gcx
                    .store
                    .arenas
                    .enum_definitions
                    .alloc(enum_definition_from_wire(gcx, en, symbols));
                (def_from_wire(def), en)
            })
            .collect(),
        def_to_constraints: wire
            .def_to_constraints
            .iter()
            .map(|(def, constraints)| {
                (
                    def_from_wire(def),
                    constraints
                        .iter()
                        .map(|constraint| Spanned {
                            value: constraint_from_wire(gcx, &constraint.value),
                            span: span_from_wire(&constraint.span, remap),
                        })
                        .collect(),
                )
            })
            .collect(),
        def_to_canon_constraints: wire
            .def_to_canon_constraints
            .iter()
            .map(|(def, constraints)| {
                (
                    def_from_wire(def),
                    constraints
                        .iter()
                        .map(|constraint| Spanned {
                            value: constraint_from_wire(gcx, &constraint.value),
                            span: span_from_wire(&constraint.span, remap),
                        })
                        .collect(),
                )
            })
            .collect(),
        impl_to_type_head: wire
            .impl_to_type_head
            .iter()
            .map(|(def, head)| (def_from_wire(def), type_head_from_wire(head)))
            .collect(),
        impl_to_target_ty: wire
            .impl_to_target_ty
            .iter()
            .map(|(def, ty)| (def_from_wire(def), ty_from_wire(gcx, ty)))
            .collect(),
        type_head_to_impls: wire
            .type_head_to_impls
            .iter()
            .map(|(head, ids)| {
                (
                    type_head_from_wire(head),
                    ids.iter().map(def_from_wire).collect(),
                )
            })
            .collect(),
        type_head_to_members: wire
            .type_head_to_members
            .iter()
            .map(|(head, members)| {
                (
                    type_head_from_wire(head),
                    type_member_index_from_wire(members, symbols),
                )
            })
            .collect(),
        def_to_generics: wire
            .def_to_generics
            .iter()
            .map(|(def, generics)| {
                let generics: &'a Generics = gcx
                    .store
                    .arenas
                    .generics
                    .alloc(generics_from_wire(generics, placeholder_span));
                (def_from_wire(def), generics)
            })
            .collect(),
        generic_type_defaults: wire
            .generic_type_defaults
            .iter()
            .map(|(def, ty)| (def_from_wire(def), ty_from_wire(gcx, ty)))
            .collect(),
        generic_const_param_tys: wire
            .generic_const_param_tys
            .iter()
            .map(|(def, ty)| (def_from_wire(def), ty_from_wire(gcx, ty)))
            .collect(),
        generic_const_defaults: wire
            .generic_const_defaults
            .iter()
            .map(|(def, value)| (def_from_wire(def), const_from_wire(gcx, value)))
            .collect(),
        def_to_attributes: wire
            .def_to_attributes
            .iter()
            .map(|(def, attrs)| {
                let attrs: hir::AttributeList = attrs
                    .iter()
                    .map(|attr| attribute_from_wire(attr, remap, symbols))
                    .collect();
                let attrs: &'a hir::AttributeList = gcx.store.arenas.global.alloc(attrs);
                (def_from_wire(def), attrs)
            })
            .collect(),
        def_to_iface_def: wire
            .def_to_iface_def
            .iter()
            .map(|(def, iface)| {
                let iface: &'a InterfaceDefinition<'a> = gcx
                    .store
                    .arenas
                    .interface_definitions
                    .alloc(interface_def_from_wire(gcx, iface, remap, symbols));
                (def_from_wire(def), iface)
            })
            .collect(),
        interface_to_supers: wire
            .interface_to_supers
            .iter()
            .map(|(def, supers)| {
                (
                    def_from_wire(def),
                    supers.iter().map(def_from_wire).collect(),
                )
            })
            .collect(),
        conformance_records: wire
            .conformance_records
            .iter()
            .map(|(id, record)| {
                (
                    conformance_id_from_wire(id),
                    conformance_record_from_wire(gcx, record, remap),
                )
            })
            .collect(),
        conformance_by_interface_head: wire
            .conformance_by_interface_head
            .iter()
            .map(|((iface, head), ids)| {
                (
                    (def_from_wire(iface), type_head_from_wire(head)),
                    ids.iter().map(conformance_id_from_wire).collect(),
                )
            })
            .collect(),
        conformance_by_interface: wire
            .conformance_by_interface
            .iter()
            .map(|(iface, ids)| {
                (
                    def_from_wire(iface),
                    ids.iter().map(conformance_id_from_wire).collect(),
                )
            })
            .collect(),
        conformance_by_head: wire
            .conformance_by_head
            .iter()
            .map(|(head, ids)| {
                (
                    type_head_from_wire(head),
                    ids.iter().map(conformance_id_from_wire).collect(),
                )
            })
            .collect(),
        conformance_by_extension: wire
            .conformance_by_extension
            .iter()
            .map(|(ext, ids)| {
                (
                    def_from_wire(ext),
                    ids.iter().map(conformance_id_from_wire).collect(),
                )
            })
            .collect(),
        next_conformance_record_index: wire.next_conformance_record_index,
        interface_requirements: wire
            .interface_requirements
            .iter()
            .map(|(def, reqs)| {
                let reqs: &'a InterfaceRequirements<'a> = gcx
                    .store
                    .arenas
                    .interface_requirements
                    .alloc(interface_requirements_from_wire(gcx, reqs, symbols));
                (def_from_wire(def), reqs)
            })
            .collect(),
        selection_cache: Default::default(),
        witness_cache: Default::default(),
        alias_table: alias_table_from_wire(&wire.alias_table, remap, placeholder_span, symbols),
        resolved_aliases: wire
            .resolved_aliases
            .iter()
            .map(|(def, ty)| (def_from_wire(def), ty_from_wire(gcx, ty)))
            .collect(),
        def_to_escape_summary: wire
            .def_to_escape_summary
            .iter()
            .map(|(def, summary)| (def_from_wire(def), escape_summary_from_wire(summary)))
            .collect(),
        closure_captures: wire
            .closure_captures
            .iter()
            .map(|(def, captures)| {
                (
                    def_from_wire(def),
                    closure_captures_from_wire(gcx, captures, symbols),
                )
            })
            .collect(),
        empty_generics: None,
        empty_attributes: None,
        synthetic_methods: wire
            .synthetic_methods
            .iter()
            .map(|((head, method_id), info)| {
                (
                    (type_head_from_wire(head), def_from_wire(method_id)),
                    synthetic_method_info_from_wire(gcx, info, symbols),
                )
            })
            .collect(),
        visible_traits: Default::default(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn minimal_resolution_wire() -> ResolutionOutputWire {
        ResolutionOutputWire {
            resolutions: vec![],
            node_to_definition: vec![],
            definition_to_kind: vec![],
            definition_to_parent: vec![],
            definition_to_ident: vec![],
            definition_to_visibility: vec![],
            file_scope_mapping: vec![],
            definition_scope_mapping: vec![],
            expression_resolutions: vec![],
            scopes: vec![ScopeWire {
                parent: None,
                kind: ScopeKindWire::Block(0),
                entries: vec![],
                glob_imports: vec![],
                glob_exports: vec![],
            }],
            root_scope: 0,
        }
    }

    #[test]
    fn symbol_table_ref_marks_invalid_symbol_id() {
        let table = SymbolTableWire {
            symbols: vec!["alpha".into()],
        };
        let invalid = Cell::new(None);
        let symbols = SymbolTableRef::new(&table, &invalid);

        assert_eq!(symbols.resolve_str(SymbolIdWire(0)), "alpha");
        assert_eq!(invalid.get(), None);

        assert_eq!(symbols.resolve_str(SymbolIdWire(7)), "<invalid-symbol-id>");
        assert_eq!(invalid.get(), Some(7));
    }

    #[test]
    fn validate_scope_graph_rejects_invalid_root_scope() {
        let mut wire = minimal_resolution_wire();
        wire.root_scope = 99;
        let err = validate_scope_graph_for_hydration(&wire).unwrap_err();
        assert!(err.to_string().contains("root scope"));
    }

    #[test]
    fn validate_scope_graph_rejects_parent_cycles() {
        let mut wire = minimal_resolution_wire();
        wire.scopes = vec![
            ScopeWire {
                parent: Some(1),
                kind: ScopeKindWire::Block(0),
                entries: vec![],
                glob_imports: vec![],
                glob_exports: vec![],
            },
            ScopeWire {
                parent: Some(0),
                kind: ScopeKindWire::Block(1),
                entries: vec![],
                glob_imports: vec![],
                glob_exports: vec![],
            },
        ];
        wire.root_scope = 0;

        let err = validate_scope_graph_for_hydration(&wire).unwrap_err();
        assert!(err.to_string().contains("cycle"));
    }
}
