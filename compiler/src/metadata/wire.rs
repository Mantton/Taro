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
            PackageAliasTable, StructDefinition, StructField, StructRepr, SyntheticDefinition,
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
    /// Absent for an ordinary build, present and possibly empty for a reporting build.
    pub(crate) allocation_report: Option<crate::compile::allocation_report::AllocationReport>,
    pub(crate) embedded_inputs: crate::compile::assets::AssetInputs,
    pub file_table: Vec<FileMappingWire>,
    pub semantic_payload: Option<Vec<u8>>,
    pub mir_payload: Option<Vec<u8>>,
    pub inline_mir_payload: Option<Vec<u8>>,
    /// Subset of canonical MIR bodies for `const func` definitions (and their
    /// reachable helpers) attached to semantic-only dependency metadata so
    /// downstream `taro check` builds can evaluate imported `const func` calls.
    pub const_fn_mir_payload: Option<Vec<u8>>,
    pub std_items: Option<StdItemRegistryWire>,
    pub synthetic_definitions: Vec<SyntheticDefinitionWire>,
    pub emitted_instances: Vec<InstanceWire>,
    pub class_dispatch_types: Vec<TyWire>,
    pub class_dispatch_calls: Vec<InstanceWire>,
    pub erased_opening_types: Vec<TyWire>,
    pub erased_opening_calls: Vec<InstanceWire>,
    pub class_super_calls: Vec<SpanWire>,
    /// Warnings the package's compilation reported, replayed when the
    /// metadata is reused. `None` when it compiled without lint warnings
    /// (as a dependency), so a root build cannot replay them.
    pub warnings: Option<Vec<WarningWire>>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SuggestionWire {
    pub message: String,
    pub span: SpanWire,
    pub replacement: String,
    pub machine_applicable: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WarningWire {
    pub message: String,
    pub span: Option<SpanWire>,
    pub suggestion: Option<SuggestionWire>,
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
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
    AssociatedProperty,
    AssociatedSubscript,
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
    Internal(DefIdWire),
    Private(DefIdWire),
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
    #[serde(default)]
    pub def_to_static_mutability: Vec<(DefIdWire, MutabilityWire)>,
    pub def_to_class_default_contract: Vec<(DefIdWire, crate::sema::models::ClassDefaultContract)>,
    pub erased_async_self_arguments: Vec<(DefIdWire, Vec<GenericArgumentWire>)>,
    pub class_adoptions: Vec<(ConformanceRecordIdWire, Vec<ClassWitnessMethodWire>)>,

    pub def_to_fn_sig: Vec<(DefIdWire, LabeledFunctionSignatureWire)>,

    #[serde(default)]
    pub def_to_async_body_output: Vec<(DefIdWire, TyWire)>,
    pub def_to_struct_def: Vec<(DefIdWire, StructDefinitionWire)>,
    pub def_to_enum_def: Vec<(DefIdWire, EnumDefinitionWire)>,
    pub def_to_constraints: Vec<(DefIdWire, Vec<ConstraintSpannedWire>)>,
    pub def_to_canon_constraints: Vec<(DefIdWire, Vec<ConstraintSpannedWire>)>,
    pub impl_to_type_head: Vec<(DefIdWire, TypeHeadWire)>,
    pub impl_to_target_ty: Vec<(DefIdWire, TyWire)>,
    pub type_head_to_impls: Vec<(TypeHeadWire, Vec<DefIdWire>)>,
    pub type_head_to_members: Vec<(TypeHeadWire, TypeMemberIndexWire)>,
    pub native_subscripts: Vec<(DefIdWire, NativeSubscriptEntryWire)>,
    pub class_subscripts: Vec<(DefIdWire, Vec<(DefIdWire, NativeSubscriptEntryWire)>)>,
    #[serde(default)]
    pub type_head_to_properties:
        Vec<(TypeHeadWire, Vec<(SymbolIdWire, ComputedPropertyEntryWire)>)>,
    #[serde(default)]
    pub type_head_to_interface_properties: Vec<(
        TypeHeadWire,
        Vec<((DefIdWire, SymbolIdWire), Vec<ComputedPropertyEntryWire>)>,
    )>,
    pub def_to_generics: Vec<(DefIdWire, GenericsWire)>,
    pub generic_type_defaults: Vec<(DefIdWire, TyWire)>,
    pub generic_const_param_tys: Vec<(DefIdWire, TyWire)>,
    pub generic_const_defaults: Vec<(DefIdWire, ConstWire)>,
    pub def_to_attributes: Vec<(DefIdWire, Vec<AttributeWire>)>,
    #[serde(default)]
    pub def_to_unsafe: Vec<DefIdWire>,
    #[serde(default)]
    pub def_to_const_fn: Vec<DefIdWire>,
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
    pub resolved_interface_aliases: Vec<(DefIdWire, Vec<InterfaceReferenceWire>)>,
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
    Reference(Box<TyWire>),
    Tuple(Vec<TyWire>),
    LabeledTuple {
        elements: Vec<TyWire>,
        labels: Vec<(usize, String)>,
    },
    FnPointer {
        inputs: Vec<TyWire>,
        output: Box<TyWire>,
        kind: ClosureKindWire,
        is_unsafe: bool,
        abi: Option<AbiWire>,
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
    ExistentialSelf(u32),
    Closure {
        closure_def_id: DefIdWire,
        kind: ClosureKindWire,
        captured_generics: Vec<GenericArgumentWire>,
        inputs: Vec<TyWire>,
        output: Box<TyWire>,
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
    Opaque,
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
    EnumUnitVariant(DefIdWire),
    Bytes(Vec<u8>),
    Array(Vec<ConstValueWire>),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum GenericArgumentWire {
    Type(TyWire),
    Const(ConstWire),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StructFieldWire {
    pub default_provider: Option<DefIdWire>,
    pub name: SymbolIdWire,
    pub ty: TyWire,
    pub mutability: MutabilityWire,
    pub def_id: DefIdWire,
    pub visibility: VisibilityWire,
    pub coding_key: Option<SymbolIdWire>,
    pub coding_skip: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StructDefinitionWire {
    pub adt_def: AdtDefWire,
    pub class_info: Option<ClassInfoWire>,
    pub positional: bool,
    pub has_initializer: bool,
    pub repr: StructReprWire,
    pub fields: Vec<StructFieldWire>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ClassInfoWire {
    pub base: Option<TyWire>,
    pub methods: Vec<ClassMethodWire>,
    pub initializers: Vec<ClassInitializerWire>,
    pub payload: Option<DefIdWire>,
    pub is_final: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ClassInitializerWire {
    pub definition: DefIdWire,
    pub family: DefIdWire,
    pub implementation: DefIdWire,
    pub owner: TyWire,
    pub is_convenience: bool,
    pub is_required: bool,
    pub is_inherited: bool,
    pub delegations: Vec<DefIdWire>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ClassMethodWire {
    pub returns_self: bool,
    pub family: DefIdWire,
    pub implementation: DefIdWire,
    pub owner: TyWire,
    pub is_final: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ClassWitnessMethodWire {
    pub requirement: DefIdWire,
    pub slot: ClassMethodWire,
    pub is_registered: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum StructReprWire {
    Taro,
    C,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EnumVariantFieldWire {
    pub label: Option<SymbolIdWire>,
    pub ty: TyWire,
    pub mutability: MutabilityWire,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum EnumVariantKindWire {
    Unit,
    Tuple(Vec<EnumVariantFieldWire>),
    Struct(Vec<EnumVariantFieldWire>),
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
    pub is_lazy: bool,
    pub label: Option<String>,
    pub name: String,
    pub ty: TyWire,
    pub default_provider: Option<DefIdWire>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AbiWire {
    C,
    Blocking,
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
    pub is_anonymous: bool,
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
    #[serde(default)]
    pub properties: Vec<InterfacePropertyRequirementWire>,
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
pub struct InterfacePropertyRequirementWire {
    pub id: DefIdWire,
    pub name: SymbolIdWire,
    pub ty: TyWire,
    pub getter_id: DefIdWire,
    pub getter_is_required: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InterfaceConstantRequirementWire {
    pub id: DefIdWire,
    pub name: SymbolIdWire,
    pub ty: TyWire,
    pub has_default: bool,
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConformanceRecordIdWire {
    pub package: u32,
    pub index: u32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TypeHeadWire {
    Primary(PrimaryTypeWire),
    Nominal(DefIdWire),
    Parameter(DefIdWire),
    Closure(DefIdWire),
    Reference,
    Pointer(MutabilityWire),
    Tuple(u16),
    Array,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TypeMemberIndexWire {
    pub inherent_static: Vec<(SymbolIdWire, MemberSetWire)>,
    pub inherent_constants: Vec<(SymbolIdWire, Vec<DefIdWire>)>,
    pub inherent_instance: Vec<(SymbolIdWire, MemberSetWire)>,
    pub trait_methods: Vec<((DefIdWire, SymbolIdWire), MemberSetWire)>,
    pub trait_methods_by_name: Vec<(SymbolIdWire, Vec<DefIdWire>)>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ComputedPropertyEntryWire {
    pub property_id: DefIdWire,
    pub ty: TyWire,
    pub getter_id: DefIdWire,
    pub visibility: VisibilityWire,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NativeSubscriptEntryWire {
    pub getter_is_default: bool,
    pub setter_is_default: bool,
    pub is_override: bool,
    pub is_final: bool,
    pub getter: Option<DefIdWire>,
    pub setter: Option<DefIdWire>,
    pub address: Option<DefIdWire>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MemberSetWire {
    pub members: Vec<DefIdWire>,
    pub fingerprints: Vec<(u64, DefIdWire)>,
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
pub struct ClosureCapturesWire {
    pub captures: Vec<CapturedVarWire>,
    pub kind: ClosureKindWire,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CapturedVarWire {
    pub source_id: u32,
    pub root_ty: TyWire,
    pub projection: Vec<(u32, TyWire)>,
    pub name: SymbolIdWire,
    pub ty: TyWire,
    pub capture_kind: CaptureKindWire,
    pub source_immutable: bool,
    pub field_index: u32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum CaptureKindWire {
    ByCopy,
    ByRef,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ClosureKindWire {
    Fn,
    AsyncFn,
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
    MemberwiseEncode,
    MemberwiseDecode,
    MemberwisePartialOrder,
    MemberwiseTotalOrder,
    MemberwiseDefault,
    MemberwiseDebug,
    ClosureCall,
    PropertyFieldGetter { field_index: u32 },
    EnumRawValue,
    EnumFromRawValue,
    EnumCaseName,
    EnumCaseAt,
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
        value: i128,
        suffix: Option<IntegerTypeSuffixWire>,
    },
    Float(f64),
    Nil,
    Bytes(Vec<u8>),
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum StdItemWire {
    Optional,
    Result,
    List,
    ListIterator,
    ClassHandle,
    AtomicHandle,
    SyncGenerator,
    AsyncGenerator,
    Set,
    Dictionary,
    Range,
    ClosedRange,
    RangeFrom,
    RangeTo,
    RangeToInclusive,
    RangeFull,
    MaybeUninit,
    Span,
    Benchmark,
    AnyObject,
    Clone,
    Hashable,
    Equatable,
    Encodable,
    Decodable,
    From,
    Iterator,
    Iterable,
    AsyncIterator,
    AsyncIterable,
    Fn,
    AsyncFn,
    Tuple,
    Add,
    AddAssign,
    Sub,
    SubAssign,
    Mul,
    MulAssign,
    Div,
    DivAssign,
    Rem,
    RemAssign,
    Neg,
    Not,
    BitAnd,
    BitAndAssign,
    BitOr,
    BitOrAssign,
    BitXor,
    BitXorAssign,
    Shl,
    ShlAssign,
    Shr,
    ShrAssign,
    BitNot,
    Contains,
    PartialEq,
    PartialOrd,
    Ord,
    Default,
    Display,
    Debug,
    DebugDisplay,
    OptionalSomeVariant,
    OptionalSomeCtor,
    OptionalNoneVariant,
    OptionalNoneCtor,
    ResultOkVariant,
    ResultOkCtor,
    ResultErrVariant,
    ResultErrCtor,
    Task,
    PanicPayload,
    Deref,
    BenchmarkReport,
    MainErrorReport,
    RawValue,
    CaseIterable,
    DebugValue,
    DebugValueAt,
    DebugString,
    Assert,
    AssertWithMessage,
    DebugAssert,
    DebugAssertWithMessage,
    AssertFail,
    AssertFailWithMessage,
    Closeable,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SyntheticDefinitionWire {
    pub kind: SyntheticDefinitionKindWire,
    pub id: DefIdWire,
    pub name: String,
    pub generics: GenericsWire,
    pub signature: LabeledFunctionSignatureWire,
    pub span: SpanWire,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SyntheticDefinitionKindWire {
    ClassDecoder {
        class: DefIdWire,
        initializer: DefIdWire,
    },
    ClassDecodingInitializer {
        class: DefIdWire,
    },
    ClassEncoder {
        class: DefIdWire,
    },
    ClassPayload {
        class: DefIdWire,
    },
    ClassPayloadInitializer {
        class: DefIdWire,
        initializer: DefIdWire,
    },
    InheritedClassInitializer {
        class: DefIdWire,
        initializer: DefIdWire,
    },
    InitializerEnvironment {
        class: DefIdWire,
        initializer: DefIdWire,
    },
    InheritedInitializerDefault {
        initializer: DefIdWire,
        provider: DefIdWire,
    },
    ClassInitializerDispatch {
        initializer: DefIdWire,
    },
    ClassConvenienceInitializer {
        initializer: DefIdWire,
    },
    ClassConstructionDescriptor {
        class: DefIdWire,
    },
    ClassObjectDescriptor {
        class: DefIdWire,
    },
    ErasedTakeAs {
        context: DefIdWire,
    },
    ErasedAsRef {
        context: DefIdWire,
    },
    ErasedPayloadReference {
        context: DefIdWire,
    },
    StaticInitializer {
        storage: DefIdWire,
    },
    StaticReference {
        storage: DefIdWire,
    },
    ErasedAsyncSelf {
        context: DefIdWire,
        method: DefIdWire,
    },
    ErasedAsyncSelfDefault {
        adapter: DefIdWire,
        provider: DefIdWire,
    },
    ErasedDefault {
        source: DefIdWire,
        provider: DefIdWire,
        parameter: usize,
    },
    ClassDefaultBody {
        source: DefIdWire,
    },
    AdoptedClassDefault {
        conformance: ConformanceRecordIdWire,
        source: DefIdWire,
    },
    DelegatedMethod {
        conformance: ConformanceRecordIdWire,
        source: DefIdWire,
        field: u32,
        borrow_field: bool,
    },
    AdoptedClassDefaultArgument {
        method: DefIdWire,
        provider: DefIdWire,
    },
    Ordinary,
    AsyncPoll,
    BuiltinCopyClone,
    FunctionPointerCall {
        is_async: bool,
    },
    TupleClone,
    ArrayClone,
    ClosureClone,
    PrimitiveOperator(StdItemWire),
    TupleConformance(StdItemWire),
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
    pub method_interface: InterfaceReferenceWire,
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
    pub source_scopes: Vec<SourceScopeDataWire>,
    pub locals: Vec<LocalDeclWire>,
    pub basic_blocks: Vec<BasicBlockDataWire>,
    pub start_block: u32,
    pub return_local: u32,
    pub phase: MirPhaseWire,
    #[serde(default)]
    pub is_async: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SourceScopeDataWire {
    pub definition: DefIdWire,
    pub callsite: Option<SpanWire>,
    pub parent: Option<u32>,
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
    ConstructorSelf,
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
    SourceScope(u32),
    StorageLive(u32),
    StorageDead(u32),
    SetInitialized(u32),
    Assign(PlaceWire, RvalueWire),

    KeepAlive(OperandWire),
    Nop,
    SetDiscriminant {
        place: PlaceWire,
        variant_index: u32,
    },
    GcSafepoint(mir::GcSafepointKind),
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

    Yield {
        value: OperandWire,
        resume: u32,
        resume_arg: PlaceWire,
        no_result: Option<u32>,
        cancel: u32,
        cancel_complete: u32,
        unwind: CallUnwindActionWire,
    },
    GeneratorYield {
        value: OperandWire,
        resume: u32,
        cancel: u32,
        cancel_complete: u32,
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
    CopyWith(PlaceWire, CopyModifiersWire),
    Constant(ConstantWire),
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub struct CopyModifiersWire {
    pub init: bool,
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
    GlobalVariableAddress(DefIdWire),
    ConstParam(GenericParameterWire),
    InterfaceConstant(DefIdWire, Vec<GenericArgumentWire>),
    Bytes(Vec<u8>),
    ConstArray(Vec<ConstValueWire>),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RvalueWire {
    Use(OperandWire),
    CopyValue {
        source: PlaceWire,
    },
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
        place: PlaceWire,
    },
    CleanupAddress {
        place: PlaceWire,
    },
    Discriminant {
        place: PlaceWire,
    },
    Zeroed {
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
    Alloc {
        ty: TyWire,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum CastKindWire {
    Numeric,
    BoxExistential,
    ExistentialUpcast,
    ClassObjectOwner,
    NativeClassHandle,
    ClassUpcast,
    ClassSelfResult,
    ExistentialTypeIs { target: TyWire },
    ExistentialTryCast { target: TyWire },
    Pointer,
    ClosureToFnPointer,
    ClassFromOwner,
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

// List exact unit-variant mappings once while keeping both matches exhaustive.
// Wire enum declarations above retain their serialized discriminant order.
macro_rules! wire_enum_conversions {
    ($to:ident, $from:ident, $native:path, $wire:ident, [$($variant:ident),+ $(,)?]) => {
        #[inline]
        pub fn $to(value: $native) -> $wire {
            use $native as Native;
            match value {
                $(Native::$variant => $wire::$variant,)+
            }
        }

        #[inline]
        pub fn $from(value: &$wire) -> $native {
            use $native as Native;
            match value {
                $($wire::$variant => Native::$variant,)+
            }
        }
    };
}

wire_enum_conversions!(
    mutability_to_wire,
    mutability_from_wire,
    hir::Mutability,
    MutabilityWire,
    [Mutable, Immutable,]
);

wire_enum_conversions!(
    int_ty_to_wire,
    int_ty_from_wire,
    IntTy,
    IntTyWire,
    [ISize, I8, I16, I32, I64,]
);

wire_enum_conversions!(
    uint_ty_to_wire,
    uint_ty_from_wire,
    UIntTy,
    UIntTyWire,
    [USize, U8, U16, U32, U64,]
);

wire_enum_conversions!(
    float_ty_to_wire,
    float_ty_from_wire,
    FloatTy,
    FloatTyWire,
    [F32, F64,]
);

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

wire_enum_conversions!(
    variant_ctor_kind_to_wire,
    variant_ctor_kind_from_wire,
    VariantCtorKind,
    VariantCtorKindWire,
    [Function, Constant,]
);

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
        DefinitionKind::AssociatedProperty => DefinitionKindWire::AssociatedProperty,
        DefinitionKind::AssociatedSubscript => DefinitionKindWire::AssociatedSubscript,
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
        DefinitionKindWire::AssociatedProperty => DefinitionKind::AssociatedProperty,
        DefinitionKindWire::AssociatedSubscript => DefinitionKind::AssociatedSubscript,
        DefinitionKindWire::AssociatedType => DefinitionKind::AssociatedType,
        DefinitionKindWire::VariantConstructor(v) => {
            DefinitionKind::VariantConstructor(variant_ctor_kind_from_wire(v))
        }
        DefinitionKindWire::OpaqueType => DefinitionKind::OpaqueType,
    }
}

wire_enum_conversions!(
    std_item_to_wire,
    std_item_from_wire,
    hir::StdItem,
    StdItemWire,
    [
        Optional,
        Result,
        List,
        ListIterator,
        ClassHandle,
        AtomicHandle,
        SyncGenerator,
        AsyncGenerator,
        Set,
        Dictionary,
        Range,
        ClosedRange,
        RangeFrom,
        RangeTo,
        RangeToInclusive,
        RangeFull,
        MaybeUninit,
        Span,
        Benchmark,
        AnyObject,
        Clone,
        Hashable,
        Equatable,
        Encodable,
        Decodable,
        From,
        Iterator,
        Iterable,
        AsyncIterator,
        AsyncIterable,
        Fn,
        AsyncFn,
        Tuple,
        Add,
        AddAssign,
        Sub,
        SubAssign,
        Mul,
        MulAssign,
        Div,
        DivAssign,
        Rem,
        RemAssign,
        Neg,
        Not,
        BitAnd,
        BitAndAssign,
        BitOr,
        BitOrAssign,
        BitXor,
        BitXorAssign,
        Shl,
        ShlAssign,
        Shr,
        ShrAssign,
        BitNot,
        Contains,
        PartialEq,
        PartialOrd,
        Ord,
        Default,
        Display,
        Debug,
        DebugDisplay,
        OptionalSomeVariant,
        OptionalSomeCtor,
        OptionalNoneVariant,
        OptionalNoneCtor,
        ResultOkVariant,
        ResultOkCtor,
        ResultErrVariant,
        ResultErrCtor,
        Task,
        PanicPayload,
        Deref,
        BenchmarkReport,
        MainErrorReport,
        RawValue,
        CaseIterable,
        DebugValue,
        DebugValueAt,
        DebugString,
        Assert,
        AssertWithMessage,
        DebugAssert,
        DebugAssertWithMessage,
        AssertFail,
        AssertFailWithMessage,
        Closeable,
    ]
);

wire_enum_conversions!(
    abi_to_wire,
    abi_from_wire,
    hir::Abi,
    AbiWire,
    [C, Blocking, Runtime, Intrinsic,]
);

wire_enum_conversions!(
    int_suffix_to_wire,
    int_suffix_from_wire,
    IntegerTypeSuffix,
    IntegerTypeSuffixWire,
    [I8, I16, I32, I64, U8, U16, U32, U64,]
);

#[inline]
pub fn literal_to_wire(v: &hir::Literal) -> LiteralWire {
    match v {
        hir::Literal::Bool(v) => LiteralWire::Bool(*v),
        hir::Literal::Rune(v) => LiteralWire::Rune(*v),
        hir::Literal::String(v) => LiteralWire::String(v.as_str().to_string()),
        hir::Literal::Bytes(v) => LiteralWire::Bytes(v.with_bytes(<[u8]>::to_vec)),
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
        LiteralWire::Bytes(v) => hir::Literal::Bytes(crate::span::InternedBytes::new(v)),
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
        ConstValue::Bytes(v) => ConstValueWire::Bytes(v.with_bytes(<[u8]>::to_vec)),
        ConstValue::Float(v) => ConstValueWire::Float(v),
        ConstValue::Unit => ConstValueWire::Unit,
        ConstValue::EnumUnitVariant(v) => ConstValueWire::EnumUnitVariant(def_to_wire(v)),
        ConstValue::Array(arr) => {
            ConstValueWire::Array(arr.with_elements(|elems| elems.iter().copied().map(const_value_to_wire).collect()))
        }
    }
}

#[inline]
pub fn const_value_from_wire(v: &ConstValueWire) -> ConstValue {
    match v {
        ConstValueWire::Integer(v) => ConstValue::Integer(*v),
        ConstValueWire::Bool(v) => ConstValue::Bool(*v),
        ConstValueWire::Rune(v) => ConstValue::Rune(*v),
        ConstValueWire::String(v) => ConstValue::String(Symbol::new(v)),
        ConstValueWire::Bytes(v) => ConstValue::Bytes(crate::span::InternedBytes::new(v)),
        ConstValueWire::Float(v) => ConstValue::Float(*v),
        ConstValueWire::Unit => ConstValue::Unit,
        ConstValueWire::EnumUnitVariant(v) => ConstValue::EnumUnitVariant(def_from_wire(v)),
        ConstValueWire::Array(elems) => ConstValue::Array(
            crate::sema::models::InternedConstArray::new(
                elems.iter().map(const_value_from_wire).collect(),
            ),
        ),
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

wire_enum_conversions!(
    alias_kind_to_wire,
    alias_kind_from_wire,
    AliasKind,
    AliasKindWire,
    [Inherent, Weak, Projection, Opaque,]
);

wire_enum_conversions!(
    closure_kind_to_wire,
    closure_kind_from_wire,
    ClosureKind,
    ClosureKindWire,
    [Fn, AsyncFn,]
);

#[inline]
pub fn capture_kind_to_wire(v: CaptureKind) -> CaptureKindWire {
    match v {
        CaptureKind::ByCopy => CaptureKindWire::ByCopy,
        CaptureKind::ByRef => CaptureKindWire::ByRef,
    }
}

#[inline]
pub fn capture_kind_from_wire(v: &CaptureKindWire) -> CaptureKind {
    match v {
        CaptureKindWire::ByCopy => CaptureKind::ByCopy,
        CaptureKindWire::ByRef => CaptureKind::ByRef,
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
            TyKind::Reference(ty) => TyKindWire::Reference(Box::new(ty_to_wire(ty))),
            TyKind::Tuple(items) if !v.tuple_labels().is_empty() => TyKindWire::LabeledTuple {
                elements: items.iter().copied().map(ty_to_wire).collect(),
                labels: v
                    .tuple_labels()
                    .iter()
                    .map(|(index, symbol)| (*index, symbol.as_str().to_string()))
                    .collect(),
            },
            TyKind::Tuple(items) => {
                TyKindWire::Tuple(items.iter().copied().map(ty_to_wire).collect())
            }
            TyKind::FnPointer {
                inputs,
                output,
                effects,
            } => TyKindWire::FnPointer {
                kind: closure_kind_to_wire(effects.kind),
                is_unsafe: effects.is_unsafe,
                abi: effects.abi.map(abi_to_wire),
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
            TyKind::ExistentialSelf(depth) => TyKindWire::ExistentialSelf(depth),
            TyKind::Closure {
                closure_def_id,
                kind,
                captured_generics,
                inputs,
                output,
            } => TyKindWire::Closure {
                closure_def_id: def_to_wire(closure_def_id),
                kind: closure_kind_to_wire(kind),
                captured_generics: captured_generics
                    .iter()
                    .copied()
                    .map(generic_arg_to_wire)
                    .collect(),
                inputs: inputs.iter().copied().map(ty_to_wire).collect(),
                output: Box::new(ty_to_wire(output)),
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
        TyKindWire::Reference(ty) => TyKind::Reference(ty_from_wire(gcx, ty)),
        TyKindWire::LabeledTuple { elements, labels } => {
            let elements = elements
                .iter()
                .map(|item| ty_from_wire(gcx, item))
                .collect();
            let labels = gcx.store.arenas.global.alloc_slice_fill_iter(
                labels
                    .iter()
                    .map(|(index, name)| (*index, Symbol::new(name))),
            );
            return Ty::new(
                TyKind::Tuple(gcx.store.interners.intern_ty_list(elements)),
                gcx,
            )
            .with_tuple_labels(labels, gcx);
        }
        TyKindWire::Tuple(items) => {
            let items: Vec<_> = items.iter().map(|item| ty_from_wire(gcx, item)).collect();
            TyKind::Tuple(gcx.store.interners.intern_ty_list(items))
        }
        TyKindWire::FnPointer {
            inputs,
            output,
            kind,
            is_unsafe,
            abi,
        } => {
            let inputs: Vec<_> = inputs.iter().map(|item| ty_from_wire(gcx, item)).collect();
            TyKind::FnPointer {
                effects: crate::sema::models::FunctionPointerEffects {
                    kind: closure_kind_from_wire(kind),
                    is_unsafe: *is_unsafe,
                    abi: abi.as_ref().map(abi_from_wire),
                },
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
        TyKindWire::ExistentialSelf(depth) => TyKind::ExistentialSelf(*depth),
        TyKindWire::Closure {
            closure_def_id,
            kind,
            captured_generics,
            inputs,
            output,
        } => {
            let captured_generics: Vec<_> = captured_generics
                .iter()
                .map(|arg| generic_arg_from_wire(gcx, arg))
                .collect();
            let inputs: Vec<_> = inputs.iter().map(|item| ty_from_wire(gcx, item)).collect();
            TyKind::Closure {
                closure_def_id: def_from_wire(closure_def_id),
                kind: closure_kind_from_wire(kind),
                captured_generics: gcx.store.interners.intern_generic_args(captured_generics),
                inputs: gcx.store.interners.intern_ty_list(inputs),
                output: ty_from_wire(gcx, output),
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
        Visibility::Internal(v) => VisibilityWire::Internal(def_to_wire(v)),
        Visibility::Private(v) => VisibilityWire::Private(def_to_wire(v)),
    }
}

pub fn visibility_from_wire(v: &VisibilityWire) -> Visibility {
    match v {
        VisibilityWire::Public => Visibility::Public,
        VisibilityWire::Internal(v) => Visibility::Internal(def_from_wire(v)),
        VisibilityWire::Private(v) => Visibility::Private(def_from_wire(v)),
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
        TypeHead::Parameter(v) => TypeHeadWire::Parameter(def_to_wire(v)),
        TypeHead::Closure(v) => TypeHeadWire::Closure(def_to_wire(v)),
        TypeHead::Reference => TypeHeadWire::Reference,
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
        TypeHeadWire::Parameter(v) => TypeHead::Parameter(def_from_wire(v)),
        TypeHeadWire::Closure(v) => TypeHead::Closure(def_from_wire(v)),
        TypeHeadWire::Reference => TypeHead::Reference,
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
        is_lazy: v.is_lazy,
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
        is_lazy: v.is_lazy,
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
                is_anonymous: param.is_anonymous,
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
                is_anonymous: param.is_anonymous,
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
        class_info: v.class_info.map(|class| ClassInfoWire {
            initializers: class
                .initializers
                .iter()
                .map(|initializer| ClassInitializerWire {
                    definition: def_to_wire(initializer.definition),
                    family: def_to_wire(initializer.family),
                    implementation: def_to_wire(initializer.implementation),
                    owner: ty_to_wire(initializer.owner),
                    is_convenience: initializer.is_convenience,
                    is_required: initializer.is_required,
                    is_inherited: initializer.is_inherited,
                    delegations: initializer
                        .delegations
                        .iter()
                        .map(|id| def_to_wire(*id))
                        .collect(),
                })
                .collect(),
            base: class.base.map(|ty| ty_to_wire(ty)),
            methods: class
                .methods
                .iter()
                .map(|method| ClassMethodWire {
                    returns_self: method.returns_self,
                    family: def_to_wire(method.family),
                    implementation: def_to_wire(method.implementation),
                    owner: ty_to_wire(method.owner),
                    is_final: method.is_final,
                })
                .collect(),
            payload: class.payload.map(def_to_wire),
            is_final: class.is_final,
        }),
        adt_def: adt_def_to_wire(v.adt_def),
        positional: v.positional,
        has_initializer: v.has_initializer,
        repr: struct_repr_to_wire(v.repr),
        fields: v
            .fields
            .iter()
            .map(|field| StructFieldWire {
                default_provider: field.default_provider.map(def_to_wire),
                name: symbols.intern_symbol(field.name),
                ty: ty_to_wire(field.ty),
                mutability: mutability_to_wire(field.mutability),
                def_id: def_to_wire(field.def_id),
                visibility: visibility_to_wire(field.visibility),
                coding_key: field.coding_key.map(|k| symbols.intern_symbol(k)),
                coding_skip: field.coding_skip,
            })
            .collect(),
    }
}

pub fn struct_definition_from_wire<'a>(
    gcx: GlobalContext<'a>,
    v: &StructDefinitionWire,
    symbols: SymbolTableRef<'_>,
) -> StructDefinition<'a> {
    let fields: Vec<_> = v
        .fields
        .iter()
        .map(|field| StructField {
            default_provider: field.default_provider.as_ref().map(def_from_wire),
            name: Symbol::new(symbols.resolve_str(field.name)),
            ty: ty_from_wire(gcx, &field.ty),
            mutability: mutability_from_wire(&field.mutability),
            def_id: def_from_wire(&field.def_id),
            visibility: visibility_from_wire(&field.visibility),
            coding_key: field
                .coding_key
                .map(|k| Symbol::new(symbols.resolve_str(k))),
            coding_skip: field.coding_skip,
        })
        .collect();
    StructDefinition {
        class_info: v
            .class_info
            .as_ref()
            .map(|class| crate::sema::models::ClassInfo {
                initializers: gcx.store.arenas.global.alloc_slice_copy(
                    &class
                        .initializers
                        .iter()
                        .map(|initializer| crate::sema::models::ClassInitializer {
                            definition: def_from_wire(&initializer.definition),
                            family: def_from_wire(&initializer.family),
                            implementation: def_from_wire(&initializer.implementation),
                            owner: ty_from_wire(gcx, &initializer.owner),
                            is_convenience: initializer.is_convenience,
                            is_required: initializer.is_required,
                            is_inherited: initializer.is_inherited,
                            delegations: gcx.store.arenas.global.alloc_slice_copy(
                                &initializer
                                    .delegations
                                    .iter()
                                    .map(def_from_wire)
                                    .collect::<Vec<_>>(),
                            ),
                        })
                        .collect::<Vec<_>>(),
                ),
                base: class.base.as_ref().map(|ty| ty_from_wire(gcx, ty)),
                methods: gcx.store.arenas.global.alloc_slice_copy(
                    &class
                        .methods
                        .iter()
                        .map(|method| crate::sema::models::ClassMethod {
                            returns_self: method.returns_self,
                            family: def_from_wire(&method.family),
                            implementation: def_from_wire(&method.implementation),
                            owner: ty_from_wire(gcx, &method.owner),
                            is_final: method.is_final,
                        })
                        .collect::<Vec<_>>(),
                ),
                payload: class.payload.as_ref().map(def_from_wire),
                is_final: class.is_final,
            }),
        adt_def: adt_def_from_wire(&v.adt_def),
        positional: v.positional,
        has_initializer: v.has_initializer,
        repr: struct_repr_from_wire(&v.repr),
        fields: gcx.store.arenas.global.alloc_slice_copy(&fields),
    }
}

fn struct_repr_to_wire(v: StructRepr) -> StructReprWire {
    match v {
        StructRepr::Taro => StructReprWire::Taro,
        StructRepr::C => StructReprWire::C,
    }
}

fn struct_repr_from_wire(v: &StructReprWire) -> StructRepr {
    match v {
        StructReprWire::Taro => StructRepr::Taro,
        StructReprWire::C => StructRepr::C,
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
                    EnumVariantKind::Tuple(fields) | EnumVariantKind::Struct(fields) => {
                        let fields = fields
                            .iter()
                            .map(|field| EnumVariantFieldWire {
                                label: field.label.map(|v| symbols.intern_symbol(v)),
                                ty: ty_to_wire(field.ty),
                                mutability: mutability_to_wire(field.mutability),
                            })
                            .collect();
                        if matches!(variant.kind, EnumVariantKind::Struct(..)) {
                            EnumVariantKindWire::Struct(fields)
                        } else {
                            EnumVariantKindWire::Tuple(fields)
                        }
                    }
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
                EnumVariantKindWire::Tuple(fields) | EnumVariantKindWire::Struct(fields) => {
                    let fields: Vec<_> = fields
                        .iter()
                        .map(|field| EnumVariantField {
                            label: field.label.map(|v| Symbol::new(symbols.resolve_str(v))),
                            ty: ty_from_wire(gcx, &field.ty),
                            mutability: mutability_from_wire(&field.mutability),
                        })
                        .collect();
                    let fields = gcx.store.arenas.global.alloc_slice_copy(&fields);
                    if matches!(&variant.kind, EnumVariantKindWire::Struct(..)) {
                        EnumVariantKind::Struct(fields)
                    } else {
                        EnumVariantKind::Tuple(fields)
                    }
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
        properties: v
            .properties
            .iter()
            .map(|property| InterfacePropertyRequirementWire {
                id: def_to_wire(property.id),
                name: symbols.intern_symbol(property.name),
                ty: ty_to_wire(property.ty),
                getter_id: def_to_wire(property.getter_id),
                getter_is_required: property.getter_is_required,
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
                has_default: constant.has_default,
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
        properties: v
            .properties
            .iter()
            .map(
                |property| crate::sema::models::InterfacePropertyRequirement {
                    id: def_from_wire(&property.id),
                    name: Symbol::new(symbols.resolve_str(property.name)),
                    ty: ty_from_wire(gcx, &property.ty),
                    getter_id: def_from_wire(&property.getter_id),
                    getter_is_required: property.getter_is_required,
                },
            )
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
                has_default: constant.has_default,
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

pub fn computed_property_entry_to_wire(
    v: crate::compile::context::ComputedPropertyEntry<'_>,
) -> ComputedPropertyEntryWire {
    ComputedPropertyEntryWire {
        property_id: def_to_wire(v.property_id),
        ty: ty_to_wire(v.ty),
        getter_id: def_to_wire(v.getter_id),
        visibility: visibility_to_wire(v.visibility),
    }
}

pub fn computed_property_entry_from_wire<'a>(
    gcx: GlobalContext<'a>,
    v: &ComputedPropertyEntryWire,
) -> crate::compile::context::ComputedPropertyEntry<'a> {
    crate::compile::context::ComputedPropertyEntry {
        property_id: def_from_wire(&v.property_id),
        ty: ty_from_wire(gcx, &v.ty),
        getter_id: def_from_wire(&v.getter_id),
        visibility: visibility_from_wire(&v.visibility),
    }
}

pub fn type_member_index_to_wire(
    v: &crate::compile::context::TypeMemberIndex,
    symbols: &mut SymbolTableBuilder,
) -> TypeMemberIndexWire {
    TypeMemberIndexWire {
        inherent_constants: v
            .inherent_constants
            .iter()
            .map(|(name, ids)| {
                (
                    symbols.intern_symbol(*name),
                    ids.iter().copied().map(def_to_wire).collect(),
                )
            })
            .collect(),
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
    }
}

pub fn type_member_index_from_wire(
    v: &TypeMemberIndexWire,
    symbols: SymbolTableRef<'_>,
) -> crate::compile::context::TypeMemberIndex {
    crate::compile::context::TypeMemberIndex {
        inherent_constants: v
            .inherent_constants
            .iter()
            .map(|(name, ids)| {
                (
                    Symbol::new(symbols.resolve_str(*name)),
                    ids.iter().map(def_from_wire).collect(),
                )
            })
            .collect(),
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
        interface_sets: Default::default(),
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
                root_ty: ty_to_wire(capture.root_ty),
                projection: capture
                    .projection
                    .iter()
                    .map(|field| (field.field.index() as u32, ty_to_wire(field.ty)))
                    .collect(),
                name: symbols.intern_symbol(capture.name),
                ty: ty_to_wire(capture.ty),
                capture_kind: capture_kind_to_wire(capture.capture_kind),
                source_immutable: capture.source_immutable,
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
                root_ty: ty_from_wire(gcx, &capture.root_ty),
                projection: gcx.store.arenas.global.alloc_slice_clone(
                    &capture
                        .projection
                        .iter()
                        .map(|(field, ty)| crate::sema::models::CaptureProjection {
                            field: crate::thir::FieldIndex::from_raw(*field),
                            ty: ty_from_wire(gcx, ty),
                        })
                        .collect::<Vec<_>>(),
                ),
                name: Symbol::new(symbols.resolve_str(capture.name)),
                ty: ty_from_wire(gcx, &capture.ty),
                capture_kind: capture_kind_from_wire(&capture.capture_kind),
                source_immutable: capture.source_immutable,
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
            SyntheticMethodKind::MemberwiseEncode => SyntheticMethodKindWire::MemberwiseEncode,
            SyntheticMethodKind::MemberwiseDecode => SyntheticMethodKindWire::MemberwiseDecode,
            SyntheticMethodKind::MemberwisePartialOrder => {
                SyntheticMethodKindWire::MemberwisePartialOrder
            }
            SyntheticMethodKind::MemberwiseTotalOrder => {
                SyntheticMethodKindWire::MemberwiseTotalOrder
            }
            SyntheticMethodKind::MemberwiseDefault => SyntheticMethodKindWire::MemberwiseDefault,
            SyntheticMethodKind::MemberwiseDebug => SyntheticMethodKindWire::MemberwiseDebug,
            SyntheticMethodKind::EnumRawValue => SyntheticMethodKindWire::EnumRawValue,
            SyntheticMethodKind::EnumFromRawValue => SyntheticMethodKindWire::EnumFromRawValue,
            SyntheticMethodKind::EnumCaseName => SyntheticMethodKindWire::EnumCaseName,
            SyntheticMethodKind::EnumCaseAt => SyntheticMethodKindWire::EnumCaseAt,
            SyntheticMethodKind::ClosureCall => SyntheticMethodKindWire::ClosureCall,
            SyntheticMethodKind::PropertyFieldGetter(field_index) => {
                SyntheticMethodKindWire::PropertyFieldGetter {
                    field_index: field_index as u32,
                }
            }
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
            SyntheticMethodKindWire::MemberwiseEncode => SyntheticMethodKind::MemberwiseEncode,
            SyntheticMethodKindWire::MemberwiseDecode => SyntheticMethodKind::MemberwiseDecode,
            SyntheticMethodKindWire::MemberwisePartialOrder => {
                SyntheticMethodKind::MemberwisePartialOrder
            }
            SyntheticMethodKindWire::MemberwiseTotalOrder => {
                SyntheticMethodKind::MemberwiseTotalOrder
            }
            SyntheticMethodKindWire::MemberwiseDefault => SyntheticMethodKind::MemberwiseDefault,
            SyntheticMethodKindWire::MemberwiseDebug => SyntheticMethodKind::MemberwiseDebug,
            SyntheticMethodKindWire::EnumRawValue => SyntheticMethodKind::EnumRawValue,
            SyntheticMethodKindWire::EnumFromRawValue => SyntheticMethodKind::EnumFromRawValue,
            SyntheticMethodKindWire::EnumCaseName => SyntheticMethodKind::EnumCaseName,
            SyntheticMethodKindWire::EnumCaseAt => SyntheticMethodKind::EnumCaseAt,
            SyntheticMethodKindWire::ClosureCall => SyntheticMethodKind::ClosureCall,
            SyntheticMethodKindWire::PropertyFieldGetter { field_index } => {
                SyntheticMethodKind::PropertyFieldGetter(field_index as usize)
            }
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
                method_interface: interface_reference_to_wire(virtual_call.method_interface),
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
            method_interface: interface_reference_from_wire(gcx, &virtual_call.method_interface),
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
        kind: synthetic_kind_to_wire(v.kind),
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
            kind: synthetic_kind_from_wire(&v.kind),
            name: Symbol::new(&v.name),
            generics,
            signature,
            span: span_from_wire(&v.span, remap),
        },
    )
}

fn synthetic_kind_to_wire(
    kind: crate::sema::models::SyntheticDefinitionKind,
) -> SyntheticDefinitionKindWire {
    use crate::sema::models::SyntheticDefinitionKind as M;
    use SyntheticDefinitionKindWire as W;
    match kind {
        M::ClassDecoder { class, initializer } => W::ClassDecoder {
            class: def_to_wire(class),
            initializer: def_to_wire(initializer),
        },
        M::ClassDecodingInitializer { class } => W::ClassDecodingInitializer {
            class: def_to_wire(class),
        },
        M::ClassEncoder { class } => W::ClassEncoder {
            class: def_to_wire(class),
        },
        M::ClassPayload { class } => W::ClassPayload {
            class: def_to_wire(class),
        },
        M::ClassPayloadInitializer { class, initializer } => W::ClassPayloadInitializer {
            class: def_to_wire(class),
            initializer: def_to_wire(initializer),
        },
        M::InheritedClassInitializer { class, initializer } => W::InheritedClassInitializer {
            class: def_to_wire(class),
            initializer: def_to_wire(initializer),
        },
        M::InitializerEnvironment { class, initializer } => W::InitializerEnvironment {
            class: def_to_wire(class),
            initializer: def_to_wire(initializer),
        },
        M::InheritedInitializerDefault {
            initializer,
            provider,
        } => W::InheritedInitializerDefault {
            initializer: def_to_wire(initializer),
            provider: def_to_wire(provider),
        },
        M::ClassInitializerDispatch { initializer } => W::ClassInitializerDispatch {
            initializer: def_to_wire(initializer),
        },
        M::ClassConvenienceInitializer { initializer } => W::ClassConvenienceInitializer {
            initializer: def_to_wire(initializer),
        },
        M::ClassConstructionDescriptor { class } => W::ClassConstructionDescriptor {
            class: def_to_wire(class),
        },
        M::ClassObjectDescriptor { class } => W::ClassObjectDescriptor {
            class: def_to_wire(class),
        },
        M::ErasedAsRef { context } => W::ErasedAsRef {
            context: def_to_wire(context),
        },
        M::ErasedPayloadReference { context } => W::ErasedPayloadReference {
            context: def_to_wire(context),
        },
        M::StaticInitializer { storage } => W::StaticInitializer {
            storage: def_to_wire(storage),
        },
        M::StaticReference { storage } => W::StaticReference {
            storage: def_to_wire(storage),
        },
        M::ErasedAsyncSelf { context, method } => W::ErasedAsyncSelf {
            context: def_to_wire(context),
            method: def_to_wire(method),
        },
        M::ErasedAsyncSelfDefault { adapter, provider } => W::ErasedAsyncSelfDefault {
            adapter: def_to_wire(adapter),
            provider: def_to_wire(provider),
        },
        M::ErasedDefault {
            source,
            provider,
            parameter,
        } => W::ErasedDefault {
            source: def_to_wire(source),
            provider: def_to_wire(provider),
            parameter,
        },
        M::ErasedTakeAs { context } => W::ErasedTakeAs {
            context: def_to_wire(context),
        },
        M::ClassDefaultBody { source } => W::ClassDefaultBody {
            source: def_to_wire(source),
        },
        M::AdoptedClassDefault {
            conformance,
            source,
        } => W::AdoptedClassDefault {
            conformance: conformance_id_to_wire(conformance),
            source: def_to_wire(source),
        },
        M::DelegatedMethod {
            conformance,
            source,
            field,
            borrow_field,
        } => W::DelegatedMethod {
            conformance: conformance_id_to_wire(conformance),
            source: def_to_wire(source),
            field,
            borrow_field,
        },
        M::AdoptedClassDefaultArgument { method, provider } => W::AdoptedClassDefaultArgument {
            method: def_to_wire(method),
            provider: def_to_wire(provider),
        },
        M::Ordinary => W::Ordinary,
        M::AsyncPoll => W::AsyncPoll,
        M::BuiltinCopyClone => W::BuiltinCopyClone,
        M::FunctionPointerCall { is_async } => W::FunctionPointerCall { is_async },
        M::TupleClone => W::TupleClone,
        M::ArrayClone => W::ArrayClone,
        M::ClosureClone => W::ClosureClone,
        M::PrimitiveOperator(item) => W::PrimitiveOperator(std_item_to_wire(item)),
        M::TupleConformance(item) => W::TupleConformance(std_item_to_wire(item)),
    }
}
fn synthetic_kind_from_wire(
    kind: &SyntheticDefinitionKindWire,
) -> crate::sema::models::SyntheticDefinitionKind {
    use crate::sema::models::SyntheticDefinitionKind as M;
    use SyntheticDefinitionKindWire as W;
    match kind {
        W::ClassDecoder { class, initializer } => M::ClassDecoder {
            class: def_from_wire(class),
            initializer: def_from_wire(initializer),
        },
        W::ClassDecodingInitializer { class } => M::ClassDecodingInitializer {
            class: def_from_wire(class),
        },
        W::ClassEncoder { class } => M::ClassEncoder {
            class: def_from_wire(class),
        },
        W::ClassPayload { class } => M::ClassPayload {
            class: def_from_wire(class),
        },
        W::ClassPayloadInitializer { class, initializer } => M::ClassPayloadInitializer {
            class: def_from_wire(class),
            initializer: def_from_wire(initializer),
        },
        W::InheritedClassInitializer { class, initializer } => M::InheritedClassInitializer {
            class: def_from_wire(class),
            initializer: def_from_wire(initializer),
        },
        W::InitializerEnvironment { class, initializer } => M::InitializerEnvironment {
            class: def_from_wire(class),
            initializer: def_from_wire(initializer),
        },
        W::InheritedInitializerDefault {
            initializer,
            provider,
        } => M::InheritedInitializerDefault {
            initializer: def_from_wire(initializer),
            provider: def_from_wire(provider),
        },
        W::ClassInitializerDispatch { initializer } => M::ClassInitializerDispatch {
            initializer: def_from_wire(initializer),
        },
        W::ClassConvenienceInitializer { initializer } => M::ClassConvenienceInitializer {
            initializer: def_from_wire(initializer),
        },
        W::ClassConstructionDescriptor { class } => M::ClassConstructionDescriptor {
            class: def_from_wire(class),
        },
        W::ClassObjectDescriptor { class } => M::ClassObjectDescriptor {
            class: def_from_wire(class),
        },
        W::ErasedAsRef { context } => M::ErasedAsRef {
            context: def_from_wire(context),
        },
        W::ErasedPayloadReference { context } => M::ErasedPayloadReference {
            context: def_from_wire(context),
        },
        W::StaticInitializer { storage } => M::StaticInitializer {
            storage: def_from_wire(storage),
        },
        W::StaticReference { storage } => M::StaticReference {
            storage: def_from_wire(storage),
        },
        W::ErasedAsyncSelf { context, method } => M::ErasedAsyncSelf {
            context: def_from_wire(context),
            method: def_from_wire(method),
        },
        W::ErasedAsyncSelfDefault { adapter, provider } => M::ErasedAsyncSelfDefault {
            adapter: def_from_wire(adapter),
            provider: def_from_wire(provider),
        },
        W::ErasedDefault {
            source,
            provider,
            parameter,
        } => M::ErasedDefault {
            source: def_from_wire(source),
            provider: def_from_wire(provider),
            parameter: *parameter,
        },
        W::ErasedTakeAs { context } => M::ErasedTakeAs {
            context: def_from_wire(context),
        },
        W::ClassDefaultBody { source } => M::ClassDefaultBody {
            source: def_from_wire(source),
        },
        W::AdoptedClassDefault {
            conformance,
            source,
        } => M::AdoptedClassDefault {
            conformance: conformance_id_from_wire(&conformance),
            source: def_from_wire(source),
        },
        W::DelegatedMethod {
            conformance,
            source,
            field,
            borrow_field,
        } => M::DelegatedMethod {
            conformance: conformance_id_from_wire(conformance),
            source: def_from_wire(source),
            field: *field,
            borrow_field: *borrow_field,
        },
        W::AdoptedClassDefaultArgument { method, provider } => M::AdoptedClassDefaultArgument {
            method: def_from_wire(method),
            provider: def_from_wire(provider),
        },
        W::Ordinary => M::Ordinary,
        W::AsyncPoll => M::AsyncPoll,
        W::BuiltinCopyClone => M::BuiltinCopyClone,
        W::FunctionPointerCall { is_async } => M::FunctionPointerCall {
            is_async: *is_async,
        },
        W::TupleClone => M::TupleClone,
        W::ArrayClone => M::ArrayClone,
        W::ClosureClone => M::ClosureClone,
        W::PrimitiveOperator(item) => M::PrimitiveOperator(std_item_from_wire(item)),
        W::TupleConformance(item) => M::TupleConformance(std_item_from_wire(item)),
    }
}

wire_enum_conversions!(
    local_kind_to_wire,
    local_kind_from_wire,
    mir::LocalKind,
    LocalKindWire,
    [Param, User, ConstructorSelf, Temp, Return,]
);

wire_enum_conversions!(
    mir_phase_to_wire,
    mir_phase_from_wire,
    mir::MirPhase,
    MirPhaseWire,
    [Built, CfgClean, Lowered,]
);

wire_enum_conversions!(
    unary_op_to_wire,
    unary_op_from_wire,
    mir::UnaryOperator,
    UnaryOperatorWire,
    [LogicalNot, Negate, BitwiseNot,]
);

wire_enum_conversions!(
    binary_op_to_wire,
    binary_op_from_wire,
    mir::BinaryOperator,
    BinaryOperatorWire,
    [
        Add, Sub, Mul, Div, Rem, BitAnd, BitOr, BitXor, BitShl, BitShr, Eql, Lt, Gt, Leq, Geq, Neq,
    ]
);

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
            mir::ConstantKind::Bytes(v) => ConstantKindWire::Bytes(v.with_bytes(<[u8]>::to_vec)),
            mir::ConstantKind::ConstArray(arr) => ConstantKindWire::ConstArray(
                arr.with_elements(|elems| elems.iter().copied().map(const_value_to_wire).collect()),
            ),
            mir::ConstantKind::Integer(v) => ConstantKindWire::Integer(*v),
            mir::ConstantKind::Float(v) => ConstantKindWire::Float(*v),
            mir::ConstantKind::Unit => ConstantKindWire::Unit,
            mir::ConstantKind::Function(id, args, ty) => ConstantKindWire::Function(
                def_to_wire(*id),
                args.iter().copied().map(generic_arg_to_wire).collect(),
                ty_to_wire(*ty),
            ),
            mir::ConstantKind::GlobalVariableAddress(id) => {
                ConstantKindWire::GlobalVariableAddress(def_to_wire(*id))
            }
            mir::ConstantKind::InterfaceConstant(id, args) => ConstantKindWire::InterfaceConstant(
                def_to_wire(*id),
                args.iter().copied().map(generic_arg_to_wire).collect(),
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
            ConstantKindWire::Bytes(v) => {
                mir::ConstantKind::Bytes(crate::span::InternedBytes::new(v))
            }
            ConstantKindWire::ConstArray(elems) => mir::ConstantKind::ConstArray(
                crate::sema::models::InternedConstArray::new(
                    elems.iter().map(const_value_from_wire).collect(),
                ),
            ),
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
            ConstantKindWire::GlobalVariableAddress(id) => {
                mir::ConstantKind::GlobalVariableAddress(def_from_wire(id))
            }
            ConstantKindWire::InterfaceConstant(id, args) => mir::ConstantKind::InterfaceConstant(
                def_from_wire(id),
                gcx.store.interners.intern_generic_args(
                    args.iter()
                        .map(|arg| generic_arg_from_wire(gcx, arg))
                        .collect(),
                ),
            ),
            ConstantKindWire::ConstParam(param) => {
                mir::ConstantKind::ConstParam(generic_param_from_wire(param))
            }
        },
    }
}

pub fn operand_to_wire(v: &mir::Operand<'_>) -> OperandWire {
    match v {
        mir::Operand::Copy(v) => OperandWire::Copy(place_to_wire(v)),

        mir::Operand::CopyWith(v, modifiers) => OperandWire::CopyWith(
            place_to_wire(v),
            CopyModifiersWire {
                init: modifiers.init,
            },
        ),
        mir::Operand::Constant(v) => OperandWire::Constant(mir_constant_to_wire(v)),
    }
}

pub fn operand_from_wire<'a>(gcx: GlobalContext<'a>, v: &OperandWire) -> mir::Operand<'a> {
    match v {
        OperandWire::Copy(v) => mir::Operand::Copy(place_from_wire(gcx, v)),

        OperandWire::CopyWith(v, modifiers) => mir::Operand::CopyWith(
            place_from_wire(gcx, v),
            mir::CopyModifiers {
                init: modifiers.init,
            },
        ),
        OperandWire::Constant(v) => mir::Operand::Constant(mir_constant_from_wire(gcx, v)),
    }
}

pub fn cast_kind_to_wire(v: &mir::CastKind<'_>) -> CastKindWire {
    match v {
        mir::CastKind::Numeric => CastKindWire::Numeric,
        mir::CastKind::BoxExistential => CastKindWire::BoxExistential,
        mir::CastKind::ExistentialUpcast => CastKindWire::ExistentialUpcast,
        mir::CastKind::ClassObjectOwner => CastKindWire::ClassObjectOwner,
        mir::CastKind::NativeClassHandle => CastKindWire::NativeClassHandle,
        mir::CastKind::ClassFromOwner => CastKindWire::ClassFromOwner,
        mir::CastKind::ClassSelfResult => CastKindWire::ClassSelfResult,
        mir::CastKind::ClassUpcast => CastKindWire::ClassUpcast,
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
        CastKindWire::ClassObjectOwner => mir::CastKind::ClassObjectOwner,
        CastKindWire::NativeClassHandle => mir::CastKind::NativeClassHandle,
        CastKindWire::ClassFromOwner => mir::CastKind::ClassFromOwner,
        CastKindWire::ClassSelfResult => mir::CastKind::ClassSelfResult,
        CastKindWire::ClassUpcast => mir::CastKind::ClassUpcast,
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
        mir::Rvalue::Alloc { ty } => RvalueWire::Alloc {
            ty: ty_to_wire(*ty),
        },
        mir::Rvalue::Use(v) => RvalueWire::Use(operand_to_wire(v)),
        mir::Rvalue::CopyValue { source } => RvalueWire::CopyValue {
            source: place_to_wire(source),
        },
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
        mir::Rvalue::Ref { place } => RvalueWire::Ref {
            place: place_to_wire(place),
        },
        mir::Rvalue::CleanupAddress { place } => RvalueWire::CleanupAddress {
            place: place_to_wire(place),
        },
        mir::Rvalue::Discriminant { place } => RvalueWire::Discriminant {
            place: place_to_wire(place),
        },
        mir::Rvalue::Zeroed { ty } => RvalueWire::Zeroed {
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
        RvalueWire::Alloc { ty } => mir::Rvalue::Alloc {
            ty: ty_from_wire(gcx, ty),
        },
        RvalueWire::Use(v) => mir::Rvalue::Use(operand_from_wire(gcx, v)),
        RvalueWire::CopyValue { source } => mir::Rvalue::CopyValue {
            source: place_from_wire(gcx, source),
        },
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
        RvalueWire::Ref { place } => mir::Rvalue::Ref {
            place: place_from_wire(gcx, place),
        },
        RvalueWire::CleanupAddress { place } => mir::Rvalue::CleanupAddress {
            place: place_from_wire(gcx, place),
        },
        RvalueWire::Discriminant { place } => mir::Rvalue::Discriminant {
            place: place_from_wire(gcx, place),
        },
        RvalueWire::Zeroed { ty } => mir::Rvalue::Zeroed {
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
            mir::StatementKind::SourceScope(scope) => {
                StatementKindWire::SourceScope(scope.index() as u32)
            }
            mir::StatementKind::StorageLive(local) => {
                StatementKindWire::StorageLive(local.index() as u32)
            }
            mir::StatementKind::StorageDead(local) => {
                StatementKindWire::StorageDead(local.index() as u32)
            }
            mir::StatementKind::SetInitialized(local) => {
                StatementKindWire::SetInitialized(local.index() as u32)
            }
            mir::StatementKind::Assign(place, rvalue) => {
                StatementKindWire::Assign(place_to_wire(place), rvalue_to_wire(rvalue))
            }

            mir::StatementKind::KeepAlive(operand) => {
                StatementKindWire::KeepAlive(operand_to_wire(operand))
            }
            mir::StatementKind::GcSafepoint(kind) => StatementKindWire::GcSafepoint(*kind),
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
            StatementKindWire::SourceScope(scope) => {
                mir::StatementKind::SourceScope(mir::SourceScopeId::from_raw(*scope))
            }
            StatementKindWire::StorageLive(local) => {
                mir::StatementKind::StorageLive(mir::LocalId::from_raw(*local))
            }
            StatementKindWire::StorageDead(local) => {
                mir::StatementKind::StorageDead(mir::LocalId::from_raw(*local))
            }
            StatementKindWire::SetInitialized(local) => {
                mir::StatementKind::SetInitialized(mir::LocalId::from_raw(*local))
            }
            StatementKindWire::Assign(place, rvalue) => mir::StatementKind::Assign(
                place_from_wire(gcx, place),
                rvalue_from_wire(gcx, rvalue),
            ),

            StatementKindWire::KeepAlive(operand) => {
                mir::StatementKind::KeepAlive(operand_from_wire(gcx, operand))
            }
            StatementKindWire::GcSafepoint(kind) => mir::StatementKind::GcSafepoint(*kind),
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

            mir::TerminatorKind::Yield {
                value,
                resume,
                resume_arg,
                no_result,
                cancel,
                cancel_complete,
                unwind,
            } => TerminatorKindWire::Yield {
                value: operand_to_wire(value),
                resume: resume.index() as u32,
                resume_arg: place_to_wire(resume_arg),
                no_result: no_result.map(|block| block.index() as u32),
                cancel: cancel.index() as u32,
                cancel_complete: cancel_complete.index() as u32,
                unwind: unwind_to_wire(*unwind),
            },
            mir::TerminatorKind::GeneratorYield {
                value,
                resume,
                cancel,
                cancel_complete,
            } => TerminatorKindWire::GeneratorYield {
                value: operand_to_wire(value),
                resume: resume.index() as u32,
                cancel: cancel.index() as u32,
                cancel_complete: cancel_complete.index() as u32,
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

            TerminatorKindWire::Yield {
                value,
                resume,
                resume_arg,
                no_result,
                cancel,
                cancel_complete,
                unwind,
            } => mir::TerminatorKind::Yield {
                value: operand_from_wire(gcx, value),
                resume: mir::BasicBlockId::from_raw(*resume),
                resume_arg: place_from_wire(gcx, resume_arg),
                no_result: no_result.map(mir::BasicBlockId::from_raw),
                cancel: mir::BasicBlockId::from_raw(*cancel),
                cancel_complete: mir::BasicBlockId::from_raw(*cancel_complete),
                unwind: unwind_from_wire(unwind),
            },
            TerminatorKindWire::GeneratorYield {
                value,
                resume,
                cancel,
                cancel_complete,
            } => mir::TerminatorKind::GeneratorYield {
                value: operand_from_wire(gcx, value),
                resume: mir::BasicBlockId::from_raw(*resume),
                cancel: mir::BasicBlockId::from_raw(*cancel),
                cancel_complete: mir::BasicBlockId::from_raw(*cancel_complete),
            },
        },
        span: span_from_wire(&v.span, remap),
    }
}

pub fn mir_body_to_wire(v: &mir::Body<'_>) -> BodyWire {
    BodyWire {
        owner: def_to_wire(v.owner),
        source_scopes: v
            .source_scopes
            .iter()
            .map(|scope| SourceScopeDataWire {
                definition: def_to_wire(scope.definition),
                callsite: scope.callsite.map(span_to_wire),
                parent: scope.parent.map(|parent| parent.index() as u32),
            })
            .collect(),
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
        phase: mir_phase_to_wire(v.phase),
        is_async: v.is_async,
    }
}

pub fn mir_body_from_wire<'a>(
    gcx: GlobalContext<'a>,
    v: &BodyWire,
    remap: FileRemap<'_>,
) -> mir::Body<'a> {
    mir::Body {
        escape_locals: Vec::new(),

        owner: def_from_wire(&v.owner),
        source_scopes: v
            .source_scopes
            .iter()
            .map(|scope| mir::SourceScopeData {
                definition: def_from_wire(&scope.definition),
                callsite: scope
                    .callsite
                    .as_ref()
                    .map(|span| span_from_wire(span, remap)),
                parent: scope.parent.map(mir::SourceScopeId::from_raw),
            })
            .collect(),
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
        phase: mir_phase_from_wire(&v.phase),
        is_async: v.is_async,
        generator_element_ty: None,
    }
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

/// Validate every scope reference and return parents before children for allocation.
fn validate_scope_graph_for_hydration(
    wire: &ResolutionOutputWire,
) -> Result<Vec<usize>, WireDecodeError> {
    fn scope_idx(scope_id: u32, count: usize, context: &str) -> Result<usize, WireDecodeError> {
        let index = scope_id as usize;
        if index >= count {
            return Err(WireDecodeError::new(format!(
                "{context}: invalid scope index {scope_id} (scope count = {count})",
            )));
        }
        Ok(index)
    }
    let count = wire.scopes.len();
    scope_idx(wire.root_scope, count, "root scope")?;
    for (_, scope) in &wire.file_scope_mapping {
        scope_idx(*scope, count, "file scope mapping")?;
    }
    for (_, scope) in &wire.definition_scope_mapping {
        scope_idx(*scope, count, "definition scope mapping")?;
    }
    for scope in &wire.scopes {
        for (usages, context) in [
            (&scope.glob_imports, "glob import module scope"),
            (&scope.glob_exports, "glob export module scope"),
        ] {
            for usage in usages {
                if let Some(index) = usage.module_scope {
                    scope_idx(index, count, context)?;
                }
            }
        }
    }

    #[derive(Clone, Copy)]
    enum State {
        Unvisited,
        Visiting,
        Visited,
    }
    let mut states = vec![State::Unvisited; count];
    let mut order = Vec::with_capacity(count);
    let mut path = Vec::new();
    for start in 0..count {
        let mut index = start;
        loop {
            match states[index] {
                State::Visited => break,
                State::Visiting => {
                    return Err(WireDecodeError::new(format!(
                        "cycle detected while validating scope graph at index {index}",
                    )));
                }
                State::Unvisited => {}
            }
            states[index] = State::Visiting;
            path.push(index);
            let Some(parent) = wire.scopes[index].parent else {
                break;
            };
            index = scope_idx(parent, count, "scope parent")?;
        }
        for index in path.drain(..).rev() {
            states[index] = State::Visited;
            order.push(index);
        }
    }
    Ok(order)
}

pub fn resolution_output_from_wire<'a>(
    gcx: GlobalContext<'a>,
    wire: &ResolutionOutputWire,
    remap: FileRemap<'_>,
    symbols: SymbolTableRef<'_>,
) -> Result<ResolutionOutput<'a>, WireDecodeError> {
    let scope_order = validate_scope_graph_for_hydration(wire)?;

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
    for index in scope_order {
        let scope = &wire.scopes[index];
        let parent = scope.parent.map(|parent| {
            built_scopes[parent as usize].expect("validated parent is built before its children")
        });
        let kind = scope_kind_from_wire(&scope.kind, remap);
        built_scopes[index] = Some(Interned::new_unchecked(
            gcx.store.arenas.scopes.alloc(ScopeData::new(kind, parent)),
        ));
    }
    let scope_by_id = |index: u32| built_scopes[index as usize].expect("validated scope is built");

    for (idx, scope_wire) in wire.scopes.iter().enumerate() {
        let scope = scope_by_id(idx as u32);
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
            let module_scope = usage.module_scope.map(scope_by_id);
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
            let module_scope = usage.module_scope.map(scope_by_id);
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

    let root_scope = scope_by_id(wire.root_scope);
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
            .map(|(def, vis)| (def_from_wire(def), visibility_from_wire(vis)))
            .collect(),
        file_scope_mapping: wire
            .file_scope_mapping
            .iter()
            .filter_map(|(file, scope)| {
                let file = remap.old_to_new.get(file).copied()?;
                let scope = scope_by_id(*scope);
                Some((file, scope))
            })
            .collect(),
        definition_scope_mapping: wire
            .definition_scope_mapping
            .iter()
            .map(|(def, scope)| (def_from_wire(def), scope_by_id(*scope)))
            .collect(),
        block_scope_mapping: FxHashMap::default(),
        // Source-only speculative diagnostics never cross a package boundary;
        // exported checked MIR already contains the chosen bracket branch.
        member_bracket_diagnostics: FxHashMap::default(),
        break_label_resolutions: FxHashMap::default(),
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
        def_to_static_mutability: db
            .def_to_static_mutability
            .iter()
            .map(|(def, mutability)| (def_to_wire(*def), mutability_to_wire(*mutability)))
            .collect(),

        def_to_class_default_contract: db
            .def_to_class_default_contract
            .iter()
            .map(|(id, contract)| (def_to_wire(*id), *contract))
            .collect(),
        erased_async_self_arguments: db
            .erased_async_self_arguments
            .iter()
            .map(|(id, args)| {
                (
                    def_to_wire(*id),
                    args.iter().copied().map(generic_arg_to_wire).collect(),
                )
            })
            .collect(),
        class_adoptions: db
            .class_adoptions
            .iter()
            .map(|adoption| {
                (
                    conformance_id_to_wire(adoption.conformance),
                    adoption
                        .methods
                        .iter()
                        .map(|method| ClassWitnessMethodWire {
                            requirement: def_to_wire(method.requirement),
                            slot: ClassMethodWire {
                                returns_self: method.slot.returns_self,
                                family: def_to_wire(method.slot.family),
                                implementation: def_to_wire(method.slot.implementation),
                                owner: ty_to_wire(method.slot.owner),
                                is_final: method.slot.is_final,
                            },
                            is_registered: method.is_registered,
                        })
                        .collect(),
                )
            })
            .collect(),

        def_to_fn_sig: db
            .def_to_fn_sig
            .iter()
            .map(|(def, sig)| (def_to_wire(*def), signature_to_wire(sig)))
            .collect(),
        def_to_async_body_output: db
            .def_to_async_body_output
            .iter()
            .map(|(def, ty)| (def_to_wire(*def), ty_to_wire(*ty)))
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
        class_subscripts: db
            .class_subscripts
            .iter()
            .map(|(class, entries)| {
                (
                    def_to_wire(*class),
                    entries
                        .iter()
                        .map(|(id, entry)| {
                            (
                                def_to_wire(*id),
                                NativeSubscriptEntryWire {
                                    getter: entry.getter.map(def_to_wire),
                                    setter: entry.setter.map(def_to_wire),
                                    address: entry.address.map(def_to_wire),
                                    getter_is_default: entry.getter_is_default,
                                    setter_is_default: entry.setter_is_default,
                                    is_override: entry.is_override,
                                    is_final: entry.is_final,
                                },
                            )
                        })
                        .collect(),
                )
            })
            .collect(),
        native_subscripts: db
            .native_subscripts
            .iter()
            .map(|(&id, entry)| {
                (
                    def_to_wire(id),
                    NativeSubscriptEntryWire {
                        getter: entry.getter.map(def_to_wire),
                        setter: entry.setter.map(def_to_wire),
                        address: entry.address.map(def_to_wire),
                        getter_is_default: entry.getter_is_default,
                        setter_is_default: entry.setter_is_default,
                        is_override: entry.is_override,
                        is_final: entry.is_final,
                    },
                )
            })
            .collect(),
        type_head_to_properties: db
            .type_head_to_properties
            .iter()
            .map(|(head, properties)| {
                (
                    type_head_to_wire(*head),
                    properties
                        .iter()
                        .map(|(name, property)| {
                            (
                                symbols.intern_symbol(*name),
                                computed_property_entry_to_wire(*property),
                            )
                        })
                        .collect(),
                )
            })
            .collect(),
        type_head_to_interface_properties: db
            .type_head_to_interface_properties
            .iter()
            .map(|(head, properties)| {
                (
                    type_head_to_wire(*head),
                    properties
                        .iter()
                        .map(|((interface_id, name), entries)| {
                            (
                                (def_to_wire(*interface_id), symbols.intern_symbol(*name)),
                                entries
                                    .iter()
                                    .copied()
                                    .map(computed_property_entry_to_wire)
                                    .collect(),
                            )
                        })
                        .collect(),
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
        def_to_unsafe: db.def_to_unsafe.iter().copied().map(def_to_wire).collect(),
        def_to_const_fn: db.def_to_const_fn.iter().copied().map(def_to_wire).collect(),
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
        resolved_interface_aliases: db
            .resolved_interface_aliases
            .iter()
            .map(|(def, interfaces)| {
                (
                    def_to_wire(*def),
                    interfaces
                        .iter()
                        .copied()
                        .map(interface_reference_to_wire)
                        .collect(),
                )
            })
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
        def_to_class_default_contract: wire
            .def_to_class_default_contract
            .iter()
            .map(|(id, contract)| (def_from_wire(id), *contract))
            .collect(),
        erased_async_self_arguments: wire
            .erased_async_self_arguments
            .iter()
            .map(|(id, args)| {
                (
                    def_from_wire(id),
                    gcx.store.interners.intern_generic_args(
                        args.iter()
                            .map(|arg| generic_arg_from_wire(gcx, arg))
                            .collect(),
                    ),
                )
            })
            .collect(),
        class_adoptions: wire
            .class_adoptions
            .iter()
            .map(
                |(conformance, methods)| crate::sema::models::ClassAdoption {
                    conformance: conformance_id_from_wire(conformance),
                    methods: gcx.store.arenas.global.alloc_slice_copy(
                        &methods
                            .iter()
                            .map(|method| crate::sema::models::ClassWitnessMethod {
                                requirement: def_from_wire(&method.requirement),
                                slot: crate::sema::models::ClassMethod {
                                    returns_self: method.slot.returns_self,
                                    family: def_from_wire(&method.slot.family),
                                    implementation: def_from_wire(&method.slot.implementation),
                                    owner: ty_from_wire(gcx, &method.slot.owner),
                                    is_final: method.slot.is_final,
                                },
                                is_registered: method.is_registered,
                            })
                            .collect::<Vec<_>>(),
                    ),
                },
            )
            .collect(),

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
        def_to_static_mutability: wire
            .def_to_static_mutability
            .iter()
            .map(|(def, mutability)| (def_from_wire(def), mutability_from_wire(mutability)))
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
        def_to_async_body_output: wire
            .def_to_async_body_output
            .iter()
            .map(|(def, ty)| (def_from_wire(def), ty_from_wire(gcx, ty)))
            .collect(),
        def_to_struct_def: wire
            .def_to_struct_def
            .iter()
            .map(|(def, st)| {
                let st: &'a StructDefinition<'a> = gcx
                    .store
                    .arenas
                    .struct_definitions
                    .alloc(struct_definition_from_wire(gcx, st, symbols));
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
        class_subscripts: wire
            .class_subscripts
            .iter()
            .map(|(class, entries)| {
                (
                    def_from_wire(class),
                    entries
                        .iter()
                        .map(|(id, entry)| {
                            (
                                def_from_wire(id),
                                crate::compile::context::NativeSubscriptEntry {
                                    getter: entry.getter.as_ref().map(def_from_wire),
                                    setter: entry.setter.as_ref().map(def_from_wire),
                                    address: entry.address.as_ref().map(def_from_wire),
                                    getter_is_default: entry.getter_is_default,
                                    setter_is_default: entry.setter_is_default,
                                    is_override: entry.is_override,
                                    is_final: entry.is_final,
                                },
                            )
                        })
                        .collect(),
                )
            })
            .collect(),
        native_subscripts: wire
            .native_subscripts
            .iter()
            .map(|(id, entry)| {
                (
                    def_from_wire(id),
                    crate::compile::context::NativeSubscriptEntry {
                        getter: entry.getter.as_ref().map(def_from_wire),
                        setter: entry.setter.as_ref().map(def_from_wire),
                        address: entry.address.as_ref().map(def_from_wire),
                        getter_is_default: entry.getter_is_default,
                        setter_is_default: entry.setter_is_default,
                        is_override: entry.is_override,
                        is_final: entry.is_final,
                    },
                )
            })
            .collect(),
        type_head_to_properties: wire
            .type_head_to_properties
            .iter()
            .map(|(head, properties)| {
                (
                    type_head_from_wire(head),
                    properties
                        .iter()
                        .map(|(name, property)| {
                            (
                                Symbol::new(symbols.resolve_str(*name)),
                                computed_property_entry_from_wire(gcx, property),
                            )
                        })
                        .collect(),
                )
            })
            .collect(),
        type_head_to_interface_properties: wire
            .type_head_to_interface_properties
            .iter()
            .map(|(head, properties)| {
                (
                    type_head_from_wire(head),
                    properties
                        .iter()
                        .map(|((interface_id, name), entries)| {
                            (
                                (
                                    def_from_wire(interface_id),
                                    Symbol::new(symbols.resolve_str(*name)),
                                ),
                                entries
                                    .iter()
                                    .map(|entry| computed_property_entry_from_wire(gcx, entry))
                                    .collect(),
                            )
                        })
                        .collect(),
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
        def_to_unsafe: wire.def_to_unsafe.iter().map(def_from_wire).collect(),
        def_to_const_fn: wire.def_to_const_fn.iter().map(def_from_wire).collect(),
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
        resolved_interface_aliases: wire
            .resolved_interface_aliases
            .iter()
            .map(|(def, interfaces)| {
                let interfaces = interfaces
                    .iter()
                    .map(|interface| interface_reference_from_wire(gcx, interface))
                    .collect::<Vec<_>>();
                (
                    def_from_wire(def),
                    gcx.store.arenas.global.alloc_slice_clone(&interfaces) as &'a [_],
                )
            })
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

    #[test]
    fn internal_visibility_roundtrips_with_its_defining_package_identity() {
        let owner = DefinitionID::new(PackageIndex::from_raw(7), DefinitionIndex::from_raw(19));
        let visibility = Visibility::Internal(owner);
        let encoded = visibility_to_wire(visibility);
        assert_eq!(visibility_from_wire(&encoded), visibility);
    }

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
    fn enum_payload_mutability_and_labels_roundtrip_through_wire() {
        crate::mir::test_support::with_test_gcx(|gcx| {
            let definition = DefinitionID::new(
                crate::PackageIndex::new(2),
                crate::sema::resolve::models::DefinitionIndex::from_raw(7),
            );
            let fields = gcx.store.arenas.global.alloc_slice_copy(&[
                EnumVariantField {
                    label: Some(gcx.intern_symbol("fixed")),
                    ty: gcx.types.int32,
                    mutability: hir::Mutability::Immutable,
                },
                EnumVariantField {
                    label: Some(gcx.intern_symbol("editable")),
                    ty: gcx.types.int32,
                    mutability: hir::Mutability::Mutable,
                },
            ]);
            let item = EnumVariant {
                name: gcx.intern_symbol("item"),
                def_id: definition,
                ctor_def_id: definition,
                kind: EnumVariantKind::Struct(fields),
                discriminant: 0,
            };
            let variants = gcx.store.arenas.global.alloc_slice_copy(&[
                item,
                EnumVariant {
                    kind: EnumVariantKind::Struct(&[]),
                    ..item
                },
                EnumVariant {
                    kind: EnumVariantKind::Tuple(&[]),
                    ..item
                },
                EnumVariant {
                    kind: EnumVariantKind::Unit,
                    ..item
                },
                EnumVariant {
                    kind: EnumVariantKind::Tuple(fields),
                    ..item
                },
            ]);
            let original = EnumDefinition {
                adt_def: AdtDef {
                    id: definition,
                    kind: AdtKind::Enum,
                },
                variants,
            };
            let mut symbols = SymbolTableBuilder::default();
            let wire = enum_definition_to_wire(&original, &mut symbols);
            let table = symbols.finish();
            let invalid = Cell::new(None);
            let restored =
                enum_definition_from_wire(gcx, &wire, SymbolTableRef::new(&table, &invalid));
            let EnumVariantKind::Struct(decoded) = restored.variants[0].kind else {
                panic!("struct payload")
            };
            assert_eq!(decoded, fields);
            assert!(matches!(
                restored.variants[1].kind,
                EnumVariantKind::Struct([])
            ));
            assert!(matches!(
                restored.variants[2].kind,
                EnumVariantKind::Tuple([])
            ));
            assert!(matches!(restored.variants[3].kind, EnumVariantKind::Unit));
            assert!(
                matches!(restored.variants[4].kind, EnumVariantKind::Tuple(decoded) if decoded == fields)
            );
            assert!(invalid.get().is_none());
        });
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
    fn from_std_item_roundtrips_through_wire() {
        for item in [
            hir::StdItem::From,
            hir::StdItem::Span,
            hir::StdItem::ListIterator,
            hir::StdItem::ClassHandle,
            hir::StdItem::AnyObject,
            hir::StdItem::MainErrorReport,
        ] {
            let wire = std_item_to_wire(item);
            assert_eq!(std_item_from_wire(&wire), item);
        }
    }

    #[test]
    fn primitive_operator_roles_survive_metadata_roundtrip() {
        // The role is part of the helper's identity, not merely its display
        // name: importing Sub as Add would silently change generic behavior.
        for &item in crate::mir::primitive_operators::ITEMS {
            for kind in [crate::sema::models::SyntheticDefinitionKind::PrimitiveOperator(item)] {
                let wire = synthetic_kind_to_wire(kind);
                assert_eq!(synthetic_kind_from_wire(&wire), kind);
            }
        }
    }

    #[test]
    fn function_abis_roundtrip_through_wire() {
        for abi in [
            hir::Abi::C,
            hir::Abi::Blocking,
            hir::Abi::Runtime,
            hir::Abi::Intrinsic,
        ] {
            let wire = abi_to_wire(abi);
            assert_eq!(abi_from_wire(&wire), abi);
        }
    }

    #[test]
    fn managed_allocation_roundtrips_without_instance_placement_state() {
        crate::mir::test_support::with_test_gcx(|gcx| {
            let value = mir::Rvalue::Alloc {
                ty: gcx.types.int32,
            };
            let decoded = rvalue_from_wire(gcx, &rvalue_to_wire(&value));
            assert!(matches!(decoded, mir::Rvalue::Alloc { ty } if ty == gcx.types.int32));
            let mut body = crate::mir::test_support::minimal_body(gcx);
            body.escape_locals.fill(true);
            let span = body.locals[body.return_local].span;
            let files = FxHashMap::from_iter([(span.file.index() as u32, span.file)]);
            let decoded = mir_body_from_wire(
                gcx,
                &mir_body_to_wire(&body),
                FileRemap { old_to_new: &files },
            );
            assert!(
                decoded.escape_locals.is_empty(),
                "placement must be recomputed for each concrete instance"
            );
        });
    }

    #[test]
    fn cleanup_storage_address_roundtrips_as_a_raw_pointer_not_a_borrow() {
        crate::mir::test_support::with_test_gcx(|gcx| {
            let mut body = crate::mir::test_support::minimal_body(gcx);
            let source = crate::mir::test_support::push_temp(&mut body, gcx.types.int32);
            let pointer = Ty::new(
                TyKind::Pointer(gcx.types.int32, hir::Mutability::Mutable),
                gcx,
            );
            let destination = crate::mir::test_support::push_temp(&mut body, pointer);
            let value = mir::Rvalue::CleanupAddress {
                place: mir::Place::from_local(source),
            };
            let decoded = rvalue_from_wire(gcx, &rvalue_to_wire(&value));
            assert!(
                matches!(&decoded, mir::Rvalue::CleanupAddress { place } if place.local == source)
            );
            body.basic_blocks[body.start_block]
                .statements
                .push(mir::Statement {
                    span: body.locals[source].span,
                    kind: mir::StatementKind::Assign(mir::Place::from_local(destination), decoded),
                });
            assert!(
                crate::mir::optimize::validate::validate_body_structure(
                    gcx,
                    &body,
                    "cleanup storage address wire roundtrip"
                )
                .is_ok()
            );
        });
    }

    #[test]
    fn reference_capture_and_address_roundtrip_through_wire() {
        crate::mir::test_support::with_test_gcx(|gcx| {
            assert!(matches!(
                capture_kind_from_wire(&capture_kind_to_wire(CaptureKind::ByRef)),
                CaptureKind::ByRef
            ));
            let mut body = crate::mir::test_support::minimal_body(gcx);
            let ty = Ty::new(TyKind::Reference(gcx.types.int32), gcx);
            let source = crate::mir::test_support::push_temp(&mut body, ty);
            body.locals[source].mutable = false;
            let destination =
                crate::mir::test_support::push_temp(&mut body, Ty::new(TyKind::Reference(ty), gcx));
            let value = mir::Rvalue::Ref {
                place: mir::Place::from_local(source),
            };
            let decoded = rvalue_from_wire(gcx, &rvalue_to_wire(&value));
            assert!(matches!(&decoded, mir::Rvalue::Ref { place } if place.local == source));
            body.basic_blocks[body.start_block]
                .statements
                .push(mir::Statement {
                    span: body.locals[source].span,
                    kind: mir::StatementKind::Assign(mir::Place::from_local(destination), decoded),
                });
            assert!(
                crate::mir::optimize::validate::validate_body_structure(
                    gcx,
                    &body,
                    "reference capture wire roundtrip"
                )
                .is_ok()
            );
            assert!(crate::mir::optimize::validate::validate_mutability(gcx, &body).is_ok());
        });
    }

    #[test]
    fn mir_inline_source_scopes_and_initialization_roundtrip_through_wire() {
        crate::mir::test_support::with_test_gcx(|gcx| {
            let mut body = crate::mir::test_support::minimal_body(gcx);
            let nested_definition = DefinitionID::new(
                crate::PackageIndex::new(2),
                crate::sema::resolve::models::DefinitionIndex::from_raw(7),
            );
            let span = body.locals[body.return_local].span;
            let nested_scope = body.source_scopes.push(mir::SourceScopeData {
                definition: nested_definition,
                callsite: Some(span),
                parent: Some(mir::SourceScopeId::from_raw(0)),
            });
            body.basic_blocks[body.start_block]
                .statements
                .push(mir::Statement {
                    kind: mir::StatementKind::SourceScope(nested_scope),
                    span,
                });
            body.basic_blocks[body.start_block]
                .statements
                .push(mir::Statement {
                    kind: mir::StatementKind::SetInitialized(body.return_local),
                    span,
                });

            let wire = mir_body_to_wire(&body);
            let file_remap = FxHashMap::from_iter([(span.file.index() as u32, span.file)]);
            let decoded = mir_body_from_wire(
                gcx,
                &wire,
                FileRemap {
                    old_to_new: &file_remap,
                },
            );

            assert_eq!(decoded.source_scopes.len(), 2);
            assert_eq!(
                decoded.source_scopes[nested_scope].definition,
                nested_definition
            );
            assert_eq!(
                decoded.source_scopes[nested_scope].parent,
                Some(mir::SourceScopeId::from_raw(0))
            );
            assert!(matches!(
                decoded.basic_blocks[decoded.start_block].statements[0].kind,
                mir::StatementKind::SourceScope(scope) if scope == nested_scope
            ));
            assert!(matches!(
                decoded.basic_blocks[decoded.start_block].statements[1].kind,
                mir::StatementKind::SetInitialized(local) if local == decoded.return_local
            ));
        });
    }

    #[test]
    fn hydration_rejects_invalid_scope_mappings_instead_of_dropping_them() {
        crate::mir::test_support::with_test_gcx(|gcx| {
            let file_remap = FxHashMap::from_iter([(0, FileID::new(0))]);
            let table = SymbolTableWire { symbols: vec![] };
            let invalid = Cell::new(None);
            for file_mapping in [true, false] {
                let mut wire = minimal_resolution_wire();
                if file_mapping {
                    wire.file_scope_mapping.push((0, 99));
                } else {
                    wire.definition_scope_mapping.push((
                        DefIdWire {
                            package: 1,
                            index: 0,
                        },
                        99,
                    ));
                }
                let result = resolution_output_from_wire(
                    gcx,
                    &wire,
                    FileRemap {
                        old_to_new: &file_remap,
                    },
                    SymbolTableRef::new(&table, &invalid),
                );
                assert!(result.is_err(), "invalid scope mapping must fail hydration");
            }
        });
    }

    #[test]
    fn hydration_builds_out_of_order_parents_and_cyclic_glob_references() {
        crate::mir::test_support::with_test_gcx(|gcx| {
            let file_remap = FxHashMap::from_iter([(0, FileID::new(0))]);
            let table = SymbolTableWire { symbols: vec![] };
            let invalid = Cell::new(None);
            let mut wire = minimal_resolution_wire();
            wire.scopes.push(wire.scopes[0].clone());
            wire.scopes[0].parent = Some(1);
            wire.root_scope = 1;
            wire.file_scope_mapping.push((0, 0));
            wire.scopes[0].glob_imports.push(GlobUsageWire {
                id: 0,
                span: span_to_wire(Span::empty(FileID::new(0))),
                module_scope: Some(1),
            });
            wire.scopes[1].glob_exports.push(GlobUsageWire {
                id: 1,
                span: span_to_wire(Span::empty(FileID::new(0))),
                module_scope: Some(0),
            });
            let output = resolution_output_from_wire(
                gcx,
                &wire,
                FileRemap {
                    old_to_new: &file_remap,
                },
                SymbolTableRef::new(&table, &invalid),
            )
            .expect("valid parent and glob graphs");
            let child = output.file_scope_mapping[&FileID::new(0)];
            assert_eq!(child.parent, Some(output.root_scope));
            assert!(output.root_scope.parent.is_none());
            assert_eq!(
                child.glob_imports.borrow()[0].module_scope.get(),
                Some(output.root_scope)
            );
            assert_eq!(
                output.root_scope.glob_exports.borrow()[0]
                    .module_scope
                    .get(),
                Some(child)
            );

            for imported in [true, false] {
                let mut invalid_wire = wire.clone();
                let usage = if imported {
                    &mut invalid_wire.scopes[0].glob_imports[0]
                } else {
                    &mut invalid_wire.scopes[1].glob_exports[0]
                };
                usage.module_scope = Some(99);
                assert!(validate_scope_graph_for_hydration(&invalid_wire).is_err());
            }
        });
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

    #[test]
    fn struct_initializer_and_defaults_survive_metadata() {
        crate::mir::test_support::with_test_gcx(|gcx| {
            let definition = crate::mir::test_support::minimal_body(gcx).owner;
            let original = StructDefinition {
                class_info: None,
                adt_def: AdtDef {
                    id: definition,
                    kind: AdtKind::Struct,
                },
                positional: false,
                has_initializer: true,
                repr: StructRepr::Taro,
                fields: gcx.store.arenas.global.alloc_slice_copy(&[StructField {
                    default_provider: Some(definition),
                    name: gcx.intern_symbol("value"),
                    ty: gcx.types.int32,
                    mutability: crate::hir::Mutability::Immutable,
                    def_id: definition,
                    visibility: Visibility::Public,
                    coding_key: Some(gcx.intern_symbol("display_value")),
                    coding_skip: false,
                }]),
            };
            let mut symbols = SymbolTableBuilder::default();
            let wire = struct_definition_to_wire(&original, &mut symbols);
            let table = symbols.finish();
            let invalid = Cell::new(None);
            let decoded =
                struct_definition_from_wire(gcx, &wire, SymbolTableRef::new(&table, &invalid));
            assert!(decoded.has_initializer);
            assert_eq!(decoded.fields[0].default_provider, Some(definition));
            assert_eq!(
                decoded.fields[0].coding_key,
                Some(gcx.intern_symbol("display_value"))
            );
            assert!(!decoded.fields[0].coding_skip);
            assert_eq!(decoded.fields[0].ty, gcx.types.int32);
        });
    }

    #[test]
    fn nominal_class_metadata_roundtrips() {
        crate::mir::test_support::with_test_gcx(|gcx| {
            let id = crate::mir::test_support::minimal_body(gcx).owner;
            for is_final in [false, true] {
                let class = Ty::new(
                    TyKind::Adt(
                        AdtDef {
                            id,
                            kind: AdtKind::Struct,
                        },
                        crate::sema::models::GenericArguments::empty(),
                    ),
                    gcx,
                );
                let initializers = gcx.store.arenas.global.alloc_slice_copy(&[
                    crate::sema::models::ClassInitializer {
                        definition: id,
                        family: id,
                        implementation: id,
                        owner: class,
                        is_convenience: is_final,
                        is_required: !is_final,
                        is_inherited: false,
                        delegations: gcx.store.arenas.global.alloc_slice_copy(&[id]),
                    },
                ]);
                let original = StructDefinition {
                    adt_def: AdtDef {
                        id,
                        kind: AdtKind::Struct,
                    },
                    class_info: Some(crate::sema::models::ClassInfo {
                        initializers,
                        base: None,
                        methods: &[],
                        payload: Some(id),
                        is_final,
                    }),
                    positional: false,
                    has_initializer: true,
                    repr: StructRepr::Taro,
                    fields: &[],
                };
                let mut symbols = SymbolTableBuilder::default();
                let wire = struct_definition_to_wire(&original, &mut symbols);
                let table = symbols.finish();
                let invalid = Cell::new(None);
                let decoded =
                    struct_definition_from_wire(gcx, &wire, SymbolTableRef::new(&table, &invalid));
                assert_eq!(decoded.class_info, original.class_info);
                assert!(decoded.has_initializer);
            }
        });
    }

    #[test]
    fn inherited_initializer_synthetic_kinds_roundtrip() {
        let class = crate::hir::DefinitionID::new(
            crate::PackageIndex::new(3),
            crate::sema::resolve::models::DefinitionIndex::from_raw(17),
        );
        let initializer = crate::hir::DefinitionID::new(
            crate::PackageIndex::new(2),
            crate::sema::resolve::models::DefinitionIndex::from_raw(29),
        );
        for kind in [
            crate::sema::models::SyntheticDefinitionKind::ErasedTakeAs { context: class },
            crate::sema::models::SyntheticDefinitionKind::ErasedAsRef { context: class },
            crate::sema::models::SyntheticDefinitionKind::ErasedPayloadReference { context: class },
            crate::sema::models::SyntheticDefinitionKind::ErasedDefault {
                source: class,
                provider: initializer,
                parameter: 2,
            },
            crate::sema::models::SyntheticDefinitionKind::ErasedAsyncSelf {
                context: class,
                method: initializer,
            },
            crate::sema::models::SyntheticDefinitionKind::ErasedAsyncSelfDefault {
                adapter: class,
                provider: initializer,
            },
            crate::sema::models::SyntheticDefinitionKind::ClassInitializerDispatch { initializer },
            crate::sema::models::SyntheticDefinitionKind::ClassConvenienceInitializer {
                initializer,
            },
            crate::sema::models::SyntheticDefinitionKind::ClassConstructionDescriptor { class },
            crate::sema::models::SyntheticDefinitionKind::ClassObjectDescriptor { class },
            crate::sema::models::SyntheticDefinitionKind::ClassDefaultBody {
                source: initializer,
            },
            crate::sema::models::SyntheticDefinitionKind::InheritedClassInitializer {
                class,
                initializer,
            },
            crate::sema::models::SyntheticDefinitionKind::InitializerEnvironment {
                class,
                initializer,
            },
            crate::sema::models::SyntheticDefinitionKind::InheritedInitializerDefault {
                initializer,
                provider: class,
            },
        ] {
            assert_eq!(
                synthetic_kind_from_wire(&synthetic_kind_to_wire(kind)),
                kind
            );
        }
    }

    #[test]
    fn struct_repr_roundtrip_through_wire() {
        for repr in [StructRepr::Taro, StructRepr::C] {
            let wire = struct_repr_to_wire(repr);
            let decoded = struct_repr_from_wire(&wire);
            assert_eq!(decoded, repr);
        }
    }
}

#[cfg(test)]
mod function_pointer_effect_tests {
    #[test]
    fn function_pointer_effects_survive_wire_round_trip() {
        crate::test_support::with_test_gcx(|gcx| {
            use crate::sema::models::{ClosureKind, FunctionPointerEffects, Ty, TyKind};
            for effects in [
                FunctionPointerEffects::default(),
                FunctionPointerEffects {
                    kind: ClosureKind::AsyncFn,
                    ..Default::default()
                },
                FunctionPointerEffects {
                    is_unsafe: true,
                    ..Default::default()
                },
                FunctionPointerEffects {
                    abi: Some(crate::hir::Abi::C),
                    ..Default::default()
                },
            ] {
                let pointer = Ty::new(
                    TyKind::FnPointer {
                        effects,
                        inputs: gcx.store.interners.intern_ty_list(vec![gcx.types.int32]),
                        output: gcx.types.int32,
                    },
                    gcx,
                );
                assert_eq!(
                    pointer,
                    super::ty_from_wire(gcx, &super::ty_to_wire(pointer))
                );
                assert_eq!(
                    crate::sema::models::callable_signature(pointer).is_some(),
                    !effects.is_unsafe && effects.abi.is_none()
                );
            }
        });
    }
}
