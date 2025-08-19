use crate::{
    GlobalContext,
    infer::keys::{FloatVarID, IntVarID},
    utils::{constraint2str, interface_ref2str, ty2str},
};
use core::fmt;
use index_vec::{IndexVec, define_index_type};
use rustc_hash::FxHashMap;
use std::{collections::HashMap, fmt::Display};
use taroc_ast_ir::OperatorKind;
use taroc_data_structures::Interned;
use taroc_hir::{CtorKind, DefinitionID, Mutability};
use taroc_span::{Identifier, Span, Spanned, Symbol};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Ty<'arena>(Interned<'arena, TyKind<'arena>>);

impl<'arena> Ty<'arena> {
    pub fn with_kind(k: Interned<'arena, TyKind<'arena>>) -> Ty<'arena> {
        Ty(k)
    }

    #[inline]
    pub fn kind(self) -> TyKind<'arena> {
        *self.0.0
    }

    pub fn is_error(self) -> bool {
        matches!(self.kind(), TyKind::Error)
    }

    #[inline]
    pub fn is_infer(self) -> bool {
        matches!(self.kind(), TyKind::Infer(..))
    }

    #[inline]
    pub fn is_ty_var(self) -> bool {
        matches!(self.kind(), TyKind::Infer(InferTy::TyVar(_)))
    }

    pub fn is_fn(self) -> bool {
        matches!(self.kind(), TyKind::FnDef(..) | TyKind::Function { .. })
    }

    pub fn dereference(self) -> Option<Ty<'arena>> {
        match self.kind() {
            TyKind::Reference(ty, _) | TyKind::Pointer(ty, _) => Some(ty),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TyKind<'arena> {
    Bool,
    Rune,
    String,
    Int(IntTy),
    UInt(UIntTy),
    Float(FloatTy),

    Pointer(Ty<'arena>, Mutability),
    Reference(Ty<'arena>, Mutability),

    Array(Ty<'arena>, u32),
    Tuple(&'arena [Ty<'arena>]),

    Adt(AdtDef, &'arena [GenericArgument<'arena>]),

    // any <interface> | <interface>
    Existential(&'arena [InterfaceReference<'arena>]),
    Opaque(&'arena [InterfaceReference<'arena>]),
    Parameter(GenericParameter),
    FnDef(DefinitionID, &'arena [GenericArgument<'arena>]),
    Function {
        inputs: &'arena [Ty<'arena>],
        output: Ty<'arena>,
    },
    // Represents Interface::AssociatedType (e.g., Self::Element or C::Element),
    AssociatedType(AssocTyKind<'arena>),
    /// Type inference variable (for generic instantiation)
    Infer(InferTy),
    Error,
    Placeholder,
}

impl<'ctx> Ty<'ctx> {
    pub fn get_adt_arguments(&self) -> Option<GenericArguments<'ctx>> {
        match self.kind() {
            TyKind::Adt(_, args) => Some(args),
            _ => None,
        }
    }

    pub fn adt_def(self) -> Option<AdtDef> {
        match self.kind() {
            TyKind::Adt(def, _) => Some(def),
            _ => None, // Not the ADT or a reference to it
        }
    }

    pub fn is_concrete(self) -> bool {
        !matches!(
            self.kind(),
            TyKind::Parameter(_)
                | TyKind::AssociatedType(_)
                | TyKind::Opaque(_)
                | TyKind::Existential(_)
                | TyKind::Error
                | TyKind::Infer(_)
        )
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AdtKind {
    Struct,
    Enum,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AdtDef {
    pub name: Symbol,
    pub kind: AdtKind,
    pub id: DefinitionID,
}

// MARK: Generics
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GenericParameter {
    pub index: usize,
    pub name: Symbol,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GenericArgument<'arena> {
    Type(Ty<'arena>),
    Const(usize),
}

impl<'arena> GenericArgument<'arena> {
    pub fn ty(self) -> Option<Ty<'arena>> {
        match self {
            GenericArgument::Type(ty) => Some(ty),
            GenericArgument::Const(_) => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InferTy {
    TyVar(TyVarID),
    IntVar(IntVarID),
    FloatVar(FloatVarID),
    FnVar(FnVarID),
    FreshTy(u32),
}

pub type GenericArguments<'arena> = &'arena [GenericArgument<'arena>];

#[derive(Debug, Clone)]
pub struct Generics {
    pub parameters: Vec<GenericParameterDefinition>,
    pub has_self: bool,
    pub parent: Option<DefinitionID>,
    pub parent_count: usize,
}

impl Generics {
    pub fn total_count(&self) -> usize {
        return self.parameters.len();
    }
    pub fn is_empty(&self) -> bool {
        return self.parameters.len() == 0;
    }
    pub fn default_count(&self) -> usize {
        let mut count = 0;
        for param in self.parameters.iter() {
            match &param.kind {
                GenericParameterDefinitionKind::Type { default } => {
                    if default.is_some() {
                        count += 1;
                    }
                }
                GenericParameterDefinitionKind::Const { has_default } => {
                    if *has_default {
                        count += 1;
                    }
                }
            }
        }

        return count;
    }
}

#[derive(Debug, Clone)]
pub struct GenericParameterDefinition {
    pub name: Symbol,
    pub id: DefinitionID,
    pub index: usize,
    pub kind: GenericParameterDefinitionKind,
}

#[derive(Debug, Clone)]
pub enum GenericParameterDefinitionKind {
    Type {
        default: Option<Box<taroc_hir::Type>>,
    },
    Const {
        has_default: bool,
    },
}

impl GenericParameterDefinitionKind {
    pub fn has_default(&self) -> bool {
        match self {
            GenericParameterDefinitionKind::Type { default } => default.is_some(),
            GenericParameterDefinitionKind::Const { has_default } => *has_default,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct AdtFieldDefinition<'ctx> {
    pub id: DefinitionID,
    pub name: Symbol,
    pub index: usize,
    pub ty: Ty<'ctx>,
}

#[derive(Debug, Clone)]
pub struct VariantDefinition<'ctx> {
    pub id: DefinitionID,
    pub ctor: Option<(CtorKind, DefinitionID)>,
    pub name: Symbol,
    pub discriminant: usize,
    pub fields: IndexVec<FieldIndex, AdtFieldDefinition<'ctx>>,
}

#[derive(Debug, Clone)]
pub struct StructDefinition<'ctx> {
    pub variant: &'ctx VariantDefinition<'ctx>,
}

#[derive(Debug, Clone)]
pub struct EnumDefinition<'ctx> {
    pub variants: Vec<&'ctx VariantDefinition<'ctx>>,
}

#[derive(Debug, Clone)]
pub struct InterfaceDefinition<'ctx> {
    pub id: DefinitionID,
    pub superfaces: Vec<Spanned<InterfaceReference<'ctx>>>,
    pub assoc_types: HashMap<Symbol, DefinitionID>,
}

define_index_type! {
    pub struct FieldIndex = u32;
}

define_index_type! {
    pub struct VariantIndex = u32;
}

#[derive(Debug, Clone, Default)]
pub struct InterfaceRequirements<'ctx> {
    pub methods: Vec<InterfaceMethodRequirement<'ctx>>,
    pub operators: Vec<InterfaceOperatorRequirement<'ctx>>,
    pub types: Vec<AssociatedTypeDefinition<'ctx>>,
}

#[derive(Debug, Clone)]
pub struct InterfaceMethodRequirement<'ctx> {
    pub id: DefinitionID,
    pub name: Symbol,
    pub signature: &'ctx LabeledFunctionSignature<'ctx>,
    pub is_required: bool,
}

#[derive(Debug, Clone)]
pub struct InterfaceOperatorRequirement<'ctx> {
    pub kind: OperatorKind,
    pub signature: &'ctx LabeledFunctionSignature<'ctx>,
    pub is_required: bool,
}

// For interface types (any/some Protocol)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct InterfaceReference<'ctx> {
    pub id: DefinitionID,
    pub arguments: GenericArguments<'ctx>, // Doesn't contain Self
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeErasure {
    Existential, // any Protocol
    Opaque,      // some Protocol
}

#[derive(Debug, Clone)]
pub struct AssociatedTypeDefinition<'ctx> {
    pub id: DefinitionID,
    pub name: Symbol,
    // Optional: A default type if the implementer doesn't provide one
    pub default_type: Option<Ty<'ctx>>,
}

#[derive(Debug, Clone)]
pub struct LabeledFunctionSignature<'ctx> {
    pub inputs: Vec<LabeledFunctionParameter<'ctx>>,
    pub output: Ty<'ctx>,
    pub is_async: bool,
    pub is_variadic: bool,
    pub id: DefinitionID,
}

impl<'ctx> LabeledFunctionSignature<'ctx> {
    pub fn min_parameter_count(&self) -> usize {
        self.inputs.len() - self.inputs.iter().filter(|i| i.has_default).count()
    }
}

impl<'ctx> LabeledFunctionSignature<'ctx> {
    /// Compare two signatures ignoring types (`ty`, `output`) and the `id`.
    ///
    /// Returns `true` when:
    /// * both have the same `is_async` / `is_variadic` flags,
    /// * the parameter list is the same length, and
    /// * every parameter’s `label`, and `has_default` match in order.
    pub fn same_shape(&self, other: &Self) -> bool {
        // Quick field/length checks first.
        if self.is_async != other.is_async
            || self.is_variadic != other.is_variadic
            || self.inputs.len() != other.inputs.len()
        {
            return false;
        }

        // Compare each parameter, ignoring `ty`.
        self.inputs
            .iter()
            .zip(&other.inputs)
            .all(|(a, b)| a.label == b.label && a.has_default == b.has_default)
    }
}

#[derive(Debug, Clone)]
pub struct LabeledFunctionParameter<'ctx> {
    pub label: Option<Symbol>,
    pub name: Symbol,
    pub ty: Ty<'ctx>,
    pub has_default: bool,
}

#[derive(Debug, Clone, Copy)]
pub struct ConformanceRecord<'ctx> {
    pub target: SimpleType,
    pub interface: InterfaceReference<'ctx>,
    pub extension: DefinitionID,
    pub location: Span,
    pub is_conditional: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Constraint<'ctx> {
    /// `T: P1 & P2 & …`
    Bound {
        ty: Ty<'ctx>,
        interface: InterfaceReference<'ctx>,
    },

    /// `T == U`
    TypeEquality(Ty<'ctx>, Ty<'ctx>),
}

pub type SpannedConstraints<'ctx> = Vec<Spanned<Constraint<'ctx>>>;

#[derive(Clone, Copy)]
pub enum ConformanceResult {
    NotConformant,
    /// Holds the ID of the extension to check for conditional conformance constraints
    Conforms(Option<DefinitionID>),
}

#[derive(Debug, Clone, Copy)]
pub struct ParamEnv<'ctx> {
    pub constraints: &'ctx [Constraint<'ctx>],
}

impl<'ctx> ParamEnv<'ctx> {
    pub fn new(constraints: &'ctx [Constraint<'ctx>]) -> ParamEnv<'ctx> {
        ParamEnv { constraints }
    }
}

index_vec::define_index_type! {
    pub struct TyVarID = u32;
}

index_vec::define_index_type! {
    pub struct FnVarID = u32;
}

#[derive(Debug, Clone, Copy)]
pub enum Adjustment {
    MutRefConstCast,        // &mut -> &
    MutPtrConstCast,        // *mut -> *const
    BoxExistential,         // S -> any P
    OpaqueErase,            // some P -> any P
    WrapOptional,           // T -> T?
    WrapNilToOptionalNone,  // nil/NilVar -> T?
    ExpressionBodiedReturn, // fn { <expr> } -> fn { return <expr> }
    AutoRef,                // T -> &T
    AutoMutRef,             // T -> &mut T
    AutoDeref,              // &T -> T
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AssocTyKind<'ctx> {
    Inherent(DefinitionID),
    DependentMember {
        base: Ty<'ctx>,
        name: Identifier,
        anchors: &'ctx [DefinitionID], // all associated types reachable with this name from `base`
    },
}

// HELPERS
impl<'ctx> Ty<'ctx> {
    /// Fast “syntactic” check: does this type mention any generic parameters?
    pub fn needs_instantiation(self) -> bool {
        fn visit<'ctx>(ty: Ty<'ctx>) -> bool {
            match ty.kind() {
                // A generic parameter definitely needs instantiation
                TyKind::Parameter(_) => true,
                // Walk composite types
                TyKind::Pointer(inner, _) | TyKind::Reference(inner, _) => visit(inner),
                TyKind::Array(elem, _) => visit(elem),
                TyKind::Tuple(elems) => elems.iter().copied().any(visit),
                TyKind::Function { inputs, output, .. } => {
                    inputs.iter().copied().any(visit) || visit(output)
                }
                TyKind::FnDef(_, args) => args.iter().filter_map(|ga| ga.ty()).any(visit),
                TyKind::Adt(_, args) => args.iter().filter_map(|ga| ga.ty()).any(visit),
                TyKind::AssociatedType(k) => match k {
                    AssocTyKind::Inherent(_) => false,
                    AssocTyKind::DependentMember { base, .. } => base.needs_instantiation(),
                },
                // Existential, associated, infer, error, primitives …
                _ => false,
            }
        }
        visit(self)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SimpleType {
    Rune,
    Bool,
    String,
    Array,
    Int(IntTy),
    UInt(UIntTy),
    Float(FloatTy),
    Adt(DefinitionID),
    Interface(DefinitionID),
    Reference(Mutability),
    Pointer(Mutability),
    Tuple(u16),
}

impl SimpleType {
    pub fn format<'ctx>(&self, gcx: GlobalContext<'ctx>) -> String {
        use SimpleType::*;
        match *self {
            Rune => "rune".into(),
            Bool => "bool".into(),
            String => "string".into(),
            Array => "array".into(),
            Int(ref k) => k.to_string(),
            UInt(ref k) => k.to_string(),
            Float(ref k) => k.to_string(),
            Adt(id) | Interface(id) => gcx.ident_for(id).symbol.to_string(),
            Reference(mutability) => match mutability {
                Mutability::Immutable => "&T",
                Mutability::Mutable => "&T",
            }
            .into(),
            Pointer(mutability) => match mutability {
                Mutability::Immutable => "*const T",
                Mutability::Mutable => "*T",
            }
            .into(),
            Tuple(size) => format!("tuple(T0...T{size}"),
        }
    }
}

impl<'ctx> Ty<'ctx> {
    #[track_caller]
    pub fn to_simple_type(self) -> SimpleType {
        match self.kind() {
            TyKind::Bool => SimpleType::Bool,
            TyKind::Rune => SimpleType::Rune,
            TyKind::String => SimpleType::String,
            TyKind::Int(int_ty) => SimpleType::Int(int_ty),
            TyKind::UInt(uint_ty) => SimpleType::UInt(uint_ty),
            TyKind::Float(float_ty) => SimpleType::Float(float_ty),
            TyKind::Pointer(_, mutability) => SimpleType::Pointer(mutability),
            TyKind::Reference(_, mutability) => SimpleType::Reference(mutability),
            TyKind::Array(..) => SimpleType::Array,
            TyKind::Adt(adt_def, _) => SimpleType::Adt(adt_def.id),
            TyKind::Tuple(..)
            | TyKind::Existential(..)
            | TyKind::Opaque(..)
            | TyKind::Parameter(..)
            | TyKind::FnDef(..)
            | TyKind::Function { .. }
            | TyKind::AssociatedType { .. }
            | TyKind::Infer(..)
            | TyKind::Placeholder
            | TyKind::Error => unreachable!(),
        }
    }
}

/// keeps all aliases for one package
#[derive(Default, Debug, Clone)]
pub struct PackageAliasTable {
    pub aliases: FxHashMap<DefinitionID, AliasEntry>, // NEW – file‑scope aliases
    pub by_type: FxHashMap<SimpleType, AliasBucket>,  // existing per‑type buckets
}

#[derive(Default, Debug, Clone)]
pub struct AliasBucket {
    /// All aliases visible on this nominal type, regardless of where‑clauses.
    pub aliases: FxHashMap<Symbol, (DefinitionID, Span)>,
}

/// Raw info kept for a single alias during harvesting
#[derive(Debug, Clone)]
pub struct AliasEntry {
    pub ast_type: Box<taroc_hir::Type>, // AST Type
    pub span: Span,                     // source range for diagnostics
    pub ext_id: Option<DefinitionID>,   // which extension declared it (for blame)
    pub alias_id: DefinitionID,
    pub symbol: Symbol,
}

// Display for the various primitive type enums
impl Display for IntTy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            IntTy::ISize => "isize",
            IntTy::I8 => "int8",
            IntTy::I16 => "int16",
            IntTy::I32 => "int32",
            IntTy::I64 => "int64",
        };
        write!(f, "{}", s)
    }
}

impl Display for UIntTy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            UIntTy::USize => "usize",
            UIntTy::U8 => "uint8",
            UIntTy::U16 => "uint16",
            UIntTy::U32 => "uint32",
            UIntTy::U64 => "uint64",
        };
        write!(f, "{}", s)
    }
}

impl Display for FloatTy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            FloatTy::F32 => "float",
            FloatTy::F64 => "double",
        };
        write!(f, "{}", s)
    }
}

impl<'gcx> Ty<'gcx> {
    pub fn format(self, gcx: GlobalContext<'gcx>) -> String {
        ty2str(self, gcx)
    }
}

impl<'gcx> Constraint<'gcx> {
    pub fn format(self, gcx: GlobalContext<'gcx>) -> String {
        constraint2str(self, gcx)
    }
}

impl<'gcx> InterfaceReference<'gcx> {
    pub fn format(self, gcx: GlobalContext<'gcx>) -> String {
        interface_ref2str(self, gcx)
    }
}
