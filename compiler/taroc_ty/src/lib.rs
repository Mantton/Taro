use indexmap::IndexMap;
use rustc_hash::FxHashMap;
use taroc_data_structures::Interned;
use taroc_hir::{DefinitionID, Mutability};
use taroc_span::{FileID, Symbol};
use taroc_token::OperatorKind;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Ty<'arena>(Interned<'arena, TyKind<'arena>>);

impl<'arena> Ty<'arena> {
    pub fn with_kind(k: Interned<'arena, TyKind<'arena>>) -> Ty<'arena> {
        Ty(k)
    }
    pub fn kind(self) -> TyKind<'arena> {
        *self.0.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TyKind<'arena> {
    Bool,
    Rune,
    Int(IntTy),
    UInt(UIntTy),
    Float(FloatTy),

    Pointer(Ty<'arena>, Mutability),
    Reference(Ty<'arena>, Mutability),

    Array(Ty<'arena>, u32),
    Tuple(&'arena [Ty<'arena>]),

    Adt(
        DefinitionID,
        &'arena [GenericArgument<'arena>],
        Option<Ty<'arena>>,
    ),

    // any <interface> | <interface>
    Existential(&'arena [InterfaceReference<'arena>]),
    Parameter(GenericParameter),
    Function {
        inputs: &'arena [Ty<'arena>],
        output: Ty<'arena>,
        is_async: bool,
    },
    Variadic(Ty<'arena>),
    // Represents Interface::AssociatedType (e.g., Self::Element or C::Element)
    AssociatedType(DefinitionID),
    Infer,
    Error,
    Ignore,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntTy {
    Int,
    I8,
    I16,
    I32,
    I64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UIntTy {
    UInt,
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

// MARK: Generics
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GenericParameter {
    pub parent: DefinitionID,
    pub id: DefinitionID,
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

pub type GenericArguments<'arena> = &'arena [GenericArgument<'arena>];

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Visibility {
    Public,
    ModuleRestricted(DefinitionID),
    FileRestricted(FileID),
}

#[derive(Debug, Clone)]
pub struct Generics {
    pub parameters: Vec<GenericParameterDefinition>,
    pub has_self: bool,
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

#[derive(Debug, Clone)]
pub struct StructField<'ctx> {
    pub name: Symbol,
    pub ty: Ty<'ctx>,
    pub mutability: Mutability,
}

#[derive(Debug, Clone)]
pub struct StructDefinition<'ctx> {
    pub id: DefinitionID,
    pub name: Symbol,
    pub fields: FxHashMap<Symbol, StructField<'ctx>>,
}

#[derive(Debug, Clone)]
pub struct EnumDefinition<'ctx> {
    pub id: DefinitionID,
    pub name: Symbol,
    pub variants: IndexMap<Symbol, EnumVariant<'ctx>>,
}

#[derive(Debug, Clone)]
pub struct EnumVariant<'ctx> {
    pub id: DefinitionID,
    pub name: Symbol,
    pub kind: EnumVariantKind<'ctx>,
    pub discriminant: usize,
}

#[derive(Debug, Clone)]
pub enum EnumVariantKind<'ctx> {
    Unit,
    Tuple(Vec<Ty<'ctx>>),
    Struct(StructDefinition<'ctx>),
}

#[derive(Debug, Clone)]
pub struct InterfaceDefinition<'ctx> {
    pub id: DefinitionID,
    pub name: Symbol,
    pub requirements: InterfaceRequirements<'ctx>,
    pub parameters: GenericArguments<'ctx>,
}

#[derive(Debug, Clone, Default)]
pub struct InterfaceRequirements<'ctx> {
    pub methods: Vec<InterfaceMethodRequirement<'ctx>>,
    pub operators: Vec<InterfaceOperatorRequirement<'ctx>>,
    pub properties: Vec<InterfacePropertyRequirement<'ctx>>,
    pub types: Vec<AssociatedTypeDefinition<'ctx>>,
}

#[derive(Debug, Clone)]
pub struct InterfaceMethodRequirement<'ctx> {
    pub name: Symbol,
    pub signature: LabeledFunctionSignature<'ctx>,
    pub is_required: bool,
}

#[derive(Debug, Clone)]
pub struct InterfacePropertyRequirement<'ctx> {
    pub name: Symbol,
    pub signature: ComputedPropertySignature<'ctx>,
}

#[derive(Debug, Clone)]
pub struct InterfaceOperatorRequirement<'ctx> {
    pub kind: OperatorKind,
    pub signature: LabeledFunctionSignature<'ctx>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct InterfaceReference<'ctx> {
    pub id: DefinitionID,
    pub arguments: GenericArguments<'ctx>,
}

#[derive(Debug, Clone)]
pub struct AssociatedTypeDefinition<'ctx> {
    pub name: Symbol,
    // Optional: A default type if the implementer doesn't provide one
    pub default_type: Option<Ty<'ctx>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LabeledFunctionSignature<'ctx> {
    pub receiver: Option<ReceiverKind>,
    pub inputs: Vec<LabeledFunctionParameter<'ctx>>,
    pub output: Ty<'ctx>,
    pub is_async: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LabeledFunctionParameter<'ctx> {
    pub label: Option<Symbol>,
    pub ty: Ty<'ctx>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ReceiverKind {
    Owned, // For a normal 'Self'
    Mut,   // For a &mut Self
    Const, // For a &const Self
}

#[derive(Debug, Default)]
pub struct DefinitionFunctionsData<'ctx> {
    // Methods
    pub methods: FxHashMap<Symbol, Vec<LabeledFunctionSignature<'ctx>>>,
    pub static_methods: FxHashMap<Symbol, Vec<LabeledFunctionSignature<'ctx>>>,
    // Operators
    pub operators: FxHashMap<OperatorKind, Vec<LabeledFunctionSignature<'ctx>>>,
    // Properties
    pub properties: FxHashMap<Symbol, ComputedPropertySignature<'ctx>>,
    pub static_properties: FxHashMap<Symbol, Vec<LabeledFunctionSignature<'ctx>>>,
    // Constructors
    pub constructors: Vec<LabeledFunctionSignature<'ctx>>,
}

#[derive(Debug, Clone)]
pub struct ComputedPropertySignature<'ctx> {
    pub ty: Ty<'ctx>,
}

#[derive(Debug)]
pub struct ConformanceRecord<'ctx> {
    pub ty: DefinitionID,
    pub interface: DefinitionID,
    pub type_witnesses: FxHashMap<Symbol, Ty<'ctx>>,
}
