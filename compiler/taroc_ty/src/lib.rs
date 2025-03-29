use indexmap::IndexMap;
use rustc_hash::FxHashMap;
use taroc_data_structures::Interned;
use taroc_hir::{DefinitionID, InterfaceType, Mutability};
use taroc_span::{FileID, Symbol};

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
    Void,
    Bool,
    Rune,
    Int(IntTy),
    UInt(UIntTy),
    Float(FloatTy),

    Pointer(Ty<'arena>, Mutability),
    Reference(Ty<'arena>, Mutability),

    Array(Ty<'arena>, u32),
    Tuple(&'arena [Ty<'arena>]),

    Adt(DefinitionID, &'arena [GenericArgument<'arena>]),

    // Interfaces
    Existential(&'arena [ExisitentialPredicate<'arena>], InterfaceType),

    AliasPlaceholder,
    Parameter,
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
struct GenericParameter {
    id: usize,
    name: Symbol,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GenericArgument<'arena> {
    Type(Ty<'arena>),
    Const(usize),
}

pub type GenericArguments<'arena> = &'arena [GenericArgument<'arena>];

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ExisitentialPredicate<'ctx> {
    pub id: DefinitionID,
    pub arguments: GenericArguments<'ctx>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Visibility {
    Public,
    ModuleRestricted(DefinitionID),
    FileRestricted(FileID),
}

#[derive(Debug, Clone)]
pub struct Generics {
    pub parameters: Vec<GenericParameterDefinition>,
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
    pub conformances: Vec<InterfaceReference<'ctx>>,
    pub fields: FxHashMap<Symbol, StructField<'ctx>>,
}

#[derive(Debug, Clone)]
pub struct EnumDefinition<'ctx> {
    pub id: DefinitionID,
    pub name: Symbol,
    pub conformances: Vec<InterfaceReference<'ctx>>,
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
    pub conformances: Vec<InterfaceReference<'ctx>>,
    pub associated_types: Vec<AssociatedTypeDeclaration<'ctx>>, // TODO!
    pub requirements: Vec<InterfaceRequirement<'ctx>>,
}

#[derive(Debug, Clone)]
pub enum InterfaceRequirement<'ctx> {
    Method(InterfaceMethodRequirement<'ctx>),
}

#[derive(Debug, Clone)]
pub struct InterfaceMethodRequirement<'ctx> {
    pub name: Symbol,
    pub is_required: bool,
    pub signature: Ty<'ctx>,
}

#[derive(Debug, Clone)]
pub struct InterfaceReference<'ctx> {
    pub id: DefinitionID,
    pub arguments: &'ctx GenericArguments<'ctx>,
}

#[derive(Debug, Clone)]
pub struct AssociatedTypeDeclaration<'ctx> {
    pub name: Symbol,
    // Constraints on the associated type (e.g., must implement these interfaces)
    pub conformances: Vec<InterfaceReference<'ctx>>,
    // Optional: A default type if the implementer doesn't provide one
    pub default_type: Option<Ty<'ctx>>,
}
