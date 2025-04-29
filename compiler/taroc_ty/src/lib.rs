use core::fmt;
use indexmap::IndexMap;
use rustc_hash::FxHashMap;
use std::fmt::Display;
use taroc_ast_ir::OperatorKind;
use taroc_data_structures::Interned;
use taroc_hir::{DefinitionID, Mutability};
use taroc_span::{FileID, Span, Symbol};

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
        AdtDef,
        &'arena [GenericArgument<'arena>],
        Option<Ty<'arena>>,
    ),

    // any <interface> | <interface>
    Existential(&'arena [InterfaceReference<'arena>]),
    Parameter(GenericParameter),
    FnDef(DefinitionID, &'arena [GenericArgument<'arena>]),
    Function {
        inputs: &'arena [Ty<'arena>],
        output: Ty<'arena>,
        is_async: bool,
    },
    // Represents Interface::AssociatedType (e.g., Self::Element or C::Element)
    AssociatedType(DefinitionID),
    Infer(InferTy),
    Error,
    Ignore,
    OverloadedFn(&'arena [DefinitionID]),
}

// In your type representation logic (e.g., impl Ty<'ctx> or a helper)
impl<'ctx> Ty<'ctx> {
    /// Attempts to retrieve the GenericArgs associated with this type,
    /// assuming it represents an instance of the given adt_definition_id
    /// (potentially through references).
    pub fn get_adt_arguments(&self, target: DefinitionID) -> Option<GenericArguments<'ctx>> {
        match self.kind() {
            TyKind::Adt(def, args, _) if def.id == target => Some(args),
            TyKind::Reference(inner_ty, _) => {
                // Recurse on the inner type
                inner_ty.get_adt_arguments(target)
            }
            _ => None, // Not the ADT or a reference to it
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
    // pub parent: DefinitionID,
    // pub id: DefinitionID,
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
    pub is_required: bool,
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
    pub inputs: Vec<LabeledFunctionParameter<'ctx>>,
    pub output: Ty<'ctx>,
    pub is_async: bool,
    pub is_variadic: bool,
    pub id: DefinitionID,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LabeledFunctionParameter<'ctx> {
    pub label: Option<Symbol>,
    pub ty: Ty<'ctx>,
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
    pub method_witnesses: FxHashMap<Symbol, DefinitionID>,
}

#[derive(Debug, Clone, Copy)]
pub enum Constraint<'ctx> {
    /// `T: P1 & P2 & …`
    Bound {
        ty: Ty<'ctx>,
        interface: InterfaceReference<'ctx>,
    },

    /// `T == U`
    TypeEquality(Ty<'ctx>, Ty<'ctx>),
}

#[derive(Debug, Clone, Default)]
pub struct DefinitionConstraints<'ctx> {
    pub constraints: Vec<(Constraint<'ctx>, Span)>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum InferTy {
    TyVar(TyVid),
    IntVar(IntVid),
    FloatVar(FloatVid),
    NilVar(NilVid),
}

index_vec::define_index_type! {
    pub struct TyVid = u32;
}

index_vec::define_index_type! {
    pub struct IntVid = u32;
}

index_vec::define_index_type! {
    pub struct FloatVid = u32;
}

index_vec::define_index_type! {
    pub struct NilVid = u32;
}

#[derive(Debug, Default, Clone, Copy)]
pub struct VarBinding<'ctx, T> {
    pub parent: Option<T>,
    pub bound_ty: Option<Ty<'ctx>>,
}

pub enum Direction<'ctx> {
    Synth,
    Check(Ty<'ctx>),
}

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

pub struct Coercion<'ctx> {
    pub adjustments: Vec<Adjustment>,
    pub ty: Ty<'ctx>,
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
                TyKind::Adt(_, args, _) => args.iter().filter_map(|ga| ga.ty()).any(visit),
                // Existential, associated, infer, error, primitives …
                _ => false,
            }
        }
        visit(self)
    }
}

// DISPLAY
//
// Implement Display for the interned type wrapper
impl<'arena> Display for Ty<'arena> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Delegate to the underlying kind
        write!(f, "{}", self.kind())
    }
}

// Display for the various primitive type enums
impl Display for IntTy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            IntTy::ISize => "isize",
            IntTy::I8 => "i8",
            IntTy::I16 => "i16",
            IntTy::I32 => "i32",
            IntTy::I64 => "i64",
        };
        write!(f, "{}", s)
    }
}

impl Display for UIntTy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            UIntTy::USize => "usize",
            UIntTy::U8 => "u8",
            UIntTy::U16 => "u16",
            UIntTy::U32 => "u32",
            UIntTy::U64 => "u64",
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

// Display for interface references (e.g., trait bounds)
impl<'arena> Display for InterfaceReference<'arena> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.id)?;
        if !self.arguments.is_empty() {
            write!(f, "<")?;
            for (i, arg) in self.arguments.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                match arg {
                    GenericArgument::Type(t) => write!(f, "{}", t)?,
                    GenericArgument::Const(c) => write!(f, "{}", c)?,
                }
            }
            write!(f, ">")?;
        }
        Ok(())
    }
}

// Display for the core TyKind enum
impl<'arena> Display for TyKind<'arena> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TyKind::Bool => write!(f, "bool"),
            TyKind::Rune => write!(f, "rune"),
            TyKind::Int(i) => write!(f, "{}", i),
            TyKind::UInt(u) => write!(f, "{}", u),
            TyKind::Float(fl) => write!(f, "{}", fl),
            TyKind::Pointer(inner, mutability) => match mutability {
                Mutability::Immutable => write!(f, "*const {}", inner),
                Mutability::Mutable => write!(f, "*mut {}", inner),
            },
            TyKind::Reference(inner, mutability) => match mutability {
                Mutability::Immutable => write!(f, "&const {}", inner),
                Mutability::Mutable => write!(f, "&mut {}", inner),
            },
            TyKind::Array(elem, size) => write!(f, "[{}; {}]", elem, size),
            TyKind::Tuple(elems) => {
                write!(f, "(")?;
                if elems.len() == 1 {
                    // Single-element tuple needs a trailing comma
                    write!(f, "{},", elems[0])?;
                } else {
                    for (i, ty) in elems.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", ty)?;
                    }
                }
                write!(f, ")")
            }
            TyKind::Adt(def, args, parent) => {
                if let Some(s) = parent {
                    write!(f, "{}::", s)?;
                }
                write!(f, "{}", def.name)?;
                if !args.is_empty() {
                    write!(f, "<")?;
                    for (i, arg) in args.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        match arg {
                            GenericArgument::Type(t) => write!(f, "{}", t)?,
                            GenericArgument::Const(c) => write!(f, "{}", c)?,
                        }
                    }
                    write!(f, ">")?;
                }

                Ok(())
            }
            TyKind::Existential(ifaces) => {
                for (i, iface) in ifaces.iter().enumerate() {
                    if i > 0 {
                        write!(f, " | ")?;
                    }
                    write!(f, "{}", iface)?;
                }
                Ok(())
            }
            TyKind::Parameter(param) => write!(f, "{}", param.name),
            TyKind::Function {
                inputs,
                output,
                is_async,
            } => {
                if *is_async {
                    write!(f, "async ")?;
                }
                write!(f, "(")?;
                for (i, inp) in inputs.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", inp)?;
                }
                write!(f, ") -> {}", output)
            }
            TyKind::AssociatedType(def_id) => write!(f, "{}", def_id),
            TyKind::Infer(v) => write!(f, "{v:?}"),
            TyKind::Error => write!(f, "<error>"),
            TyKind::Ignore => write!(f, "_"),
            TyKind::FnDef(id, args) => {
                write!(f, "{}", id)?;
                if !args.is_empty() {
                    write!(f, "<")?;
                    for (i, arg) in args.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        match arg {
                            GenericArgument::Type(t) => write!(f, "{}", t)?,
                            GenericArgument::Const(c) => write!(f, "{}", c)?,
                        }
                    }
                    write!(f, ">")?;
                }
                Ok(())
            }
            TyKind::OverloadedFn(..) => write!(f, "function"),
        }
    }
}

/// A helper wrapper so we can implement `Display` for a slice of
/// `GenericArgument<'ctx>`.
pub struct GenericArgs<'a, 'ctx>(pub &'a [GenericArgument<'ctx>]);

impl<'a, 'ctx> fmt::Display for GenericArgs<'a, 'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("<")?;
        for (i, arg) in self.0.iter().enumerate() {
            if i != 0 {
                f.write_str(", ")?;
            }
            write!(f, "{arg}")?; // relies on the impl below
        }
        f.write_str(">") // closing bracket
    }
}

/// Nice printing for one argument (`Int`, `const 4`, …).
impl<'ctx> fmt::Display for GenericArgument<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            GenericArgument::Type(ty) => write!(f, "{ty}"),
            GenericArgument::Const(v) => write!(f, "{v}"),
        }
    }
}
