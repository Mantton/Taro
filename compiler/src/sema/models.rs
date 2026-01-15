use ena::unify::UnifyKey;
use rustc_hash::FxHashMap;
use std::hash::{Hash, Hasher};

use crate::{
    compile::context::Gcx,
    hir::{self, DefinitionID, Mutability},
    sema::{
        resolve::models::TypeHead,
        tycheck::infer::keys::{FloatVarID, IntVarID, NilVarID},
    },
    span::{Span, Spanned, Symbol},
    utils::intern::Interned,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Ty<'arena>(Interned<'arena, TyKind<'arena>>);

impl<'arena> Ty<'arena> {
    pub fn with_kind(k: Interned<'arena, TyKind<'arena>>) -> Ty<'arena> {
        Ty(k)
    }

    pub fn new(k: TyKind<'arena>, gcx: Gcx<'arena>) -> Ty<'arena> {
        gcx.store.interners.intern_ty(k)
    }

    pub fn error(gcx: Gcx<'arena>) -> Ty<'arena> {
        Ty::new(TyKind::Error, gcx)
    }

    #[inline]
    pub fn new_int(gcx: Gcx<'arena>, i: IntTy) -> Ty<'arena> {
        use IntTy::*;
        match i {
            I8 => gcx.types.int8,
            I16 => gcx.types.int16,
            I32 => gcx.types.int32,
            I64 => gcx.types.int64,
            ISize => gcx.types.int,
        }
    }

    #[inline]
    pub fn new_uint(gcx: Gcx<'arena>, i: UIntTy) -> Ty<'arena> {
        use UIntTy::*;
        match i {
            U8 => gcx.types.uint8,
            U16 => gcx.types.uint16,
            U32 => gcx.types.uint32,
            U64 => gcx.types.uint64,
            USize => gcx.types.uint,
        }
    }

    #[inline]
    pub fn new_float(gcx: Gcx<'arena>, f: FloatTy) -> Ty<'arena> {
        use FloatTy::*;
        match f {
            F32 => gcx.types.float32,
            F64 => gcx.types.float64,
        }
    }

    pub fn from_labeled_signature(
        gcx: Gcx<'arena>,
        signature: &LabeledFunctionSignature<'arena>,
    ) -> Ty<'arena> {
        let inputs: Vec<Ty<'arena>> = signature.inputs.iter().map(|param| param.ty).collect();
        let output = signature.output;

        let kind = TyKind::FnPointer {
            inputs: gcx.store.interners.intern_ty_list(inputs),
            output,
        };

        Ty::new(kind, gcx)
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

    pub fn contains_inference(self) -> bool {
        fn visit<'ctx>(ty: Ty<'ctx>) -> bool {
            match ty.kind() {
                TyKind::Infer(_) => true,
                TyKind::Alias { .. } => true, // unnormalized aliases might hide inference vars
                TyKind::Adt(_, args) => args.iter().any(|arg| match arg {
                    GenericArgument::Type(ty) => visit(*ty),
                    GenericArgument::Const(c) => {
                        matches!(c.kind, ConstKind::Infer(_)) || visit(c.ty)
                    }
                }),
                TyKind::Pointer(inner, _) | TyKind::Reference(inner, _) => visit(inner),
                TyKind::Array { element, .. } => visit(element), // Skip const len for now, usually it doesn't affect member lookup
                TyKind::Tuple(elems) => elems.iter().any(|t| visit(*t)),
                TyKind::FnPointer { inputs, output } => {
                    inputs.iter().any(|t| visit(*t)) || visit(output)
                }
                TyKind::BoxedExistential { interfaces } => interfaces.iter().any(|iface| {
                    iface.arguments.iter().any(|arg| match arg {
                        GenericArgument::Type(ty) => visit(*ty),
                        GenericArgument::Const(c) => {
                            matches!(c.kind, ConstKind::Infer(_)) || visit(c.ty)
                        }
                    })
                }),
                _ => false,
            }
        }
        visit(self)
    }

    pub fn is_fn(self) -> bool {
        matches!(self.kind(), TyKind::FnPointer { .. })
    }

    pub fn is_pointer(self) -> bool {
        matches!(self.kind(), TyKind::Pointer(..) | TyKind::Reference(..))
    }

    pub fn dereference(self) -> Option<Ty<'arena>> {
        match self.kind() {
            TyKind::Reference(ty, _) | TyKind::Pointer(ty, _) => Some(ty),
            _ => None,
        }
    }
}

impl<'arena> Ty<'arena> {
    pub fn format(self, gcx: Gcx<'arena>) -> String {
        match self.kind() {
            TyKind::Bool => "bool".into(),
            TyKind::Rune => "rune".into(),
            TyKind::String => "string".into(),
            TyKind::Int(i) => i.name_str().into(),
            TyKind::UInt(u) => u.name_str().into(),
            TyKind::Float(f) => f.name_str().into(),
            TyKind::Array { element, len } => {
                let len_str = match len.kind {
                    ConstKind::Value(ConstValue::Integer(i)) => format!("{i}"),
                    ConstKind::Param(p) => p.name.as_str().into(),
                    ConstKind::Infer(_) => "_".into(),
                    _ => "<const>".into(),
                };
                format!("[{}; {}]", element.format(gcx), len_str)
            }
            TyKind::Adt(adt, args) => {
                let mut out = String::from(adt.name.as_str());
                out.push_str(&format_generic_args(args, gcx));
                out
            }
            TyKind::Pointer(inner, mt) => {
                format!("*{}{}", mt.display_str(), inner.format(gcx))
            }
            TyKind::Reference(inner, mt) => {
                format!("&{}{}", mt.display_str(), inner.format(gcx))
            }
            TyKind::Tuple(items) => {
                let mut out = "(".to_owned();
                for (i, t) in items.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    out.push_str(&t.format(gcx));
                }
                if items.len() == 1 {
                    out.push(',');
                } // 1‑tuple trailing comma
                out.push(')');
                out
            }
            TyKind::FnPointer { inputs, output } => {
                let mut out = String::new();
                out.push('(');
                for (i, input) in inputs.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    out.push_str(&input.format(gcx));
                }
                out.push_str(") -> ");
                out.push_str(&output.format(gcx));
                out
            }
            TyKind::BoxedExistential { interfaces } => {
                if interfaces.is_empty() {
                    return "any".into();
                }
                let parts: Vec<_> = interfaces.iter().map(|i| i.format(gcx)).collect();
                format!("any {}", parts.join(" & "))
            }
            TyKind::Error => "<<error>>".into(),
            TyKind::Never => "!".into(),
            TyKind::Infer(k) => match k {
                InferTy::TyVar(id) => format!("{{var({})}}", id._raw),
                InferTy::IntVar(id) => format!("{{integer({})}}", id.index()),
                InferTy::FloatVar(id) => format!("{{float({})}}", id.index()),
                InferTy::NilVar(id) => format!("{{nil({})}}", id.index()),
                InferTy::FreshTy(id) => format!("{{fresh({})}}", id),
            },
            TyKind::Parameter(p) => format!("{}", p.name.as_str()),
            TyKind::Alias { kind, def_id, args } => {
                let ident = gcx.definition_ident(def_id);
                if kind == AliasKind::Projection {
                    if let Some(GenericArgument::Type(self_ty)) = args.get(0) {
                        let mut out = format!("{}.{}", self_ty.format(gcx), ident.symbol.as_str());
                        if args.len() > 1 {
                            out.push_str(&format_generic_args(&args[1..], gcx));
                        }
                        out
                    } else {
                        // Fallback/Should not happen for valid projections
                        let mut out = String::from(ident.symbol.as_str());
                        out.push_str(&format_generic_args(args, gcx));
                        out
                    }
                } else {
                    let mut out = String::from(ident.symbol.as_str());
                    out.push_str(&format_generic_args(args, gcx));
                    out
                }
            }
            TyKind::Closure {
                inputs,
                output,
                kind,
                ..
            } => {
                let kind_str = match kind {
                    ClosureKind::Fn => "Fn",
                    ClosureKind::FnMut => "FnMut",
                    ClosureKind::FnOnce => "FnOnce",
                };
                let mut out = format!("closure<{}>((", kind_str);
                for (i, input) in inputs.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    out.push_str(&input.format(gcx));
                }
                out.push_str(") -> ");
                out.push_str(&output.format(gcx));
                out.push(')');
                out
            }
        }
    }
}

// HELPERS
impl<'ctx> Ty<'ctx> {
    /// Fast “syntactic” check: does this type mention any generic parameters?
    pub fn needs_instantiation(self) -> bool {
        fn visit<'ctx>(ty: Ty<'ctx>) -> bool {
            fn const_needs_instantiation<'ctx>(c: Const<'ctx>) -> bool {
                matches!(c.kind, ConstKind::Param(_) | ConstKind::Infer(_)) || visit(c.ty)
            }

            match ty.kind() {
                // A generic parameter definitely needs instantiation
                TyKind::Parameter(_) => true,
                TyKind::Adt(_, args) => args.iter().any(|arg| match arg {
                    GenericArgument::Type(ty) => visit(*ty),
                    GenericArgument::Const(c) => const_needs_instantiation(*c),
                }),
                // Walk composite types
                TyKind::Pointer(inner, _) | TyKind::Reference(inner, _) => visit(inner),
                TyKind::Array { element, len } => visit(element) || const_needs_instantiation(len),
                TyKind::Tuple(elems) => elems.iter().copied().any(visit),
                TyKind::FnPointer { inputs, output, .. } => {
                    inputs.iter().copied().any(visit) || visit(output)
                }
                // Existential, associated, infer, error, primitives …
                TyKind::BoxedExistential { interfaces } => interfaces.iter().any(|iface| {
                    iface.arguments.iter().any(|arg| match arg {
                        GenericArgument::Type(ty) => visit(*ty),
                        GenericArgument::Const(c) => const_needs_instantiation(*c),
                    })
                }),
                TyKind::Alias { args, .. } => args.iter().any(|arg| match arg {
                    GenericArgument::Type(ty) => visit(*ty),
                    GenericArgument::Const(c) => const_needs_instantiation(*c),
                }),
                _ => false,
            }
        }
        visit(self)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TyKind<'arena> {
    Array {
        element: Ty<'arena>,
        len: Const<'arena>,
    },
    Bool,
    Rune,
    String,
    Int(IntTy),
    UInt(UIntTy),
    Float(FloatTy),
    Adt(AdtDef, GenericArguments<'arena>),
    Pointer(Ty<'arena>, Mutability),
    Reference(Ty<'arena>, Mutability),
    Tuple(&'arena [Ty<'arena>]),
    FnPointer {
        inputs: &'arena [Ty<'arena>],
        output: Ty<'arena>,
    },
    BoxedExistential {
        interfaces: &'arena [InterfaceReference<'arena>],
    },
    Alias {
        kind: AliasKind,
        def_id: DefinitionID,
        args: GenericArguments<'arena>,
    },
    Infer(InferTy),
    Parameter(GenericParameter),
    /// Anonymous closure type with captured environment
    Closure {
        /// Unique ID for this closure definition
        closure_def_id: DefinitionID,
        /// Generic arguments captured from enclosing scope
        captured_generics: GenericArguments<'arena>,
        /// Input parameter types
        inputs: &'arena [Ty<'arena>],
        /// Output type
        output: Ty<'arena>,
        /// Callable kind
        kind: ClosureKind,
    },
    Error,
    Never,
}

/// Kind of type alias
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AliasKind {
    /// Impl block associated type: `impl Foo { type Bar = Int }`
    Inherent,
    /// Top-level type alias: `type Foo = [Int]`
    Weak,
    /// Interface associated type accessed on a type parameter: `T.Item`
    Projection,
}

/// Classification of a closure's callable behavior
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ClosureKind {
    /// Can be called multiple times with shared access to captures (&self)
    Fn,
    /// Can be called multiple times with mutable access to captures (&mut self)
    FnMut,
    /// Can be called at most once, consuming the closure (self)
    FnOnce,
}

/// How a variable is captured by a closure
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CaptureKind {
    /// Value copied into closure (for Copy types)
    ByCopy,
    /// Reference to the original value stored in env
    ByRef { mutable: bool },
    /// Value moved into closure (ownership transferred)
    ByMove,
}

/// A variable captured by a closure
#[derive(Debug, Clone, Copy)]
pub struct CapturedVar<'arena> {
    /// The NodeID of the captured variable in the enclosing scope
    pub source_id: hir::NodeID,
    /// Name of the captured variable
    pub name: Symbol,
    /// Type of the captured value (original type, not ref type)
    pub ty: Ty<'arena>,
    /// How this variable is captured
    pub capture_kind: CaptureKind,
    /// Field index in the environment struct
    pub field_index: crate::thir::FieldIndex,
}

/// Information about a closure's captured environment
#[derive(Debug, Clone)]
pub struct ClosureCaptures<'arena> {
    /// All captured variables
    pub captures: Vec<CapturedVar<'arena>>,
    /// The callable kind inferred from body analysis
    pub kind: ClosureKind,
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StructField<'arena> {
    pub name: Symbol,
    pub ty: Ty<'arena>,
    pub mutability: Mutability,
    pub def_id: DefinitionID,
    pub visibility: crate::sema::resolve::models::Visibility,
}

#[derive(Debug, Clone)]
pub struct StructDefinition<'arena> {
    pub adt_def: AdtDef,
    pub fields: &'arena [StructField<'arena>],
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct EnumVariantField<'arena> {
    pub label: Option<Symbol>,
    pub ty: Ty<'arena>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum EnumVariantKind<'arena> {
    Unit,
    Tuple(&'arena [EnumVariantField<'arena>]),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct EnumVariant<'arena> {
    pub name: Symbol,
    pub def_id: DefinitionID,
    pub ctor_def_id: DefinitionID,
    pub kind: EnumVariantKind<'arena>,
    pub discriminant: u64,
}

#[derive(Debug, Clone)]
pub struct EnumDefinition<'arena> {
    pub adt_def: AdtDef,
    pub variants: &'arena [EnumVariant<'arena>],
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
pub struct LabeledFunctionSignature<'ctx> {
    pub inputs: Vec<LabeledFunctionParameter<'ctx>>,
    pub output: Ty<'ctx>,
    pub is_variadic: bool,
    pub abi: Option<crate::hir::Abi>,
}

impl LabeledFunctionSignature<'_> {
    pub fn min_parameter_count(&self) -> usize {
        self.inputs
            .len()
            .checked_sub(
                self.inputs
                    .iter()
                    .filter(|i| i.default_provider.is_some())
                    .count(),
            )
            .unwrap_or(0)
    }

    /// Compare two signatures ignoring types (`ty`, `output`).
    ///
    /// Returns `true` when:
    /// * both have the same `is_variadic` flag,
    /// * the parameter list is the same length, and
    /// * every parameter's `label` and `default_provider` status match in order.
    pub fn same_shape(&self, other: &Self) -> bool {
        // Quick field/length checks first.
        if self.is_variadic != other.is_variadic || self.inputs.len() != other.inputs.len() {
            return false;
        }

        // Compare each parameter, ignoring `ty`.
        self.inputs.iter().zip(&other.inputs).all(|(a, b)| {
            a.label == b.label && a.default_provider.is_some() == b.default_provider.is_some()
        })
    }
}

#[derive(Debug, Clone, Copy)]
pub struct LabeledFunctionParameter<'ctx> {
    pub label: Option<Symbol>,
    pub name: Symbol,
    pub ty: Ty<'ctx>,
    pub default_provider: Option<DefinitionID>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Constraint<'ctx> {
    /// `T == U`
    TypeEquality(Ty<'ctx>, Ty<'ctx>),
    /// `T: Interface`
    Bound {
        ty: Ty<'ctx>,
        interface: InterfaceReference<'ctx>,
    },
}

index_vec::define_index_type! {
    pub struct TyVarID = u32;
}

index_vec::define_index_type! {
    pub struct ConstVarID = u32;
}

index_vec::define_index_type! {
    pub struct FnVarID = u32;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InferTy {
    TyVar(TyVarID),
    IntVar(IntVarID),
    FloatVar(FloatVarID),
    NilVar(NilVarID),
    FreshTy(u32),
}

// MARK: Generics
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GenericParameter {
    pub index: usize,
    pub name: Symbol,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Const<'arena> {
    pub ty: Ty<'arena>,
    pub kind: ConstKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ConstKind {
    Value(ConstValue),
    Param(GenericParameter),
    Infer(ConstVarID),
}

#[derive(Debug, Clone, Copy)]
pub enum ConstValue {
    Integer(i128),
    Bool(bool),
    Rune(char),
    String(crate::span::Symbol),
    Float(f64),
    Unit,
}

impl PartialEq for ConstValue {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (ConstValue::Integer(a), ConstValue::Integer(b)) => a == b,
            (ConstValue::Bool(a), ConstValue::Bool(b)) => a == b,
            (ConstValue::Rune(a), ConstValue::Rune(b)) => a == b,
            (ConstValue::String(a), ConstValue::String(b)) => a == b,
            (ConstValue::Float(a), ConstValue::Float(b)) => a.to_bits() == b.to_bits(),
            (ConstValue::Unit, ConstValue::Unit) => true,
            _ => false,
        }
    }
}

impl Eq for ConstValue {}

impl Hash for ConstValue {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            ConstValue::Integer(v) => {
                0u8.hash(state);
                v.hash(state);
            }
            ConstValue::Bool(v) => {
                1u8.hash(state);
                v.hash(state);
            }
            ConstValue::Rune(v) => {
                2u8.hash(state);
                v.hash(state);
            }
            ConstValue::String(v) => {
                3u8.hash(state);
                v.hash(state);
            }
            ConstValue::Float(v) => {
                4u8.hash(state);
                v.to_bits().hash(state);
            }
            ConstValue::Unit => {
                5u8.hash(state);
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GenericArgument<'arena> {
    Type(Ty<'arena>),
    Const(Const<'arena>),
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

/// Format generic arguments as a bracketed list, e.g., "[Int, String]"
/// Returns empty string if args is empty.
pub fn format_generic_args<'ctx>(args: GenericArguments<'ctx>, gcx: Gcx<'ctx>) -> String {
    if args.is_empty() {
        return String::new();
    }

    let mut out = String::from("[");
    for (i, arg) in args.iter().enumerate() {
        if i > 0 {
            out.push_str(", ");
        }
        match arg {
            GenericArgument::Type(ty) => out.push_str(&ty.format(gcx)),
            GenericArgument::Const(c) => out.push_str(&format!("{:?}", c)),
        }
    }
    out.push(']');
    out
}
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
        self.parameters.is_empty() && self.parent_count == 0
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
                GenericParameterDefinitionKind::Const { default, .. } => {
                    if default.is_some() {
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
        default: Option<Box<hir::Type>>,
    },
    Const {
        ty: Box<hir::Type>,
        default: Option<hir::AnonConst>,
    },
}

impl GenericParameterDefinitionKind {
    pub fn has_default(&self) -> bool {
        match self {
            GenericParameterDefinitionKind::Type { default } => default.is_some(),
            GenericParameterDefinitionKind::Const { default, .. } => default.is_some(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct InterfaceDefinition<'ctx> {
    pub id: DefinitionID,
    pub superfaces: Vec<Spanned<InterfaceReference<'ctx>>>,
    pub assoc_types: FxHashMap<Symbol, DefinitionID>,
}

#[derive(Debug, Clone, Default)]
pub struct InterfaceRequirements<'ctx> {
    pub methods: Vec<InterfaceMethodRequirement<'ctx>>,
    pub types: Vec<AssociatedTypeDefinition<'ctx>>,
    pub constants: Vec<InterfaceConstantRequirement<'ctx>>,
}

#[derive(Debug, Clone)]
pub struct InterfaceMethodRequirement<'ctx> {
    pub id: DefinitionID,
    pub name: Symbol,
    pub signature: &'ctx LabeledFunctionSignature<'ctx>,
    pub has_self: bool,
    pub is_required: bool,
}

#[derive(Debug, Clone)]
pub struct InterfaceConstantRequirement<'ctx> {
    pub id: DefinitionID,
    pub name: Symbol,
    pub ty: Ty<'ctx>,
    pub default: Option<Const<'ctx>>, // Evaluated default value if provided
}

// For interface types (any/some Protocol)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct InterfaceReference<'ctx> {
    pub id: DefinitionID,
    pub arguments: GenericArguments<'ctx>, // Self is arguments[0] when has_self
    pub bindings: &'ctx [AssociatedTypeBinding<'ctx>],
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AssociatedTypeBinding<'ctx> {
    pub name: Symbol,
    pub ty: Ty<'ctx>,
}

impl<'ctx> InterfaceReference<'ctx> {
    pub fn format(self, gcx: Gcx<'ctx>) -> String {
        let name = gcx.definition_ident(self.id).symbol;

        // Skip Self (index 0) when formatting - it's implicit
        let skip = if self.arguments.len() > 0 { 1 } else { 0 };
        let display_args = &self.arguments[skip..];

        let mut out = String::from(name.as_str());
        out.push_str(&format_generic_args(display_args, gcx));

        if !self.bindings.is_empty() {
            if display_args.is_empty() {
                out.push('<');
            } else {
                // Remove closing ']'
                out.pop();
                out.push_str(", ");
            }

            let bindings: Vec<_> = self
                .bindings
                .iter()
                .map(|b| format!("{} = {}", b.name.as_str(), b.ty.format(gcx)))
                .collect();
            out.push_str(&bindings.join(", "));

            if display_args.is_empty() {
                out.push('>');
            } else {
                out.push(']');
            }
        }

        out
    }
}

#[derive(Debug, Clone)]
pub struct AssociatedTypeDefinition<'ctx> {
    pub id: DefinitionID,
    pub name: Symbol,
    // Optional: A default type if the implementer doesn't provide one
    pub default_type: Option<Ty<'ctx>>,
}

#[derive(Debug, Clone, Copy)]
pub struct ConformanceRecord<'ctx> {
    pub target: TypeHead,
    pub interface: InterfaceReference<'ctx>,
    pub extension: DefinitionID,
    pub location: Span,
    pub is_conditional: bool,
    /// True if the conformance was declared inline on the type definition (struct Foo: T {}),
    /// false if declared via impl block (impl T for Foo {}). Inline conformances allow auto-synthesis.
    pub is_inline: bool,
}

/// Witness mappings for a conformance - maps interface requirements to implementations
#[derive(Debug, Clone, Default)]
pub struct ConformanceWitness<'ctx> {
    /// Maps interface method → implementing method
    pub method_witnesses: FxHashMap<DefinitionID, MethodWitness<'ctx>>,
    /// Maps interface operator kind → implementing operator
    pub operator_witnesses: FxHashMap<hir::OperatorKind, DefinitionID>,
    /// Maps interface constant → implementing constant
    pub constant_witnesses: FxHashMap<DefinitionID, DefinitionID>,
    /// Maps interface associated type → concrete type
    pub type_witnesses: FxHashMap<DefinitionID, Ty<'ctx>>,
    /// The ID of the extension or definition providing compliance.
    pub extension_id: Option<DefinitionID>,
}

/// How a method requirement is satisfied in a conformance.
#[derive(Debug, Clone, Copy)]
pub enum MethodImplementation {
    /// User-provided implementation.
    Concrete(DefinitionID),
    /// Compiler-synthesized implementation.
    /// The DefinitionID is populated during THIR synthesis to allow linkage.
    Synthetic(SyntheticMethodKind, Option<DefinitionID>),
    /// Default implementation from interface definition.
    Default(DefinitionID),
}

impl MethodImplementation {
    /// Returns the implementing definition ID for concrete/default implementations.
    /// Returns None for synthetic implementations (which require special code generation).
    pub fn impl_id(self) -> Option<DefinitionID> {
        match self {
            MethodImplementation::Concrete(id) | MethodImplementation::Default(id) => Some(id),
            MethodImplementation::Synthetic(_, id) => id,
        }
    }

    /// Returns true if this is a synthetic implementation.
    pub fn is_synthetic(self) -> bool {
        matches!(self, MethodImplementation::Synthetic(..))
    }
}

#[derive(Debug, Clone)]
pub struct SyntheticDefinition<'arena> {
    pub name: crate::span::Symbol,
    pub generics: &'arena Generics,
    pub signature: &'arena LabeledFunctionSignature<'arena>,
    pub span: crate::span::Span,
}

/// Kind of synthesized method for code generation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SyntheticMethodKind {
    /// Clone for Copy types: just dereference self (`*self`)
    CopyClone,
    /// Clone for non-Copy types: memberwise clone each field
    MemberwiseClone,
    /// Hashable.hash: hash each field
    MemberwiseHash,
    /// Equatable.==: compare each field for equality
    MemberwiseEquality,
    /// Fn.call: invoke closure with shared access.
    ClosureCall,
    /// FnMut.call_mut: invoke closure with mutable access.
    ClosureCallMut,
    /// FnOnce.call_once: invoke closure consuming self.
    ClosureCallOnce,
}

/// Mapping from an interface method to its implementation and instantiation template.
#[derive(Debug, Clone, Copy)]
pub struct MethodWitness<'ctx> {
    /// How this method is implemented (concrete, synthetic, or default).
    pub implementation: MethodImplementation,
    /// Generic argument template expressed in terms of the interface method's params.
    pub args_template: GenericArguments<'ctx>,
}

/// Definition of a type alias (top-level or associated)
#[derive(Debug, Clone, Default)]
pub struct PackageAliasTable {
    pub aliases: FxHashMap<DefinitionID, AliasDefinition>, // NEW – file‑scope aliases
    pub by_type: FxHashMap<TypeHead, AliasBucket>,         // existing per‑type buckets
}

#[derive(Default, Debug, Clone)]
pub struct AliasBucket {
    /// All aliases visible on this nominal type, regardless of where‑clauses.
    pub aliases: FxHashMap<Symbol, (DefinitionID, Span)>,
}

#[derive(Debug, Clone)]
pub struct AliasDefinition {
    pub id: DefinitionID,
    pub name: Symbol,
    pub kind: AliasKind,
    pub span: Span,
    /// The HIR type to lower
    pub ast_ty: Box<hir::Type>,
    /// For Inherent aliases - which extension declared it
    pub extension_id: Option<DefinitionID>,
}
