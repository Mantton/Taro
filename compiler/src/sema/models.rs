use ena::unify::UnifyKey;

use crate::{
    compile::context::Gcx,
    hir::{self, DefinitionID, Mutability},
    sema::tycheck::infer::keys::{FloatVarID, IntVarID},
    span::Symbol,
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

    pub fn is_fn(self) -> bool {
        matches!(self.kind(), TyKind::FnPointer { .. })
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
            TyKind::Adt(adt) => adt.name.as_str().into(),
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
            TyKind::GcPtr => "GcPtr".into(),
            TyKind::Error => "<<error>>".into(),
            TyKind::Infer(k) => match k {
                InferTy::TyVar(id) => format!("{{var({})}}", id._raw),
                InferTy::IntVar(id) => format!("{{integer({})}}", id.index()),
                InferTy::FloatVar(id) => format!("{{float({})}}", id.index()),
                InferTy::FreshTy(_) => todo!(),
            },
            TyKind::Parameter(p) => format!("{}", p.name.as_str()),
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
    Adt(AdtDef),
    Pointer(Ty<'arena>, Mutability),
    Reference(Ty<'arena>, Mutability),
    GcPtr,
    Tuple(&'arena [Ty<'arena>]),
    FnPointer {
        inputs: &'arena [Ty<'arena>],
        output: Ty<'arena>,
    },
    Infer(InferTy),
    Parameter(GenericParameter),
    Error,
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
        self.inputs.len() - self.inputs.iter().filter(|i| i.has_default).count()
    }
}

#[derive(Debug, Clone, Copy)]
pub struct LabeledFunctionParameter<'ctx> {
    pub label: Option<Symbol>,
    pub name: Symbol,
    pub ty: Ty<'ctx>,
    pub has_default: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Constraint<'ctx> {
    /// `T == U`
    TypeEquality(Ty<'ctx>, Ty<'ctx>),
}

index_vec::define_index_type! {
    pub struct TyVarID = u32;
}

index_vec::define_index_type! {
    pub struct FnVarID = u32;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InferTy {
    TyVar(TyVarID),
    IntVar(IntVarID),
    FloatVar(FloatVarID),
    FreshTy(u32),
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
    Const(usize), // TODO: Replace this with a typesystem represenation of a constant
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
                GenericParameterDefinitionKind::Const { default } => {
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
    Type { default: Option<Box<hir::Type>> },
    Const { default: Option<usize> },
}

impl GenericParameterDefinitionKind {
    pub fn has_default(&self) -> bool {
        match self {
            GenericParameterDefinitionKind::Type { default } => default.is_some(),
            GenericParameterDefinitionKind::Const { default } => default.is_some(),
        }
    }
}
