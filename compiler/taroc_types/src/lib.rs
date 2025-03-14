use taroc_data_structures::Interned;
use taroc_hir::DefinitionID;
use taroc_span::{FileID, Symbol};



#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Ty<'arena>(Interned<'arena, TyKind<'arena>>);

impl Ty<'_> {
    pub fn with_kind<'arena>(k: Interned<'arena, TyKind<'arena>>) -> Ty<'arena> {
        Ty(k)
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
    Slice(Ty<'arena>),
    Tuple(&'arena [Ty<'arena>]),

    Adt {
        id: DefinitionID,
        name: Symbol,
        kind: AdtKind,
        arguments: &'arena [GenericArgument<'arena>],
    },

    Parameter,
    Infer,
    Error,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AdtKind {
    Struct,
    Enum,
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Mutability {
    Mutable,
    Immutable,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InterfaceType {
    Some,
    Any,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Visibility {
    Public,
    ModuleRestricted(DefinitionID),
    FileRestricted(FileID),
}
