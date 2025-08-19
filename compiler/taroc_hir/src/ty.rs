use super::{NodeID, path::Path};
use crate::{AnonConst, FieldDefinition, TaggedPath};
use std::fmt::Debug;
use taroc_span::Span;

#[derive(Debug, Clone)]
pub struct Type {
    pub id: NodeID,
    pub span: Span,
    pub kind: TypeKind,
}

#[derive(Debug, Clone)]
pub enum TypeKind {
    /// Pointer : *T | *const T
    Pointer(Box<Type>, Mutability),
    /// Reference: &T | &const T
    Reference(Box<Type>, Mutability),
    /// Array: [T; N]
    Array(Box<Type>, AnonConst),
    /// Tuple Type
    ///
    /// `(T, V)`
    Tuple(Vec<Box<Type>>),
    /// Path Type
    ///
    /// `Foo` | `Foo::Bar::Baz` | `Foo<T>`
    Path(Path),
    Function {
        inputs: Vec<Box<Type>>,
        output: Box<Type>,
        is_async: bool,
    },
    // Type to be inferred
    Infer,
    // Interface types
    /// `some T`
    Opaque(Vec<TaggedPath>),
    /// `any T`
    Exisitential(Vec<TaggedPath>),
    AnonStruct {
        fields: Vec<FieldDefinition>,
    },
    Malformed,
}

pub use taroc_ast_ir::Mutability;
