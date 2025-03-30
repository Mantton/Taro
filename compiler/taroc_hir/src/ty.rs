use crate::TaggedPath;

use super::{NodeID, expression::AnonConst, path::Path};
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
    /// Pointer Type
    ///
    /// `*T` | `*const T` | `*raw T`
    Pointer(Box<Type>, Mutability),
    /// Reference Type
    ///
    /// `&T`
    Reference(Box<Type>, Mutability),
    /// Tuple Type
    ///
    /// `(T, V)`
    Tuple(Vec<Box<Type>>),
    /// Path Type
    ///
    /// `Foo` | `Foo::Bar::Baz` | `Foo<T>`
    Path(Path),
    /// An Array with a fixed size `N`
    ///
    /// `[N]T`
    Array {
        size: AnonConst,
        element: Box<Type>,
    },
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
}

pub use taroc_ast::Mutability;
