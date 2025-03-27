use std::fmt::Debug;

use taroc_span::Span;

use super::{NodeID, adt::FieldDefinition, expression::AnonConst, path::Path};

#[derive(Debug)]
pub struct Type {
    pub id: NodeID,
    pub span: Span,
    pub kind: TypeKind,
}

#[derive(Debug)]
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
        output: Option<Box<Type>>,
        is_async: bool,
    },
    // func (&mut self)
    ImplicitSelf,

    // |a, b| { a + b }
    InferedClosureParameter,

    /// Interface types
    ///
    /// `some T` | `any T`
    SomeOrAny(InterfaceType, Box<Type>),

    /// Foo & Bar
    Composite(Vec<Box<Type>>),
}

pub use taroc_ast::InterfaceType;
pub use taroc_ast::Mutability;
