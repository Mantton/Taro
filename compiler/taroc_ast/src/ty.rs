use crate::FieldDefinition;

use super::{expression::AnonConst, path::Path};
use taroc_ast_ir::Mutability;
use taroc_span::Span;

#[derive(Debug)]
pub struct Type {
    pub span: Span,
    pub kind: TypeKind,
}

#[derive(Debug)]
pub enum TypeKind {
    /// Path Type
    ///
    /// `Foo` | `Foo::Bar::Baz` | `Foo<T>`
    Path(Path),
    /// Pointer Type
    ///
    /// `*mut T` | `*const T`
    Pointer(Box<Type>, Mutability),
    /// Reference Type
    ///
    /// `&T` | `&mut T`
    Reference(Box<Type>, Mutability),
    /// Paren type
    /// `(T)`
    Parenthesis(Box<Type>),
    /// Tuple Type
    ///
    /// `(T, V)`
    Tuple(Vec<Box<Type>>),
    /// Optional Type
    ///
    /// `T?`
    Optional(Box<Type>),
    /// An Array with a fixed size `N`
    ///
    /// `[N]T`
    Array {
        size: AnonConst,
        element: Box<Type>,
    },
    /// A Dynamic, growable array
    ///
    /// `[]T`
    List(Box<Type>),
    /// A hash-map
    ///
    /// `[T:V]`
    Dictionary {
        key: Box<Type>,
        value: Box<Type>,
    },
    /// Anonymous Struct Type
    ///
    /// `let foo : struct { age: int, name: int } = struct { age: 10, name: ""}`
    AnonStruct {
        fields: Vec<FieldDefinition>,
    },
    /// (T, V) -> X
    Function {
        inputs: Vec<Box<Type>>,
        output: Box<Type>,
        is_async: bool,
    },
    /// Ty of, self, &mut self, &self
    ImplicitSelf,
    // { a, b in a + b}
    InferedClosureParameter,
    // Interface types
    /// `some T`
    Opaque(Vec<Path>),
    /// `any T`
    Exisitential(Vec<Path>),
    /// `~T` -> Option<&T>
    OptionalReference(Box<Type>, Mutability),
}
