use super::{
    AttributeList, Block, NodeID, Visibility, function::Function, local::Local, path::Path,
    ty::Type,
};
use crate::{AnonConst, Generics, Variant};
use std::collections::HashMap;
use taroc_span::{Identifier, Span};

#[derive(Debug)]
pub struct Declaration {
    pub id: NodeID,
    pub span: Span,
    pub identifier: Identifier,
    pub kind: DeclarationKind,
    pub visibility: Visibility,
    pub attributes: AttributeList,
}

#[derive(Debug)]
pub enum DeclarationKind {
    /// `fn main() {}`
    Function(Function),
    /// `init()` | `init?()`
    Constructor(Function, bool),
    /// `let | var VALUE = 10`
    Variable(Local),
    /// `const VALUE: Uint = 10`
    Constant(Box<Type>, AnonConst),
    /// `import foo::bar`
    Import(PathTree),
    /// `export foo::bar`
    Export(PathTree),
    /// `extend Foo`
    ///
    /// `extend Foo where Element is Numerical`
    Extend(Extend),
    /// `type Foo = Optional<int>`
    TypeAlias(TypeAlias),

    /// `extern "c" {}`
    Extern(Extern),
    /// `namespace Foo {}`
    Namespace(Namespace),
    /// `bridge C {}`
    Bridge(Bridge),
    /// `var count: Int {}`
    Computed(ComputedProperty),
    /// `case Foo, case Bar {}, case Baz`
    EnumCase(EnumCase),
    /// `associatedtype Foo`
    AssociatedType,
    /// `struct Foo {}` | `enum Foo {}` | `interface Foo {}`
    DefinedType(DefinedType),
}

#[derive(Debug)]
pub struct TypeAlias {
    pub generics: Generics,
    pub ty: Option<Box<Type>>,
}

#[derive(Debug)]
pub struct Extend {
    pub ty_ref_id: NodeID,
    pub ty: Path,
    pub declarations: Vec<Declaration>,
}

#[derive(Debug)]
pub struct Extern {
    pub abi: Abi,
    pub declarations: Vec<Declaration>,
}

#[derive(Debug, Clone)]
pub enum Abi {
    C,
    TaroInstrinsic,
    Error,
}

#[derive(Debug)]
pub struct Namespace {
    pub declarations: Vec<Declaration>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeclarationContext {
    Module,
    Extend,
    Statement,
    Extern,
    Namespace,
    Struct,
    Enum,
    Interface,
}

pub enum FunctionContext {
    Free,
    Extern,
    Declaration(DeclarationContext),
}

#[derive(Debug, Clone)]
pub struct Bridge {
    pub values: HashMap<String, BridgeValue>,
}

#[derive(Debug, Clone)]
pub enum BridgeValue {
    String(String),
    Array(Vec<String>),
    Dict(Box<Bridge>),
}

#[derive(Debug)]
pub struct PathTree {
    pub root: Path,
    pub node: PathTreeNode,
    pub span: Span,
}

#[derive(Debug)]
pub enum PathTreeNode {
    Simple {
        alias: Option<Identifier>,
    },
    Nested {
        nodes: Vec<(PathTree, NodeID)>,
        span: Span,
    },
    Glob,
}

#[derive(Debug)]
pub struct ComputedProperty {
    pub id: NodeID,
    pub ty: Box<Type>,
    pub block: Block,
}

#[derive(Debug)]
pub enum DefinedTypeKind {
    Struct,
    Enum,
    Interface,
}

#[derive(Debug)]
pub struct DefinedType {
    pub kind: DefinedTypeKind,
    pub generics: Generics,
    pub declarations: Vec<Declaration>,
}

#[derive(Debug)]
pub struct EnumCase {
    pub members: Vec<Variant>,
}
