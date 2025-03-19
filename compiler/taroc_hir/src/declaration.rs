use std::collections::HashMap;
use taroc_span::{Identifier, Span};

use super::{
    AttributeList, Block, NodeID, Visibility,
    adt::{Enum, Struct},
    function::Function,
    generics::Generics,
    local::Local,
    path::Path,
    ty::Type,
};

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
    /// `import foo::bar`
    Import(PathTree),
    /// `export foo::bar`
    Export(PathTree),
    /// `interface Walkable`
    Interface(Interface),
    /// `extend Foo`
    ///
    /// `extend Foo where Element is Numerical`
    Extend(Extend),
    /// `conform Foo as Bar`
    ///
    /// `conform Foo as Bar where Element is Numerical`
    Conform(Conform),
    /// `type Foo = Optional<int>`
    TypeAlias(TypeAlias),
    /// `struct Foo {}` | `struct Foo()` | `struct Foo`
    Struct(Struct),
    /// `enum Foo {}`
    Enum(Enum),
    /// `extern "c" {}`
    Extern(Extern),
    /// `namespace Foo {}`
    Namespace(Namespace),
    /// `bridge C {}`
    Bridge(Bridge),
    /// `var count: Int {}`
    Computed(ComputedProperty),
}

#[derive(Debug)]
pub struct TypeAlias {
    pub generics: Generics,
    pub ty: Option<Box<Type>>,
}

#[derive(Debug)]
pub struct Interface {
    pub declarations: Vec<Declaration>,
    pub extensions: Option<Vec<Path>>,
    pub generics: Generics,
}

#[derive(Debug)]
pub struct Extend {
    pub ty_ref_id: NodeID,
    pub ty: Path,
    pub generics: Generics,
    pub declarations: Vec<Declaration>,
}

#[derive(Debug)]
pub struct Conform {
    pub ty_ref_id: NodeID,
    pub interface_ref_id: NodeID,
    pub ty: Path,
    pub interface: Path,
    pub generics: Generics,
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
    Interface,
    Conform,
    Extend,
    Statement,
    Extern,
    Namespace,
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
    pub block: Option<Block>,
}
