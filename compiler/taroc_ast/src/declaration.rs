use super::{
    attribute::AttributeList, function::Function, local::Local, path::Path, ty::Type,
    visibility::Visibility,
};
use crate::{AnonConst, EnumDefinition, Generics, StructDefinition};
use std::collections::HashMap;
use taroc_ast_ir::OperatorKind;
use taroc_span::{Identifier, Span, Spanned, Symbol};

#[derive(Debug)]
pub struct Declaration {
    pub span: Span,
    pub identifier: Identifier,
    pub kind: DeclarationKind,
    pub visibility: Visibility,
    pub attributes: AttributeList,
}

#[derive(Debug)]
pub enum DeclarationKind {
    /// `interface Foo {}`
    Interface(InterfaceDefinition),
    /// `struct Foo {}` | `struct Foo()` | struct Foo
    Struct(StructDefinition),
    /// `enum Foo {}`
    Enum(EnumDefinition),
    /// `fn main() {}`
    Function(Function),
    /// `operator +()`
    Operator(OperatorKind, Function),
    /// `let | var VALUE = 10`
    Variable(Local),
    /// `const VALUE: Uint = 10`
    Constant(Box<Type>, AnonConst),
    /// `import foo::bar`
    Import(PathTree),
    /// `export foo::bar`
    Export(PathTree),
    /// `extend Foo`
    Extend(Extend),
    /// `type Foo = Optional<int>`
    TypeAlias(TypeAlias),
    /// `extern "c" {}`
    Extern(Extern),
    /// `namespace Foo {}`
    Namespace(Namespace),
    /// `bridge C {}`
    Bridge(Bridge),
}

#[derive(Debug)]
pub struct TypeAlias {
    pub generics: Generics,
    pub ty: Option<Box<Type>>,
}

#[derive(Debug)]
pub struct Extend {
    pub ty: Box<Type>,
    pub generics: Generics,
    pub declarations: Vec<Declaration>,
}

#[derive(Debug)]
pub struct Extern {
    pub abi: Spanned<Symbol>,
    pub declarations: Vec<Declaration>,
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

#[derive(Debug)]
pub struct Bridge {
    pub values: HashMap<Symbol, BridgeValue>,
}

#[derive(Debug)]
pub enum BridgeValue {
    String(Symbol),
    Array(Vec<Symbol>),
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
    Simple { alias: Option<Identifier> },
    Nested { nodes: Vec<PathTree>, span: Span },
    Glob,
}

#[derive(Debug)]
pub struct InterfaceDefinition {
    pub generics: Generics,
    pub declarations: Vec<Declaration>,
}
