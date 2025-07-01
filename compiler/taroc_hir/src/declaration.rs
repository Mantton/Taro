use super::{AttributeList, NodeID, Visibility, function::Function, path::Path, ty::Type};
use crate::{EnumDefinition, Expression, Generics, StructDefinition};
use taroc_ast_ir::OperatorKind;
use taroc_span::{Identifier, Span, Spanned};

#[derive(Debug, Clone)]
pub struct Declaration<K = DeclarationKind> {
    pub id: NodeID,
    pub span: Span,
    pub identifier: Identifier,
    pub kind: K,
    pub visibility: Visibility,
    pub attributes: AttributeList,
}

#[derive(Debug, Clone)]
pub enum DeclarationKind {
    /// `interface Foo {}`
    Interface(InterfaceDefinition),
    /// `struct Foo {}` | `struct Foo()` | struct Foo
    Struct(StructDefinition),
    /// `enum Foo {}`
    Enum(EnumDefinition),
    /// `fn main() {}`
    Function(Function),

    /// `let | var VALUE = 10`
    Static(StaticDeclaration),
    /// `const VALUE: Uint = 10`
    Constant(ConstantDeclaration),
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
    ///
    Malformed,
}

pub type FunctionDeclaration = Declaration<FunctionDeclarationKind>;
#[derive(Debug, Clone)]
pub enum FunctionDeclarationKind {
    Struct(StructDefinition),
    Enum(EnumDefinition),
    Function(Function),
    Constant(ConstantDeclaration),
    TypeAlias(TypeAlias),
}

pub type AssociatedDeclaration = Declaration<AssociatedDeclarationKind>;
#[derive(Debug, Clone)]
pub enum AssociatedDeclarationKind {
    Constant(ConstantDeclaration),
    Function(Function),
    Type(TypeAlias),
    Operator(OperatorKind, Function),
}

pub type ForeignDeclaration = Declaration<ForeignDeclarationKind>;
#[derive(Debug, Clone)]
pub enum ForeignDeclarationKind {
    Function(Function),
    Type(TypeAlias),
}

#[derive(Debug, Clone)]
pub struct TypeAlias {
    pub generics: Generics,
    pub ty: Option<Box<Type>>,
}

#[derive(Debug, Clone)]
pub struct Extend {
    pub ty: Box<Type>,
    pub generics: Generics,
    pub declarations: Vec<AssociatedDeclaration>,
}

#[derive(Debug, Clone)]
pub struct Extern {
    pub abi: Spanned<Abi>,
    pub declarations: Vec<ForeignDeclaration>,
}

#[derive(Debug, Clone)]
pub enum Abi {
    C,
    TaroInstrinsic,
    Error,
}

#[derive(Debug, Clone)]
pub struct Namespace {
    pub declarations: Vec<Declaration>,
}

#[derive(Debug, Clone)]
pub struct PathTree {
    pub root: Path,
    pub node: PathTreeNode,
    pub span: Span,
}

#[derive(Debug, Clone)]
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

#[derive(Debug, Clone)]
pub struct InterfaceDefinition {
    pub generics: Generics,
    pub declarations: Vec<AssociatedDeclaration>,
}

#[derive(Debug, Clone)]
pub struct ConstantDeclaration {
    pub identifier: Identifier,
    pub ty: Box<Type>,
    pub expr: Option<Box<Expression>>,
}

#[derive(Debug, Clone)]
pub struct StaticDeclaration {
    pub identifier: Identifier,
    pub ty: Box<Type>,
    pub expr: Option<Box<Expression>>,
}
