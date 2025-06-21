use super::{
    attribute::AttributeList, function::Function, local::Local, path::Path, ty::Type,
    visibility::Visibility,
};
use crate::{EnumDefinition, Expression, Generics, StructDefinition};
use std::collections::HashMap;
use taroc_ast_ir::OperatorKind;
use taroc_span::{Identifier, Span, Spanned, Symbol};

#[derive(Debug)]
pub struct Declaration<K = DeclarationKind> {
    pub span: Span,
    pub identifier: Identifier,
    pub kind: K,
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
    Constant(ConstantDeclaration),
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

pub type FunctionDeclaration = Declaration<FunctionDeclarationKind>;
#[derive(Debug)]
pub enum FunctionDeclarationKind {
    Struct(StructDefinition),
    Enum(EnumDefinition),
    Function(Function),
    Constant(ConstantDeclaration),
    TypeAlias(TypeAlias),
}

pub type AssociatedDeclaration = Declaration<AssociatedDeclarationKind>;
#[derive(Debug)]
pub enum AssociatedDeclarationKind {
    Constant(ConstantDeclaration),
    Function(Function),
    Type(TypeAlias),
    Operator(OperatorKind, Function),
}

pub type ForeignDeclaration = Declaration<ForeignDeclarationKind>;
#[derive(Debug)]
pub enum ForeignDeclarationKind {
    Function(Function),
    Type(TypeAlias),
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
    pub declarations: Vec<AssociatedDeclaration>,
}

#[derive(Debug)]
pub struct Extern {
    pub abi: Spanned<Symbol>,
    pub declarations: Vec<ForeignDeclaration>,
}

#[derive(Debug)]
pub struct Namespace {
    pub declarations: Vec<Declaration>,
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
    pub declarations: Vec<AssociatedDeclaration>,
}

#[derive(Debug)]
pub struct ConstantDeclaration {
    pub identifier: Identifier,
    pub ty: Box<Type>,
    pub expr: Option<Box<Expression>>,
}

impl TryFrom<DeclarationKind> for ForeignDeclarationKind {
    type Error = DeclarationKind;

    fn try_from(kind: DeclarationKind) -> Result<ForeignDeclarationKind, DeclarationKind> {
        Ok(match kind {
            DeclarationKind::Function(node) => ForeignDeclarationKind::Function(node),
            DeclarationKind::TypeAlias(node) => ForeignDeclarationKind::Type(node),
            _ => return Err(kind),
        })
    }
}

impl TryFrom<DeclarationKind> for AssociatedDeclarationKind {
    type Error = DeclarationKind;

    fn try_from(kind: DeclarationKind) -> Result<AssociatedDeclarationKind, DeclarationKind> {
        Ok(match kind {
            DeclarationKind::Constant(node) => AssociatedDeclarationKind::Constant(node),
            DeclarationKind::Function(node) => AssociatedDeclarationKind::Function(node),
            DeclarationKind::TypeAlias(node) => AssociatedDeclarationKind::Type(node),
            DeclarationKind::Operator(op, node) => AssociatedDeclarationKind::Operator(op, node),

            _ => return Err(kind),
        })
    }
}

impl TryFrom<DeclarationKind> for FunctionDeclarationKind {
    type Error = DeclarationKind;

    fn try_from(kind: DeclarationKind) -> Result<FunctionDeclarationKind, DeclarationKind> {
        Ok(match kind {
            DeclarationKind::Function(node) => FunctionDeclarationKind::Function(node),
            DeclarationKind::Struct(node) => FunctionDeclarationKind::Struct(node),
            DeclarationKind::Enum(node) => FunctionDeclarationKind::Enum(node),
            DeclarationKind::Constant(node) => FunctionDeclarationKind::Constant(node),
            DeclarationKind::TypeAlias(node) => FunctionDeclarationKind::TypeAlias(node),
            _ => return Err(kind),
        })
    }
}
