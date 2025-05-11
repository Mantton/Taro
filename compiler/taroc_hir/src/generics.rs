use super::{NodeID, path::Path, ty::Type};
use crate::AnonConst;
use taroc_span::{Identifier, Span};

#[derive(Debug, Clone)]
pub struct TypeParameter {
    pub id: NodeID,
    pub span: Span,
    pub identifier: Identifier,
    pub bounds: Option<GenericBounds>,
    pub kind: TypeParameterKind,
}

#[derive(Debug, Clone)]
pub enum TypeParameterKind {
    Type {
        default: Option<Box<Type>>,
    },
    Constant {
        ty: Box<Type>,
        default: Option<AnonConst>,
    },
}

#[derive(Debug, Clone)]
pub struct TypeParameters {
    pub span: Span,
    pub parameters: Vec<TypeParameter>,
}

#[derive(Debug, Clone)]
pub struct TypeArguments {
    pub span: Span,
    pub arguments: Vec<TypeArgument>,
}

#[derive(Debug, Clone)]
pub enum TypeArgument {
    Type(Box<Type>),
    Const(AnonConst),
}

/// `where T: X & Y`
#[derive(Debug, Clone)]
pub struct GenericWhereClause {
    pub requirements: GenericRequirementList,
    pub span: Span,
}

/// `T: X & Y, V == T`
pub type GenericRequirementList = Vec<GenericRequirement>;

#[derive(Debug, Clone)]
pub enum GenericRequirement {
    /// `Foo == Bar`
    SameTypeRequirement(RequiredTypeConstraint),
    /// `Self::Foo: Hashable`
    ConformanceRequirement(ConformanceConstraint),
}

/// `Foo == Bar`
#[derive(Debug, Clone)]
pub struct RequiredTypeConstraint {
    pub bounded_type: Box<Type>,
    pub bound: Box<Type>,
    pub span: Span,
}

/// `Self::Foo: Hashable`
#[derive(Debug, Clone)]
pub struct ConformanceConstraint {
    pub bounded_type: Box<Type>,
    pub bounds: GenericBounds,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct GenericBound {
    pub path: TaggedPath,
}

pub type GenericBounds = Vec<GenericBound>;

#[derive(Debug, Clone)]
pub struct Inheritance {
    pub interfaces: Vec<TaggedPath>,
}

#[derive(Debug, Clone)]
pub struct TaggedPath {
    pub path: Path,
    pub id: NodeID,
}

#[derive(Debug, Clone)]
pub struct Generics {
    pub type_parameters: Option<TypeParameters>,
    pub where_clause: Option<GenericWhereClause>,
    pub conformance: Option<Inheritance>,
}
