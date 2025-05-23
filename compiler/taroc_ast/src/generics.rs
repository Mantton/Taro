use super::{path::Path, ty::Type};
use crate::AnonConst;
use taroc_span::{Identifier, Span};

#[derive(Debug)]
pub struct TypeParameter {
    pub span: Span,
    pub identifier: Identifier,
    /// The interfaces this parameter must conform to
    ///
    /// `Option<T: Hash & Display & Identifiable>`
    pub bounds: Option<GenericBounds>,
    pub kind: TypeParameterKind,
}

#[derive(Debug)]
pub enum TypeParameterKind {
    Type {
        default: Option<Box<Type>>,
    },
    Constant {
        ty: Box<Type>,
        default: Option<AnonConst>,
    },
}

#[derive(Debug)]
pub struct TypeParameters {
    pub span: Span,
    pub parameters: Vec<TypeParameter>,
}

#[derive(Debug)]
pub struct TypeArguments {
    pub span: Span,
    pub arguments: Vec<TypeArgument>,
}

#[derive(Debug)]
pub enum TypeArgument {
    Type(Box<Type>),
    Const(AnonConst),
}

#[derive(Debug)]
pub struct Generics {
    pub type_parameters: Option<TypeParameters>,
    pub where_clause: Option<GenericWhereClause>,
    pub conformances: Option<Conformances>,
}

/// `where T: X & Y`
#[derive(Debug)]
pub struct GenericWhereClause {
    pub requirements: GenericRequirementList,
    pub span: Span,
}

/// `T: X & Y, V == T`
pub type GenericRequirementList = Vec<GenericRequirement>;

#[derive(Debug)]
pub enum GenericRequirement {
    /// `Foo == Bar`
    SameTypeRequirement(RequiredTypeConstraint),
    /// `Self::Foo: Hashable`
    ConformanceRequirement(ConformanceConstraint),
}

/// `Foo == Bar`
#[derive(Debug)]
pub struct RequiredTypeConstraint {
    pub bounded_type: Box<Type>,
    pub bound: Box<Type>,
    pub span: Span,
}

/// `Self::Foo: Hashable`
#[derive(Debug)]
pub struct ConformanceConstraint {
    pub bounded_type: Box<Type>,
    pub bounds: GenericBounds,
    pub span: Span,
}

#[derive(Debug)]
pub struct GenericBound {
    pub path: Path,
}

pub type GenericBounds = Vec<GenericBound>;

#[derive(Debug)]
pub struct Conformances {
    pub interfaces: Vec<Path>,
}
