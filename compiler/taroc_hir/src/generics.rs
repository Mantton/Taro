use taroc_span::{Identifier, Span};

use super::{NodeID, expression::AnonConst, path::Path, ty::Type};

#[derive(Debug)]
pub struct TypeParameter {
    pub id: NodeID,
    pub span: Span,
    pub identifier: Identifier,
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
    pub arguments: Vec<Box<Type>>,
}

#[derive(Debug)]
pub struct Generics {
    pub parameters: TypeParameters,
    pub where_clause: Option<GenericWhereClause>,
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
    pub bounded_type: Path,
    pub bound: Box<Type>,
    pub span: Span,
}

/// `Self::Foo: Hashable`
#[derive(Debug)]
pub struct ConformanceConstraint {
    pub bounded_type: Path,
    pub bounds: GenericBounds,
    pub span: Span,
}

#[derive(Debug)]
pub struct GenericBound {
    pub path: Path,
}

pub type GenericBounds = Vec<GenericBound>;
