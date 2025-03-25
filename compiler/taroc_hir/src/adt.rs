use super::{NodeID, Visibility, expression::AnonConst, ty::Type};
use taroc_ast::Mutability;
use taroc_span::{Identifier, Span};

#[derive(Debug)]
pub struct Variant {
    pub id: NodeID,
    pub identifier: Identifier,
    pub kind: VariantKind,
    pub discriminant: Option<AnonConst>,
    pub span: Span,
}

#[derive(Debug)]
pub struct FieldDefinition {
    pub id: NodeID,
    pub visibility: Visibility,
    pub mutability: Mutability,
    pub identifier: Identifier,
    pub ty: Box<Type>,
    pub span: Span,
}

#[derive(Debug)]
pub enum VariantKind {
    Unit(NodeID),
    Tuple(NodeID, Vec<FieldDefinition>),
    Struct(NodeID, Vec<FieldDefinition>),
}
