use super::{NodeID, Visibility, expression::AnonConst, ty::Type};
use taroc_ast_ir::Mutability;
use taroc_span::{Identifier, Span};

#[derive(Debug, Clone)]
pub struct Variant {
    pub id: NodeID,
    pub identifier: Identifier,
    pub kind: VariantKind,
    pub discriminant: Option<AnonConst>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct FieldDefinition {
    pub id: NodeID,
    pub visibility: Visibility,
    pub mutability: Mutability,
    pub identifier: Identifier,
    pub ty: Box<Type>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum VariantKind {
    Unit,
    Tuple(Vec<FieldDefinition>),
    Struct(Vec<FieldDefinition>),
}
