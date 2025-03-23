use super::{CtorKind, NodeID, Visibility, expression::AnonConst, ty::Type};
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

impl VariantKind {
    pub fn ctor(&self) -> (CtorKind, NodeID) {
        match self {
            VariantKind::Unit(id) => (CtorKind::Const, *id),
            VariantKind::Tuple(id, _) => (CtorKind::Fn, *id),
            VariantKind::Struct(id, _) => (CtorKind::Fn, *id),
        }
    }
}
