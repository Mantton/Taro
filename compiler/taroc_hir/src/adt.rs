use crate::Generics;

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
    Unit(NodeID),
    Tuple(NodeID, Vec<FieldDefinition>),
    Struct(Vec<FieldDefinition>),
}

#[derive(Debug, Clone)]
pub struct StructDefinition {
    pub generics: Generics,
    pub variant: VariantKind,
}

#[derive(Debug, Clone)]
pub struct EnumDefinition {
    pub generics: Generics,
    pub variants: Vec<Variant>,
}

impl VariantKind {
    /// Return the `NodeId` of this variant's constructor, if it has one.
    pub fn ctor_node_id(&self) -> Option<NodeID> {
        match *self {
            VariantKind::Struct(..) => None,
            VariantKind::Tuple(id, _) | VariantKind::Unit(id) => Some(id),
        }
    }
}
