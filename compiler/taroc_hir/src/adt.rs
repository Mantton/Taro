use taroc_span::{Identifier, Span};

use super::{CtorKind, NodeID, Visibility, expression::AnonConst, generics::Generics, ty::Type};

#[derive(Debug)]
pub struct Struct {
    pub generics: Generics,
    pub variant: VariantKind,
}

#[derive(Debug)]
pub struct Enum {
    pub generics: Generics,
    pub variants: Vec<Variant>,
}

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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Mutability {
    Mutable,
    Immutable,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InterfaceType {
    Some,
    Any,
}
