use taroc_span::{Identifier, Span};

use super::{Label, expression::AnonConst, generics::Generics, ty::Type, visibility::Visibility};

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
    pub identifier: Identifier,
    pub kind: VariantKind,
    pub discriminant: Option<AnonConst>,
    pub span: Span,
}

#[derive(Debug)]
pub struct FieldDefinition {
    pub visibility: Visibility,
    pub mutability: Mutability,
    pub label: Option<Label>,
    pub identifier: Identifier,
    pub ty: Box<Type>,
    pub span: Span,
}

#[derive(Debug)]
pub enum VariantKind {
    Unit,
    Tuple(Vec<FieldDefinition>),
    Struct(Vec<FieldDefinition>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Mutability {
    Mutable,
    Immutable,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InterfaceType {
    Some,
    Any,
}
