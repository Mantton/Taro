use super::{Label, expression::AnonConst, ty::Type, visibility::Visibility};
use crate::Generics;
use taroc_ast_ir::Mutability;
use taroc_span::{Identifier, Span};

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

#[derive(Debug)]
pub struct StructDefinition {
    pub generics: Generics,
    pub variant: VariantKind,
}

#[derive(Debug)]
pub struct EnumDefinition {
    pub generics: Generics,
    pub cases: Vec<EnumCase>,
}

#[derive(Debug)]
pub struct EnumCase {
    pub variants: Vec<Variant>,
}
