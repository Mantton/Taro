use taroc_span::{Identifier, Symbol};

#[derive(Debug, Clone)]
pub struct Attribute {
    pub identifier: Identifier,
}

pub type AttributeList = Vec<Attribute>;

pub fn attributes_contain(attrs: &AttributeList, sym: Symbol) -> bool {
    attrs.iter().any(|attr| attr.identifier.symbol == sym)
}
