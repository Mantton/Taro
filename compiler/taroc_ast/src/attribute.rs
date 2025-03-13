use taroc_span::Identifier;

#[derive(Debug)]
pub struct Attribute {
    pub identifier: Identifier,
}

pub type AttributeList = Vec<Attribute>;
