mod operator;
pub use operator::*;
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Mutability {
    Mutable,
    Immutable,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LocalSource {
    StoredProperty,
    StaticProperty,
    Variable,
    TopLevelDecl,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FunctionSource {
    Free,
    Interface,
    Adt,
    Constructor,
    Operator,
}
