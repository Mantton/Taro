mod operator;
pub use operator::*;
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Mutability {
    Mutable,
    Immutable,
}

#[derive(Debug, Clone, Copy)]
pub struct BindingMode(pub Mutability);
