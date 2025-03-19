use taroc_ast::Mutability;

use super::{NodeID, expression::Expression, pattern::BindingPattern, ty::Type};

#[derive(Debug)]
pub struct Local {
    pub id: NodeID,
    pub mutability: Mutability,
    pub pattern: BindingPattern,
    pub ty: Option<Box<Type>>,
    pub initializer: Option<Box<Expression>>,
}
