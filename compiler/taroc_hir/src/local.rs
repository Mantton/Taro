use super::{NodeID, expression::Expression, pattern::BindingPattern, ty::Type};
use taroc_ast_ir::Mutability;

#[derive(Debug, Clone)]
pub struct Local {
    pub id: NodeID,
    pub mutability: Mutability,
    pub pattern: BindingPattern,
    pub ty: Option<Box<Type>>,
    pub initializer: Option<Box<Expression>>,
}
