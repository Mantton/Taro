use super::{NodeID, expression::Expression, ty::Type};
use crate::Pattern;
use taroc_ast_ir::Mutability;

#[derive(Debug, Clone)]
pub struct Local {
    pub id: NodeID,
    pub mutability: Mutability,
    pub pattern: Pattern,
    pub ty: Option<Box<Type>>,
    pub initializer: Option<Box<Expression>>,
}
