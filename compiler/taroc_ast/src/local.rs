use super::{expression::Expression, ty::Type};
use crate::Pattern;
use taroc_ast_ir::Mutability;

#[derive(Debug)]
pub struct Local {
    pub mutability: Mutability,
    pub pattern: Pattern,
    pub ty: Option<Box<Type>>,
    pub initializer: Option<Box<Expression>>,
    pub is_shorthand: bool,
}
