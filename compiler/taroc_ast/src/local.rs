use taroc_ast_ir::{LocalSource, Mutability};

use super::{expression::Expression, pattern::BindingPattern, ty::Type};

#[derive(Debug)]
pub struct Local {
    pub mutability: Mutability,
    pub pattern: BindingPattern,
    pub ty: Option<Box<Type>>,
    pub initializer: Option<Box<Expression>>,
    pub is_shorthand: bool,
    pub source: LocalSource,
}
