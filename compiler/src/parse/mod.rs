pub(crate) mod escape;
pub mod lexer;
pub mod token;
pub use token::{Base, IntegerTypeSuffix};
pub mod parser;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SyntaxMode {
    Strict,
    Recover,
}

pub(crate) const MISSING_MEMBER_NAME_DIAGNOSTIC: usize = 1001;
