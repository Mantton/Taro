#![feature(associated_type_defaults)]
#![feature(if_let_guard)]
// #![allow(unused)]
mod ast;
mod ast_lowering;
pub mod compile;
pub mod constants;
pub mod codegen;
pub mod diagnostics;
pub mod error;
pub mod mir;
mod thir;
mod hir;
mod parse;
mod sema;
mod span;
mod utils;

pub use span::PackageIndex;
