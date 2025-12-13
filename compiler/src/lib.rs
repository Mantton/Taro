#![feature(associated_type_defaults)]
#![feature(if_let_guard)]
// #![allow(unused)]
mod ast;
mod ast_lowering;
pub mod codegen;
pub mod compile;
pub mod constants;
pub mod diagnostics;
pub mod error;
mod hir;
pub mod mir;
mod parse;
mod sema;
mod span;
mod thir;
mod utils;

pub use span::PackageIndex;
