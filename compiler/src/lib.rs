#![feature(associated_type_defaults)]
mod ast;
mod ast_lowering;
#[cfg(test)]
#[path = "../build_identity.rs"]
mod build_identity;
mod cfg;
mod cfg_eval;
pub mod codegen;
pub mod compile;
pub mod constants;
pub mod diagnostics;
pub mod error;
mod hir;
mod interner;
pub mod metadata;
pub mod mir;
pub mod package;
mod parse;
pub mod runtime_abi;
mod sema;
pub mod span;
pub mod specialize;
#[cfg(test)]
mod test_support;
mod thir;
mod utils;

pub use span::PackageIndex;
