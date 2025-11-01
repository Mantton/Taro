#![feature(associated_type_defaults)]
#![allow(unused)]
mod ast;
pub mod compile;
pub mod constants;
mod diagnostics;
pub mod error;
pub mod package;
mod parse;
mod sema;
mod span;
