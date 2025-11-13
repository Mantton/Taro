#![feature(associated_type_defaults)]
#![feature(if_let_guard)]
#![allow(unused)]
mod ast;
pub mod compile;
pub mod constants;
mod diagnostics;
pub mod error;
mod parse;
mod sema;
mod span;
mod utils;
