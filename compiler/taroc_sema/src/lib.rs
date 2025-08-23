#![feature(if_let_guard)]

mod check;
mod collect;
mod context;
mod error;
mod extend;
pub mod fold;
mod freshen;
mod infer;
mod lower;
mod models;
mod normalize;
pub mod passes;
mod recursive;
mod ty;
pub mod typing;
mod utils;

pub use context::*;
