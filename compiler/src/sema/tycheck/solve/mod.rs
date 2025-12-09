use crate::{sema::models::Ty, span::Span};

mod constraint;
mod context;
mod solver;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Goal<'ctx> {
    Equal(Ty<'ctx>, Ty<'ctx>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Obligation<'ctx> {
    pub location: Span,
    pub goal: Goal<'ctx>,
}

pub use context::ObligationCtx;
