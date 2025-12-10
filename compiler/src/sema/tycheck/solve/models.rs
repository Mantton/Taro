use crate::{
    sema::{error::TypeError, models::Ty},
    span::Span,
};

#[derive(Debug, Clone)]
pub enum Goal<'ctx> {
    Equal(Ty<'ctx>, Ty<'ctx>),
}

#[derive(Debug, Clone)]
pub struct Obligation<'ctx> {
    pub location: Span,
    pub goal: Goal<'ctx>,
}

pub enum SolverResult<'ctx> {
    Deferred,
    Solved(Vec<Obligation<'ctx>>), // Solved, With Sub-Obligations
    Error(TypeError<'ctx>),        // Failed, With Error
}
