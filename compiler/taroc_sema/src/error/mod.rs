use crate::ty::{GenericArgument, Ty};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExpectedFound<T> {
    pub expected: T,
    pub found: T,
}

impl<T> ExpectedFound<T> {
    pub fn new(expected: T, found: T) -> Self {
        ExpectedFound { expected, found }
    }
}

pub enum TypeError<'ctx> {
    Mutability,
    ArgCount,
    TupleArity(ExpectedFound<usize>),
    TyMismatch(ExpectedFound<Ty<'ctx>>),
    ArgMismatch(ExpectedFound<GenericArgument<'ctx>>),
    NoOverloadCandidateMatch,
    ConformanceNotMet,
    UnknownField,
    NotAStruct,
    TupleIndexOutOfBounds(ExpectedFound<usize>),
    NotATuple,
    UnknownMethod,
    InvalidMethodReceiver,
}
