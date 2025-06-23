use taroc_hir::OperatorKind;

use crate::{
    GlobalContext,
    ty::{GenericArgument, Ty},
};

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
    NoUnaryOperator(Ty<'ctx>, OperatorKind),
    NoBinaryOperator(Ty<'ctx>, Ty<'ctx>, OperatorKind),
    CannotDereference(Ty<'ctx>),
    InvalidPointerEquality(Ty<'ctx>),
}

impl<'ctx> TypeError<'ctx> {
    pub fn format(self, gcx: GlobalContext<'ctx>) -> String {
        match self {
            TypeError::Mutability => "mutability mismatch".into(),
            TypeError::ArgCount => "argument count mismatch".into(),
            TypeError::TupleArity(ef) => format!(
                "expected tuple of length {}, found {}",
                ef.expected, ef.found
            ),
            TypeError::TyMismatch(ef) => format!(
                "expected {}, found {}",
                ef.expected.format(gcx),
                ef.found.format(gcx)
            ),
            TypeError::ArgMismatch(ef) => {
                let expected = match ef.expected {
                    GenericArgument::Type(t) => t.format(gcx),
                    GenericArgument::Const(v) => v.to_string(),
                };
                let found = match ef.found {
                    GenericArgument::Type(t) => t.format(gcx),
                    GenericArgument::Const(v) => v.to_string(),
                };
                format!("expected argument {expected}, found {found}")
            }
            TypeError::NoOverloadCandidateMatch => "no overload candidate matches".into(),
            TypeError::ConformanceNotMet => "required interface conformance not met".into(),
            TypeError::UnknownField => "unknown field".into(),
            TypeError::NotAStruct => "not a struct".into(),
            TypeError::TupleIndexOutOfBounds(ef) => format!(
                "tuple index out of bounds: length is {}, index is {}",
                ef.expected, ef.found
            ),
            TypeError::NotATuple => "not a tuple".into(),
            TypeError::UnknownMethod => "unknown method".into(),
            TypeError::InvalidMethodReceiver => "invalid method receiver".into(),
            TypeError::NoUnaryOperator(ty, op) => {
                format!("no unary operator '{:?}' for type '{}'", op, ty.format(gcx))
            }
            TypeError::NoBinaryOperator(lhs, rhs, op) => format!(
                "no binary operator '{:?}' for types '{}' and '{}'",
                op,
                lhs.format(gcx),
                rhs.format(gcx)
            ),
            TypeError::CannotDereference(ty) => {
                format!("cannot dereference type '{}'", ty.format(gcx))
            }
            TypeError::InvalidPointerEquality(ty) => {
                format!("cannot use pointer equality for type '{}'", ty.format(gcx))
            }
        }
    }
}
