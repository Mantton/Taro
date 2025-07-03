use taroc_hir::OperatorKind;
use taroc_span::Symbol;

use crate::{
    GlobalContext,
    ty::{GenericArgument, InterfaceReference, Ty},
    utils::interface_ref2str,
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
    ConformanceNotMet(Ty<'ctx>, InterfaceReference<'ctx>),
    UnknownField(Symbol, Ty<'ctx>),
    NotAStruct(Ty<'ctx>),
    TupleIndexOutOfBounds(ExpectedFound<usize>),
    NotATuple,
    UnknownMethod,
    NoUnaryOperator(Ty<'ctx>, OperatorKind),
    NoBinaryOperator(Ty<'ctx>, Ty<'ctx>, OperatorKind),
    CannotDereference(Ty<'ctx>),
    InvalidPointerEquality(Ty<'ctx>),
    CannotCast(Ty<'ctx>, Ty<'ctx>),
    CannotMatchAgainst(Ty<'ctx>, Ty<'ctx>),
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
            TypeError::ConformanceNotMet(ty, interface) => format!(
                "{} does not conform to {}",
                ty.format(gcx),
                interface_ref2str(interface, gcx)
            ),
            TypeError::UnknownField(name, ty) => {
                format!("unknown field named \"{name}\" on {}", ty.format(gcx))
            }
            TypeError::NotAStruct(ty) => {
                format!("{} is not a struct", ty.format(gcx))
            }
            TypeError::TupleIndexOutOfBounds(ef) => format!(
                "tuple index out of bounds: length is {}, index is {}",
                ef.expected, ef.found
            ),
            TypeError::NotATuple => "not a tuple".into(),
            TypeError::UnknownMethod => "unknown method".into(),
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
            TypeError::CannotCast(ty, ty1) => {
                format!("cannot cast '{}' to '{}", ty.format(gcx), ty1.format(gcx))
            }
            TypeError::CannotMatchAgainst(ty, ty1) => {
                format!(
                    "cannot match '{}' to '{}, add a supporting '~=' operator",
                    ty.format(gcx),
                    ty1.format(gcx)
                )
            }
        }
    }
}
