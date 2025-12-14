use crate::{
    compile::context::Gcx,
    sema::models::Ty,
    span::{Spanned, Symbol},
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

#[derive(Debug, Clone, Copy)]
pub enum TypeError<'ctx> {
    Mutability(ExpectedFound<Ty<'ctx>>),
    TyMismatch(ExpectedFound<Ty<'ctx>>),
    TupleArity(ExpectedFound<usize>),
    Apply(ApplyValidationError),
    NoOverloadMatches,
    AmbiguousOverload,
    NoSuchMember { name: Symbol, on: Ty<'ctx> },
    NotCallable { found: Ty<'ctx> },
}

pub type SpannedError<'ctx> = Spanned<TypeError<'ctx>>;
pub type SpannedErrorList<'ctx> = Vec<SpannedError<'ctx>>;

impl<'ctx> TypeError<'ctx> {
    pub fn format(self, gcx: Gcx<'ctx>) -> String {
        match self {
            TypeError::Mutability(ef) | TypeError::TyMismatch(ef) => {
                format!(
                    "expected {}, found {}",
                    ef.expected.format(gcx),
                    ef.found.format(gcx)
                )
            }
            TypeError::TupleArity(ef) => format!(
                "expected tuple of length {}, found {}",
                ef.expected, ef.found
            ),
            TypeError::Apply(e) => format!("{e}"),
            TypeError::NoOverloadMatches => "no overload matches this call".into(),
            TypeError::AmbiguousOverload => {
                "ambiguous overload; unable to pick a best candidate".into()
            }
            TypeError::NoSuchMember { name, on } => {
                format!("no member named '{}' found on type {}", name, on.format(gcx))
            }
            TypeError::NotCallable { found } => {
                format!("cannot call value of type {}", found.format(gcx))
            }
        }
    }
}

// Validation errors
#[derive(Debug, Clone, Copy)]
pub enum ApplyValidationError {
    ArityMismatch {
        expected_min: usize,
        expected_max: Option<usize>,
        provided: usize,
    },
    LabelMismatch {
        param_index: usize,
        expected: Option<Symbol>,
        provided: Option<Symbol>,
    },
    MissingRequiredParameter {
        param_index: usize,
        param_name: Symbol,
    },
    ExtraArgument {
        arg_index: usize,
    },
}

impl std::fmt::Display for ApplyValidationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ApplyValidationError::ArityMismatch {
                expected_min,
                expected_max,
                provided,
            } => match expected_max {
                Some(max) if max == expected_min => {
                    write!(
                        f,
                        "Expected exactly {} argument{}, but {} {} provided",
                        expected_min,
                        if *expected_min == 1 { "" } else { "s" },
                        provided,
                        if *provided == 1 { "was" } else { "were" }
                    )
                }
                Some(max) => {
                    write!(
                        f,
                        "Expected {}-{} arguments, but {} {} provided",
                        expected_min,
                        max,
                        provided,
                        if *provided == 1 { "was" } else { "were" }
                    )
                }
                None => {
                    write!(
                        f,
                        "Expected at least {} argument{}, but {} {} provided",
                        expected_min,
                        if *expected_min == 1 { "" } else { "s" },
                        provided,
                        if *provided == 1 { "was" } else { "were" }
                    )
                }
            },
            ApplyValidationError::LabelMismatch {
                param_index,
                expected,
                provided,
            } => match (expected, provided) {
                (Some(exp), Some(prov)) => {
                    write!(
                        f,
                        "Argument label mismatch at parameter {}: expected '{}', but '{}' was provided",
                        param_index + 1,
                        exp,
                        prov
                    )
                }
                (Some(exp), None) => {
                    write!(
                        f,
                        "Missing argument label at parameter {}: expected '{}', but no label was provided",
                        param_index + 1,
                        exp
                    )
                }
                (None, Some(prov)) => {
                    write!(
                        f,
                        "Unexpected argument label at parameter {}: '{}' was provided, but no label was expected",
                        param_index + 1,
                        prov
                    )
                }
                (None, None) => {
                    write!(f, "Label validation error at parameter {}", param_index + 1)
                }
            },
            ApplyValidationError::MissingRequiredParameter {
                param_index,
                param_name,
            } => {
                write!(
                    f,
                    "Missing required parameter '{}' at position {}",
                    param_name,
                    param_index + 1
                )
            }
            ApplyValidationError::ExtraArgument { arg_index } => {
                write!(
                    f,
                    "Extra argument at position {}: no corresponding parameter",
                    arg_index + 1
                )
            }
        }
    }
}

impl std::error::Error for ApplyValidationError {}
