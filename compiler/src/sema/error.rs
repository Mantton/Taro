use crate::{compile::context::Gcx, sema::models::Ty, span::Spanned};

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
    TyMismatch(ExpectedFound<Ty<'ctx>>),
}

pub type SpannedError<'ctx> = Spanned<TypeError<'ctx>>;

impl<'ctx> TypeError<'ctx> {
    pub fn format(self, gcx: Gcx<'ctx>) -> String {
        match self {
            TypeError::TyMismatch(ef) => {
                format!(
                    "expected {}, found {}",
                    ef.expected.format(gcx),
                    ef.found.format(gcx)
                )
            }
        }
    }
}
