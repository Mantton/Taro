use crate::{check::context::func::FnCtx, ty::Ty};

#[derive(Debug, Clone, Copy)]
pub enum Expectation<'ctx> {
    None,
    HasType(Ty<'ctx>),
    CastableToType(Ty<'ctx>),
}

impl<'rcx, 'gcx> Expectation<'gcx> {
    pub fn to_option(self) -> Option<Ty<'gcx>> {
        match self {
            Expectation::None => None,
            Expectation::HasType(ty) | Expectation::CastableToType(ty) => Some(ty),
        }
    }

    pub fn only_has_type(self) -> Option<Ty<'gcx>> {
        match self {
            Expectation::HasType(ty) => Some(ty),
            _ => None,
        }
    }
}
