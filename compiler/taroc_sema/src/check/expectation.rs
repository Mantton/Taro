use crate::{check::context::func::FnCtx, ty::Ty};

#[derive(Debug, Clone, Copy)]
pub enum Expectation<'ctx> {
    None,
    HasType(Ty<'ctx>),
    CastableToType(Ty<'ctx>),
}

impl<'rcx, 'gcx> Expectation<'gcx> {
    pub fn resolve(self, fcx: &FnCtx<'rcx, 'gcx>) -> Expectation<'gcx> {
        match self {
            Expectation::None => Expectation::None,
            Expectation::HasType(ty) => Expectation::HasType(fcx.resolve_vars_if_possible(ty)),
            Expectation::CastableToType(ty) => {
                Expectation::CastableToType(fcx.resolve_vars_if_possible(ty))
            }
        }
    }
    pub fn to_option(self, fcx: &FnCtx<'rcx, 'gcx>) -> Option<Ty<'gcx>> {
        match self.resolve(fcx) {
            Expectation::None => None,
            Expectation::HasType(ty) | Expectation::CastableToType(ty) => Some(ty),
        }
    }

    pub fn only_has_type(self, fcx: &FnCtx<'rcx, 'gcx>) -> Option<Ty<'gcx>> {
        match self.resolve(fcx) {
            Expectation::HasType(ty) => Some(ty),
            _ => None,
        }
    }
}
