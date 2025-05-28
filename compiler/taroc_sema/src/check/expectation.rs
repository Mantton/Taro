use crate::ty::Ty;

use super::context::func::FnCtx;

#[derive(Debug, Clone, Copy)]
pub enum Expectation<'ctx> {
    None,
    HasType(Ty<'ctx>),
    CastableToType(Ty<'ctx>),
}

impl<'rcx, 'gcx> Expectation<'gcx> {
    fn resolve(self, fcx: &FnCtx<'rcx, 'gcx>) -> Expectation<'gcx> {
        match self {
            Expectation::None => Expectation::None,
            Expectation::HasType(t) => Expectation::HasType(t), // TODO
            Expectation::CastableToType(t) => Expectation::CastableToType(t), // TODO
        }
    }

    pub fn to_option(self, fcx: &FnCtx<'rcx, 'gcx>) -> Option<Ty<'gcx>> {
        match self.resolve(fcx) {
            Expectation::None => None,
            Expectation::HasType(ty) | Expectation::CastableToType(ty) => Some(ty),
        }
    }

    pub fn only_has_type(self, fcx: &FnCtx<'rcx, 'gcx>) -> Option<Ty<'gcx>> {
        match self {
            Expectation::HasType(ty) => Some(ty),
            _ => None,
        }
    }
}
