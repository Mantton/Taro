use crate::resolver::Resolver;
use taroc_resolve_models::NameBinding;

pub trait ToNameBinding<'ctx> {
    fn to_name_binding(self, arenas: &Resolver<'ctx>) -> NameBinding<'ctx>;
}

impl<'ctx> ToNameBinding<'ctx> for NameBinding<'ctx> {
    fn to_name_binding(self, _: &Resolver<'ctx>) -> NameBinding<'ctx> {
        self
    }
}
