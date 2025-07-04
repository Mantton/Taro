use taroc_resolve_models::NameBinding;
use taroc_sema::GlobalContext;

pub trait ToNameBinding<'ctx>: Clone {
    fn to_name_binding(self, gcx: GlobalContext<'ctx>) -> NameBinding<'ctx>;
}

impl<'ctx> ToNameBinding<'ctx> for NameBinding<'ctx> {
    fn to_name_binding(self, _: GlobalContext<'ctx>) -> NameBinding<'ctx> {
        self
    }
}
