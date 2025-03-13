use taroc_resolve_models::NameBinding;

use super::arena::ResolverArena;

pub trait ToNameBinding<'arena> {
    fn to_name_binding(self, arenas: &'arena ResolverArena<'arena>) -> NameBinding<'arena>;
}

impl<'arena> ToNameBinding<'arena> for NameBinding<'arena> {
    fn to_name_binding(self, _: &'arena ResolverArena<'arena>) -> NameBinding<'arena> {
        self
    }
}
