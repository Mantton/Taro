use std::marker::PhantomData;

use bumpalo::Bump;
use taroc_data_structures::Interned;
use taroc_resolve_models::{
    DefContextData, DefContextKind, DefinitionContext, ExternalDefUsageData,
    ExternalDefinitionUsage, NameBinding, NameBindingData,
};
use taroc_span::Span;

pub struct ResolverArena<'arena> {
    bump: Bump,
    _values: PhantomData<DefinitionContext<'arena>>,
}

impl<'arena> ResolverArena<'arena> {
    pub fn new() -> ResolverArena<'arena> {
        ResolverArena {
            bump: Bump::new(),
            _values: PhantomData::default(),
        }
    }

    pub fn new_context(
        &'arena self,
        parent: Option<DefinitionContext<'arena>>,
        kind: DefContextKind,
        span: Span,
    ) -> DefinitionContext<'arena> {
        let data = DefContextData {
            parent,
            kind,
            span,
            resolutions: Default::default(),
            glob_exports: Default::default(),
            glob_imports: Default::default(),
        };
        // Allocate the context data in the bump arena.
        let allocated = self.bump.alloc(data);
        let p = Interned::new_unchecked(allocated);
        DefinitionContext::new(p)
    }

    pub fn alloc_external_usage(
        &'arena self,
        data: ExternalDefUsageData<'arena>,
    ) -> ExternalDefinitionUsage<'arena> {
        let allocated = self.bump.alloc(data);
        Interned::new_unchecked(allocated)
        // In your actual code you might wrap this Interned pointer into a newtype
        // or convert it appropriately.
    }

    pub fn alloc_binding(&'arena self, data: NameBindingData<'arena>) -> NameBinding<'arena> {
        let allocated = self.bump.alloc(data);
        Interned::new_unchecked(allocated)
        // Similarly, wrap or convert as needed.
    }

    pub fn alloc_slice_copy<T>(&self, src: &[T]) -> &mut [T]
    where
        T: Copy,
    {
        self.bump.alloc_slice_copy(&src)
    }
}
