use crate::resolver::Resolver;
use taroc_data_structures::Interned;
use taroc_resolve_models::{
    DefContextData, DefContextKind, DefinitionContext, ExternalDefUsageData,
    ExternalDefinitionUsage, NameBinding, NameBindingData,
};
use taroc_span::Span;

impl<'ctx> Resolver<'ctx> {
    pub fn alloc_context(
        &self,
        parent: Option<DefinitionContext<'ctx>>,
        kind: DefContextKind,
        span: Span,
    ) -> DefinitionContext<'ctx> {
        let data = DefContextData {
            parent,
            kind,
            span,
            resolutions: Default::default(),
            glob_exports: Default::default(),
            glob_imports: Default::default(),
        };
        // Allocate the context data in the bump arena.
        let allocated = self
            .session
            .context
            .store
            .interners
            .arenas
            .resolve
            .alloc(data);
        let p = Interned::new_unchecked(allocated);
        DefinitionContext::new(p)
    }

    pub fn alloc_external_usage(
        &self,
        data: ExternalDefUsageData<'ctx>,
    ) -> ExternalDefinitionUsage<'ctx> {
        let allocated = self
            .session
            .context
            .store
            .interners
            .arenas
            .resolve
            .alloc(data);
        Interned::new_unchecked(allocated)
        // In your actual code you might wrap this Interned pointer into a newtype
        // or convert it appropriately.
    }

    pub fn alloc_binding(&self, data: NameBindingData<'ctx>) -> NameBinding<'ctx> {
        let allocated = self
            .session
            .context
            .store
            .interners
            .arenas
            .resolve
            .alloc(data);
        Interned::new_unchecked(allocated)
        // Similarly, wrap or convert as needed.
    }

    pub fn alloc_slice_copy<T>(&self, src: &[T]) -> &'ctx mut [T]
    where
        T: Copy,
    {
        self.session
            .context
            .store
            .interners
            .arenas
            .resolve
            .alloc_slice_copy(&src)
    }
}
