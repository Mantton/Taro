use crate::resolver::Resolver;
use taroc_data_structures::Interned;
use taroc_resolve_models::{
    DefContextData, DefContextKind, DefinitionContext, ExternalDefUsageData,
    ExternalDefinitionUsage, NameBinding, NameBindingData,
};
use taroc_sema::GlobalContext;
use taroc_span::Span;

pub fn alloc_context<'ctx>(
    context: GlobalContext<'ctx>,
    parent: Option<DefinitionContext<'ctx>>,
    kind: DefContextKind,
    span: Span,
) -> DefinitionContext<'ctx> {
    let data = DefContextData {
        parent,
        kind,
        span,
        namespace: Default::default(),
        glob_exports: Default::default(),
        glob_imports: Default::default(),
        explicit_imports: Default::default(),
        explicit_exports: Default::default(),
    };
    // Allocate the context data in the bump arena.
    let allocated = context.store.interners.arenas.resolve.alloc(data);
    let p = Interned::new_unchecked(allocated);
    DefinitionContext::new(p)
}

pub fn alloc_binding<'ctx>(
    context: GlobalContext<'ctx>,
    data: NameBindingData<'ctx>,
) -> NameBinding<'ctx> {
    let allocated = context.store.interners.arenas.resolve.alloc(data);
    Interned::new_unchecked(allocated)
}

impl<'ctx> Resolver<'ctx> {
    pub fn alloc_external_usage(
        &self,
        data: ExternalDefUsageData<'ctx>,
    ) -> ExternalDefinitionUsage<'ctx> {
        let allocated = self.gcx.store.interners.arenas.resolve.alloc(data);
        Interned::new_unchecked(allocated)
    }

    pub fn alloc_slice_copy<T>(&self, src: &[T]) -> &'ctx mut [T]
    where
        T: Copy,
    {
        self.gcx
            .store
            .interners
            .arenas
            .resolve
            .alloc_slice_copy(&src)
    }
}
