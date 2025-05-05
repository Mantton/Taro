use taroc_context::GlobalContext;
use taroc_hir::{DefinitionID, TypeAlias};
use taroc_resolve_models::{DefinitionContext, NameBinding, ParentScope};
use taroc_span::{FileID, Identifier, Span};

pub trait ToNameBinding<'ctx> {
    fn to_name_binding(self, arenas: GlobalContext<'ctx>) -> NameBinding<'ctx>;
}

impl<'ctx> ToNameBinding<'ctx> for NameBinding<'ctx> {
    fn to_name_binding(self, _: GlobalContext<'ctx>) -> NameBinding<'ctx> {
        self
    }
}

pub struct DefinitionExtensionData<'ctx> {
    pub ty: taroc_hir::Type,
    pub extension_context: DefinitionContext<'ctx>,
}

pub struct UnresolvedAlias<'ctx> {
    pub _name: Identifier,
    pub span: Span,
    pub alias: TypeAlias,
    pub parent: ParentScope<'ctx>,
}
