use crate::resolver::Resolver;
use taroc_hir::{DefinitionID, TypeAlias};
use taroc_resolve_models::{DefinitionContext, NameBinding};
use taroc_span::{FileID, Identifier, Span, Symbol};

pub trait ToNameBinding<'ctx> {
    fn to_name_binding(self, arenas: &Resolver<'ctx>) -> NameBinding<'ctx>;
}

impl<'ctx> ToNameBinding<'ctx> for NameBinding<'ctx> {
    fn to_name_binding(self, _: &Resolver<'ctx>) -> NameBinding<'ctx> {
        self
    }
}

pub struct DefinitionExtensionData<'ctx> {
    pub path: taroc_hir::TaggedPath,
    pub extension_context: DefinitionContext<'ctx>,
    pub module_id: DefinitionID,
    pub file_id: FileID,
}

#[derive(Clone, Copy)]
pub struct ParentContext {
    pub module: DefinitionID,
    pub file: FileID,
}

pub struct UnresolvedAlias<'ctx> {
    pub name: Identifier,
    pub span: Span,
    pub alias: TypeAlias,
    pub parent: DefinitionContext<'ctx>,
}
