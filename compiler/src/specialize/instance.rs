use crate::{hir::DefinitionID, sema::models::GenericArguments};

/// Represents a specialized instance of a generic function.
///
/// This is the unit of code generation: each `Instance` will result in
/// a distinct LLVM function being emitted via monomorphization.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Instance<'ctx> {
    /// The definition ID of the generic function.
    pub def_id: DefinitionID,
    /// The concrete type arguments for this instantiation.
    pub args: GenericArguments<'ctx>,
}

impl<'ctx> Instance<'ctx> {
    /// Create a new instance.
    pub fn new(def_id: DefinitionID, args: GenericArguments<'ctx>) -> Self {
        Self { def_id, args }
    }

    /// Get the definition ID of this instance.
    pub fn def_id(&self) -> DefinitionID {
        self.def_id
    }

    /// Get the generic arguments of this instance.
    pub fn args(&self) -> GenericArguments<'ctx> {
        self.args
    }
}
