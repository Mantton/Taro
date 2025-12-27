use crate::{hir::DefinitionID, mir::layout::Shape, sema::models::GenericArguments};

/// Represents a specialized instance of a generic function.
///
/// This is the unit of code generation: each `Instance` will result in
/// a distinct LLVM function being emitted.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Instance<'ctx> {
    /// Monomorphized instance with concrete types.
    /// Used when function has `@mono` attribute or by default.
    /// Example: `foo::<i32, String>`
    Concrete(DefinitionID, GenericArguments<'ctx>),

    /// Shape-specialized instance.
    /// Multiple concrete type combinations that share the same runtime layout
    /// will use the same compiled code.
    /// Example: `foo::<Shape(i32), Shape(ptr)>` used for both `(i32, *T)` and `(i32, *U)`
    Shape(DefinitionID, &'ctx [Shape]),
}

impl<'ctx> Instance<'ctx> {
    /// Get the definition ID of this instance.
    pub fn def_id(&self) -> DefinitionID {
        match self {
            Instance::Concrete(id, _) => *id,
            Instance::Shape(id, _) => *id,
        }
    }

    /// Returns true if this is a concrete (monomorphized) instance.
    pub fn is_concrete(&self) -> bool {
        matches!(self, Instance::Concrete(_, _))
    }

    /// Returns true if this is a shape-specialized instance.
    pub fn is_shape(&self) -> bool {
        matches!(self, Instance::Shape(_, _))
    }
}
