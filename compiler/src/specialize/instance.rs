use crate::{
    hir::DefinitionID,
    sema::models::GenericArguments,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VirtualInstance {
    pub method_id: DefinitionID,
    pub method_interface: DefinitionID,
    pub slot: usize,
    pub table_index: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InstanceKind {
    /// A user-defined callable item.
    Item(DefinitionID),
    /// Dynamic dispatch through an existential witness table.
    Virtual(VirtualInstance),
}

/// Represents a resolved call target.
///
/// `InstanceKind::Item` is the unit of code generation; `InstanceKind::Virtual`
/// represents an existential dispatch that does not produce its own function.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Instance<'ctx> {
    /// The specific callable to invoke (direct or virtual).
    pub kind: InstanceKind,
    /// The concrete type arguments for this instantiation.
    pub args: GenericArguments<'ctx>,
}

impl<'ctx> Instance<'ctx> {
    /// Create a direct (monomorphized) instance.
    pub fn item(def_id: DefinitionID, args: GenericArguments<'ctx>) -> Self {
        Self {
            kind: InstanceKind::Item(def_id),
            args,
        }
    }

    /// Create a virtual (existential) instance.
    pub fn virtual_call(
        method_id: DefinitionID,
        method_interface: DefinitionID,
        slot: usize,
        table_index: usize,
        args: GenericArguments<'ctx>,
    ) -> Self {
        Self {
            kind: InstanceKind::Virtual(VirtualInstance {
                method_id,
                method_interface,
                slot,
                table_index,
            }),
            args,
        }
    }

    /// Get the definition ID of this instance.
    pub fn def_id(&self) -> DefinitionID {
        match self.kind {
            InstanceKind::Item(def_id) => def_id,
            InstanceKind::Virtual(virtual_call) => virtual_call.method_id,
        }
    }

    /// Get the generic arguments of this instance.
    pub fn args(&self) -> GenericArguments<'ctx> {
        self.args
    }

    pub fn kind(&self) -> InstanceKind {
        self.kind
    }

    pub fn is_item(&self) -> bool {
        matches!(self.kind, InstanceKind::Item(_))
    }
}
