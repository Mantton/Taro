use crate::{
    hir::{self, DefinitionID, Resolution},
    sema::{
        models::{GenericArguments, Ty},
        tycheck::solve::{Adjustment, InterfaceCallInfo},
    },
};
use rustc_hash::FxHashMap;

#[derive(Debug, Default)]
pub struct TypeCheckResults<'ctx> {
    node_tys: FxHashMap<hir::NodeID, Ty<'ctx>>,
    node_adjustments: FxHashMap<hir::NodeID, Vec<Adjustment<'ctx>>>,
    interface_calls: FxHashMap<hir::NodeID, InterfaceCallInfo>,
    field_indices: FxHashMap<hir::NodeID, usize>,
    overload_sources: FxHashMap<hir::NodeID, DefinitionID>,
    value_resolutions: FxHashMap<hir::NodeID, Resolution>,
    instantiations: FxHashMap<hir::NodeID, GenericArguments<'ctx>>,
    /// Maps pattern NodeIDs to their inferred binding modes (for Binding patterns)
    binding_modes: FxHashMap<hir::NodeID, hir::BindingMode>,
}

impl<'ctx> TypeCheckResults<'ctx> {
    pub fn extend_from(&mut self, mut other: TypeCheckResults<'ctx>) {
        self.node_tys.extend(other.node_tys.drain());
        self.node_adjustments.extend(other.node_adjustments.drain());
        self.interface_calls.extend(other.interface_calls.drain());
        self.field_indices.extend(other.field_indices.drain());
        self.overload_sources.extend(other.overload_sources.drain());
        self.value_resolutions
            .extend(other.value_resolutions.drain());
        self.instantiations.extend(other.instantiations.drain());
        self.binding_modes.extend(other.binding_modes.drain());
    }

    pub fn record_node_type(&mut self, id: hir::NodeID, ty: Ty<'ctx>) {
        self.node_tys.insert(id, ty);
    }

    pub fn record_node_adjustments(&mut self, id: hir::NodeID, adjustments: Vec<Adjustment<'ctx>>) {
        if adjustments.is_empty() {
            return;
        }
        self.node_adjustments.insert(id, adjustments);
    }

    pub fn record_interface_call(&mut self, id: hir::NodeID, info: InterfaceCallInfo) {
        self.interface_calls.insert(id, info);
    }

    pub fn record_field_index(&mut self, id: hir::NodeID, index: usize) {
        self.field_indices.insert(id, index);
    }

    pub fn record_overload_source(&mut self, id: hir::NodeID, def_id: DefinitionID) {
        self.overload_sources.insert(id, def_id);
    }

    pub fn record_value_resolution(&mut self, id: hir::NodeID, resolution: Resolution) {
        self.value_resolutions.insert(id, resolution);
    }

    pub fn record_instantiation(&mut self, id: hir::NodeID, args: GenericArguments<'ctx>) {
        self.instantiations.insert(id, args);
    }

    #[track_caller]
    pub fn node_type(&self, id: hir::NodeID) -> Ty<'ctx> {
        *self.node_tys.get(&id).expect("type of node")
    }

    pub fn node_adjustments(&self, id: hir::NodeID) -> Option<&[Adjustment<'ctx>]> {
        self.node_adjustments.get(&id).map(|v| v.as_slice())
    }

    pub fn interface_call(&self, id: hir::NodeID) -> Option<InterfaceCallInfo> {
        self.interface_calls.get(&id).copied()
    }

    pub fn field_index(&self, id: hir::NodeID) -> Option<usize> {
        self.field_indices.get(&id).copied()
    }

    pub fn overload_source(&self, id: hir::NodeID) -> Option<DefinitionID> {
        self.overload_sources.get(&id).copied()
    }

    pub fn value_resolution(&self, id: hir::NodeID) -> Option<Resolution> {
        self.value_resolutions.get(&id).cloned()
    }

    pub fn instantiation(&self, id: hir::NodeID) -> Option<GenericArguments<'ctx>> {
        self.instantiations.get(&id).cloned()
    }

    pub fn record_binding_mode(&mut self, id: hir::NodeID, mode: hir::BindingMode) {
        self.binding_modes.insert(id, mode);
    }

    pub fn binding_mode(&self, id: hir::NodeID) -> Option<hir::BindingMode> {
        self.binding_modes.get(&id).copied()
    }
}
