use crate::{
    hir::{self, DefinitionID, Resolution},
    sema::{
        models::{GenericArguments, Ty},
        tycheck::solve::{Adjustment, InterfaceCallInfo, ResolvedPropertyRead},
    },
};
use rustc_hash::{FxHashMap, FxHashSet};

/// Reserved before THIR allocates any other synthetic local in this method.
pub(crate) const DYNAMIC_SELF_CONTEXT_LOCAL_RAW: u32 = u32::MAX;

#[derive(Debug, Clone, Copy)]
pub(crate) struct DynamicSelfContext<'ctx> {
    pub receiver: hir::NodeID,
    pub receiver_ty: Ty<'ctx>,
    pub class: Ty<'ctx>,
}

/// Each capability keeps its own declaration environment. Partial class
/// overrides may inherit an accessor from a differently parameterized ancestor.
#[derive(Debug, Clone, Copy)]
pub(crate) struct NativeAccessor<'ctx> {
    pub source: DefinitionID,
    pub arguments: GenericArguments<'ctx>,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct NativeIndex<'ctx> {
    pub getter: NativeAccessor<'ctx>,
    pub setter: Option<NativeAccessor<'ctx>>,
    pub address: Option<NativeAccessor<'ctx>>,
    pub use_address: bool,
}

#[derive(Debug, Default, Clone)]
pub struct TypeCheckResults<'ctx> {
    /// `super.init` produces a private base payload, not a published object.
    pub(crate) base_initializer_calls: FxHashSet<hir::NodeID>,
    pub(crate) self_initializer_calls: FxHashSet<hir::NodeID>,
    pub(crate) dynamic_self_calls: FxHashSet<hir::NodeID>,
    pub(crate) dynamic_self_contexts: FxHashMap<DefinitionID, DynamicSelfContext<'ctx>>,
    bound_methods: FxHashMap<hir::NodeID, BoundMethod>,
    pub(crate) selected_brackets: FxHashMap<hir::NodeID, hir::Expression>,
    pub(crate) native_indices: FxHashMap<hir::NodeID, NativeIndex<'ctx>>,
    /// Immediate specialized calls keep ordinary method receiver semantics;
    /// they do not create a temporary bound closure that owns result debts.
    pub(crate) elaborated_method_calls: FxHashMap<hir::NodeID, hir::Expression>,
    /// Compiler-generated bound-method bodies preserve the selected signature,
    /// including explicit generics absent from value parameters/results.
    pub(crate) selected_method_calls:
        FxHashMap<hir::NodeID, (DefinitionID, GenericArguments<'ctx>)>,
    node_tys: FxHashMap<hir::NodeID, Ty<'ctx>>,
    node_adjustments: FxHashMap<hir::NodeID, Vec<Adjustment<'ctx>>>,
    interface_calls: FxHashMap<hir::NodeID, InterfaceCallInfo>,
    field_indices: FxHashMap<hir::NodeID, usize>,
    property_reads: FxHashMap<hir::NodeID, ResolvedPropertyRead>,
    overload_sources: FxHashMap<hir::NodeID, DefinitionID>,
    value_resolutions: FxHashMap<hir::NodeID, Resolution>,
    instantiations: FxHashMap<hir::NodeID, GenericArguments<'ctx>>,
    async_calls: FxHashSet<hir::NodeID>,
    result_propagation_conversions: FxHashMap<hir::NodeID, ResultPropagationConversion<'ctx>>,
}

impl<'ctx> TypeCheckResults<'ctx> {
    pub fn extend_from(&mut self, mut other: TypeCheckResults<'ctx>) {
        self.base_initializer_calls
            .extend(other.base_initializer_calls.drain());
        self.self_initializer_calls
            .extend(other.self_initializer_calls.drain());
        self.dynamic_self_calls
            .extend(other.dynamic_self_calls.drain());
        self.dynamic_self_contexts
            .extend(other.dynamic_self_contexts.drain());
        self.bound_methods.extend(other.bound_methods.drain());
        self.selected_brackets
            .extend(other.selected_brackets.drain());
        self.native_indices.extend(other.native_indices.drain());
        self.elaborated_method_calls
            .extend(other.elaborated_method_calls.drain());
        self.selected_method_calls
            .extend(other.selected_method_calls.drain());
        self.node_tys.extend(other.node_tys.drain());
        self.node_adjustments.extend(other.node_adjustments.drain());
        self.interface_calls.extend(other.interface_calls.drain());
        self.field_indices.extend(other.field_indices.drain());
        self.property_reads.extend(other.property_reads.drain());
        self.overload_sources.extend(other.overload_sources.drain());
        self.value_resolutions
            .extend(other.value_resolutions.drain());
        self.instantiations.extend(other.instantiations.drain());
        self.async_calls.extend(other.async_calls.drain());
        self.result_propagation_conversions
            .extend(other.result_propagation_conversions.drain());
    }

    pub fn record_bound_method(&mut self, id: hir::NodeID, method: BoundMethod) {
        self.bound_methods.insert(id, method);
    }

    pub fn bound_method(&self, id: hir::NodeID) -> Option<&BoundMethod> {
        self.bound_methods.get(&id)
    }

    pub fn bound_method_closure(&self, id: DefinitionID) -> Option<&BoundMethod> {
        self.bound_methods
            .values()
            .find(|method| method.closure.def_id == id)
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

    pub fn record_property_read(&mut self, id: hir::NodeID, info: ResolvedPropertyRead) {
        self.property_reads.insert(id, info);
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

    pub fn record_async_call(&mut self, id: hir::NodeID) {
        self.async_calls.insert(id);
    }

    pub fn record_result_propagation_conversion(
        &mut self,
        id: hir::NodeID,
        conversion: ResultPropagationConversion<'ctx>,
    ) {
        self.result_propagation_conversions.insert(id, conversion);
    }

    #[track_caller]
    pub fn node_type(&self, id: hir::NodeID) -> Ty<'ctx> {
        *self.node_tys.get(&id).expect("type of node")
    }

    pub fn try_node_type(&self, id: hir::NodeID) -> Option<Ty<'ctx>> {
        self.node_tys.get(&id).cloned()
    }

    pub fn node_adjustments(&self, id: hir::NodeID) -> Option<&[Adjustment<'ctx>]> {
        self.node_adjustments.get(&id).map(|v| v.as_slice())
    }

    pub fn interface_call(&self, id: hir::NodeID) -> Option<InterfaceCallInfo> {
        self.interface_calls.get(&id).cloned()
    }

    pub fn field_index(&self, id: hir::NodeID) -> Option<usize> {
        self.field_indices.get(&id).cloned()
    }

    pub fn property_read(&self, id: hir::NodeID) -> Option<ResolvedPropertyRead> {
        self.property_reads.get(&id).copied()
    }

    pub fn overload_source(&self, id: hir::NodeID) -> Option<DefinitionID> {
        self.overload_sources.get(&id).cloned()
    }

    pub fn value_resolution(&self, id: hir::NodeID) -> Option<Resolution> {
        self.value_resolutions.get(&id).cloned()
    }

    pub fn instantiation(&self, id: hir::NodeID) -> Option<GenericArguments<'ctx>> {
        self.instantiations.get(&id).cloned()
    }

    pub fn is_async_call(&self, id: hir::NodeID) -> bool {
        self.async_calls.contains(&id)
    }

    pub fn result_propagation_conversion(
        &self,
        id: hir::NodeID,
    ) -> Option<ResultPropagationConversion<'ctx>> {
        self.result_propagation_conversions.get(&id).copied()
    }
}

#[derive(Debug, Clone, Copy)]
pub struct ResultPropagationConversion<'ctx> {
    pub method_id: DefinitionID,
    pub generic_args: GenericArguments<'ctx>,
    pub target_ty: Ty<'ctx>,
}

/// A method value reuses ordinary closure lowering, with its synthetic receiver
/// capture initialized from the actual source expression exactly once.
#[derive(Debug, Clone)]
pub struct BoundMethod {
    pub closure: hir::ClosureExpr,
    pub receiver: hir::Expression,
}
