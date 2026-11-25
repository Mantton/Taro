use crate::{
    hir::{self, DefinitionID, Resolution},
    sema::{
        models::{GenericArguments, Ty},
        tycheck::solve::{Adjustment, InterfaceCallInfo, ResolvedField, ResolvedPropertyRead},
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
    /// Inclusive scalar bounds after endpoint types and constant names are resolved.
    pub(crate) pattern_ranges: FxHashMap<hir::NodeID, std::ops::RangeInclusive<i128>>,
    /// `super.init` produces a private base payload, not a published object.
    pub(crate) base_initializer_calls: FxHashSet<hir::NodeID>,
    pub(crate) self_initializer_calls: FxHashSet<hir::NodeID>,
    pub(crate) dynamic_self_calls: FxHashSet<hir::NodeID>,
    pub(crate) dynamic_self_contexts: FxHashMap<DefinitionID, DynamicSelfContext<'ctx>>,
    bound_methods: FxHashMap<hir::NodeID, BoundMethod>,
    pub(crate) lazy_arguments: FxHashMap<hir::NodeID, hir::Expression>,
    pub(crate) selected_brackets: FxHashMap<hir::NodeID, hir::Expression>,
    pub(crate) native_indices: FxHashMap<hir::NodeID, NativeIndex<'ctx>>,
    /// Selected call syntax lowered to a direct specialized method call or
    /// a positional struct aggregate before THIR construction.
    pub(crate) elaborated_calls: FxHashMap<hir::NodeID, hir::Expression>,
    /// Separate coercion sites for RHS tuple projections. Destination nodes
    /// retain their own reference/place adjustments.
    pub(crate) tuple_assignment_values: FxHashMap<hir::NodeID, hir::NodeID>,
    /// Compiler-generated bound-method bodies preserve the selected signature,
    /// including explicit generics absent from value parameters/results.
    pub(crate) selected_method_calls:
        FxHashMap<hir::NodeID, (DefinitionID, GenericArguments<'ctx>)>,
    pub(crate) missing_member_receivers: FxHashMap<hir::NodeID, bool>,
    node_tys: FxHashMap<hir::NodeID, Ty<'ctx>>,
    node_adjustments: FxHashMap<hir::NodeID, Vec<Adjustment<'ctx>>>,
    interface_calls: FxHashMap<hir::NodeID, InterfaceCallInfo>,
    fields: FxHashMap<hir::NodeID, ResolvedField>,
    property_reads: FxHashMap<hir::NodeID, ResolvedPropertyRead>,
    overload_sources: FxHashMap<hir::NodeID, DefinitionID>,
    value_resolutions: FxHashMap<hir::NodeID, Resolution>,
    instantiations: FxHashMap<hir::NodeID, GenericArguments<'ctx>>,
    async_calls: FxHashSet<hir::NodeID>,
    async_var_bindings: FxHashSet<hir::NodeID>,
    result_propagation_conversions: FxHashMap<hir::NodeID, ResultPropagationConversion<'ctx>>,
    pub(crate) sync_generators: FxHashMap<DefinitionID, Ty<'ctx>>,
    pub(crate) async_generators: FxHashMap<DefinitionID, Ty<'ctx>>,
    pub(crate) comptime_expansions: FxHashMap<hir::NodeID, Vec<hir::Block>>,
    pub(crate) type_name_literals: FxHashMap<hir::NodeID, crate::span::Symbol>,
    pub(crate) for_loop_direct_iterators: FxHashSet<hir::NodeID>,
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
        self.pattern_ranges.extend(other.pattern_ranges.drain());
        self.bound_methods.extend(other.bound_methods.drain());
        self.lazy_arguments.extend(other.lazy_arguments.drain());
        self.selected_brackets
            .extend(other.selected_brackets.drain());
        self.native_indices.extend(other.native_indices.drain());
        self.elaborated_calls
            .extend(other.elaborated_calls.drain());
        self.tuple_assignment_values
            .extend(other.tuple_assignment_values.drain());
        self.selected_method_calls
            .extend(other.selected_method_calls.drain());
        self.missing_member_receivers
            .extend(other.missing_member_receivers.drain());
        self.node_tys.extend(other.node_tys.drain());
        self.node_adjustments.extend(other.node_adjustments.drain());
        self.interface_calls.extend(other.interface_calls.drain());
        self.fields.extend(other.fields.drain());
        self.property_reads.extend(other.property_reads.drain());
        self.overload_sources.extend(other.overload_sources.drain());
        self.value_resolutions
            .extend(other.value_resolutions.drain());
        self.instantiations.extend(other.instantiations.drain());
        self.async_calls.extend(other.async_calls.drain());
        self.async_var_bindings
            .extend(other.async_var_bindings.drain());
        self.result_propagation_conversions
            .extend(other.result_propagation_conversions.drain());
        self.sync_generators.extend(other.sync_generators.drain());
        self.async_generators.extend(other.async_generators.drain());
        self.comptime_expansions
            .extend(other.comptime_expansions.drain());
        self.type_name_literals
            .extend(other.type_name_literals.drain());
        self.for_loop_direct_iterators
            .extend(other.for_loop_direct_iterators.drain());
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

    pub(crate) fn record_field(&mut self, id: hir::NodeID, field: ResolvedField) {
        self.fields.insert(id, field);
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

    pub fn record_async_var_binding(&mut self, id: hir::NodeID) {
        self.async_var_bindings.insert(id);
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
        self.fields.get(&id).map(|field| field.index)
    }

    pub(crate) fn field_definition(&self, id: hir::NodeID) -> Option<DefinitionID> {
        self.fields.get(&id)?.definition
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

    pub fn is_async_var_binding(&self, id: hir::NodeID) -> bool {
        self.async_var_bindings.contains(&id)
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
    pub kind: ResultPropagationConversionKind<'ctx>,
    pub target_ty: Ty<'ctx>,
}

/// How `expr!` turns the operand's error into the enclosing function's error.
#[derive(Debug, Clone, Copy)]
pub enum ResultPropagationConversionKind<'ctx> {
    /// Call `TargetE.from(error)` through the `From[E]` conformance.
    From {
        method_id: DefinitionID,
        generic_args: GenericArguments<'ctx>,
    },
    /// Box a concrete error into the existential target, as an ordinary
    /// coercion to that existential would.
    BoxExistential {
        interfaces: &'ctx [crate::sema::models::InterfaceReference<'ctx>],
    },
}

/// A method value reuses ordinary closure lowering, with its synthetic receiver
/// capture initialized from the actual source expression exactly once.
#[derive(Debug, Clone)]
pub struct BoundMethod {
    pub closure: hir::ClosureExpr,
    pub receiver: hir::Expression,
}
