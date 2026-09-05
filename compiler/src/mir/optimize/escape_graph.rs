//! Instance-aware interprocedural escape analysis.
//!
//! Shared MIR remains generic. This module resolves calls with the concrete
//! substitutions of a codegen [`Instance`], computes summaries over the
//! resulting direct-call graph, and records one conservative placement bitmap
//! on the instance-local MIR clone.

use crate::{
    codegen::mangle::mangle_instance,
    compile::context::{Gcx, GlobalContext},
    error::{CompileResult, ReportedError},
    hir::Abi,
    mir::{
        BasicBlockId, Body, CallUnwindAction, ConstantKind, InstanceEscapeSummary, LocalId,
        LocalKind, Operand, ParamEscapeSummary, Place, PlaceElem, Rvalue, StatementKind,
        TerminatorKind,
    },
    runtime_abi::{
        RuntimeParamEscapeEffect, intrinsic_param_escape_effect, intrinsic_return_deref,
        param_escape_effect_for_symbol,
    },
    sema::{
        models::{
            AdtKind, CaptureKind, EnumVariantKind, GenericArgument, GenericArguments, Ty, TyKind,
        },
        tycheck::utils::instantiate::{instantiate_const_with_args, instantiate_ty_with_args},
    },
    specialize::{Instance, InstanceKind, resolve_instance},
};
use index_vec::IndexVec;
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::VecDeque;

const MAX_DEREF: i16 = u8::MAX as i16;

/// Compute and apply the single placement decision for a concrete codegen
/// instance. The transformation helpers live below the graph so allocation
/// promotion and address-taken-local heapification cannot disagree about
/// provenance.
pub fn apply_instance_placement<'ctx>(
    gcx: Gcx<'ctx>,
    instance: Instance<'ctx>,
    body: &mut Body<'ctx>,
) -> CompileResult<()> {
    ensure_instance_summaries(gcx, instance)?;
    let placement = {
        let summaries = gcx.store.instance_escape_summaries.borrow();
        EscapeGraph::build(
            gcx,
            body,
            AnalysisMode::Instance {
                caller: instance,
                summaries: &summaries,
            },
        )?
        .placement()
    };

    body.escape_locals.clear();
    body.escape_locals.resize(body.locals.len(), false);
    for local in &placement.heap_locals {
        body.escape_locals[local.index()] = true;
    }

    // These are temporarily delegated to the established rewrites. The graph
    // owns both decisions; the helpers merely materialize them.
    allocation_rewrite::promote_allocation_sites(
        gcx,
        body,
        &placement.escaping_alloc_sites,
        &placement.allocation_keepalive_blocks,
    )?;
    heapify_rewrite::apply_heapified_locals(gcx, body)?;
    Ok(())
}

/// Conservative source-async bridge used before coroutine frame construction.
/// Only address-taken local placement is applied here. Synthesized constructor,
/// poll, and drop bodies later take the ordinary concrete-instance path.
pub fn apply_async_bridge<'ctx>(gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
    let placement = EscapeGraph::build(gcx, body, AnalysisMode::AsyncBridge)?.placement();
    body.escape_locals.clear();
    body.escape_locals.resize(body.locals.len(), false);
    for local in placement.heap_locals {
        body.escape_locals[local.index()] = true;
    }
    heapify_rewrite::apply_heapified_locals(gcx, body)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct AllocationSite {
    pub block: BasicBlockId,
    pub statement: usize,
}

#[derive(Debug, Default)]
struct EscapePlacement {
    heap_locals: FxHashSet<LocalId>,
    escaping_alloc_sites: FxHashSet<AllocationSite>,
    allocation_keepalive_blocks: FxHashMap<AllocationSite, FxHashSet<BasicBlockId>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum NodeKind {
    Heap,
    Return,
    /// The storage occupied by a MIR local, as distinct from its current value.
    Storage(LocalId),
    /// Initial value of one formal parameter.
    Parameter(LocalId),
    /// Value produced by one statement or terminator definition.
    Value,
    /// Storage allocated by one explicit managed allocation statement.
    Allocation(AllocationSite),
}

#[derive(Clone, Copy, Debug)]
struct Edge {
    target: usize,
    deref: i16,
}

struct EscapeGraph {
    nodes: Vec<NodeKind>,
    edges: Vec<Vec<Edge>>,
    heap: usize,
    returned: usize,
    storage: Vec<usize>,
    parameter_nodes: Vec<usize>,
    statement_values: FxHashMap<(BasicBlockId, usize), usize>,
    terminator_values: FxHashMap<BasicBlockId, usize>,
    allocation_nodes: FxHashMap<AllocationSite, usize>,
    overlapping_allocations: FxHashSet<AllocationSite>,
    allocation_live_blocks: FxHashMap<AllocationSite, FxHashSet<BasicBlockId>>,
    saturated: bool,
}

type FlowState = Vec<FxHashSet<usize>>;

#[derive(Clone, Copy)]
enum AnalysisMode<'a, 'ctx> {
    Instance {
        caller: Instance<'ctx>,
        summaries: &'a FxHashMap<Instance<'ctx>, InstanceEscapeSummary>,
    },
    AsyncBridge,
    #[cfg(test)]
    FixedEffects {
        params: &'a [ParamEscapeSummary],
    },
}

impl EscapeGraph {
    fn build<'a, 'ctx>(
        gcx: Gcx<'ctx>,
        body: &Body<'ctx>,
        mode: AnalysisMode<'a, 'ctx>,
    ) -> CompileResult<Self> {
        let mut graph = Self {
            nodes: Vec::new(),
            edges: Vec::new(),
            heap: 0,
            returned: 0,
            storage: Vec::with_capacity(body.locals.len()),
            parameter_nodes: Vec::new(),
            statement_values: FxHashMap::default(),
            terminator_values: FxHashMap::default(),
            allocation_nodes: FxHashMap::default(),
            overlapping_allocations: FxHashSet::default(),
            allocation_live_blocks: FxHashMap::default(),
            saturated: false,
        };
        graph.heap = graph.push_node(NodeKind::Heap);
        graph.returned = graph.push_node(NodeKind::Return);
        for local in body.locals.indices() {
            let node = graph.push_node(NodeKind::Storage(local));
            graph.storage.push(node);
        }

        let mut entry_state = empty_flow_state(body.locals.len());
        for (local, declaration) in body.locals.iter_enumerated() {
            if declaration.kind == LocalKind::Param {
                let node = graph.push_node(NodeKind::Parameter(local));
                graph.parameter_nodes.push(node);
                entry_state[local.index()].insert(node);
                graph.add_edge(graph.storage(local), node, 1);
            }
        }

        for (block, data) in body.basic_blocks.iter_enumerated() {
            for (statement, value) in data.statements.iter().enumerate() {
                if let StatementKind::Assign(destination, rvalue) = &value.kind {
                    if !place_has_deref(destination) {
                        let node = graph.push_node(NodeKind::Value);
                        graph.statement_values.insert((block, statement), node);
                    }
                    if matches!(rvalue, Rvalue::Alloc { .. }) {
                        let site = AllocationSite { block, statement };
                        let node = graph.push_node(NodeKind::Allocation(site));
                        graph.allocation_nodes.insert(site, node);
                    }
                }
            }
            if let Some(terminator) = &data.terminator {
                let destination = match &terminator.kind {
                    TerminatorKind::Call { destination, .. } => Some(destination),
                    TerminatorKind::Yield { resume_arg, .. } => Some(resume_arg),
                    _ => None,
                };
                if destination.is_some_and(|place| !place_has_deref(place)) {
                    let node = graph.push_node(NodeKind::Value);
                    graph.terminator_values.insert(block, node);
                }
            }
        }

        let (in_states, reachable) = graph.compute_flow_states(body, entry_state);
        graph.add_flow_edges(gcx, body, mode, &in_states, &reachable)?;
        graph.overlapping_allocations = graph.find_overlapping_allocations(body, &in_states);
        graph.allocation_live_blocks = graph.find_allocation_live_blocks(body, &in_states);
        Ok(graph)
    }

    fn push_node(&mut self, kind: NodeKind) -> usize {
        let index = self.nodes.len();
        self.nodes.push(kind);
        self.edges.push(Vec::new());
        index
    }

    fn storage(&self, local: LocalId) -> usize {
        self.storage[local.index()]
    }

    fn add_edge(&mut self, destination: usize, source: usize, deref: i16) {
        if !self.edges[destination]
            .iter()
            .any(|edge| edge.target == source && edge.deref == deref)
        {
            self.edges[destination].push(Edge {
                target: source,
                deref,
            });
        }
    }

    fn place_deref(place: &Place<'_>) -> i16 {
        place
            .projection
            .iter()
            .filter(|element| matches!(element, PlaceElem::Deref))
            .count()
            .min(MAX_DEREF as usize) as i16
    }

    fn add_place_edge(
        &mut self,
        destination: usize,
        place: &Place<'_>,
        state: &FlowState,
        adjustment: i16,
    ) {
        let deref = Self::place_deref(place).saturating_add(adjustment);
        if deref == -1 {
            self.add_edge(destination, self.storage(place.local), -1);
            return;
        }
        for &source in &state[place.local.index()] {
            self.add_edge(destination, source, deref);
        }
    }

    fn add_operand_edge(
        &mut self,
        destination: usize,
        operand: &Operand<'_>,
        state: &FlowState,
        adjustment: i16,
    ) {
        match operand {
            Operand::Copy(place) | Operand::Move(place) | Operand::CopyWith(place, _) => {
                self.add_place_edge(destination, place, state, adjustment)
            }
            Operand::Constant(_) => {}
        }
    }

    fn add_rvalue_edges<'a, 'ctx>(
        &mut self,
        gcx: Gcx<'ctx>,
        body: &Body<'ctx>,
        mode: AnalysisMode<'a, 'ctx>,
        destination: usize,
        rvalue: &Rvalue<'ctx>,
        state: &FlowState,
        allocation: Option<usize>,
    ) {
        match rvalue {
            Rvalue::Use(operand) | Rvalue::Repeat { operand, .. } => {
                if operand_may_carry_provenance(gcx, body, operand, mode) {
                    self.add_operand_edge(destination, operand, state, 0);
                }
            }
            // Pointer casts preserve provenance even when their source is an
            // integer-shaped raw representation.
            Rvalue::Cast { operand, .. } => self.add_operand_edge(destination, operand, state, 0),
            Rvalue::Ref { place, .. } => self.add_place_edge(destination, place, state, -1),
            Rvalue::UnaryOp { .. }
            | Rvalue::BinaryOp { .. }
            | Rvalue::Discriminant { .. }
            | Rvalue::Zeroed { .. } => {}
            Rvalue::Alloc { .. } => {
                if let Some(allocation) = allocation {
                    self.add_edge(destination, allocation, -1);
                }
            }
            Rvalue::Aggregate { fields, .. } => {
                for field in fields {
                    if operand_may_carry_provenance(gcx, body, field, mode) {
                        self.add_operand_edge(destination, field, state, 0);
                    }
                }
            }
        }
    }

    fn add_call_edges<'a, 'ctx>(
        &mut self,
        gcx: Gcx<'ctx>,
        body: &Body<'ctx>,
        function: &Operand<'ctx>,
        arguments: &[Operand<'ctx>],
        destination_value: Option<usize>,
        state: &FlowState,
        mode: AnalysisMode<'a, 'ctx>,
    ) -> CompileResult<()> {
        let destination = destination_value.unwrap_or(self.heap);
        let callee = match mode {
            AnalysisMode::Instance { caller, .. } => resolve_direct_callee(gcx, caller, function),
            AnalysisMode::AsyncBridge => None,
            #[cfg(test)]
            AnalysisMode::FixedEffects { .. } => None,
        };

        for (index, argument) in arguments.iter().enumerate() {
            let effect = match mode {
                AnalysisMode::Instance { summaries, .. } => {
                    let known = callee
                        .and_then(|instance| summaries.get(&instance))
                        .and_then(|summary| summary.params.get(index).copied());
                    match known {
                        Some(effect) => effect,
                        None => conservative_parameter_effect(gcx, callee, index)?,
                    }
                }
                AnalysisMode::AsyncBridge => capture_and_return(),
                #[cfg(test)]
                AnalysisMode::FixedEffects { params } => params
                    .get(index)
                    .copied()
                    .unwrap_or_else(capture_and_return),
            };

            let carries_provenance = operand_may_carry_provenance(gcx, body, argument, mode);
            if effect.heap_capture && carries_provenance {
                self.add_operand_edge(self.heap, argument, state, 0);
            }
            if carries_provenance && let Some(deref) = effect.return_deref {
                self.add_operand_edge(destination, argument, state, i16::from(deref));
            }
        }
        Ok(())
    }

    fn compute_flow_states(
        &self,
        body: &Body<'_>,
        entry_state: FlowState,
    ) -> (
        IndexVec<BasicBlockId, FlowState>,
        IndexVec<BasicBlockId, bool>,
    ) {
        let mut in_states = IndexVec::from(
            (0..body.basic_blocks.len())
                .map(|_| empty_flow_state(body.locals.len()))
                .collect::<Vec<_>>(),
        );
        let mut reachable = IndexVec::from(vec![false; body.basic_blocks.len()]);
        in_states[body.start_block] = entry_state;
        reachable[body.start_block] = true;
        let mut worklist = VecDeque::from([body.start_block]);

        while let Some(block) = worklist.pop_front() {
            let mut state = in_states[block].clone();
            let data = &body.basic_blocks[block];
            for (statement, value) in data.statements.iter().enumerate() {
                self.transfer_statement_state(block, statement, &value.kind, &mut state);
            }

            let Some(terminator) = &data.terminator else {
                continue;
            };
            match &terminator.kind {
                TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    target,
                    unwind,
                    ..
                } => {
                    kill_moved_operand(func, &mut state);
                    for argument in args {
                        kill_moved_operand(argument, &mut state);
                    }
                    let mut normal = state.clone();
                    self.define_terminator_destination(block, destination, &mut normal);
                    propagate_state(
                        *target,
                        &normal,
                        &mut in_states,
                        &mut reachable,
                        &mut worklist,
                    );
                    if let CallUnwindAction::Cleanup(cleanup) = unwind {
                        let mut cleanup_state = state;
                        clear_complete_destination(destination, &mut cleanup_state);
                        propagate_state(
                            *cleanup,
                            &cleanup_state,
                            &mut in_states,
                            &mut reachable,
                            &mut worklist,
                        );
                    }
                }
                TerminatorKind::Yield {
                    value,
                    resume_arg,
                    resume,
                    cancel,
                    unwind,
                    ..
                } => {
                    kill_moved_operand(value, &mut state);
                    let mut resumed = state.clone();
                    self.define_terminator_destination(block, resume_arg, &mut resumed);
                    propagate_state(
                        *resume,
                        &resumed,
                        &mut in_states,
                        &mut reachable,
                        &mut worklist,
                    );
                    let mut cancelled = state.clone();
                    clear_complete_destination(resume_arg, &mut cancelled);
                    propagate_state(
                        *cancel,
                        &cancelled,
                        &mut in_states,
                        &mut reachable,
                        &mut worklist,
                    );
                    if let CallUnwindAction::Cleanup(cleanup) = unwind {
                        propagate_state(
                            *cleanup,
                            &cancelled,
                            &mut in_states,
                            &mut reachable,
                            &mut worklist,
                        );
                    }
                }
                _ => {
                    for successor in terminator.kind.successors() {
                        propagate_state(
                            successor,
                            &state,
                            &mut in_states,
                            &mut reachable,
                            &mut worklist,
                        );
                    }
                }
            }
        }
        (in_states, reachable)
    }

    fn transfer_statement_state(
        &self,
        block: BasicBlockId,
        statement: usize,
        kind: &StatementKind<'_>,
        state: &mut FlowState,
    ) {
        match kind {
            StatementKind::StorageLive(local) => state[local.index()].clear(),
            StatementKind::Assign(destination, rvalue) => {
                kill_moved_rvalue(rvalue, state);
                if let Some(&value) = self.statement_values.get(&(block, statement)) {
                    define_place(destination, value, state);
                }
            }
            StatementKind::KeepAlive(operand) => kill_moved_operand(operand, state),
            StatementKind::SourceScope(_)
            | StatementKind::SetInitialized(_)
            | StatementKind::GcSafepoint(_)
            | StatementKind::Nop
            | StatementKind::SetDiscriminant { .. } => {}
        }
    }

    fn define_terminator_destination(
        &self,
        block: BasicBlockId,
        destination: &Place<'_>,
        state: &mut FlowState,
    ) {
        if let Some(&value) = self.terminator_values.get(&block) {
            define_place(destination, value, state);
        }
    }

    fn add_flow_edges<'a, 'ctx>(
        &mut self,
        gcx: Gcx<'ctx>,
        body: &Body<'ctx>,
        mode: AnalysisMode<'a, 'ctx>,
        in_states: &IndexVec<BasicBlockId, FlowState>,
        reachable: &IndexVec<BasicBlockId, bool>,
    ) -> CompileResult<()> {
        let async_liveness = matches!(mode, AnalysisMode::AsyncBridge)
            .then(|| crate::mir::analysis::liveness::compute_liveness(body));

        for (block, data) in body.basic_blocks.iter_enumerated() {
            if !reachable[block] {
                continue;
            }
            let mut state = in_states[block].clone();
            for (statement, value) in data.statements.iter().enumerate() {
                if let StatementKind::Assign(destination, rvalue) = &value.kind {
                    let sink = self
                        .statement_values
                        .get(&(block, statement))
                        .copied()
                        .unwrap_or(self.heap);
                    if !destination.projection.is_empty() && !place_has_deref(destination) {
                        for &prior in &state[destination.local.index()] {
                            self.add_edge(sink, prior, 0);
                        }
                    }
                    let allocation = self
                        .allocation_nodes
                        .get(&AllocationSite { block, statement })
                        .copied();
                    self.add_rvalue_edges(gcx, body, mode, sink, rvalue, &state, allocation);
                    if let Some(&defined) = self.statement_values.get(&(block, statement)) {
                        self.add_edge(self.storage(destination.local), defined, 1);
                    }
                }
                self.transfer_statement_state(block, statement, &value.kind, &mut state);
            }

            let Some(terminator) = &data.terminator else {
                continue;
            };
            match &terminator.kind {
                TerminatorKind::Call { func, args, .. } => self.add_call_edges(
                    gcx,
                    body,
                    func,
                    args,
                    self.terminator_values.get(&block).copied(),
                    &state,
                    mode,
                )?,
                TerminatorKind::Yield { value, .. } => {
                    if operand_may_carry_provenance(gcx, body, value, mode) {
                        self.add_operand_edge(self.heap, value, &state, 0);
                    }
                    if let Some(liveness) = &async_liveness {
                        for local in liveness.live_after_terminator(block) {
                            if local_may_carry_provenance(gcx, body, *local, mode) {
                                for &source in &state[local.index()] {
                                    self.add_edge(self.heap, source, 0);
                                }
                            }
                        }
                    }
                }
                TerminatorKind::Return => {
                    if local_may_carry_provenance(gcx, body, body.return_local, mode) {
                        for &source in &state[body.return_local.index()] {
                            self.add_edge(self.returned, source, 0);
                        }
                    }
                }
                TerminatorKind::UnresolvedGoto => self.saturated = true,
                TerminatorKind::Goto { .. }
                | TerminatorKind::SwitchInt { .. }
                | TerminatorKind::ResumeUnwind
                | TerminatorKind::Unreachable => {}
            }

            if let Some(&defined) = self.terminator_values.get(&block) {
                let destination = match &terminator.kind {
                    TerminatorKind::Call { destination, .. } => Some(destination),
                    TerminatorKind::Yield { resume_arg, .. } => Some(resume_arg),
                    _ => None,
                };
                if let Some(destination) = destination {
                    self.add_edge(self.storage(destination.local), defined, 1);
                }
            }
        }
        Ok(())
    }

    /// A stack slot may be reused when the same allocation statement executes
    /// again only if no value produced by its previous execution is still
    /// live. This retains loop-site promotion after inlining while preserving
    /// allocation identity when aliases really do cross a backedge.
    fn find_overlapping_allocations(
        &self,
        body: &Body<'_>,
        in_states: &IndexVec<BasicBlockId, FlowState>,
    ) -> FxHashSet<AllocationSite> {
        let liveness = crate::mir::analysis::liveness::compute_liveness(body);
        let mut overlapping = FxHashSet::default();
        for (block, data) in body.basic_blocks.iter_enumerated() {
            let mut state = in_states[block].clone();
            for (statement, value) in data.statements.iter().enumerate() {
                let site = AllocationSite { block, statement };
                if let Some(&allocation) = self.allocation_nodes.get(&site)
                    && liveness
                        .live_before_statement(block, statement)
                        .iter()
                        .any(|local| {
                            state[local.index()]
                                .iter()
                                .any(|source| self.node_reaches(*source, allocation))
                        })
                {
                    overlapping.insert(site);
                }
                self.transfer_statement_state(block, statement, &value.kind, &mut state);
            }
        }
        overlapping
    }

    /// Identify the blocks in which an alias of each allocation is live.
    ///
    /// Stack-promoted storage with GC-bearing fields needs a typed companion
    /// root only while some raw/reference alias can still reach it. Recording
    /// that region on the pre-rewrite graph avoids extending every promoted
    /// object to function exit while still covering calls and polls inserted
    /// later in instance finalization.
    fn find_allocation_live_blocks(
        &self,
        body: &Body<'_>,
        in_states: &IndexVec<BasicBlockId, FlowState>,
    ) -> FxHashMap<AllocationSite, FxHashSet<BasicBlockId>> {
        let liveness = crate::mir::analysis::liveness::compute_liveness(body);
        let mut reachable_cache: FxHashMap<usize, Vec<AllocationSite>> = FxHashMap::default();
        let mut blocks: FxHashMap<AllocationSite, FxHashSet<BasicBlockId>> = FxHashMap::default();

        for (block, data) in body.basic_blocks.iter_enumerated() {
            let mut state = in_states[block].clone();
            for (statement, value) in data.statements.iter().enumerate() {
                self.record_live_allocation_blocks(
                    block,
                    liveness.live_before_statement(block, statement),
                    &state,
                    &mut reachable_cache,
                    &mut blocks,
                );
                self.transfer_statement_state(block, statement, &value.kind, &mut state);
            }
            self.record_live_allocation_blocks(
                block,
                liveness.live_before_terminator(block),
                &state,
                &mut reachable_cache,
                &mut blocks,
            );
        }
        blocks
    }

    fn record_live_allocation_blocks(
        &self,
        block: BasicBlockId,
        live: &FxHashSet<LocalId>,
        state: &FlowState,
        reachable_cache: &mut FxHashMap<usize, Vec<AllocationSite>>,
        blocks: &mut FxHashMap<AllocationSite, FxHashSet<BasicBlockId>>,
    ) {
        for local in live {
            for &source in &state[local.index()] {
                let sites = reachable_cache
                    .entry(source)
                    .or_insert_with(|| self.reachable_allocations(source));
                for &site in sites.iter() {
                    blocks.entry(site).or_default().insert(block);
                }
            }
        }
    }

    fn reachable_allocations(&self, start: usize) -> Vec<AllocationSite> {
        let mut seen = FxHashSet::default();
        let mut pending = vec![start];
        let mut allocations = FxHashSet::default();
        while let Some(node) = pending.pop() {
            if !seen.insert(node) {
                continue;
            }
            if let NodeKind::Allocation(site) = self.nodes[node] {
                allocations.insert(site);
            }
            pending.extend(self.edges[node].iter().map(|edge| edge.target));
        }
        let mut allocations: Vec<_> = allocations.into_iter().collect();
        allocations.sort_by_key(|site| (site.block.index(), site.statement));
        allocations
    }

    fn node_reaches(&self, start: usize, target: usize) -> bool {
        let mut seen = FxHashSet::default();
        let mut pending = vec![start];
        while let Some(node) = pending.pop() {
            if node == target {
                return true;
            }
            if seen.insert(node) {
                pending.extend(self.edges[node].iter().map(|edge| edge.target));
            }
        }
        false
    }

    fn trace_from(&mut self, start: usize) -> Vec<Option<i16>> {
        let mut distance = vec![None; self.nodes.len()];
        distance[start] = Some(0);
        let mut queue = VecDeque::from([start]);

        while let Some(node) = queue.pop_front() {
            let current: i16 = distance[node].expect("queued escape node has a distance");
            for edge in &self.edges[node] {
                let raw = current.saturating_add(edge.deref);
                let next = raw.clamp(-MAX_DEREF, MAX_DEREF);
                if raw != next {
                    self.saturated = true;
                }
                let should_update = distance[edge.target].is_none_or(|known| next < known);
                if should_update {
                    distance[edge.target] = Some(next);
                    queue.push_back(edge.target);
                }
            }
        }

        distance
    }

    fn summary(mut self) -> InstanceEscapeSummary {
        let heap = self.trace_from(self.heap);
        let returned = self.trace_from(self.returned);
        if self.saturated {
            return InstanceEscapeSummary {
                params: vec![
                    ParamEscapeSummary {
                        heap_capture: true,
                        return_deref: Some(0),
                    };
                    self.parameter_nodes.len()
                ],
            };
        }

        InstanceEscapeSummary {
            params: self
                .parameter_nodes
                .iter()
                .map(|node| ParamEscapeSummary {
                    heap_capture: heap[*node].is_some_and(|deref| deref >= 0),
                    return_deref: returned[*node]
                        .filter(|deref| *deref >= 0)
                        .map(|deref| deref as u8),
                })
                .collect(),
        }
    }

    fn placement(mut self) -> EscapePlacement {
        let heap = self.trace_from(self.heap);
        let returned = self.trace_from(self.returned);
        let mut placement = EscapePlacement::default();

        if self.saturated {
            for kind in &self.nodes {
                match kind {
                    NodeKind::Storage(local) => {
                        placement.heap_locals.insert(*local);
                    }
                    NodeKind::Allocation(site) => {
                        placement.escaping_alloc_sites.insert(*site);
                    }
                    NodeKind::Heap
                    | NodeKind::Return
                    | NodeKind::Parameter(_)
                    | NodeKind::Value => {}
                }
            }
            return placement;
        }

        for (node, kind) in self.nodes.iter().enumerate() {
            let address_escapes = heap[node].is_some_and(|deref| deref < 0)
                || returned[node].is_some_and(|deref| deref < 0);
            if !address_escapes {
                continue;
            }
            match kind {
                NodeKind::Storage(local) => {
                    placement.heap_locals.insert(*local);
                }
                NodeKind::Allocation(site) => {
                    placement.escaping_alloc_sites.insert(*site);
                }
                NodeKind::Heap | NodeKind::Return | NodeKind::Parameter(_) | NodeKind::Value => {}
            }
        }
        placement
            .escaping_alloc_sites
            .extend(self.overlapping_allocations);
        self.allocation_live_blocks
            .retain(|site, _| !placement.escaping_alloc_sites.contains(site));
        placement.allocation_keepalive_blocks = self.allocation_live_blocks;
        placement
    }
}

fn empty_flow_state(local_count: usize) -> FlowState {
    vec![FxHashSet::default(); local_count]
}

fn operand_may_carry_provenance<'a, 'ctx>(
    gcx: Gcx<'ctx>,
    body: &Body<'ctx>,
    operand: &Operand<'ctx>,
    mode: AnalysisMode<'a, 'ctx>,
) -> bool {
    match operand {
        Operand::Copy(place) | Operand::Move(place) | Operand::CopyWith(place, _) => {
            type_may_carry_provenance(gcx, concrete_place_ty(gcx, body, place, mode))
        }
        Operand::Constant(_) => false,
    }
}

fn local_may_carry_provenance<'a, 'ctx>(
    gcx: Gcx<'ctx>,
    body: &Body<'ctx>,
    local: LocalId,
    mode: AnalysisMode<'a, 'ctx>,
) -> bool {
    let ty = match mode {
        AnalysisMode::Instance { caller, .. } => {
            instantiate_ty_with_args(gcx, body.locals[local].ty, caller.args())
        }
        AnalysisMode::AsyncBridge => body.locals[local].ty,
        #[cfg(test)]
        AnalysisMode::FixedEffects { .. } => body.locals[local].ty,
    };
    type_may_carry_provenance(gcx, ty)
}

fn concrete_place_ty<'a, 'ctx>(
    gcx: Gcx<'ctx>,
    body: &Body<'ctx>,
    place: &Place<'ctx>,
    mode: AnalysisMode<'a, 'ctx>,
) -> Ty<'ctx> {
    let mut ty = body.locals[place.local].ty;
    for projection in &place.projection {
        match projection {
            PlaceElem::Deref => ty = ty.dereference().unwrap_or_else(|| Ty::error(gcx)),
            PlaceElem::Field(_, field_ty) => ty = *field_ty,
            PlaceElem::VariantDowncast { .. } => {}
        }
    }
    match mode {
        AnalysisMode::Instance { caller, .. } => instantiate_ty_with_args(gcx, ty, caller.args()),
        AnalysisMode::AsyncBridge => ty,
        #[cfg(test)]
        AnalysisMode::FixedEffects { .. } => ty,
    }
}

fn type_may_carry_provenance<'ctx>(gcx: Gcx<'ctx>, ty: Ty<'ctx>) -> bool {
    fn visit<'ctx>(gcx: Gcx<'ctx>, ty: Ty<'ctx>, visiting: &mut FxHashSet<Ty<'ctx>>) -> bool {
        if !visiting.insert(ty) {
            return true;
        }
        let carries = match ty.kind() {
            TyKind::Bool
            | TyKind::Rune
            | TyKind::Int(_)
            | TyKind::UInt(_)
            | TyKind::Float(_)
            | TyKind::FnPointer { .. }
            | TyKind::Never => false,
            TyKind::String
            | TyKind::Pointer(..)
            | TyKind::Reference(..)
            | TyKind::BoxedExistential { .. } => true,
            TyKind::Array { element, .. } => visit(gcx, element, visiting),
            TyKind::Tuple(elements) => elements
                .iter()
                .copied()
                .any(|element| visit(gcx, element, visiting)),
            TyKind::Adt(definition, arguments) => match definition.kind {
                AdtKind::Struct => {
                    gcx.get_struct_definition(definition.id)
                        .fields
                        .iter()
                        .any(|field| {
                            visit(
                                gcx,
                                instantiate_ty_with_args(gcx, field.ty, arguments),
                                visiting,
                            )
                        })
                }
                AdtKind::Enum => {
                    gcx.get_enum_definition(definition.id)
                        .variants
                        .iter()
                        .any(|variant| match variant.kind {
                            EnumVariantKind::Unit => false,
                            EnumVariantKind::Tuple(fields) => fields.iter().any(|field| {
                                visit(
                                    gcx,
                                    instantiate_ty_with_args(gcx, field.ty, arguments),
                                    visiting,
                                )
                            }),
                        })
                }
            },
            TyKind::Closure {
                closure_def_id,
                captured_generics,
                ..
            } => gcx
                .get_closure_captures(closure_def_id)
                .is_none_or(|captures| {
                    captures.captures.iter().any(|capture| {
                        matches!(capture.capture_kind, CaptureKind::ByRef { .. })
                            || visit(
                                gcx,
                                instantiate_ty_with_args(gcx, capture.ty, captured_generics),
                                visiting,
                            )
                    })
                }),
            TyKind::Alias { .. }
            | TyKind::Infer(_)
            | TyKind::Parameter(_)
            | TyKind::Opaque(_)
            | TyKind::Error => true,
        };
        visiting.remove(&ty);
        carries
    }

    visit(gcx, ty, &mut FxHashSet::default())
}

fn place_has_deref(place: &Place<'_>) -> bool {
    place
        .projection
        .iter()
        .any(|element| matches!(element, PlaceElem::Deref))
}

fn define_place(place: &Place<'_>, value: usize, state: &mut FlowState) {
    if place_has_deref(place) {
        return;
    }
    if place.projection.is_empty() {
        state[place.local.index()].clear();
    }
    state[place.local.index()].insert(value);
}

fn clear_complete_destination(place: &Place<'_>, state: &mut FlowState) {
    if place.projection.is_empty() {
        state[place.local.index()].clear();
    }
}

fn kill_moved_operand(operand: &Operand<'_>, state: &mut FlowState) {
    let moved = match operand {
        Operand::Move(place) => Some(place),
        Operand::CopyWith(place, modifiers) if modifiers.take => Some(place),
        Operand::Copy(_) | Operand::CopyWith(_, _) | Operand::Constant(_) => None,
    };
    if let Some(place) = moved
        && place.projection.is_empty()
    {
        state[place.local.index()].clear();
    }
}

fn kill_moved_rvalue(rvalue: &Rvalue<'_>, state: &mut FlowState) {
    match rvalue {
        Rvalue::Use(operand)
        | Rvalue::UnaryOp { operand, .. }
        | Rvalue::Cast { operand, .. }
        | Rvalue::Repeat { operand, .. } => kill_moved_operand(operand, state),
        Rvalue::BinaryOp { lhs, rhs, .. } => {
            kill_moved_operand(lhs, state);
            kill_moved_operand(rhs, state);
        }
        Rvalue::Aggregate { fields, .. } => {
            for field in fields {
                kill_moved_operand(field, state);
            }
        }
        Rvalue::Ref { .. }
        | Rvalue::Discriminant { .. }
        | Rvalue::Alloc { .. }
        | Rvalue::Zeroed { .. } => {}
    }
}

fn propagate_state(
    successor: BasicBlockId,
    state: &FlowState,
    in_states: &mut IndexVec<BasicBlockId, FlowState>,
    reachable: &mut IndexVec<BasicBlockId, bool>,
    worklist: &mut VecDeque<BasicBlockId>,
) {
    let mut changed = !reachable[successor];
    reachable[successor] = true;
    for (destination, source) in in_states[successor].iter_mut().zip(state) {
        let old_len = destination.len();
        destination.extend(source.iter().copied());
        changed |= destination.len() != old_len;
    }
    if changed && !worklist.contains(&successor) {
        worklist.push_back(successor);
    }
}

fn ensure_instance_summaries<'ctx>(gcx: Gcx<'ctx>, root: Instance<'ctx>) -> CompileResult<()> {
    let call_graph = InstanceCallGraph::collect(gcx, root);
    if call_graph.instances.is_empty() {
        return Ok(());
    }

    let mut summaries = gcx.store.instance_escape_summaries.borrow().clone();
    for instance in &call_graph.instances {
        summaries.entry(*instance).or_insert_with(|| {
            let parameter_count = gcx.get_signature(instance.def_id()).inputs.len();
            InstanceEscapeSummary {
                params: vec![ParamEscapeSummary::default(); parameter_count],
            }
        });
    }

    for mut component in call_graph.strongly_connected_components() {
        component.sort_by(|left, right| {
            instance_sort_key(gcx, *left).cmp(&instance_sort_key(gcx, *right))
        });
        loop {
            let mut changed = false;
            for instance in &component {
                let Some(body) = try_shared_body(gcx, *instance) else {
                    continue;
                };
                let summary = EscapeGraph::build(
                    gcx,
                    body,
                    AnalysisMode::Instance {
                        caller: *instance,
                        summaries: &summaries,
                    },
                )?
                .summary();
                if summaries.get(instance) != Some(&summary) {
                    summaries.insert(*instance, summary);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
    }

    *gcx.store.instance_escape_summaries.borrow_mut() = summaries;
    Ok(())
}

struct InstanceCallGraph<'ctx> {
    instances: Vec<Instance<'ctx>>,
    edges: Vec<Vec<usize>>,
}

impl<'ctx> InstanceCallGraph<'ctx> {
    fn collect(gcx: Gcx<'ctx>, root: Instance<'ctx>) -> Self {
        let mut pending = vec![root];
        let mut discovered = FxHashSet::default();
        let mut calls: FxHashMap<Instance<'ctx>, Vec<Instance<'ctx>>> = FxHashMap::default();

        while let Some(instance) = pending.pop() {
            if !matches!(instance.kind(), InstanceKind::Item(_)) || discovered.contains(&instance) {
                continue;
            }
            let Some(body) = try_shared_body(gcx, instance) else {
                continue;
            };
            discovered.insert(instance);
            let mut callees = Vec::new();
            for block in &body.basic_blocks {
                let Some(TerminatorKind::Call { func, .. }) =
                    block.terminator.as_ref().map(|terminator| &terminator.kind)
                else {
                    continue;
                };
                let Some(callee) = resolve_direct_callee(gcx, instance, func) else {
                    continue;
                };
                if matches!(callee.kind(), InstanceKind::Item(_))
                    && try_shared_body(gcx, callee).is_some()
                {
                    callees.push(callee);
                    pending.push(callee);
                }
            }
            callees.sort_by(|left, right| {
                instance_sort_key(gcx, *left).cmp(&instance_sort_key(gcx, *right))
            });
            callees.dedup();
            calls.insert(instance, callees);
        }

        let mut instances: Vec<_> = discovered.into_iter().collect();
        instances.sort_by(|left, right| {
            instance_sort_key(gcx, *left).cmp(&instance_sort_key(gcx, *right))
        });
        let indices: FxHashMap<_, _> = instances
            .iter()
            .enumerate()
            .map(|(index, instance)| (*instance, index))
            .collect();
        let edges = instances
            .iter()
            .map(|instance| {
                calls
                    .get(instance)
                    .into_iter()
                    .flatten()
                    .filter_map(|callee| indices.get(callee).copied())
                    .collect()
            })
            .collect();
        Self { instances, edges }
    }

    fn strongly_connected_components(&self) -> Vec<Vec<Instance<'ctx>>> {
        let mut tarjan = Tarjan::new(&self.edges);
        for node in 0..self.instances.len() {
            if tarjan.indices[node].is_none() {
                tarjan.visit(node);
            }
        }
        tarjan
            .components
            .into_iter()
            .map(|component| {
                component
                    .into_iter()
                    .map(|node| self.instances[node])
                    .collect()
            })
            .collect()
    }
}

struct Tarjan<'a> {
    graph: &'a [Vec<usize>],
    next_index: usize,
    indices: Vec<Option<usize>>,
    lowlink: Vec<usize>,
    stack: Vec<usize>,
    on_stack: Vec<bool>,
    components: Vec<Vec<usize>>,
}

impl<'a> Tarjan<'a> {
    fn new(graph: &'a [Vec<usize>]) -> Self {
        Self {
            graph,
            next_index: 0,
            indices: vec![None; graph.len()],
            lowlink: vec![0; graph.len()],
            stack: Vec::new(),
            on_stack: vec![false; graph.len()],
            components: Vec::new(),
        }
    }

    fn visit(&mut self, node: usize) {
        let index = self.next_index;
        self.next_index += 1;
        self.indices[node] = Some(index);
        self.lowlink[node] = index;
        self.stack.push(node);
        self.on_stack[node] = true;

        for &successor in &self.graph[node] {
            if self.indices[successor].is_none() {
                self.visit(successor);
                self.lowlink[node] = self.lowlink[node].min(self.lowlink[successor]);
            } else if self.on_stack[successor] {
                self.lowlink[node] = self.lowlink[node]
                    .min(self.indices[successor].expect("visited SCC node has an index"));
            }
        }

        if self.lowlink[node] != self.indices[node].expect("visited SCC root has an index") {
            return;
        }

        let mut component = Vec::new();
        loop {
            let member = self.stack.pop().expect("SCC root remains on the stack");
            self.on_stack[member] = false;
            component.push(member);
            if member == node {
                break;
            }
        }
        self.components.push(component);
    }
}

fn resolve_direct_callee<'ctx>(
    gcx: Gcx<'ctx>,
    caller: Instance<'ctx>,
    function: &Operand<'ctx>,
) -> Option<Instance<'ctx>> {
    let Operand::Constant(constant) = function else {
        return None;
    };
    let ConstantKind::Function(definition, arguments, _) = constant.value else {
        return None;
    };
    let arguments = substitute_generic_arguments(gcx, arguments, caller.args());
    Some(resolve_instance(gcx, definition, arguments))
}

fn substitute_generic_arguments<'ctx>(
    gcx: Gcx<'ctx>,
    arguments: GenericArguments<'ctx>,
    substitutions: GenericArguments<'ctx>,
) -> GenericArguments<'ctx> {
    if arguments.is_empty() || substitutions.is_empty() {
        return arguments;
    }
    let resolved = arguments
        .iter()
        .map(|argument| match argument {
            GenericArgument::Type(ty) => {
                GenericArgument::Type(instantiate_ty_with_args(gcx, *ty, substitutions))
            }
            GenericArgument::Const(value) => {
                GenericArgument::Const(instantiate_const_with_args(gcx, *value, substitutions))
            }
        })
        .collect();
    gcx.store.interners.intern_generic_args(resolved)
}

fn try_shared_body<'ctx>(gcx: Gcx<'ctx>, instance: Instance<'ctx>) -> Option<&'ctx Body<'ctx>> {
    let InstanceKind::Item(definition) = instance.kind() else {
        return None;
    };
    let packages = gcx.store.mir_packages.borrow();
    packages
        .get(&definition.package())
        .and_then(|package| package.functions.get(&definition).copied())
}

fn conservative_parameter_effect<'ctx>(
    gcx: Gcx<'ctx>,
    callee: Option<Instance<'ctx>>,
    parameter: usize,
) -> CompileResult<ParamEscapeSummary> {
    let Some(callee) = callee else {
        return Ok(capture_and_return());
    };
    let definition = callee.def_id();
    match gcx.get_signature(definition).abi {
        Some(Abi::Runtime) => {
            let symbol = gcx.definition_symbol_or_fallback(definition);
            let symbol = gcx.symbol_text(symbol);
            let Some(effect) = param_escape_effect_for_symbol(symbol.as_str(), parameter) else {
                gcx.dcx().emit_error(
                    format!(
                        "runtime ABI entry `{symbol}` is missing parameter escape classification"
                    ),
                    Some(gcx.definition_ident(definition).span),
                );
                return Err(ReportedError);
            };
            Ok(match effect {
                RuntimeParamEscapeEffect::NoCapture => ParamEscapeSummary::default(),
                RuntimeParamEscapeEffect::Capture => ParamEscapeSummary {
                    heap_capture: true,
                    return_deref: None,
                },
                RuntimeParamEscapeEffect::Return => ParamEscapeSummary {
                    heap_capture: false,
                    return_deref: Some(0),
                },
                RuntimeParamEscapeEffect::CaptureAndReturn => capture_and_return(),
            })
        }
        Some(Abi::Intrinsic) => {
            let symbol = gcx.definition_symbol_or_fallback(definition);
            let symbol = gcx.symbol_text(symbol);
            let Some(effect) = intrinsic_param_escape_effect(symbol.as_str(), parameter) else {
                gcx.dcx().emit_error(
                    format!(
                        "intrinsic ABI entry `{symbol}` is missing parameter escape classification"
                    ),
                    Some(gcx.definition_ident(definition).span),
                );
                return Err(ReportedError);
            };
            Ok(match effect {
                RuntimeParamEscapeEffect::NoCapture => ParamEscapeSummary::default(),
                RuntimeParamEscapeEffect::Capture => ParamEscapeSummary {
                    heap_capture: true,
                    return_deref: None,
                },
                RuntimeParamEscapeEffect::Return => ParamEscapeSummary {
                    heap_capture: false,
                    return_deref: intrinsic_return_deref(symbol.as_str(), parameter),
                },
                RuntimeParamEscapeEffect::CaptureAndReturn => ParamEscapeSummary {
                    heap_capture: true,
                    return_deref: intrinsic_return_deref(symbol.as_str(), parameter),
                },
            })
        }
        Some(Abi::C | Abi::Blocking) | None => Ok(capture_and_return()),
    }
}

fn capture_and_return() -> ParamEscapeSummary {
    ParamEscapeSummary {
        heap_capture: true,
        return_deref: Some(0),
    }
}

fn instance_sort_key<'ctx>(gcx: GlobalContext<'ctx>, instance: Instance<'ctx>) -> String {
    mangle_instance(gcx, instance)
}

mod allocation_rewrite {
    //! Materialization of allocation-site placement selected by `escape_graph`.

    use super::{AllocationSite, type_may_carry_provenance};
    use crate::{
        compile::context::Gcx,
        error::CompileResult,
        mir::{
            Body, CastKind, LocalDecl, LocalKind, Operand, Place, Rvalue, Statement, StatementKind,
        },
        sema::models::TyKind,
    };
    use rustc_hash::{FxHashMap, FxHashSet};

    /// Replace each nonescaping managed allocation with independent stack storage.
    ///
    /// Placement is keyed by statement rather than destination local: distinct
    /// allocations may reuse a pointer local while still receiving different
    /// escape decisions.
    pub(crate) fn promote_allocation_sites<'ctx>(
        gcx: Gcx<'ctx>,
        body: &mut Body<'ctx>,
        escaping: &FxHashSet<AllocationSite>,
        keepalive_blocks: &FxHashMap<AllocationSite, FxHashSet<crate::mir::BasicBlockId>>,
    ) -> CompileResult<()> {
        let mut promoted = FxHashMap::default();
        for (block, data) in body.basic_blocks.iter_enumerated() {
            for (statement, value) in data.statements.iter().enumerate() {
                let StatementKind::Assign(destination, Rvalue::Alloc { ty }) = &value.kind else {
                    continue;
                };
                let site = AllocationSite { block, statement };
                if escaping.contains(&site) {
                    continue;
                }

                let span = value.span;
                let stack_object = body.locals.push(LocalDecl {
                    ty: *ty,
                    kind: LocalKind::Temp,
                    mutable: true,
                    name: None,
                    span,
                });
                body.escape_locals.push(false);
                let stack_reference_ty = gcx
                    .store
                    .interners
                    .intern_ty(TyKind::Reference(*ty, crate::hir::Mutability::Mutable));
                let stack_reference = body.locals.push(LocalDecl {
                    ty: stack_reference_ty,
                    kind: LocalKind::Temp,
                    mutable: true,
                    name: None,
                    span,
                });
                body.escape_locals.push(false);
                promoted.insert(
                    site,
                    (
                        stack_object,
                        stack_reference,
                        *ty,
                        place_ty(body, gcx, destination),
                    ),
                );
            }
        }

        let mut promoted_sites: Vec<_> = promoted.iter().collect();
        promoted_sites.sort_by_key(|(site, _)| (site.block.index(), site.statement));
        let reference_initializers: Vec<_> = promoted_sites
            .iter()
            .map(|(_, (_, reference, _, _))| Statement {
                kind: StatementKind::Assign(
                    Place::from_local(*reference),
                    Rvalue::Zeroed {
                        ty: body.locals[*reference].ty,
                    },
                ),
                span: body.locals[*reference].span,
            })
            .collect();
        let mut block_keepalives: FxHashMap<_, Vec<_>> = FxHashMap::default();
        for (site, (_, reference, promoted_ty, _)) in &promoted_sites {
            if !type_may_carry_provenance(gcx, *promoted_ty) {
                continue;
            }
            let mut blocks: Vec<_> = keepalive_blocks
                .get(site)
                .into_iter()
                .flatten()
                .copied()
                .collect();
            blocks.sort_by_key(|block| block.index());
            for block in blocks {
                block_keepalives
                    .entry(block)
                    .or_default()
                    .push((*reference, body.locals[*reference].span));
            }
        }

        for (block, data) in body.basic_blocks.iter_mut_enumerated() {
            let old = std::mem::take(&mut data.statements);
            let mut rewritten = Vec::with_capacity(
                old.len()
                    + promoted.len()
                    + block_keepalives.get(&block).map_or(0, Vec::len)
                    + usize::from(block == body.start_block) * reference_initializers.len(),
            );
            if block == body.start_block {
                rewritten.extend(reference_initializers.iter().cloned());
            }
            for (statement, value) in old.into_iter().enumerate() {
                let site = AllocationSite { block, statement };
                let Statement { kind, span } = value;
                match (kind, promoted.get(&site).copied()) {
                    (
                        StatementKind::Assign(destination, Rvalue::Alloc { ty }),
                        Some((stack_object, stack_reference, promoted_ty, destination_ty)),
                    ) if ty == promoted_ty => {
                        rewritten.push(Statement {
                            kind: StatementKind::Assign(
                                Place::from_local(stack_object),
                                Rvalue::Zeroed { ty: promoted_ty },
                            ),
                            span,
                        });
                        rewritten.push(Statement {
                            kind: StatementKind::Assign(
                                Place::from_local(stack_reference),
                                Rvalue::Ref {
                                    mutable: true,
                                    place: Place::from_local(stack_object),
                                },
                            ),
                            span,
                        });
                        rewritten.push(Statement {
                            kind: StatementKind::Assign(
                                destination.clone(),
                                Rvalue::Cast {
                                    operand: Operand::Copy(Place::from_local(stack_reference)),
                                    ty: destination_ty,
                                    kind: CastKind::Pointer,
                                },
                            ),
                            span,
                        });
                    }
                    (kind, _) => rewritten.push(Statement { kind, span }),
                }
            }
            if let Some(references) = block_keepalives.get(&block) {
                for (reference, span) in references {
                    rewritten.push(Statement {
                        kind: StatementKind::KeepAlive(Operand::Copy(Place::from_local(
                            *reference,
                        ))),
                        span: *span,
                    });
                }
            }
            data.statements = rewritten;
        }
        Ok(())
    }

    fn place_ty<'ctx>(
        body: &Body<'ctx>,
        gcx: Gcx<'ctx>,
        place: &Place<'ctx>,
    ) -> crate::sema::models::Ty<'ctx> {
        let mut ty = body.locals[place.local].ty;
        for projection in &place.projection {
            match projection {
                crate::mir::PlaceElem::Deref => {
                    ty = ty
                        .dereference()
                        .unwrap_or_else(|| crate::sema::models::Ty::error(gcx));
                }
                crate::mir::PlaceElem::Field(_, field_ty) => ty = *field_ty,
                crate::mir::PlaceElem::VariantDowncast { .. } => {}
            }
        }
        ty
    }
}

mod heapify_rewrite {
    //! Materialization of address-taken-local placement selected by `escape_graph`.

    use crate::compile::context::Gcx;
    use crate::error::CompileResult;
    use crate::hir::Mutability;
    use crate::mir::optimize::MirPass;
    use crate::mir::{
        BasicBlockData, BasicBlockId, Body, CopyModifiers, LocalDecl, LocalId, LocalKind, Operand,
        Place, PlaceElem, Rvalue, Statement, StatementKind, Terminator, TerminatorKind,
    };
    use crate::sema::models::{Ty, TyKind};
    use index_vec::IndexVec;
    use rustc_hash::FxHashSet;

    pub struct ApplyEscapeAnalysis;

    pub(crate) fn apply_heapified_locals<'ctx>(
        gcx: Gcx<'ctx>,
        body: &mut Body<'ctx>,
    ) -> CompileResult<()> {
        ApplyEscapeAnalysis.run(gcx, body)
    }

    impl<'ctx> MirPass<'ctx> for ApplyEscapeAnalysis {
        fn name(&self) -> &'static str {
            "ApplyEscapeAnalysis"
        }

        fn run(&mut self, gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
            let mut heapified: Vec<Option<Ty<'ctx>>> = vec![None; body.locals.len()];
            let mut param_replacements: Vec<Option<LocalId>> = vec![None; body.locals.len()];
            let original_local_count = body.locals.len();

            for idx in 0..original_local_count {
                let kind = body.locals[idx].kind;
                if matches!(kind, LocalKind::Return) {
                    continue;
                }
                if body.escape_locals.get(idx).cloned().unwrap_or(false) {
                    let old_ty = body.locals[idx].ty;
                    let span = body.locals[idx].span;
                    let new_ty = gcx
                        .store
                        .interners
                        .intern_ty(TyKind::Reference(old_ty, Mutability::Mutable));
                    if matches!(kind, LocalKind::Param) {
                        let heap_local = body.locals.push(LocalDecl {
                            ty: new_ty,
                            kind: LocalKind::Temp,
                            mutable: true,
                            name: None,
                            span,
                        });
                        body.escape_locals.push(false);
                        heapified.push(Some(old_ty));
                        param_replacements[idx] = Some(heap_local);
                    } else {
                        body.locals[idx].ty = new_ty;
                        heapified[idx] = Some(old_ty);
                    }
                }
            }

            if heapified.iter().all(|item| item.is_none()) {
                return Ok(());
            }

            for bb in body.basic_blocks.iter_mut() {
                for stmt in &mut bb.statements {
                    rewrite_statement(stmt, &heapified, &param_replacements);
                }
                if let Some(term) = &mut bb.terminator {
                    rewrite_terminator(term, &heapified, &param_replacements);
                }
            }

            rewrite_fresh_heapified_initializations(body, &heapified);
            let declaration_allocated = materialize_heapified_storage_lives(body, &heapified);

            let span = body.locals[body.return_local].span;
            let mut allocs: Vec<Statement<'ctx>> = Vec::new();
            for (idx, ty) in heapified.iter().enumerate() {
                let Some(old_ty) = ty else { continue };
                if declaration_allocated[idx] {
                    continue;
                }
                let place = Place::from_local(LocalId::from_raw(idx as u32));
                allocs.push(Statement {
                    kind: StatementKind::Assign(place, Rvalue::Alloc { ty: *old_ty }),
                    span,
                });
            }

            let mut param_inits: Vec<Statement<'ctx>> = Vec::new();
            for (idx, heap_local) in param_replacements.iter().enumerate() {
                let Some(heap_local) = heap_local else {
                    continue;
                };
                let heap_place = Place {
                    local: *heap_local,
                    projection: vec![PlaceElem::Deref],
                };
                let param_place = Place::from_local(LocalId::from_raw(idx as u32));
                param_inits.push(Statement {
                    kind: StatementKind::Assign(
                        heap_place,
                        Rvalue::Use(Operand::Copy(param_place)),
                    ),
                    span,
                });
            }

            if !allocs.is_empty() || !param_inits.is_empty() {
                let entry = body.start_block;
                let statements = &mut body.basic_blocks[entry].statements;
                let mut insertions = Vec::with_capacity(allocs.len() + param_inits.len());
                insertions.extend(allocs);
                insertions.extend(param_inits);
                statements.splice(0..0, insertions);
            }
            Ok(())
        }
    }

    /// Replaces source binding boundaries with allocations for heapified locals.
    ///
    /// A marker in a loop executes once per iteration, so each source binding gets
    /// distinct storage. Locals without a marker are compiler-generated or
    /// parameter replacements and retain the entry-block allocation fallback.
    fn materialize_heapified_storage_lives<'ctx>(
        body: &mut Body<'ctx>,
        heapified: &[Option<Ty<'ctx>>],
    ) -> Vec<bool> {
        let mut declaration_allocated = vec![false; heapified.len()];

        for block in &mut body.basic_blocks {
            for statement in &mut block.statements {
                let StatementKind::StorageLive(local) = &statement.kind else {
                    continue;
                };
                let local = *local;
                let Some(pointee_ty) = heapified.get(local.index()).and_then(|ty| *ty) else {
                    continue;
                };

                declaration_allocated[local.index()] = true;
                statement.kind = StatementKind::Assign(
                    Place::from_local(local),
                    Rvalue::Alloc { ty: pointee_ty },
                );
            }
        }

        declaration_allocated
    }

    fn rewrite_fresh_heapified_initializations<'ctx>(
        body: &mut Body<'ctx>,
        heapified: &[Option<Ty<'ctx>>],
    ) {
        let may_assigned_in = compute_heapified_may_assigned_in(body, heapified);
        let original_blocks: Vec<BasicBlockId> = body.basic_blocks.indices().collect();

        for bb in original_blocks {
            let mut assigned = may_assigned_in[bb].clone();

            let old_statements = std::mem::take(&mut body.basic_blocks[bb].statements);
            let mut new_statements = Vec::with_capacity(old_statements.len());
            for stmt in old_statements {
                let span = stmt.span;
                match stmt.kind {
                    StatementKind::StorageLive(local) => {
                        assigned.remove(&local);
                        new_statements.push(Statement {
                            kind: StatementKind::StorageLive(local),
                            span,
                        });
                    }
                    StatementKind::Assign(destination, rvalue) => {
                        if let Some(pointee_ty) =
                            heapified_direct_deref_pointee_ty(&destination, heapified)
                        {
                            let is_first_write = !assigned.contains(&destination.local);
                            assigned.insert(destination.local);
                            if is_first_write {
                                let tmp_local = body.locals.push(LocalDecl {
                                    ty: pointee_ty,
                                    kind: LocalKind::Temp,
                                    mutable: true,
                                    name: None,
                                    span,
                                });
                                body.escape_locals.push(false);
                                new_statements.push(Statement {
                                    kind: StatementKind::Assign(
                                        Place::from_local(tmp_local),
                                        rvalue,
                                    ),
                                    span,
                                });
                                new_statements.push(Statement {
                                    kind: StatementKind::Assign(
                                        destination,
                                        Rvalue::Use(Operand::copy_with(
                                            Place::from_local(tmp_local),
                                            CopyModifiers {
                                                init: true,
                                                take: true,
                                            },
                                        )),
                                    ),
                                    span,
                                });
                                continue;
                            }
                        }

                        new_statements.push(Statement {
                            kind: StatementKind::Assign(destination, rvalue),
                            span,
                        });
                    }
                    other => new_statements.push(Statement { kind: other, span }),
                }
            }
            body.basic_blocks[bb].statements = new_statements;

            let Some(mut term) = body.basic_blocks[bb].terminator.take() else {
                continue;
            };
            if let TerminatorKind::Call {
                destination,
                target,
                ..
            } = &mut term.kind
            {
                if let Some(pointee_ty) = heapified_direct_deref_pointee_ty(destination, heapified)
                {
                    let is_first_write = !assigned.contains(&destination.local);
                    assigned.insert(destination.local);
                    if is_first_write {
                        let original_destination = destination.clone();
                        let tmp_local = body.locals.push(LocalDecl {
                            ty: pointee_ty,
                            kind: LocalKind::Temp,
                            mutable: true,
                            name: None,
                            span: term.span,
                        });
                        body.escape_locals.push(false);
                        *destination = Place::from_local(tmp_local);

                        let original_target = *target;
                        let init_block = body.basic_blocks.push(BasicBlockData {
                            note: Some("escape-init-call-destination".into()),
                            statements: vec![Statement {
                                kind: StatementKind::Assign(
                                    original_destination,
                                    Rvalue::Use(Operand::copy_with(
                                        Place::from_local(tmp_local),
                                        CopyModifiers {
                                            init: true,
                                            take: true,
                                        },
                                    )),
                                ),
                                span: term.span,
                            }],
                            terminator: Some(Terminator {
                                kind: TerminatorKind::Goto {
                                    target: original_target,
                                },
                                span: term.span,
                            }),
                        });
                        *target = init_block;
                    }
                }
            }
            body.basic_blocks[bb].terminator = Some(term);
        }
    }

    fn compute_heapified_may_assigned_in<'ctx>(
        body: &Body<'ctx>,
        heapified: &[Option<Ty<'ctx>>],
    ) -> IndexVec<BasicBlockId, FxHashSet<LocalId>> {
        let mut in_sets: IndexVec<BasicBlockId, FxHashSet<LocalId>> =
            IndexVec::from(vec![FxHashSet::default(); body.basic_blocks.len()]);
        let mut out_sets: IndexVec<BasicBlockId, FxHashSet<LocalId>> =
            IndexVec::from(vec![FxHashSet::default(); body.basic_blocks.len()]);

        let preds = body.predecessors();
        let succs = build_successors(body);
        let mut worklist: Vec<BasicBlockId> = body.basic_blocks.indices().collect();

        while let Some(bb) = worklist.pop() {
            let mut new_in = FxHashSet::default();
            for &pred in &preds[bb] {
                for &local in &out_sets[pred] {
                    new_in.insert(local);
                }
            }

            let mut new_out = new_in.clone();
            let block = &body.basic_blocks[bb];
            for stmt in &block.statements {
                apply_heapified_statement_def(stmt, heapified, &mut new_out);
            }
            if let Some(term) = &block.terminator {
                apply_heapified_terminator_def(&term.kind, heapified, &mut new_out);
            }

            let changed = new_in != in_sets[bb] || new_out != out_sets[bb];
            if changed {
                in_sets[bb] = new_in;
                out_sets[bb] = new_out;
                for &succ in &succs[bb] {
                    worklist.push(succ);
                }
            }
        }

        in_sets
    }

    fn apply_heapified_statement_def<'ctx>(
        stmt: &Statement<'ctx>,
        heapified: &[Option<Ty<'ctx>>],
        assigned: &mut FxHashSet<LocalId>,
    ) {
        match &stmt.kind {
            StatementKind::StorageLive(local) => {
                if heapified.get(local.index()).and_then(|ty| *ty).is_some() {
                    assigned.remove(local);
                }
            }
            StatementKind::Assign(destination, _) => {
                if heapified_direct_deref_pointee_ty(destination, heapified).is_some() {
                    assigned.insert(destination.local);
                }
            }
            _ => {}
        }
    }

    fn apply_heapified_terminator_def<'ctx>(
        term: &TerminatorKind<'ctx>,
        heapified: &[Option<Ty<'ctx>>],
        assigned: &mut FxHashSet<LocalId>,
    ) {
        if let TerminatorKind::Call { destination, .. } = term {
            if heapified_direct_deref_pointee_ty(destination, heapified).is_some() {
                assigned.insert(destination.local);
            }
        }
    }

    fn build_successors(body: &Body<'_>) -> IndexVec<BasicBlockId, Vec<BasicBlockId>> {
        let mut succs: IndexVec<BasicBlockId, Vec<BasicBlockId>> =
            IndexVec::from(vec![Vec::new(); body.basic_blocks.len()]);
        for (bb, data) in body.basic_blocks.iter_enumerated() {
            if let Some(term) = &data.terminator {
                succs[bb] = term.kind.successors();
            }
        }
        succs
    }

    fn heapified_direct_deref_pointee_ty<'ctx>(
        place: &Place<'ctx>,
        heapified: &[Option<Ty<'ctx>>],
    ) -> Option<Ty<'ctx>> {
        if place.projection.len() != 1 || !matches!(place.projection[0], PlaceElem::Deref) {
            return None;
        }
        heapified
            .get(place.local.index())
            .and_then(|item| item.as_ref().copied())
    }

    fn rewrite_statement<'ctx>(
        stmt: &mut Statement<'ctx>,
        heapified: &[Option<Ty<'ctx>>],
        param_replacements: &[Option<LocalId>],
    ) {
        match &mut stmt.kind {
            StatementKind::SourceScope(_)
            | StatementKind::StorageLive(_)
            | StatementKind::SetInitialized(_) => {}
            StatementKind::Assign(place, rvalue) => {
                rewrite_place(place, heapified, param_replacements);
                rewrite_rvalue(rvalue, heapified, param_replacements);
            }
            StatementKind::SetDiscriminant { place, .. } => {
                // Enum aggregate lowering runs before escape analysis. Once an
                // address-taken enum local is heapified, its already-lowered tag
                // write must target the pointee just like an ordinary assignment.
                rewrite_place(place, heapified, param_replacements);
            }
            StatementKind::KeepAlive(operand) => {
                rewrite_operand(operand, heapified, param_replacements)
            }
            StatementKind::GcSafepoint(_) | StatementKind::Nop => {}
        }
    }

    fn rewrite_rvalue<'ctx>(
        rvalue: &mut Rvalue<'ctx>,
        heapified: &[Option<Ty<'ctx>>],
        param_replacements: &[Option<LocalId>],
    ) {
        match rvalue {
            Rvalue::Use(op) => rewrite_operand(op, heapified, param_replacements),
            Rvalue::UnaryOp { operand, .. } => {
                rewrite_operand(operand, heapified, param_replacements)
            }
            Rvalue::BinaryOp { lhs, rhs, .. } => {
                rewrite_operand(lhs, heapified, param_replacements);
                rewrite_operand(rhs, heapified, param_replacements);
            }
            Rvalue::Cast { operand, .. } => rewrite_operand(operand, heapified, param_replacements),
            Rvalue::Ref { place, .. } => rewrite_place(place, heapified, param_replacements),
            Rvalue::Discriminant { place } => rewrite_place(place, heapified, param_replacements),
            Rvalue::Aggregate { fields, .. } => {
                for field in fields.iter_mut() {
                    rewrite_operand(field, heapified, param_replacements);
                }
            }
            Rvalue::Repeat { operand, .. } => {
                rewrite_operand(operand, heapified, param_replacements);
            }
            Rvalue::Alloc { .. } | Rvalue::Zeroed { .. } => {}
        }
    }

    fn rewrite_operand<'ctx>(
        operand: &mut Operand<'ctx>,
        heapified: &[Option<Ty<'ctx>>],
        param_replacements: &[Option<LocalId>],
    ) {
        match operand {
            Operand::Copy(place) | Operand::Move(place) | Operand::CopyWith(place, _) => {
                rewrite_place(place, heapified, param_replacements)
            }
            Operand::Constant(_) => {}
        }
    }

    fn rewrite_terminator<'ctx>(
        term: &mut crate::mir::Terminator<'ctx>,
        heapified: &[Option<Ty<'ctx>>],
        param_replacements: &[Option<LocalId>],
    ) {
        match &mut term.kind {
            TerminatorKind::SwitchInt { discr, .. } => {
                rewrite_operand(discr, heapified, param_replacements)
            }
            TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } => {
                rewrite_operand(func, heapified, param_replacements);
                for arg in args {
                    rewrite_operand(arg, heapified, param_replacements);
                }
                rewrite_place(destination, heapified, param_replacements);
            }
            TerminatorKind::Yield {
                value, resume_arg, ..
            } => {
                rewrite_operand(value, heapified, param_replacements);
                rewrite_place(resume_arg, heapified, param_replacements);
            }
            _ => {}
        }
    }

    fn rewrite_place<'ctx>(
        place: &mut Place<'ctx>,
        heapified: &[Option<Ty<'ctx>>],
        param_replacements: &[Option<LocalId>],
    ) {
        if let Some(local) = param_replacements
            .get(place.local.index())
            .and_then(|item| *item)
        {
            place.local = local;
        }

        if heapified
            .get(place.local.index())
            .and_then(|item| *item)
            .is_none()
        {
            return;
        }
        place.projection.insert(0, PlaceElem::Deref);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        hir::Mutability,
        mir::{
            AggregateKind, BasicBlockData, CallUnwindAction, CastKind, Constant, ConstantKind,
            LocalDecl, LocalKind, MirPhase, Operand, Place, PlaceElem, Rvalue, Statement,
            StatementKind, Terminator, TerminatorKind,
            test_support::{minimal_body, push_temp, with_test_gcx},
        },
        sema::models::{GenericArguments, Ty, TyKind},
        thir::FieldIndex,
    };
    use index_vec::IndexVec;

    fn push_parameter<'ctx>(body: &mut Body<'ctx>, ty: Ty<'ctx>) -> LocalId {
        let span = body.locals[body.return_local].span;
        body.escape_locals.push(false);
        body.locals.push(LocalDecl {
            ty,
            kind: LocalKind::Param,
            mutable: false,
            name: None,
            span,
        })
    }

    fn push_user<'ctx>(body: &mut Body<'ctx>, ty: Ty<'ctx>) -> LocalId {
        let span = body.locals[body.return_local].span;
        body.escape_locals.push(false);
        body.locals.push(LocalDecl {
            ty,
            kind: LocalKind::User,
            mutable: true,
            name: None,
            span,
        })
    }

    fn reference_ty<'ctx>(gcx: Gcx<'ctx>, ty: Ty<'ctx>) -> Ty<'ctx> {
        Ty::new(TyKind::Reference(ty, Mutability::Immutable), gcx)
    }

    fn pointer_ty<'ctx>(gcx: Gcx<'ctx>, ty: Ty<'ctx>) -> Ty<'ctx> {
        Ty::new(TyKind::Pointer(ty, Mutability::Immutable), gcx)
    }

    fn tuple_ty<'ctx>(gcx: Gcx<'ctx>, fields: Vec<Ty<'ctx>>) -> Ty<'ctx> {
        Ty::new(
            TyKind::Tuple(gcx.store.interners.intern_ty_list(fields)),
            gcx,
        )
    }

    fn unit_operand(gcx: Gcx<'_>) -> Operand<'_> {
        Operand::Constant(Constant {
            ty: gcx.types.void,
            value: ConstantKind::Unit,
        })
    }

    fn bool_operand(gcx: Gcx<'_>, value: bool) -> Operand<'_> {
        Operand::Constant(Constant {
            ty: gcx.types.bool,
            value: ConstantKind::Bool(value),
        })
    }

    fn return_block(body: &mut Body<'_>) -> BasicBlockId {
        let span = body.locals[body.return_local].span;
        body.basic_blocks.push(BasicBlockData {
            note: Some("return".into()),
            statements: Vec::new(),
            terminator: Some(Terminator {
                kind: TerminatorKind::Return,
                span,
            }),
        })
    }

    fn placement_with_effects<'ctx>(
        gcx: Gcx<'ctx>,
        body: &Body<'ctx>,
        params: &[ParamEscapeSummary],
    ) -> EscapePlacement {
        EscapeGraph::build(gcx, body, AnalysisMode::FixedEffects { params })
            .unwrap_or_else(|_| panic!("escape graph"))
            .placement()
    }

    fn summary_with_effects<'ctx>(
        gcx: Gcx<'ctx>,
        body: &Body<'ctx>,
        params: &[ParamEscapeSummary],
    ) -> InstanceEscapeSummary {
        EscapeGraph::build(gcx, body, AnalysisMode::FixedEffects { params })
            .unwrap_or_else(|_| panic!("escape graph"))
            .summary()
    }

    #[test]
    fn concrete_callee_summary_changes_placement() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let span = body.locals[body.return_local].span;
            let value = push_user(&mut body, gcx.types.int64);
            let reference = push_temp(&mut body, reference_ty(gcx, gcx.types.int64));
            let call_result = push_temp(&mut body, gcx.types.void);
            let target = return_block(&mut body);
            body.basic_blocks[body.start_block]
                .statements
                .push(Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(reference),
                        Rvalue::Ref {
                            mutable: false,
                            place: Place::from_local(value),
                        },
                    ),
                    span,
                });
            body.basic_blocks[body.start_block].terminator = Some(Terminator {
                kind: TerminatorKind::Call {
                    func: unit_operand(gcx),
                    args: vec![Operand::Copy(Place::from_local(reference))],
                    devirt_hint: None,
                    destination: Place::from_local(call_result),
                    target,
                    unwind: CallUnwindAction::Terminate,
                },
                span,
            });

            let noncapturing = placement_with_effects(
                gcx,
                &body,
                &[ParamEscapeSummary {
                    heap_capture: false,
                    return_deref: None,
                }],
            );
            let capturing = placement_with_effects(
                gcx,
                &body,
                &[ParamEscapeSummary {
                    heap_capture: true,
                    return_deref: None,
                }],
            );

            assert!(!noncapturing.heap_locals.contains(&value));
            assert!(capturing.heap_locals.contains(&value));
        });
    }

    #[test]
    fn summaries_record_return_dereference_depth() {
        with_test_gcx(|gcx| {
            let ref_ty = reference_ty(gcx, gcx.types.uint8);

            let mut direct = minimal_body(gcx);
            direct.locals[direct.return_local].ty = ref_ty;
            let parameter = push_parameter(&mut direct, ref_ty);
            let span = direct.locals[direct.return_local].span;
            direct.basic_blocks[direct.start_block]
                .statements
                .push(Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(direct.return_local),
                        Rvalue::Use(Operand::Copy(Place::from_local(parameter))),
                    ),
                    span,
                });
            assert_eq!(
                summary_with_effects(gcx, &direct, &[]).params[0],
                ParamEscapeSummary {
                    heap_capture: false,
                    return_deref: Some(0),
                }
            );

            let mut loaded = minimal_body(gcx);
            loaded.locals[loaded.return_local].ty = ref_ty;
            let nested_ref_ty = reference_ty(gcx, ref_ty);
            let parameter = push_parameter(&mut loaded, nested_ref_ty);
            let span = loaded.locals[loaded.return_local].span;
            loaded.basic_blocks[loaded.start_block]
                .statements
                .push(Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(loaded.return_local),
                        Rvalue::Use(Operand::Copy(Place {
                            local: parameter,
                            projection: vec![PlaceElem::Deref],
                        })),
                    ),
                    span,
                });
            assert_eq!(
                summary_with_effects(gcx, &loaded, &[]).params[0],
                ParamEscapeSummary {
                    heap_capture: false,
                    return_deref: Some(1),
                }
            );
        });
    }

    #[test]
    fn branch_join_propagates_all_reaching_references() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let span = body.locals[body.return_local].span;
            let ref_ty = reference_ty(gcx, gcx.types.int64);
            let left_value = push_user(&mut body, gcx.types.int64);
            let right_value = push_user(&mut body, gcx.types.int64);
            let left_ref = push_temp(&mut body, ref_ty);
            let right_ref = push_temp(&mut body, ref_ty);
            let joined = push_temp(&mut body, ref_ty);
            let call_result = push_temp(&mut body, gcx.types.void);
            let target = return_block(&mut body);
            let merge = body.basic_blocks.push(BasicBlockData {
                note: Some("merge".into()),
                statements: Vec::new(),
                terminator: Some(Terminator {
                    kind: TerminatorKind::Call {
                        func: unit_operand(gcx),
                        args: vec![Operand::Copy(Place::from_local(joined))],
                        devirt_hint: None,
                        destination: Place::from_local(call_result),
                        target,
                        unwind: CallUnwindAction::Terminate,
                    },
                    span,
                }),
            });
            let left = body.basic_blocks.push(BasicBlockData {
                note: Some("left".into()),
                statements: vec![Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(joined),
                        Rvalue::Use(Operand::Copy(Place::from_local(left_ref))),
                    ),
                    span,
                }],
                terminator: Some(Terminator {
                    kind: TerminatorKind::Goto { target: merge },
                    span,
                }),
            });
            let right = body.basic_blocks.push(BasicBlockData {
                note: Some("right".into()),
                statements: vec![Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(joined),
                        Rvalue::Use(Operand::Copy(Place::from_local(right_ref))),
                    ),
                    span,
                }],
                terminator: Some(Terminator {
                    kind: TerminatorKind::Goto { target: merge },
                    span,
                }),
            });
            body.basic_blocks[body.start_block].statements.extend([
                Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(left_ref),
                        Rvalue::Ref {
                            mutable: false,
                            place: Place::from_local(left_value),
                        },
                    ),
                    span,
                },
                Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(right_ref),
                        Rvalue::Ref {
                            mutable: false,
                            place: Place::from_local(right_value),
                        },
                    ),
                    span,
                },
            ]);
            body.basic_blocks[body.start_block].terminator = Some(Terminator {
                kind: TerminatorKind::SwitchInt {
                    discr: bool_operand(gcx, true),
                    targets: vec![(0, left)],
                    otherwise: right,
                },
                span,
            });

            let placement = placement_with_effects(
                gcx,
                &body,
                &[ParamEscapeSummary {
                    heap_capture: true,
                    return_deref: None,
                }],
            );
            assert!(placement.heap_locals.contains(&left_value));
            assert!(placement.heap_locals.contains(&right_value));
        });
    }

    #[test]
    fn call_destinations_distinguish_cleanup_and_projected_results() {
        with_test_gcx(|gcx| {
            let ref_ty = reference_ty(gcx, gcx.types.int64);
            let return_effect = [ParamEscapeSummary {
                heap_capture: false,
                return_deref: Some(0),
            }];

            let mut cleanup_body = minimal_body(gcx);
            cleanup_body.locals[cleanup_body.return_local].ty = ref_ty;
            let span = cleanup_body.locals[cleanup_body.return_local].span;
            let stale_value = push_user(&mut cleanup_body, gcx.types.int64);
            let returned_value = push_user(&mut cleanup_body, gcx.types.int64);
            let destination = push_temp(&mut cleanup_body, ref_ty);
            let argument = push_temp(&mut cleanup_body, ref_ty);
            let normal = cleanup_body.basic_blocks.push(BasicBlockData {
                note: Some("normal".into()),
                statements: vec![Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(cleanup_body.return_local),
                        Rvalue::Use(Operand::Copy(Place::from_local(destination))),
                    ),
                    span,
                }],
                terminator: Some(Terminator {
                    kind: TerminatorKind::Return,
                    span,
                }),
            });
            let cleanup = cleanup_body.basic_blocks.push(BasicBlockData {
                note: Some("cleanup".into()),
                statements: vec![Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(cleanup_body.return_local),
                        Rvalue::Use(Operand::Copy(Place::from_local(destination))),
                    ),
                    span,
                }],
                terminator: Some(Terminator {
                    kind: TerminatorKind::Return,
                    span,
                }),
            });
            cleanup_body.basic_blocks[cleanup_body.start_block]
                .statements
                .extend([
                    Statement {
                        kind: StatementKind::Assign(
                            Place::from_local(destination),
                            Rvalue::Ref {
                                mutable: false,
                                place: Place::from_local(stale_value),
                            },
                        ),
                        span,
                    },
                    Statement {
                        kind: StatementKind::Assign(
                            Place::from_local(argument),
                            Rvalue::Ref {
                                mutable: false,
                                place: Place::from_local(returned_value),
                            },
                        ),
                        span,
                    },
                ]);
            cleanup_body.basic_blocks[cleanup_body.start_block].terminator = Some(Terminator {
                kind: TerminatorKind::Call {
                    func: unit_operand(gcx),
                    args: vec![Operand::Copy(Place::from_local(argument))],
                    devirt_hint: None,
                    destination: Place::from_local(destination),
                    target: normal,
                    unwind: CallUnwindAction::Cleanup(cleanup),
                },
                span,
            });
            let placement = placement_with_effects(gcx, &cleanup_body, &return_effect);
            assert!(!placement.heap_locals.contains(&stale_value));
            assert!(placement.heap_locals.contains(&returned_value));

            let mut projected_body = minimal_body(gcx);
            let aggregate_ty = tuple_ty(gcx, vec![ref_ty]);
            projected_body.locals[projected_body.return_local].ty = aggregate_ty;
            let span = projected_body.locals[projected_body.return_local].span;
            let existing_value = push_user(&mut projected_body, gcx.types.int64);
            let returned_value = push_user(&mut projected_body, gcx.types.int64);
            let aggregate = push_temp(&mut projected_body, aggregate_ty);
            let argument = push_temp(&mut projected_body, ref_ty);
            let target = projected_body.basic_blocks.push(BasicBlockData {
                note: Some("return aggregate".into()),
                statements: vec![Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(projected_body.return_local),
                        Rvalue::Use(Operand::Copy(Place::from_local(aggregate))),
                    ),
                    span,
                }],
                terminator: Some(Terminator {
                    kind: TerminatorKind::Return,
                    span,
                }),
            });
            projected_body.basic_blocks[projected_body.start_block]
                .statements
                .extend([
                    Statement {
                        kind: StatementKind::Assign(
                            Place {
                                local: aggregate,
                                projection: vec![PlaceElem::Field(FieldIndex::from_raw(0), ref_ty)],
                            },
                            Rvalue::Ref {
                                mutable: false,
                                place: Place::from_local(existing_value),
                            },
                        ),
                        span,
                    },
                    Statement {
                        kind: StatementKind::Assign(
                            Place::from_local(argument),
                            Rvalue::Ref {
                                mutable: false,
                                place: Place::from_local(returned_value),
                            },
                        ),
                        span,
                    },
                ]);
            projected_body.basic_blocks[projected_body.start_block].terminator = Some(Terminator {
                kind: TerminatorKind::Call {
                    func: unit_operand(gcx),
                    args: vec![Operand::Copy(Place::from_local(argument))],
                    devirt_hint: None,
                    destination: Place {
                        local: aggregate,
                        projection: vec![PlaceElem::Field(FieldIndex::from_raw(0), ref_ty)],
                    },
                    target,
                    unwind: CallUnwindAction::Terminate,
                },
                span,
            });
            let placement = placement_with_effects(gcx, &projected_body, &return_effect);
            assert!(placement.heap_locals.contains(&existing_value));
            assert!(placement.heap_locals.contains(&returned_value));
        });
    }

    #[test]
    fn moves_and_storage_live_kill_stale_provenance() {
        with_test_gcx(|gcx| {
            let ref_ty = reference_ty(gcx, gcx.types.int64);
            let effect = [ParamEscapeSummary {
                heap_capture: true,
                return_deref: None,
            }];

            let mut moved_body = minimal_body(gcx);
            let span = moved_body.locals[moved_body.return_local].span;
            let first_value = push_user(&mut moved_body, gcx.types.int64);
            let replacement_value = push_user(&mut moved_body, gcx.types.int64);
            let source = push_temp(&mut moved_body, ref_ty);
            let moved = push_temp(&mut moved_body, ref_ty);
            let result = push_temp(&mut moved_body, gcx.types.void);
            let target = return_block(&mut moved_body);
            moved_body.basic_blocks[moved_body.start_block]
                .statements
                .extend([
                    Statement {
                        kind: StatementKind::Assign(
                            Place::from_local(source),
                            Rvalue::Ref {
                                mutable: false,
                                place: Place::from_local(first_value),
                            },
                        ),
                        span,
                    },
                    Statement {
                        kind: StatementKind::Assign(
                            Place::from_local(moved),
                            Rvalue::Use(Operand::Move(Place::from_local(source))),
                        ),
                        span,
                    },
                    Statement {
                        kind: StatementKind::Assign(
                            Place::from_local(source),
                            Rvalue::Ref {
                                mutable: false,
                                place: Place::from_local(replacement_value),
                            },
                        ),
                        span,
                    },
                ]);
            moved_body.basic_blocks[moved_body.start_block].terminator = Some(Terminator {
                kind: TerminatorKind::Call {
                    func: unit_operand(gcx),
                    args: vec![Operand::Copy(Place::from_local(moved))],
                    devirt_hint: None,
                    destination: Place::from_local(result),
                    target,
                    unwind: CallUnwindAction::Terminate,
                },
                span,
            });
            let placement = placement_with_effects(gcx, &moved_body, &effect);
            assert!(placement.heap_locals.contains(&first_value));
            assert!(!placement.heap_locals.contains(&replacement_value));

            let mut rebound_body = minimal_body(gcx);
            let span = rebound_body.locals[rebound_body.return_local].span;
            let value = push_user(&mut rebound_body, gcx.types.int64);
            let reference = push_temp(&mut rebound_body, ref_ty);
            let result = push_temp(&mut rebound_body, gcx.types.void);
            let target = return_block(&mut rebound_body);
            rebound_body.basic_blocks[rebound_body.start_block]
                .statements
                .extend([
                    Statement {
                        kind: StatementKind::Assign(
                            Place::from_local(reference),
                            Rvalue::Ref {
                                mutable: false,
                                place: Place::from_local(value),
                            },
                        ),
                        span,
                    },
                    Statement {
                        kind: StatementKind::StorageLive(reference),
                        span,
                    },
                ]);
            rebound_body.basic_blocks[rebound_body.start_block].terminator = Some(Terminator {
                kind: TerminatorKind::Call {
                    func: unit_operand(gcx),
                    args: vec![Operand::Copy(Place::from_local(reference))],
                    devirt_hint: None,
                    destination: Place::from_local(result),
                    target,
                    unwind: CallUnwindAction::Terminate,
                },
                span,
            });
            assert!(
                !placement_with_effects(gcx, &rebound_body, &effect)
                    .heap_locals
                    .contains(&value)
            );
        });
    }

    #[test]
    fn aggregates_projected_fields_and_raw_casts_preserve_provenance() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let span = body.locals[body.return_local].span;
            let ref_ty = reference_ty(gcx, gcx.types.uint8);
            let ptr_ty = pointer_ty(gcx, gcx.types.uint8);
            let aggregate_ty = tuple_ty(gcx, vec![ptr_ty]);
            let projected_value = push_user(&mut body, gcx.types.uint8);
            let aggregate_value = push_user(&mut body, gcx.types.uint8);
            let projected_ref = push_temp(&mut body, ref_ty);
            let aggregate_ref = push_temp(&mut body, ref_ty);
            let projected_ptr = push_temp(&mut body, ptr_ty);
            let aggregate_ptr = push_temp(&mut body, ptr_ty);
            let projected = push_temp(&mut body, aggregate_ty);
            let aggregate = push_temp(&mut body, aggregate_ty);
            let first_result = push_temp(&mut body, gcx.types.void);
            let second_result = push_temp(&mut body, gcx.types.void);
            let target = return_block(&mut body);
            let second_call = body.basic_blocks.push(BasicBlockData {
                note: Some("capture aggregate".into()),
                statements: Vec::new(),
                terminator: Some(Terminator {
                    kind: TerminatorKind::Call {
                        func: unit_operand(gcx),
                        args: vec![Operand::Copy(Place::from_local(aggregate))],
                        devirt_hint: None,
                        destination: Place::from_local(second_result),
                        target,
                        unwind: CallUnwindAction::Terminate,
                    },
                    span,
                }),
            });
            body.basic_blocks[body.start_block].statements.extend([
                Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(projected_ref),
                        Rvalue::Ref {
                            mutable: false,
                            place: Place::from_local(projected_value),
                        },
                    ),
                    span,
                },
                Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(projected_ptr),
                        Rvalue::Cast {
                            operand: Operand::Copy(Place::from_local(projected_ref)),
                            ty: ptr_ty,
                            kind: CastKind::Pointer,
                        },
                    ),
                    span,
                },
                Statement {
                    kind: StatementKind::Assign(
                        Place {
                            local: projected,
                            projection: vec![PlaceElem::Field(FieldIndex::from_raw(0), ptr_ty)],
                        },
                        Rvalue::Use(Operand::Copy(Place::from_local(projected_ptr))),
                    ),
                    span,
                },
                Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(aggregate_ref),
                        Rvalue::Ref {
                            mutable: false,
                            place: Place::from_local(aggregate_value),
                        },
                    ),
                    span,
                },
                Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(aggregate_ptr),
                        Rvalue::Cast {
                            operand: Operand::Copy(Place::from_local(aggregate_ref)),
                            ty: ptr_ty,
                            kind: CastKind::Numeric,
                        },
                    ),
                    span,
                },
                Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(aggregate),
                        Rvalue::Aggregate {
                            kind: AggregateKind::Tuple,
                            fields: IndexVec::from_vec(vec![Operand::Move(Place::from_local(
                                aggregate_ptr,
                            ))]),
                        },
                    ),
                    span,
                },
            ]);
            body.basic_blocks[body.start_block].terminator = Some(Terminator {
                kind: TerminatorKind::Call {
                    func: unit_operand(gcx),
                    args: vec![Operand::Copy(Place::from_local(projected))],
                    devirt_hint: None,
                    destination: Place::from_local(first_result),
                    target: second_call,
                    unwind: CallUnwindAction::Terminate,
                },
                span,
            });

            let placement = placement_with_effects(
                gcx,
                &body,
                &[ParamEscapeSummary {
                    heap_capture: true,
                    return_deref: None,
                }],
            );
            assert!(placement.heap_locals.contains(&projected_value));
            assert!(placement.heap_locals.contains(&aggregate_value));
        });
    }

    #[test]
    fn projected_capture_uses_weighted_flow_not_field_type_pruning() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let span = body.locals[body.return_local].span;
            let ptr_ty = pointer_ty(gcx, gcx.types.int64);
            let ref_ty = reference_ty(gcx, gcx.types.int64);
            let capture_ty = tuple_ty(gcx, vec![ref_ty]);
            let allocation = push_temp(&mut body, ptr_ty);
            let reference = push_temp(&mut body, ref_ty);
            let capture = push_temp(&mut body, capture_ty);
            let result = push_temp(&mut body, gcx.types.void);
            let target = return_block(&mut body);
            body.basic_blocks[body.start_block].statements.extend([
                Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(allocation),
                        Rvalue::Alloc {
                            ty: gcx.types.int64,
                        },
                    ),
                    span,
                },
                Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(reference),
                        Rvalue::Ref {
                            mutable: false,
                            place: Place {
                                local: allocation,
                                projection: vec![PlaceElem::Deref],
                            },
                        },
                    ),
                    span,
                },
                // Closure capture projections currently carry the captured
                // pointee type. The operand still carries a reference, so the
                // zero-weight assignment edge must not be pruned by this
                // annotation.
                Statement {
                    kind: StatementKind::Assign(
                        Place {
                            local: capture,
                            projection: vec![PlaceElem::Field(
                                FieldIndex::from_raw(0),
                                gcx.types.int64,
                            )],
                        },
                        Rvalue::Use(Operand::Copy(Place::from_local(reference))),
                    ),
                    span,
                },
            ]);
            body.basic_blocks[body.start_block].terminator = Some(Terminator {
                kind: TerminatorKind::Call {
                    func: unit_operand(gcx),
                    args: vec![Operand::Move(Place::from_local(capture))],
                    devirt_hint: None,
                    destination: Place::from_local(result),
                    target,
                    unwind: CallUnwindAction::Terminate,
                },
                span,
            });

            let placement = placement_with_effects(
                gcx,
                &body,
                &[ParamEscapeSummary {
                    heap_capture: true,
                    return_deref: None,
                }],
            );
            assert!(placement.escaping_alloc_sites.contains(&AllocationSite {
                block: body.start_block,
                statement: 0,
            }));
        });
    }

    #[test]
    fn scalar_loads_and_stores_do_not_capture_their_reference() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let span = body.locals[body.return_local].span;
            let reference = push_parameter(&mut body, reference_ty(gcx, gcx.types.int64));
            let loaded = push_temp(&mut body, gcx.types.int64);
            let pointee = Place {
                local: reference,
                projection: vec![PlaceElem::Deref],
            };
            body.basic_blocks[body.start_block].statements.extend([
                Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(loaded),
                        Rvalue::Use(Operand::Copy(pointee.clone())),
                    ),
                    span,
                },
                Statement {
                    kind: StatementKind::Assign(
                        pointee,
                        Rvalue::Use(Operand::Copy(Place::from_local(loaded))),
                    ),
                    span,
                },
            ]);

            assert_eq!(
                summary_with_effects(gcx, &body, &[]).params[0],
                ParamEscapeSummary::default()
            );
        });
    }

    #[test]
    fn allocation_sites_sharing_a_local_receive_independent_decisions() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let span = body.locals[body.return_local].span;
            let pointer = push_temp(&mut body, pointer_ty(gcx, gcx.types.int64));
            let result = push_temp(&mut body, gcx.types.void);
            let target = return_block(&mut body);
            body.basic_blocks[body.start_block].statements.extend([
                Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(pointer),
                        Rvalue::Alloc {
                            ty: gcx.types.int64,
                        },
                    ),
                    span,
                },
                Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(pointer),
                        Rvalue::Alloc {
                            ty: gcx.types.int64,
                        },
                    ),
                    span,
                },
            ]);
            body.basic_blocks[body.start_block].terminator = Some(Terminator {
                kind: TerminatorKind::Call {
                    func: unit_operand(gcx),
                    args: vec![Operand::Copy(Place::from_local(pointer))],
                    devirt_hint: None,
                    destination: Place::from_local(result),
                    target,
                    unwind: CallUnwindAction::Terminate,
                },
                span,
            });

            let placement = placement_with_effects(
                gcx,
                &body,
                &[ParamEscapeSummary {
                    heap_capture: true,
                    return_deref: None,
                }],
            );
            let first = AllocationSite {
                block: body.start_block,
                statement: 0,
            };
            let second = AllocationSite {
                block: body.start_block,
                statement: 1,
            };
            assert!(!placement.escaping_alloc_sites.contains(&first));
            assert!(placement.escaping_alloc_sites.contains(&second));

            allocation_rewrite::promote_allocation_sites(
                gcx,
                &mut body,
                &placement.escaping_alloc_sites,
                &placement.allocation_keepalive_blocks,
            )
            .unwrap_or_else(|_| panic!("allocation rewrite"));
            assert_eq!(
                body.basic_blocks
                    .iter()
                    .flat_map(|block| &block.statements)
                    .filter(|statement| matches!(
                        statement.kind,
                        StatementKind::Assign(_, Rvalue::Alloc { .. })
                    ))
                    .count(),
                1
            );
        });
    }

    #[test]
    fn shared_cleanup_preserves_returned_allocation_provenance() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let span = body.locals[body.return_local].span;
            let ptr_ty = pointer_ty(gcx, gcx.types.int64);
            let return_ty = tuple_ty(gcx, vec![ptr_ty]);
            body.locals[body.return_local].ty = return_ty;
            let pointer = push_temp(&mut body, ptr_ty);
            let dead_move = push_temp(&mut body, ptr_ty);
            body.basic_blocks[body.start_block].statements.extend([
                Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(pointer),
                        Rvalue::Alloc {
                            ty: gcx.types.int64,
                        },
                    ),
                    span,
                },
                // Aggregate lowering can leave a dead move before the actual
                // projected return store. Shared cleanup must discard it
                // before flow-sensitive provenance consumes the source.
                Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(dead_move),
                        Rvalue::Use(Operand::Move(Place::from_local(pointer))),
                    ),
                    span,
                },
                Statement {
                    kind: StatementKind::Assign(
                        Place {
                            local: body.return_local,
                            projection: vec![PlaceElem::Field(FieldIndex::from_raw(0), ptr_ty)],
                        },
                        Rvalue::Use(Operand::Move(Place::from_local(pointer))),
                    ),
                    span,
                },
            ]);
            body.basic_blocks[body.start_block].terminator = Some(Terminator {
                kind: TerminatorKind::Return,
                span,
            });

            let mut passes: Vec<Box<dyn crate::mir::optimize::MirPass<'_>>> = vec![
                Box::new(crate::mir::optimize::dse::DeadStoreElimination),
                Box::new(crate::mir::optimize::passes::DeadLocalElimination),
            ];
            crate::mir::optimize::run_passes(gcx, &mut body, &mut passes)
                .unwrap_or_else(|_| panic!("shared cleanup"));

            assert!(body.basic_blocks[body.start_block].statements.iter().all(
                |statement| !matches!(
                    &statement.kind,
                    StatementKind::Assign(destination, _)
                        if destination.local == dead_move
                )
            ));
            let placement = placement_with_effects(gcx, &body, &[]);
            assert_eq!(placement.escaping_alloc_sites.len(), 1);
        });
    }

    #[test]
    fn projected_nonescaping_allocation_is_stack_promoted() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let span = body.locals[body.return_local].span;
            let ptr_ty = pointer_ty(gcx, gcx.types.int64);
            let aggregate_ty = tuple_ty(gcx, vec![ptr_ty]);
            let aggregate = push_temp(&mut body, aggregate_ty);
            let destination = Place {
                local: aggregate,
                projection: vec![PlaceElem::Field(FieldIndex::from_raw(0), ptr_ty)],
            };
            body.basic_blocks[body.start_block]
                .statements
                .push(Statement {
                    kind: StatementKind::Assign(
                        destination.clone(),
                        Rvalue::Alloc {
                            ty: gcx.types.int64,
                        },
                    ),
                    span,
                });

            let placement = placement_with_effects(gcx, &body, &[]);
            assert!(placement.escaping_alloc_sites.is_empty());
            allocation_rewrite::promote_allocation_sites(
                gcx,
                &mut body,
                &placement.escaping_alloc_sites,
                &placement.allocation_keepalive_blocks,
            )
            .unwrap_or_else(|_| panic!("allocation rewrite"));
            let statements = &body.basic_blocks[body.start_block].statements;
            assert!(statements.iter().all(|statement| !matches!(
                statement.kind,
                StatementKind::Assign(_, Rvalue::Alloc { .. })
            )));
            assert!(statements.iter().any(|statement| matches!(
                &statement.kind,
                StatementKind::Assign(place, Rvalue::Cast { ty, .. })
                    if place == &destination && *ty == ptr_ty
            )));

            let (zero_index, stack_object) = statements
                .iter()
                .enumerate()
                .find_map(|(index, statement)| match &statement.kind {
                    StatementKind::Assign(place, Rvalue::Zeroed { ty })
                        if *ty == gcx.types.int64 =>
                    {
                        Some((index, place.local))
                    }
                    _ => None,
                })
                .expect("promoted storage is zeroed");
            let (reference_index, stack_reference) = statements
                .iter()
                .enumerate()
                .find_map(|(index, statement)| match &statement.kind {
                    StatementKind::Assign(
                        destination,
                        Rvalue::Ref {
                            place,
                            mutable: true,
                        },
                    ) if place.local == stack_object => Some((index, destination.local)),
                    _ => None,
                })
                .expect("promoted storage publishes a typed reference");
            assert!(zero_index < reference_index);
            assert!(statements.iter().all(|statement| !matches!(
                &statement.kind,
                StatementKind::KeepAlive(Operand::Copy(place))
                    if place.local == stack_reference
            )));
        });
    }

    #[test]
    fn promoted_gc_backing_is_rooted_only_in_alias_live_blocks() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let span = body.locals[body.return_local].span;
            let element_ty = pointer_ty(gcx, gcx.types.int64);
            let allocation_pointer_ty = pointer_ty(gcx, element_ty);
            let pointer = push_temp(&mut body, allocation_pointer_ty);
            let site = AllocationSite {
                block: body.start_block,
                statement: 0,
            };
            body.basic_blocks[body.start_block].statements.extend([
                Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(pointer),
                        Rvalue::Alloc { ty: element_ty },
                    ),
                    span,
                },
                Statement {
                    kind: StatementKind::KeepAlive(Operand::Copy(Place::from_local(pointer))),
                    span,
                },
            ]);
            let finished = return_block(&mut body);
            body.basic_blocks[body.start_block].terminator = Some(Terminator {
                kind: TerminatorKind::Goto { target: finished },
                span,
            });

            let placement = placement_with_effects(gcx, &body, &[]);
            assert!(placement.escaping_alloc_sites.is_empty());
            assert_eq!(
                placement.allocation_keepalive_blocks.get(&site),
                Some(&FxHashSet::from_iter([body.start_block]))
            );
            allocation_rewrite::promote_allocation_sites(
                gcx,
                &mut body,
                &placement.escaping_alloc_sites,
                &placement.allocation_keepalive_blocks,
            )
            .unwrap_or_else(|_| panic!("allocation rewrite"));

            let stack_reference = body.basic_blocks[body.start_block]
                .statements
                .iter()
                .find_map(|statement| match &statement.kind {
                    StatementKind::Assign(
                        destination,
                        Rvalue::Ref {
                            place,
                            mutable: true,
                        },
                    ) if body.locals[place.local].ty == element_ty => Some(destination.local),
                    _ => None,
                })
                .expect("promoted backing has a typed reference");
            assert!(body.basic_blocks[body.start_block].statements.iter().any(
                |statement| matches!(
                    &statement.kind,
                    StatementKind::KeepAlive(Operand::Copy(place))
                        if place.local == stack_reference
                )
            ));
            assert!(
                body.basic_blocks[finished]
                    .statements
                    .iter()
                    .all(|statement| !matches!(
                        &statement.kind,
                        StatementKind::KeepAlive(Operand::Copy(place))
                            if place.local == stack_reference
                    ))
            );
            assert!(body.basic_blocks[body.start_block].statements.iter().any(
                |statement| matches!(
                    &statement.kind,
                    StatementKind::Assign(place, Rvalue::Zeroed { ty })
                        if place.local == stack_reference
                            && *ty == body.locals[stack_reference].ty
                )
            ));
        });
    }

    fn loop_allocation_body<'ctx>(
        gcx: Gcx<'ctx>,
        consume_before_allocation: bool,
    ) -> (Body<'ctx>, AllocationSite) {
        let mut body = minimal_body(gcx);
        let span = body.locals[body.return_local].span;
        let ptr_ty = pointer_ty(gcx, gcx.types.int64);
        let pointer = push_temp(&mut body, ptr_ty);
        let carried = push_temp(&mut body, ptr_ty);
        body.basic_blocks[body.start_block]
            .statements
            .push(Statement {
                kind: StatementKind::Assign(
                    Place::from_local(carried),
                    Rvalue::Alloc {
                        ty: gcx.types.int64,
                    },
                ),
                span,
            });
        let loop_block = body.basic_blocks.push(BasicBlockData {
            note: Some("loop".into()),
            statements: Vec::new(),
            terminator: None,
        });
        body.basic_blocks[body.start_block].terminator = Some(Terminator {
            kind: TerminatorKind::Goto { target: loop_block },
            span,
        });
        if consume_before_allocation {
            body.basic_blocks[loop_block].statements.push(Statement {
                kind: StatementKind::KeepAlive(Operand::Move(Place::from_local(carried))),
                span,
            });
        }
        let statement = body.basic_blocks[loop_block].statements.len();
        body.basic_blocks[loop_block].statements.push(Statement {
            kind: StatementKind::Assign(
                Place::from_local(pointer),
                Rvalue::Alloc {
                    ty: gcx.types.int64,
                },
            ),
            span,
        });
        if !consume_before_allocation {
            body.basic_blocks[loop_block].statements.push(Statement {
                kind: StatementKind::KeepAlive(Operand::Copy(Place::from_local(carried))),
                span,
            });
        }
        body.basic_blocks[loop_block].statements.push(Statement {
            kind: StatementKind::Assign(
                Place::from_local(carried),
                Rvalue::Use(Operand::Copy(Place::from_local(pointer))),
            ),
            span,
        });
        body.basic_blocks[loop_block].terminator = Some(Terminator {
            kind: TerminatorKind::Goto { target: loop_block },
            span,
        });
        (
            body,
            AllocationSite {
                block: loop_block,
                statement,
            },
        )
    }

    #[test]
    fn loop_promotion_only_rejects_overlapping_allocation_instances() {
        with_test_gcx(|gcx| {
            let (overlapping, site) = loop_allocation_body(gcx, false);
            assert!(
                placement_with_effects(gcx, &overlapping, &[])
                    .escaping_alloc_sites
                    .contains(&site)
            );

            let (consumed, site) = loop_allocation_body(gcx, true);
            assert!(
                !placement_with_effects(gcx, &consumed, &[])
                    .escaping_alloc_sites
                    .contains(&site)
            );
        });
    }

    #[test]
    fn async_bridge_heapifies_referents_live_across_yield() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            body.is_async = true;
            let span = body.locals[body.return_local].span;
            let value = push_user(&mut body, gcx.types.int64);
            let reference = push_temp(&mut body, reference_ty(gcx, gcx.types.int64));
            let resume_arg = push_temp(&mut body, gcx.types.void);
            body.basic_blocks[body.start_block]
                .statements
                .push(Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(reference),
                        Rvalue::Ref {
                            mutable: false,
                            place: Place::from_local(value),
                        },
                    ),
                    span,
                });
            let resume = body.basic_blocks.push(BasicBlockData {
                note: Some("resume".into()),
                statements: vec![Statement {
                    kind: StatementKind::KeepAlive(Operand::Copy(Place::from_local(reference))),
                    span,
                }],
                terminator: Some(Terminator {
                    kind: TerminatorKind::Return,
                    span,
                }),
            });
            let cancel_complete = body.basic_blocks.push(BasicBlockData {
                note: Some("cancel complete".into()),
                statements: Vec::new(),
                terminator: Some(Terminator {
                    kind: TerminatorKind::Unreachable,
                    span,
                }),
            });
            let cancel = body.basic_blocks.push(BasicBlockData {
                note: Some("cancel".into()),
                statements: Vec::new(),
                terminator: Some(Terminator {
                    kind: TerminatorKind::Goto {
                        target: cancel_complete,
                    },
                    span,
                }),
            });
            body.basic_blocks[body.start_block].terminator = Some(Terminator {
                kind: TerminatorKind::Yield {
                    value: unit_operand(gcx),
                    resume,
                    resume_arg: Place::from_local(resume_arg),
                    cancel,
                    cancel_complete,
                    unwind: CallUnwindAction::Terminate,
                },
                span,
            });

            let placement = EscapeGraph::build(gcx, &body, AnalysisMode::AsyncBridge)
                .unwrap_or_else(|_| panic!("async escape graph"))
                .placement();
            assert!(placement.heap_locals.contains(&value));
        });
    }

    #[test]
    fn unresolved_and_unknown_calls_are_conservative() {
        with_test_gcx(|gcx| {
            assert_eq!(
                conservative_parameter_effect(gcx, None, 0)
                    .unwrap_or_else(|_| panic!("unknown call effect")),
                ParamEscapeSummary {
                    heap_capture: true,
                    return_deref: Some(0),
                }
            );

            let mut body = minimal_body(gcx);
            let span = body.locals[body.return_local].span;
            let pointer = push_temp(&mut body, pointer_ty(gcx, gcx.types.int64));
            body.basic_blocks[body.start_block]
                .statements
                .push(Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(pointer),
                        Rvalue::Alloc {
                            ty: gcx.types.int64,
                        },
                    ),
                    span,
                });
            body.basic_blocks[body.start_block].terminator = Some(Terminator {
                kind: TerminatorKind::UnresolvedGoto,
                span,
            });
            let placement = placement_with_effects(gcx, &body, &[]);
            assert!(placement.escaping_alloc_sites.contains(&AllocationSite {
                block: body.start_block,
                statement: 0,
            }));
        });
    }

    #[test]
    fn recursive_scc_partition_is_deterministic() {
        let graph = [vec![1], vec![0, 2], Vec::new()];
        let mut tarjan = Tarjan::new(&graph);
        for node in 0..graph.len() {
            if tarjan.indices[node].is_none() {
                tarjan.visit(node);
            }
        }
        assert_eq!(tarjan.components, vec![vec![2], vec![1, 0]]);
    }

    #[test]
    fn heapified_storage_live_allocates_at_the_binding_boundary() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let span = body.locals[body.return_local].span;
            let local = push_user(&mut body, gcx.types.int64);
            body.escape_locals[local.index()] = true;
            let loop_block = body.basic_blocks.push(BasicBlockData {
                note: Some("loop declaration".into()),
                statements: vec![Statement {
                    kind: StatementKind::StorageLive(local),
                    span,
                }],
                terminator: None,
            });
            body.basic_blocks[body.start_block].terminator = Some(Terminator {
                kind: TerminatorKind::Goto { target: loop_block },
                span,
            });
            body.basic_blocks[loop_block].terminator = Some(Terminator {
                kind: TerminatorKind::Goto { target: loop_block },
                span,
            });

            heapify_rewrite::apply_heapified_locals(gcx, &mut body)
                .unwrap_or_else(|_| panic!("heapify rewrite"));
            assert!(body.basic_blocks[body.start_block].statements.iter().all(
                |statement| !matches!(
                    &statement.kind,
                    StatementKind::Assign(place, Rvalue::Alloc { .. }) if place.local == local
                )
            ));
            assert!(matches!(
                &body.basic_blocks[loop_block].statements[0].kind,
                StatementKind::Assign(place, Rvalue::Alloc { ty })
                    if place.local == local && *ty == gcx.types.int64
            ));
        });
    }

    #[test]
    fn finalized_body_guard_is_instance_and_pointer_exact() {
        with_test_gcx(|gcx| {
            let body = minimal_body(gcx);
            let instance = Instance::item(body.owner, GenericArguments::empty());
            assert!(!gcx.is_finalized_instance_mir(instance, &body));

            let finalized = gcx.store.arenas.mir_bodies.alloc(body.clone());
            finalized.phase = MirPhase::Lowered;
            gcx.store
                .instance_mir_bodies
                .borrow_mut()
                .insert(instance, finalized);
            assert!(gcx.is_finalized_instance_mir(instance, finalized));
            assert!(!gcx.is_finalized_instance_mir(instance, &body));
        });
    }
}
