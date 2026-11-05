//! Typed stack-map emission for collecting sites. The live root list is
//! supplied by MIR liveness; this helper never guesses from LLVM temporaries.
use super::*;
use crate::codegen::gc_stack_maps::{self as gc_maps, PendingRootOperand};

#[derive(Clone, Copy)]
pub(super) struct GcRootOperand<'llvm, 'gcx> {
    pub location: PointerValue<'llvm>,
    pub ty: Ty<'gcx>,
    pub storage_deref_depth: u8,
}

/// One physical frame's stable storage plus this branch's existing, more
/// complete MIR liveness/initialization analysis. In particular, preserve its
/// no-result async edges and partial-construction fixes from the native pivot.
pub(super) struct GcStackMapFrame<'llvm, 'gcx> {
    roots: Vec<(mir::LocalId, GcRootOperand<'llvm, 'gcx>)>,
    /// Private working values can promote to SSA. Only a collecting path
    /// publishes their current bytes into the separate addressable root slot.
    spill_sources: FxHashMap<mir::LocalId, (PointerValue<'llvm>, BasicTypeEnum<'llvm>)>,
    liveness: mir::analysis::liveness::LivenessResult,
    /// Defined collector-only bytes, independently of language initialization.
    zeroed_storage: FxHashSet<mir::LocalId>,
    /// Each local with a formed address, and the locals that may hold it. A raw
    /// pointer or span can be the only remaining use of that storage, and the
    /// walker does not follow those into a stack, so its contents stay rooted
    /// exactly while a holder is live. Empty until `publish_address_holders`.
    address_holders: FxHashMap<mir::LocalId, Vec<mir::LocalId>>,
    address_exposed: FxHashSet<mir::LocalId>,
}

/// Locals whose scanner initialization can run at StorageLive instead of entry.
/// Require one marker that dominates every read, write and address formation.
/// Liveness kills the local before that marker, and aliases cannot observe its
/// bytes before it either. Missing/multiple markers and bypass paths retain the
/// conservative entry initialization, including synthetic partial aggregates.
fn storage_live_covers_observations(body: &mir::Body<'_>) -> FxHashSet<mir::LocalId> {
    use mir::{
        StatementKind,
        analysis::{dominators, liveness},
    };
    let mut starts = vec![None; body.locals.len()];
    let mut duplicates = FxHashSet::default();
    for (block, data) in body.basic_blocks.iter_enumerated() {
        for (index, statement) in data.statements.iter().enumerate() {
            if let StatementKind::StorageLive(local) = statement.kind {
                if starts[local.index()].replace((block, index)).is_some() {
                    duplicates.insert(local);
                }
            }
        }
    }
    let mut covered: FxHashSet<_> = body
        .locals
        .iter_enumerated()
        .filter_map(|(local, _)| {
            (starts[local.index()].is_some() && !duplicates.contains(&local)).then_some(local)
        })
        .collect();
    if covered.is_empty() {
        return covered;
    }
    let dominators = dominators::compute_dominators(body);
    liveness::for_each_storage_observation(body, |local, location| {
        let (block, index) = match location {
            liveness::MirLocation::Statement { block, index } => (block, index),
            liveness::MirLocation::Terminator { block } => (block, usize::MAX),
        };
        if let Some((start_block, start_index)) = starts[local.index()] {
            if !dominators.dominates(start_block, block)
                || (start_block == block && start_index >= index)
            {
                covered.remove(&local);
            }
        }
    });
    covered
}

impl<'llvm, 'gcx> Emitter<'llvm, 'gcx> {
    fn enum_constructor_initializes(&self, value: &mir::Rvalue<'gcx>, local: mir::LocalId) -> bool {
        matches!(value, mir::Rvalue::Aggregate { kind, fields }
            if kind.noncollecting_enum_ctor(self.gcx).is_some()
                && fields.iter().all(|field| field.place().is_none_or(|source| source.local != local)))
    }

    /// Synthetic temporaries can lack StorageLive. A single complete,
    /// noncollecting assignment that dominates every observation supplies their
    /// scanner bytes. Keep explicit lifetimes, partial writes, ABI storage and
    /// allocating erased copies on the existing conservative path.
    fn fully_initialized_temporaries(&mut self, body: &mir::Body<'gcx>) -> FxHashSet<mir::LocalId> {
        use mir::{
            StatementKind as S,
            analysis::{dominators, liveness},
        };
        let mut initializers = FxHashMap::default();
        let mut excluded = FxHashSet::default();
        for (block, data) in body.basic_blocks.iter_enumerated() {
            for (index, statement) in data.statements.iter().enumerate() {
                if let S::StorageLive(local) | S::StorageDead(local) = statement.kind {
                    excluded.insert(local);
                }
                let S::Assign(destination, value) = &statement.kind else {
                    continue;
                };
                let local = destination.local;
                if !destination.projection.is_empty()
                    || local == body.return_local
                    || body.locals[local].kind != mir::LocalKind::Temp
                {
                    continue;
                }
                let fully_defined = match value {
                    mir::Rvalue::Use(operand) => {
                        operand.place().is_some_and(|source| source.local != local)
                    }
                    mir::Rvalue::CopyValue { source }
                        if self
                            .gc_copy_layout_nodes_for_ty(self.place_ty(body, source))
                            .is_empty() =>
                    {
                        source.local != local
                    }
                    mir::Rvalue::Repeat {
                        operand, element, ..
                    } if self.gc_copy_layout_nodes_for_ty(*element).is_empty() => {
                        operand.place().is_some_and(|source| source.local != local)
                    }
                    // Complete noncollecting constructors define the tag and
                    // inactive bytes together. Reject a self-read just as for
                    // whole copies; their fields may still observe storage.
                    mir::Rvalue::Aggregate { .. } => {
                        self.enum_constructor_initializes(value, local)
                    }
                    _ => false,
                };
                if !fully_defined || initializers.insert(local, (block, index)).is_some() {
                    excluded.insert(local);
                }
            }
        }
        initializers.retain(|local, _| !excluded.contains(local));
        if initializers.is_empty() {
            return FxHashSet::default();
        }
        let dominators = dominators::compute_dominators(body);
        let mut covered: FxHashSet<_> = initializers.keys().copied().collect();
        liveness::for_each_storage_observation(body, |local, location| {
            let Some(&(init_block, init_index)) = initializers.get(&local) else {
                return;
            };
            let (block, index) = match location {
                liveness::MirLocation::Statement { block, index } => (block, index),
                liveness::MirLocation::Terminator { block } => (block, usize::MAX),
            };
            if !dominators.dominates(init_block, block)
                || (init_block == block && index < init_index)
            {
                covered.remove(&local);
            }
        });
        covered
    }

    /// A whole-slot copy or noncollecting enum constructor needs no scanner
    /// zero immediately before it. Cross only markers or independent private
    /// copies/pointer casts that cannot
    /// collect or observe this slot, within one block.
    /// CopyValue also qualifies when the existing copy recipe proves it cannot
    /// allocate erased payloads. Partial writes and collecting operations keep
    /// their initialization; no source initialization or root maps change.
    fn storage_live_is_fully_initialized(
        &mut self,
        body: &mir::Body<'gcx>,
        location: mir::analysis::liveness::MirLocation,
        local: mir::LocalId,
    ) -> bool {
        use mir::{StatementKind as S, analysis::liveness::MirLocation};
        let MirLocation::Statement { block, index } = location else {
            return false;
        };
        let statements = &body.basic_blocks[block].statements;
        if !matches!(statements[index].kind, S::StorageLive(id) if id == local) {
            return false;
        }
        for statement in &statements[index + 1..] {
            if statement.kind.scanner_copy_marker(local) {
                continue;
            }
            match &statement.kind {
                S::Assign(destination, value)
                    if destination.local == local && destination.projection.is_empty() =>
                {
                    if self.enum_constructor_initializes(value, local) {
                        return true;
                    }
                    let source = match value {
                        mir::Rvalue::Use(operand) => operand.place(),
                        mir::Rvalue::CopyValue { source }
                            if self
                                .gc_copy_layout_nodes_for_ty(self.place_ty(body, source))
                                .is_empty() =>
                        {
                            Some(source)
                        }
                        _ => None,
                    };
                    return source.is_some_and(|source| source.local != local);
                }
                S::Assign(destination, value)
                    if body.locals[local].kind == mir::LocalKind::Temp
                        && local != body.return_local
                        && destination.local != local
                        && destination.local != body.return_local
                        && destination.projection.is_empty()
                        && body.locals[destination.local].kind == mir::LocalKind::Temp =>
                {
                    // Inlined argument setup interleaves independent copies.
                    // A bare Temp destination is its own alloca, never an
                    // indirect ABI slot or a store through an alias. Bare
                    // source loads cannot read this slot indirectly. Reject
                    // all allocating copies, address formation and other work.
                    let source = match value {
                        mir::Rvalue::Use(operand) => operand.place(),
                        mir::Rvalue::CopyValue { source }
                            if self
                                .gc_copy_layout_nodes_for_ty(self.place_ty(body, source))
                                .is_empty() =>
                        {
                            Some(source)
                        }
                        mir::Rvalue::Cast {
                            operand,
                            ty,
                            kind: mir::CastKind::Numeric,
                        } if matches!(ty.kind(), TyKind::Pointer(..))
                            && matches!(
                                self.operand_ty(body, operand).kind(),
                                TyKind::Pointer(..)
                            ) =>
                        {
                            operand.place()
                        }
                        _ => None,
                    };
                    if source
                        .is_some_and(|source| source.local != local && source.projection.is_empty())
                    {
                        continue;
                    }
                    return false;
                }
                _ => return false,
            }
        }
        false
    }

    fn get_gc_poll(&self) -> FunctionValue<'llvm> {
        let function = if let Some(f) = self.module.get_function("__gc__poll") {
            f
        } else {
            let fn_ty = self.context.void_type().fn_type(&[], false);
            self.module
                .add_function("__gc__poll", fn_ty, Some(Linkage::External))
        };
        add_llvm_enum_function_attribute(self.context, function, "cold");
        add_llvm_enum_function_attribute(self.context, function, "nounwind");
        function
    }

    fn get_gc_poll_flags(&self) -> inkwell::values::GlobalValue<'llvm> {
        if let Some(global) = self.module.get_global("__gc__poll_flags") {
            return global;
        }
        let global = self
            .module
            .add_global(self.context.i8_type(), None, "__gc__poll_flags");
        global.set_linkage(Linkage::External);
        global
    }

    /// Emit the mutator fast path directly into generated code.
    ///
    /// Managed entry shims register the thread before any Taro code runs. A
    /// zero flag therefore means there is no GC coordination work to perform;
    /// only the uncommon non-zero case crosses into the runtime.
    pub(super) fn emit_gc_poll(&mut self, span: crate::span::Span) {
        let flags = self
            .builder
            .build_load(
                self.context.i8_type(),
                self.get_gc_poll_flags().as_pointer_value(),
                "gc_poll_flags",
            )
            .unwrap();
        flags
            .as_instruction_value()
            .expect("GC poll flag load must be an instruction")
            .set_atomic_ordering(inkwell::AtomicOrdering::Acquire)
            .expect("acquire ordering must be valid for a GC poll load");
        let pending = self
            .builder
            .build_int_compare(
                IntPredicate::NE,
                flags.into_int_value(),
                self.context.i8_type().const_zero(),
                "gc_poll_pending",
            )
            .unwrap();

        let function = self.current_fn.expect("GC poll emitted outside a function");
        let slow = self.context.append_basic_block(function, "gc_poll.slow");
        let resume = self.context.append_basic_block(function, "gc_poll.resume");
        self.builder
            .build_conditional_branch(pending, slow, resume)
            .unwrap();

        self.builder.position_at_end(slow);
        self.emit_source_typed_gc_stack_map(
            span,
            crate::codegen::gc_stack_maps::StackMapSiteKind::Poll,
        );
        self.builder
            .build_call(self.get_gc_poll(), &[], "gc_poll_slow")
            .unwrap();
        self.builder.build_unconditional_branch(resume).unwrap();
        self.builder.position_at_end(resume);
    }

    pub(super) fn emit_source_typed_gc_stack_map(
        &mut self,
        span: crate::span::Span,
        gc_kind: gc_maps::StackMapSiteKind,
    ) {
        let body = self.current_body.expect("GC source site outside MIR body");
        let location = self
            .current_mir_location
            .expect("GC source site has no MIR location");
        let function = self.current_fn.expect("GC source site outside function");
        let selector = self
            .current_stack_map_selector
            .expect("GC source selector missing");
        let ordinal = self.current_stack_map_ordinal;
        self.current_stack_map_ordinal = ordinal.checked_add(1).expect("GC site ordinal overflow");
        let frames = self.logical_frames_for_site(body, span);
        let arguments: &[Operand<'gcx>] = match location {
            mir::analysis::liveness::MirLocation::Terminator { block } => match body.basic_blocks
                [block]
                .terminator
                .as_ref()
                .map(|term| &term.kind)
            {
                Some(mir::TerminatorKind::Call { args, .. }) => args,
                _ => &[],
            },
            _ => &[],
        };
        let frame = self
            .current_gc_frame
            .take()
            .expect("GC frame was not prepared");
        let record = self.emit_gc_map_at(
            &frame, location, function, selector, ordinal, gc_kind, arguments, frames,
        );
        self.current_gc_frame = Some(frame);
        self.pending_gc_stack_maps.push(record);
    }

    /// Give an uninitialized binding defined scanner bytes, unless a proven
    /// noncollecting whole copy supplies them before any observation. This
    /// publishes no source value and changes no definite-initialization facts.
    /// Stable storage uses volatile initialization for hidden collector reads,
    /// including reference chains into partial objects. Private work storage
    /// instead publishes a volatile snapshot at the collecting site.
    pub(super) fn zero_gc_local(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &[LocalStorage<'llvm>],
        local: mir::LocalId,
    ) {
        if self
            .current_mir_location
            .is_some_and(|location| self.storage_live_is_fully_initialized(body, location, local))
        {
            return;
        }
        let preserve = !self
            .current_gc_frame
            .as_ref()
            .is_some_and(|frame| frame.spill_sources.contains_key(&local));
        self.initialize_gc_local(body, locals, local, preserve);
    }

    fn initialize_gc_local(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &[LocalStorage<'llvm>],
        local: mir::LocalId,
        preserve: bool,
    ) {
        let declaration = &body.locals[local];
        if matches!(declaration.kind, mir::LocalKind::Param)
            || self.gc_layout_nodes_for_ty(declaration.ty).is_empty()
        {
            return;
        }
        let LocalStorage::Stack(storage) = locals[local.index()] else {
            return;
        };
        let Some(ty) = self.lower_ty(declaration.ty) else {
            return;
        };
        let size = self.target_data.get_store_size(&ty);
        if preserve
            && local == body.return_local
            && !storage.as_instruction_value().is_some_and(|instruction| {
                instruction.get_opcode() == inkwell::values::InstructionOpcode::Alloca
            })
            && matches!(
                ty,
                BasicTypeEnum::StructType(_) | BasicTypeEnum::ArrayType(_)
            )
            && size >= 4 * u64::from(self.target_data.get_pointer_byte_size(None))
        {
            // Scanner storage follows the runtime's all-zero representation,
            // including null managed pointers. Clear the complete value size
            // (and its padding) so LLVM can use wider stores. Volatile keeps
            // collector-visible initialization; inline forbids an external
            // helper/collecting call during partial construction. No stronger
            // alignment is assumed for a caller-provided return destination.
            // Keep local allocas typed: LLVM's SROA splits their byte clears
            // into extra padding stores. Small returns do not amortize vector
            // setup, so they also retain their existing typed initialization.
            let intrinsic = Intrinsic::find("llvm.memset.inline")
                .expect("LLVM inline memset intrinsic")
                .get_declaration(
                    &self.module,
                    &[storage.get_type().into(), self.usize_ty.into()],
                )
                .expect("declare inline GC clear");
            self.builder
                .build_call(
                    intrinsic,
                    &[
                        storage.into(),
                        self.context.i8_type().const_zero().into(),
                        self.usize_ty.const_int(size, false).into(),
                        self.context.bool_type().const_int(1, false).into(),
                    ],
                    "",
                )
                .expect("initialize GC aggregate scanner storage");
            return;
        }
        self.builder
            .build_store(storage, ty.const_zero())
            .expect("initialize GC scanner storage")
            .set_volatile(preserve)
            .expect("preserve collector initialization");
    }

    pub(super) fn gc_frame(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &[LocalStorage<'llvm>],
    ) -> CompileResult<GcStackMapFrame<'llvm, 'gcx>> {
        let mut deferred_initialization = storage_live_covers_observations(body);
        deferred_initialization.extend(self.fully_initialized_temporaries(body));
        let mut roots = Vec::new();
        let mut spill_sources = FxHashMap::default();
        let mut zeroed_storage = FxHashSet::default();
        let mut address_taken = FxHashSet::default();
        let mut address_exposed = FxHashSet::default();
        for block in &body.basic_blocks {
            for statement in &block.statements {
                if let mir::StatementKind::Assign(_, value) = &statement.kind
                    && let Some(place) = value.addressed_place()
                    && !place.projection.contains(&mir::PlaceElem::Deref)
                {
                    address_taken.insert(place.local);
                    address_exposed.insert(place.local);
                }
            }
            // A callable shim may materialize a value argument's address for
            // its concrete reference receiver. Keep such values in their real
            // storage, as well as explicitly address-taken MIR places.
            if let Some(args) = block
                .terminator
                .as_ref()
                .and_then(|terminator| terminator.kind.call_arguments())
            {
                for argument in args {
                    if let Some(place) = argument.place()
                        && !matches!(
                            self.operand_ty(body, argument).kind(),
                            TyKind::Reference(..) | TyKind::Pointer(..)
                        )
                    {
                        address_taken.insert(place.local);
                    }
                }
            }
        }
        for (local, declaration) in body.locals.iter_enumerated() {
            let nodes = self.gc_layout_nodes_for_ty(declaration.ty);
            if nodes.is_empty() {
                continue;
            }
            let LocalStorage::Stack(storage) = locals[local.index()] else {
                self.gcx.dcx().emit_error(
                    format!(
                        "GC-bearing local {} has no addressable LLVM storage",
                        local.index()
                    ),
                    Some(declaration.span),
                );
                return Err(crate::error::ReportedError);
            };
            // A direct alloca is already a machine frame location. Indirect
            // ABI parameters/returns name external storage: spill their storage
            // address so the walker can recover it from a stable frame slot.
            let direct = storage.as_instruction_value().is_some_and(|instruction| {
                instruction.get_opcode() == inkwell::values::InstructionOpcode::Alloca
            });
            let ty = self
                .lower_ty(declaration.ty)
                .expect("GC working value type");
            // Bulk snapshots at every call can cost more than keeping a
            // larger inline value in stable storage (notably enum payloads).
            // Limit snapshots to values that fit in two pointer words.
            let spill = direct
                && !address_taken.contains(&local)
                && self.target_data.get_store_size(&ty)
                    <= 2 * u64::from(self.target_data.get_pointer_byte_size(None));
            if !matches!(declaration.kind, mir::LocalKind::Param) {
                // A private value is observed through a volatile snapshot at
                // each map. Stable/address-taken storage is observed directly
                // by the walker and still needs preserved initialization.
                if !deferred_initialization.contains(&local) {
                    self.initialize_gc_local(body, locals, local, !spill);
                }
                // A covered local is not live at any map until StorageLive or
                // its proven whole initializer supplies defined scanner bytes.
                zeroed_storage.insert(local);
            }
            let (location, storage_deref_depth) = if spill {
                let slot = self
                    .builder
                    .build_alloca(ty, "gc_root")
                    .expect("GC spill slot");
                spill_sources.insert(local, (storage, ty));
                (slot, 0)
            } else if direct {
                (storage, 0)
            } else {
                let pointer = self.context.ptr_type(AddressSpace::default());
                let slot = self
                    .builder
                    .build_alloca(pointer, "gc_storage_base")
                    .expect("GC indirect storage base");
                self.builder
                    .build_store(slot, storage)
                    .expect("publish GC storage base");
                (slot, 1)
            };
            roots.push((
                local,
                GcRootOperand {
                    location,
                    ty: declaration.ty,
                    storage_deref_depth,
                },
            ));
        }
        Ok(GcStackMapFrame {
            roots,
            spill_sources,
            liveness: mir::analysis::liveness::compute_liveness(body),
            zeroed_storage,
            address_holders: FxHashMap::default(),
            address_exposed,
        })
    }

    /// Keep GC-bearing address-taken locals rooted through their aliases.
    pub(super) fn publish_address_holders(
        &self,
        instance: Instance<'gcx>,
        body: &mir::Body<'gcx>,
        frame: &mut GcStackMapFrame<'llvm, 'gcx>,
    ) -> CompileResult<()> {
        let owners: FxHashSet<_> = frame
            .roots
            .iter()
            .map(|(local, _)| *local)
            .filter(|local| frame.address_exposed.contains(local))
            .collect();
        if !owners.is_empty() {
            frame.address_holders =
                mir::optimize::escape_graph::address_holders(self.gcx, instance, body, &owners)?;
        }
        Ok(())
    }

    pub(super) fn emit_gc_map_at(
        &mut self,
        frame: &GcStackMapFrame<'llvm, 'gcx>,
        location: mir::analysis::liveness::MirLocation,
        function: FunctionValue<'llvm>,
        selector: PointerValue<'llvm>,
        ordinal: u64,
        kind: gc_maps::StackMapSiteKind,
        native_arguments: &[Operand<'gcx>],
        logical_frames: Vec<gc_maps::PendingLogicalFrame>,
    ) -> gc_maps::PendingStackMapRecord {
        let liveness = &frame.liveness;
        let (live, initialized) = {
            // A collecting operation runs before its MIR destination write.
            // Zeroed root storage can contain initialized fields even while
            // definite initialization correctly rejects reading the whole value.
            (
                liveness.live_before(location),
                liveness.initialized_before(location),
            )
        };
        let mut selected: FxHashSet<_> = live
            .iter()
            .filter(|local| initialized.contains(local) || frame.zeroed_storage.contains(local))
            .copied()
            .collect();
        for (owner, holders) in &frame.address_holders {
            if initialized.contains(owner) && holders.iter().any(|holder| live.contains(holder)) {
                selected.insert(*owner);
            }
        }
        // Runtime/blocking calls have no managed callee frame. Even a final-use
        // argument must remain rooted for the complete call. The call lowerer
        // supplies these operands according to the ABI's collecting behavior.
        for argument in native_arguments {
            if let Some(place) = argument.place()
                && liveness.initialized_before(location).contains(&place.local)
            {
                selected.insert(place.local);
            }
        }
        let operands: Vec<_> = frame
            .roots
            .iter()
            .filter(|(local, _)| selected.contains(local))
            .map(|(local, operand)| {
                if let Some(&(source, ty)) = frame.spill_sources.get(local) {
                    let value = self
                        .builder
                        .build_load(ty, source, "gc_spill_value")
                        .expect("read private GC value");
                    self.builder
                        .build_store(operand.location, value)
                        .expect("publish GC spill")
                        .set_volatile(true)
                        .expect("preserve collector snapshot");
                }
                *operand
            })
            .collect();
        self.emit_gc_stack_map(function, selector, ordinal, kind, &operands, logical_frames)
    }

    pub(super) fn emit_gc_stack_map(
        &mut self,
        function: FunctionValue<'llvm>,
        selector: PointerValue<'llvm>,
        ordinal: u64,
        kind: gc_maps::StackMapSiteKind,
        roots: &[GcRootOperand<'llvm, 'gcx>],
        logical_frames: Vec<gc_maps::PendingLogicalFrame>,
    ) -> gc_maps::PendingStackMapRecord {
        let symbol = function.get_name().to_string_lossy().into_owned();
        let id = gc_maps::deterministic_map_id(&self.gcx.config.identifier, &symbol, ordinal);
        let selector_value = ordinal.checked_add(1).expect("GC selector overflow");
        self.preserve_diagnostic_frame(function);
        let store = self
            .builder
            .build_store(
                selector,
                self.context.i64_type().const_int(selector_value, false),
            )
            .expect("publish GC selector");
        store
            .set_volatile(true)
            .expect("GC selector must remain observable");

        let mut operands: Vec<BasicMetadataValueEnum<'llvm>> = vec![
            self.context.i64_type().const_int(id, false).into(),
            self.context.i32_type().const_zero().into(),
            selector.into(),
        ];
        let mut descriptors = Vec::new();
        for root in roots {
            assert!(
                root.storage_deref_depth <= 32,
                "invalid GC storage indirection depth"
            );
            let nodes = self.gc_layout_nodes_for_ty(root.ty);
            if nodes.is_empty() {
                continue;
            }
            operands.push(root.location.into());
            descriptors.push(PendingRootOperand {
                storage_deref_depth: root.storage_deref_depth,
                nodes,
            });
        }
        let intrinsic =
            Intrinsic::find("llvm.experimental.stackmap").expect("LLVM stack-map intrinsic");
        let declaration = intrinsic
            .get_declaration(&self.module, &[])
            .expect("declare GC stack-map intrinsic");
        let call = self
            .builder
            .build_call(declaration, &operands, "")
            .expect("emit typed GC stack map");
        call.add_attribute(
            AttributeLoc::Function,
            self.context
                .create_enum_attribute(Attribute::get_named_enum_kind_id("nounwind"), 0),
        );
        gc_maps::PendingStackMapRecord {
            id,
            emitted_function: symbol,
            kind,
            selector_value,
            roots: descriptors,
            logical_frames,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn temporary_initializer_must_precede_every_storage_observation() {
        use mir::{
            BasicBlockData, BasicBlockId, Rvalue, Statement, StatementKind as S, Terminator,
            TerminatorKind as T,
        };
        mir::test_support::with_test_gcx(|gcx| {
            let context = Context::create();
            let mut emitter = Emitter::new(
                &context,
                context.create_module("array-initializers"),
                context.create_builder(),
                gcx,
            )
            .unwrap_or_else(|_| panic!("emitter"));
            let reference = Ty::new(TyKind::Reference(gcx.types.int32), gcx);
            let array = |element| {
                Ty::new(
                    TyKind::Array {
                        element,
                        len: crate::sema::models::Const {
                            ty: gcx.types.uint,
                            kind: ConstKind::Value(ConstValue::Integer(8)),
                        },
                    },
                    gcx,
                )
            };
            let mut body = mir::test_support::minimal_body(gcx);
            let source = mir::test_support::push_temp(&mut body, array(reference));
            body.locals[source].kind = mir::LocalKind::Param;
            let local = mir::test_support::push_temp(&mut body, array(reference));
            let alias = mir::test_support::push_temp(
                &mut body,
                Ty::new(TyKind::Reference(array(reference)), gcx),
            );
            let span = body.locals[local].span;
            let statement = |kind| Statement { span, kind };
            let assign = || {
                statement(S::Assign(
                    Place::from_local(local),
                    Rvalue::CopyValue {
                        source: Place::from_local(source),
                    },
                ))
            };
            let keep = || statement(S::KeepAlive(Operand::Copy(Place::from_local(local))));
            body.basic_blocks[body.start_block].statements = vec![assign(), keep()];
            assert!(
                emitter
                    .fully_initialized_temporaries(&body)
                    .contains(&local)
            );
            for scenario in [
                "read",
                "address",
                "live",
                "dead",
                "twice",
                "self",
                "parameter",
                "return",
                "erased",
            ] {
                let mut changed = body.clone();
                let statements = &mut changed.basic_blocks[changed.start_block].statements;
                match scenario {
                    "read" => statements.insert(0, keep()),
                    "address" => statements.insert(
                        0,
                        statement(S::Assign(
                            Place::from_local(alias),
                            Rvalue::Ref {
                                place: Place::from_local(local),
                            },
                        )),
                    ),
                    "live" => statements.insert(0, statement(S::StorageLive(local))),
                    "dead" => statements.push(statement(S::StorageDead(local))),
                    "twice" => statements.push(assign()),
                    "self" => {
                        statements[0] = statement(S::Assign(
                            Place::from_local(local),
                            Rvalue::Use(Operand::Copy(Place::from_local(local))),
                        ))
                    }
                    "parameter" => changed.locals[local].kind = mir::LocalKind::Param,
                    "return" => changed.return_local = local,
                    "erased" => {
                        let erased = Ty::new(TyKind::BoxedExistential { interfaces: &[] }, gcx);
                        changed.locals[local].ty = array(erased);
                        changed.locals[source].ty = array(erased);
                    }
                    _ => unreachable!(),
                }
                assert!(
                    !emitter
                        .fully_initialized_temporaries(&changed)
                        .contains(&local),
                    "{scenario}"
                );
            }
            let id = |i| BasicBlockId::from_usize(i);
            let block = |statements, kind| BasicBlockData {
                note: None,
                statements,
                terminator: Some(Terminator { span, kind }),
            };
            let switch = |yes, no| T::SwitchInt {
                discr: Operand::Constant(mir::Constant {
                    ty: gcx.types.bool,
                    value: mir::ConstantKind::Bool(true),
                }),
                targets: vec![(1, id(yes))],
                otherwise: id(no),
            };
            body.basic_blocks = index_vec::IndexVec::from(vec![
                block(vec![], switch(1, 2)),
                block(vec![assign()], T::Goto { target: id(2) }),
                block(vec![keep()], T::Return),
            ]);
            assert!(
                !emitter
                    .fully_initialized_temporaries(&body)
                    .contains(&local),
                "bypass path"
            );
            body.basic_blocks = index_vec::IndexVec::from(vec![
                block(vec![], T::Goto { target: id(1) }),
                block(vec![assign(), keep()], switch(1, 2)),
                block(vec![], T::Return),
            ]);
            assert!(
                emitter
                    .fully_initialized_temporaries(&body)
                    .contains(&local),
                "loop overwrites before use"
            );
            // The same whole-copy proof applies to scalar handles and inline
            // aggregates, independently of their GC descriptor shape.
            let tuple = Ty::new(
                TyKind::Tuple(gcx.store.interners.intern_ty_list(vec![reference; 4])),
                gcx,
            );
            for ty in [reference, tuple] {
                let mut changed = body.clone();
                changed.locals[source].ty = ty;
                changed.locals[local].ty = ty;
                assert!(
                    emitter
                        .fully_initialized_temporaries(&changed)
                        .contains(&local)
                );
            }
        });
    }

    #[test]
    fn gc_indirect_return_initialization_uses_inline_volatile_bulk_clear() {
        use inkwell::values::AnyValue;
        mir::test_support::with_test_gcx(|gcx| {
            let context = Context::create();
            let mut emitter = Emitter::new(
                &context,
                context.create_module("gc-bulk-initialization"),
                context.create_builder(),
                gcx,
            )
            .unwrap_or_else(|_| panic!("emitter"));
            let reference = Ty::new(TyKind::Reference(gcx.types.int32), gcx);
            let padded = Ty::new(
                TyKind::Tuple(gcx.store.interners.intern_ty_list(vec![
                    gcx.types.bool,
                    reference,
                    gcx.types.uint8,
                    reference,
                ])),
                gcx,
            );
            let array = Ty::new(
                TyKind::Array {
                    element: reference,
                    len: crate::sema::models::Const {
                        ty: gcx.types.uint,
                        kind: ConstKind::Value(ConstValue::Integer(5)),
                    },
                },
                gcx,
            );
            let small = Ty::new(
                TyKind::Tuple(gcx.store.interners.intern_ty_list(vec![reference; 2])),
                gcx,
            );
            for (name, ty, returned, bulk) in [
                ("padded", padded, true, true),
                ("array", array, true, true),
                ("local", padded, false, false),
                ("small", small, true, false),
            ] {
                let mut body = mir::test_support::minimal_body(gcx);
                let local = mir::test_support::push_temp(&mut body, ty);
                if returned {
                    body.locals[local].kind = mir::LocalKind::Return;
                    body.return_local = local;
                }
                // Use external storage too: clearing must not assume an alloca
                // alignment or write beyond the ABI's complete value size.
                let pointer = context.ptr_type(AddressSpace::default());
                let function = emitter.module.add_function(
                    name,
                    context.void_type().fn_type(&[pointer.into()], false),
                    None,
                );
                emitter
                    .builder
                    .position_at_end(context.append_basic_block(function, "entry"));
                let mut locals = vec![LocalStorage::Value(None); body.locals.len()];
                let lowered = emitter.lower_ty(ty).unwrap();
                locals[local.index()] = LocalStorage::Stack(if returned {
                    function.get_first_param().unwrap().into_pointer_value()
                } else {
                    emitter.builder.build_alloca(lowered, "local").unwrap()
                });
                emitter.initialize_gc_local(&body, &locals, local, true);
                emitter.builder.build_return(None).unwrap();
                let size = emitter.target_data.get_store_size(&lowered);
                let ir = function.print_to_string().to_string();
                if !bulk {
                    assert!(
                        ir.contains("store volatile") && !ir.contains("@llvm.memset"),
                        "local and small buffers must keep typed initialization: {ir}"
                    );
                    continue;
                }
                assert!(
                    ir.contains("@llvm.memset.inline.")
                        && ir.contains(&format!("i64 {size}, i1 true")),
                    "GC aggregates need a volatile inline clear of exactly their storage size: {ir}"
                );
                assert!(
                    !ir.contains("store volatile"),
                    "do not scalarize bulk clears: {ir}"
                );
            }
            emitter.module.verify().unwrap();
        });
    }

    #[test]
    fn whole_copy_zero_elision_stops_at_observations_and_collecting_operations() {
        use mir::{Rvalue, Statement, StatementKind as S, analysis::liveness::MirLocation};
        mir::test_support::with_test_gcx(|gcx| {
            let context = Context::create();
            let mut emitter = Emitter::new(
                &context,
                context.create_module("copy-initialization"),
                context.create_builder(),
                gcx,
            )
            .unwrap_or_else(|_| panic!("emitter"));
            let mut body = mir::test_support::minimal_body(gcx);
            let reference = Ty::new(TyKind::Reference(gcx.types.int32), gcx);
            let source = mir::test_support::push_temp(&mut body, reference);
            let local = mir::test_support::push_temp(&mut body, reference);
            let other = mir::test_support::push_temp(&mut body, reference);
            let span = body.locals[local].span;
            let statement = |kind| Statement { span, kind };
            let copy = || {
                statement(S::Assign(
                    Place::from_local(local),
                    Rvalue::Use(Operand::Copy(Place::from_local(source))),
                ))
            };
            let location = MirLocation::Statement {
                block: body.start_block,
                index: 0,
            };
            body.basic_blocks[body.start_block].statements = vec![
                statement(S::StorageLive(local)),
                statement(S::StorageLive(other)),
                statement(S::Nop),
                copy(),
            ];
            assert!(emitter.storage_live_is_fully_initialized(&body, location, local));
            for value in [
                Rvalue::Use(Operand::Copy(Place::from_local(source))),
                Rvalue::CopyValue {
                    source: Place::from_local(source),
                },
            ] {
                let mut changed = body.clone();
                changed.basic_blocks[changed.start_block]
                    .statements
                    .insert(1, statement(S::Assign(Place::from_local(other), value)));
                assert!(emitter.storage_live_is_fully_initialized(&changed, location, local));
                // An indirect ABI parameter could alias external storage.
                changed.locals[other].kind = mir::LocalKind::Param;
                assert!(!emitter.storage_live_is_fully_initialized(&changed, location, local));
            }
            for barrier in [
                S::GcSafepoint(mir::GcSafepointKind::Entry),
                S::KeepAlive(Operand::Copy(Place::from_local(local))),
                S::StorageLive(local),
                S::Assign(
                    Place::from_local(other),
                    Rvalue::Ref {
                        place: Place::from_local(local),
                    },
                ),
                S::Assign(Place::from_local(local), Rvalue::Alloc { ty: reference }),
                S::Assign(Place::from_local(other), Rvalue::Alloc { ty: reference }),
                S::Assign(
                    Place::from_local(other),
                    Rvalue::Use(Operand::Copy(Place::from_local(local))),
                ),
                S::Assign(
                    Place::from_local(local),
                    Rvalue::Use(Operand::Copy(Place::from_local(local))),
                ),
            ] {
                let mut changed = body.clone();
                changed.basic_blocks[changed.start_block]
                    .statements
                    .insert(1, statement(barrier));
                assert!(!emitter.storage_live_is_fully_initialized(&changed, location, local));
            }
            let pointer = Ty::new(
                TyKind::Pointer(gcx.types.int32, hir::Mutability::Mutable),
                gcx,
            );
            let mut changed = body.clone();
            let pointer_source = mir::test_support::push_temp(&mut changed, pointer);
            let pointer_target = mir::test_support::push_temp(&mut changed, pointer);
            changed.basic_blocks[changed.start_block].statements.insert(
                1,
                statement(S::Assign(
                    Place::from_local(pointer_target),
                    Rvalue::Cast {
                        operand: Operand::Copy(Place::from_local(pointer_source)),
                        ty: pointer,
                        kind: mir::CastKind::Numeric,
                    },
                )),
            );
            assert!(emitter.storage_live_is_fully_initialized(&changed, location, local));
            let mut projected = Place::from_local(pointer_source);
            projected.projection.push(mir::PlaceElem::Deref);
            for (destination, source) in [
                (projected.clone(), Place::from_local(source)),
                (Place::from_local(other), projected),
            ] {
                let mut changed = changed.clone();
                changed.basic_blocks[changed.start_block].statements[1] =
                    statement(S::Assign(destination, Rvalue::Use(Operand::Copy(source))));
                assert!(!emitter.storage_live_is_fully_initialized(&changed, location, local));
            }
            // Even an independent destination must not hide a collecting copy.
            let erased = Ty::new(TyKind::BoxedExistential { interfaces: &[] }, gcx);
            let mut changed = body.clone();
            let erased_source = mir::test_support::push_temp(&mut changed, erased);
            let erased_target = mir::test_support::push_temp(&mut changed, erased);
            changed.basic_blocks[changed.start_block].statements.insert(
                1,
                statement(S::Assign(
                    Place::from_local(erased_target),
                    Rvalue::CopyValue {
                        source: Place::from_local(erased_source),
                    },
                )),
            );
            assert!(!emitter.storage_live_is_fully_initialized(&changed, location, local));
            // A projected store does not initialize this slot. Nor does this
            // block's terminator promise an overwrite on every outgoing edge.
            let mut partial = body.clone();
            let mut field = Place::from_local(local);
            field.projection.push(mir::PlaceElem::Deref);
            partial.basic_blocks[partial.start_block].statements[3] = statement(S::Assign(
                field,
                Rvalue::Use(Operand::Copy(Place::from_local(source))),
            ));
            assert!(!emitter.storage_live_is_fully_initialized(&partial, location, local));
            body.basic_blocks[body.start_block].statements[3] = statement(S::Assign(
                Place::from_local(local),
                Rvalue::CopyValue {
                    source: Place::from_local(source),
                },
            ));
            assert!(
                emitter.storage_live_is_fully_initialized(&body, location, local),
                "plain handles do not allocate when copied"
            );
            let erased = Ty::new(TyKind::BoxedExistential { interfaces: &[] }, gcx);
            body.locals[source].ty = erased;
            body.locals[local].ty = erased;
            assert!(
                !emitter.storage_live_is_fully_initialized(&body, location, local),
                "erased copies can collect before writing the destination"
            );
            body.basic_blocks[body.start_block].statements.truncate(1);
            assert!(!emitter.storage_live_is_fully_initialized(&body, location, local));
        });
    }

    #[test]
    fn deferred_scanner_initialization_requires_dominating_storage_live() {
        use mir::{
            BasicBlockData, BasicBlockId, Constant, ConstantKind, Rvalue, Statement,
            StatementKind as S, Terminator, TerminatorKind as T,
        };
        mir::test_support::with_test_gcx(|gcx| {
            let mut body = mir::test_support::minimal_body(gcx);
            let reference = Ty::new(TyKind::Reference(gcx.types.int32), gcx);
            let source = mir::test_support::push_temp(&mut body, reference);
            body.locals[source].kind = mir::LocalKind::Param;
            let local = mir::test_support::push_temp(&mut body, reference);
            let alias =
                mir::test_support::push_temp(&mut body, Ty::new(TyKind::Reference(reference), gcx));
            let span = body.locals[local].span;
            let statement = |kind| Statement { span, kind };
            let assign = || {
                statement(S::Assign(
                    Place::from_local(local),
                    Rvalue::Use(Operand::Copy(Place::from_local(source))),
                ))
            };
            let keep = || statement(S::KeepAlive(Operand::Copy(Place::from_local(local))));
            let start = || statement(S::StorageLive(local));
            body.basic_blocks[body.start_block].statements = vec![start(), assign(), keep()];
            assert!(storage_live_covers_observations(&body).contains(&local));
            for scenario in ["missing", "multiple", "read", "write", "address"] {
                let mut changed = body.clone();
                let statements = &mut changed.basic_blocks[changed.start_block].statements;
                match scenario {
                    "missing" => {
                        statements.remove(0);
                    }
                    "multiple" => statements.push(start()),
                    "read" => statements.insert(0, keep()),
                    "write" => statements.insert(0, assign()),
                    "address" => statements.insert(
                        0,
                        statement(S::Assign(
                            Place::from_local(alias),
                            Rvalue::Ref {
                                place: Place::from_local(local),
                            },
                        )),
                    ),
                    _ => unreachable!(),
                }
                assert!(
                    !storage_live_covers_observations(&changed).contains(&local),
                    "{scenario}"
                );
            }
            let id = |index| BasicBlockId::from_usize(index);
            let block = |statements, kind| BasicBlockData {
                note: None,
                statements,
                terminator: Some(Terminator { span, kind }),
            };
            let switch = |yes, no| T::SwitchInt {
                discr: Operand::Constant(Constant {
                    ty: gcx.types.bool,
                    value: ConstantKind::Bool(true),
                }),
                targets: vec![(1, id(yes))],
                otherwise: id(no),
            };
            body.basic_blocks = index_vec::IndexVec::from(vec![
                block(vec![], switch(1, 2)),
                block(vec![start(), assign()], T::Goto { target: id(3) }),
                block(vec![assign()], T::Goto { target: id(3) }),
                block(vec![keep()], T::Return),
            ]);
            assert!(
                !storage_live_covers_observations(&body).contains(&local),
                "join bypasses lifetime start"
            );
            body.basic_blocks[id(0)].statements.push(start());
            body.basic_blocks[id(1)].statements.remove(0);
            assert!(
                storage_live_covers_observations(&body).contains(&local),
                "entry dominates both branches"
            );
            body.basic_blocks = index_vec::IndexVec::from(vec![
                block(vec![], T::Goto { target: id(1) }),
                block(vec![start(), assign(), keep()], switch(1, 2)),
                block(vec![], T::Return),
            ]);
            assert!(
                storage_live_covers_observations(&body).contains(&local),
                "loop reinitializes at StorageLive"
            );
        });
    }

    #[test]
    fn private_gc_values_spill_only_on_the_collecting_path() {
        use mir::analysis::liveness::MirLocation;
        crate::test_support::analyze_script("func main() {}", |_, gcx| {
            let reference = Ty::new(TyKind::Reference(gcx.types.int32), gcx);
            let mut body = mir::test_support::minimal_body(gcx);
            let parameter = body.locals.push(mir::LocalDecl {
                ty: reference,
                kind: mir::LocalKind::Param,
                mutable: true,
                name: None,
                span: body.locals[body.return_local].span,
            });
            let span = body.locals[parameter].span;
            body.basic_blocks[body.start_block].statements = vec![
                mir::Statement {
                    span,
                    kind: mir::StatementKind::Nop,
                },
                mir::Statement {
                    span,
                    kind: mir::StatementKind::KeepAlive(Operand::Copy(Place::from_local(
                        parameter,
                    ))),
                },
            ];
            let body: &mir::Body<'_> = gcx.store.arenas.mir_bodies.alloc(body);
            let context = Context::create();
            let mut emitter = Emitter::new(
                &context,
                context.create_module("private-gc-spills"),
                context.create_builder(),
                gcx,
            )
            .unwrap_or_else(|_| panic!("private GC spill emitter"));
            let pointer = context.ptr_type(AddressSpace::default());
            let function = emitter.module.add_function(
                "private_gc_spill",
                pointer.fn_type(&[pointer.into()], false),
                None,
            );
            emitter
                .builder
                .position_at_end(context.append_basic_block(function, "entry"));
            let storage = emitter
                .builder
                .build_alloca(pointer, "working_value")
                .unwrap();
            let value = function.get_first_param().unwrap();
            emitter.builder.build_store(storage, value).unwrap();
            let selector = emitter
                .builder
                .build_alloca(context.i64_type(), "selector")
                .unwrap();
            let frame = emitter
                .gc_frame(
                    &body,
                    &[LocalStorage::Value(None), LocalStorage::Stack(storage)],
                )
                .unwrap_or_else(|_| panic!("private GC frame"));
            emitter.current_fn = Some(function);
            emitter.current_body = Some(body);
            emitter.current_mir_location = Some(MirLocation::Statement {
                block: body.start_block,
                index: 0,
            });
            emitter.current_stack_map_selector = Some(selector);
            emitter.current_gc_frame = Some(frame);
            emitter.emit_gc_poll(span);
            let result = emitter
                .builder
                .build_load(pointer, storage, "result")
                .unwrap();
            emitter.builder.build_return(Some(&result)).unwrap();
            emitter.module.verify().unwrap();
            emitter
                .module
                .run_passes(
                    "default<O3>",
                    &emitter.target_machine,
                    PassBuilderOptions::create(),
                )
                .unwrap();
            let ir = emitter.module.print_to_string().to_string();
            assert!(
                !ir.contains("%working_value = alloca"),
                "private work storage must promote to SSA: {ir}"
            );
            let slow = ir
                .split("gc_poll.slow:")
                .nth(1)
                .expect("collecting slow path");
            assert!(
                slow.contains("store volatile ptr %0, ptr %gc_root"),
                "publish a separate root only on the slow path: {ir}"
            );
            assert_eq!(emitter.pending_gc_stack_maps[0].roots.len(), 1);
        });
    }

    #[test]
    fn partial_aggregate_fields_are_rooted_without_publishing_a_source_value() {
        use mir::analysis::liveness::MirLocation;
        for has_lifetime_start in [false, true] {
            crate::test_support::analyze_script("func main() {}", |_, gcx| {
                let reference = Ty::new(TyKind::Reference(gcx.types.int32), gcx);
                let aggregate = Ty::new(
                    TyKind::Tuple(
                        gcx.store
                            .interners
                            .intern_ty_list(vec![reference, reference]),
                    ),
                    gcx,
                );
                let mut body = mir::test_support::minimal_body(gcx);
                let parameter = body.locals.push(mir::LocalDecl {
                    ty: reference,
                    kind: mir::LocalKind::Param,
                    mutable: true,
                    name: None,
                    span: body.locals[body.return_local].span,
                });
                let partial = mir::test_support::push_temp(&mut body, aggregate);
                let span = body.locals[partial].span;
                let mut field = Place::from_local(partial);
                field.projection.push(mir::PlaceElem::Field(
                    crate::thir::FieldIndex::new(0),
                    reference,
                ));
                body.basic_blocks[body.start_block].statements = vec![
                    mir::Statement {
                        span,
                        kind: if has_lifetime_start {
                            mir::StatementKind::StorageLive(partial)
                        } else {
                            mir::StatementKind::Nop
                        },
                    },
                    mir::Statement {
                        span,
                        kind: mir::StatementKind::Assign(
                            field.clone(),
                            mir::Rvalue::Use(Operand::Copy(Place::from_local(parameter))),
                        ),
                    },
                    mir::Statement {
                        span,
                        kind: mir::StatementKind::Nop,
                    },
                    mir::Statement {
                        span,
                        kind: mir::StatementKind::KeepAlive(Operand::Copy(field)),
                    },
                ];
                let context = Context::create();
                let mut emitter = Emitter::new(
                    &context,
                    context.create_module("partial-gc-storage"),
                    context.create_builder(),
                    gcx,
                )
                .unwrap_or_else(|_| panic!("partial storage emitter"));

                let pointer = context.ptr_type(AddressSpace::default());
                let function = emitter.module.add_function(
                    "partial_storage",
                    context.void_type().fn_type(&[pointer.into()], false),
                    None,
                );
                emitter
                    .builder
                    .position_at_end(context.append_basic_block(function, "entry"));
                let parameter_slot = emitter.builder.build_alloca(pointer, "parameter").unwrap();
                emitter
                    .builder
                    .build_store(parameter_slot, function.get_first_param().unwrap())
                    .unwrap();
                let aggregate_slot = emitter
                    .builder
                    .build_alloca(emitter.lower_ty(aggregate).unwrap(), "partial")
                    .unwrap();
                let selector = emitter
                    .builder
                    .build_alloca(context.i64_type(), "selector")
                    .unwrap();
                let mut locals = [
                    LocalStorage::Value(None),
                    LocalStorage::Stack(parameter_slot),
                    LocalStorage::Stack(aggregate_slot),
                ];
                let frame = emitter
                    .gc_frame(&body, &locals)
                    .unwrap_or_else(|_| panic!("partial GC frame"));
                // Match production lowering: frame setup allocates root slots,
                // then the declaration initializes scanner bytes at StorageLive.
                emitter.current_gc_frame = Some(frame);
                emitter
                    .lower_statement(
                        &body,
                        &mut locals,
                        &body.basic_blocks[body.start_block].statements[0],
                    )
                    .unwrap_or_else(|_| panic!("storage lifetime start"));
                let frame = emitter.current_gc_frame.take().unwrap();
                let field_slot = emitter
                    .builder
                    .build_struct_gep(
                        emitter.lower_ty(aggregate).unwrap().into_struct_type(),
                        aggregate_slot,
                        0,
                        "first_field",
                    )
                    .unwrap();
                emitter
                    .builder
                    .build_store(field_slot, function.get_first_param().unwrap())
                    .unwrap();
                let location = MirLocation::Statement {
                    block: body.start_block,
                    index: 2,
                };
                assert!(
                    !frame
                        .liveness
                        .initialized_before(location)
                        .contains(&partial),
                    "GC rooting must not initialize a source-language value"
                );
                for (ordinal, kind) in [
                    gc_maps::StackMapSiteKind::Poll,
                    gc_maps::StackMapSiteKind::Allocation,
                    gc_maps::StackMapSiteKind::Call,
                    gc_maps::StackMapSiteKind::Blocking,
                    gc_maps::StackMapSiteKind::Panic,
                ]
                .into_iter()
                .enumerate()
                {
                    let record = emitter.emit_gc_map_at(
                        &frame,
                        location,
                        function,
                        selector,
                        ordinal as u64,
                        kind,
                        &[],
                        vec![],
                    );
                    assert_eq!(
                        record.roots.len(),
                        1,
                        "the initialized field remains reachable during construction, kind={kind:?}"
                    );
                }
                emitter.builder.build_return(None).unwrap();
                emitter.module.verify().unwrap();
                emitter
                    .module
                    .run_passes(
                        "default<O3>",
                        &emitter.target_machine,
                        PassBuilderOptions::create(),
                    )
                    .unwrap();
                let ir = emitter.module.print_to_string().to_string();
                assert!(
                    ir.contains("store volatile { ptr, ptr }") && ir.contains("ptr null, 1"),
                    "the collector snapshot must retain the uninitialized field's zero bytes: {ir}"
                );
            });
        }
    }

    #[test]
    fn site_selection_keeps_only_live_zero_safe_storage_and_call_arguments() {
        use mir::analysis::liveness::MirLocation;
        crate::test_support::analyze_script("func main() {}", |_, gcx| {
            let reference = Ty::new(TyKind::Reference(gcx.types.int32), gcx);
            let mut body = mir::test_support::minimal_body(gcx);
            let initialized = mir::test_support::push_temp(&mut body, reference);
            let uninitialized = mir::test_support::push_temp(&mut body, reference);
            let span = body.locals[initialized].span;
            body.basic_blocks[body.start_block].statements = vec![
                mir::Statement {
                    span,
                    kind: mir::StatementKind::Assign(
                        Place::from_local(initialized),
                        mir::Rvalue::Zeroed { ty: reference },
                    ),
                },
                mir::Statement {
                    span,
                    kind: mir::StatementKind::Assign(
                        Place::from_local(initialized),
                        mir::Rvalue::Zeroed { ty: reference },
                    ),
                },
                mir::Statement {
                    span,
                    kind: mir::StatementKind::KeepAlive(Operand::Copy(Place::from_local(
                        initialized,
                    ))),
                },
                mir::Statement {
                    span,
                    kind: mir::StatementKind::Nop,
                },
                mir::Statement {
                    span,
                    kind: mir::StatementKind::KeepAlive(Operand::Copy(Place::from_local(
                        uninitialized,
                    ))),
                },
            ];
            let context = Context::create();
            let mut emitter = Emitter::new(
                &context,
                context.create_module("gc-selection"),
                context.create_builder(),
                gcx,
            )
            .unwrap_or_else(|_| panic!("GC selection emitter"));
            let pointer = context.ptr_type(AddressSpace::default());
            let function = emitter.module.add_function(
                "gc_selection_fixture",
                context.void_type().fn_type(&[pointer.into()], false),
                None,
            );
            emitter
                .builder
                .position_at_end(context.append_basic_block(function, "entry"));
            let selector = emitter
                .builder
                .build_alloca(context.i64_type(), "selector")
                .unwrap();
            let future = emitter
                .builder
                .build_alloca(emitter.lower_ty(reference).unwrap(), "future")
                .unwrap();
            let frame = emitter
                .gc_frame(
                    &body,
                    &[
                        LocalStorage::Value(None),
                        LocalStorage::Stack(
                            function.get_first_param().unwrap().into_pointer_value(),
                        ),
                        LocalStorage::Stack(future),
                    ],
                )
                .unwrap_or_else(|_| panic!("GC frame preparation"));
            // Zero-safe scanner storage is not a source-language value. It
            // may be traced while live without satisfying initialization.
            let entry = MirLocation::Statement {
                block: body.start_block,
                index: 0,
            };
            assert!(
                !frame
                    .liveness
                    .initialized_before(entry)
                    .contains(&initialized)
            );
            assert!(
                !frame
                    .liveness
                    .initialized_before(entry)
                    .contains(&uninitialized)
            );
            assert_eq!(frame.roots[0].1.storage_deref_depth, 1);
            assert_eq!(frame.roots[1].1.storage_deref_depth, 0);
            for (ordinal, index, kind, arguments, expected) in [
                (0, 0, gc_maps::StackMapSiteKind::Poll, vec![], 1),
                (5, 0, gc_maps::StackMapSiteKind::Allocation, vec![], 1),
                (6, 1, gc_maps::StackMapSiteKind::Allocation, vec![], 1),
                (1, 2, gc_maps::StackMapSiteKind::Poll, vec![], 2),
                (2, 3, gc_maps::StackMapSiteKind::Poll, vec![], 1),
                (3, 4, gc_maps::StackMapSiteKind::Poll, vec![], 1),
                (
                    4,
                    2,
                    gc_maps::StackMapSiteKind::Call,
                    vec![Operand::Copy(Place::from_local(initialized))],
                    2,
                ),
            ] {
                let record = emitter.emit_gc_map_at(
                    &frame,
                    MirLocation::Statement {
                        block: body.start_block,
                        index,
                    },
                    function,
                    selector,
                    ordinal,
                    kind,
                    &arguments,
                    vec![],
                );
                assert_eq!(record.roots.len(), expected, "site {ordinal}");
            }
            emitter.builder.build_return(None).unwrap();
            emitter.module.verify().expect("valid GC selection module");
        });
    }

    #[test]
    fn typed_and_rootless_sites_survive_machine_emission_and_sidecar_normalization() {
        for optimized in [false, true] {
            crate::test_support::analyze_script("func main() {}", |_, gcx| {
                let context = Context::create();
                let mut emitter = Emitter::new(
                    &context,
                    context.create_module("gc-sites"),
                    context.create_builder(),
                    gcx,
                )
                .unwrap_or_else(|_| panic!("GC site emitter"));
                let function = emitter.module.add_function(
                    "gc_site_fixture",
                    context.void_type().fn_type(&[], false),
                    None,
                );
                let entry = context.append_basic_block(function, "entry");
                emitter.builder.position_at_end(entry);
                let selector = emitter
                    .builder
                    .build_alloca(context.i64_type(), "selector")
                    .unwrap();
                let reference = Ty::new(TyKind::Reference(gcx.types.int32), gcx);
                let storage_ty = emitter.lower_ty(reference).unwrap();
                let storage = emitter
                    .builder
                    .build_alloca(storage_ty, "reference")
                    .unwrap();
                emitter
                    .builder
                    .build_store(storage, storage_ty.const_zero())
                    .unwrap();
                let poll = emitter.module.add_function(
                    "__gc__poll",
                    context.void_type().fn_type(&[], false),
                    None,
                );
                let rooted = emitter.emit_gc_stack_map(
                    function,
                    selector,
                    0,
                    gc_maps::StackMapSiteKind::Poll,
                    &[GcRootOperand {
                        location: storage,
                        ty: reference,
                        storage_deref_depth: 0,
                    }],
                    vec![],
                );
                emitter.builder.build_call(poll, &[], "").unwrap();
                let rootless = emitter.emit_gc_stack_map(
                    function,
                    selector,
                    1,
                    gc_maps::StackMapSiteKind::Poll,
                    &[],
                    vec![],
                );
                emitter.builder.build_call(poll, &[], "").unwrap();
                emitter.builder.build_return(None).unwrap();
                emitter.module.verify().expect("valid GC LLVM module");
                let ir = emitter.module.print_to_string().to_string();
                assert!(ir.contains("store volatile i64 1"));
                assert!(ir.contains("store volatile i64 2"));
                assert!(ir.contains("noinline"));
                assert!(ir.contains("\"disable-tail-calls\"=\"true\""));
                assert!(ir.contains("uwtable(sync)"));
                if optimized {
                    emitter
                        .module
                        .run_passes(
                            "default<O2>",
                            &emitter.target_machine,
                            PassBuilderOptions::create(),
                        )
                        .expect("optimize GC module");
                }
                let directory = crate::test_support::TempDir::new("gc-site-object");
                let object = directory.join("sites.o");
                let pending = directory.join("sites.stackmaps");
                let triple = emitter
                    .target_machine
                    .get_triple()
                    .as_str()
                    .to_str()
                    .unwrap()
                    .to_owned();
                gc_maps::write_pending_module(
                    &pending,
                    &gc_maps::PendingStackMapModule::new(triple.clone(), vec![rooted, rootless]),
                )
                .unwrap();
                emitter
                    .target_machine
                    .write_to_file(&emitter.module, FileType::Object, &object)
                    .unwrap();
                let metadata = gc_maps::normalize_object(&object, [pending], &triple).unwrap();
                let records = &metadata
                    .functions
                    .iter()
                    .find(|f| f.symbol.contains("gc_site_fixture"))
                    .unwrap()
                    .records;
                assert_eq!(metadata.version, 7);
                assert_eq!(records.len(), 2);
                assert_eq!(records[0].roots.len(), 1);
                assert!(records[1].roots.is_empty());
                assert_eq!(records[0].selector.value, 1);
                assert_eq!(records[1].selector.value, 2);
                crate::codegen::gc_pc_metadata::emit_object(
                    &metadata,
                    &emitter.target_machine,
                    &directory.join("sites.pcmeta.o"),
                )
                .unwrap();
            });
        }
    }
}
