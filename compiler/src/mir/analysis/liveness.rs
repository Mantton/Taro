use crate::mir::{BasicBlockId, Body, CallUnwindAction, LocalId, StatementKind, TerminatorKind};
use index_vec::IndexVec;
use rustc_hash::FxHashSet;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MirLocation {
    Statement { block: BasicBlockId, index: usize },
    Terminator { block: BasicBlockId },
}

/// Result of liveness analysis.
pub struct LivenessResult {
    /// Variables live at the entry of each block.
    pub live_in: IndexVec<BasicBlockId, FxHashSet<LocalId>>,
    /// Variables live at the exit of each block.
    pub live_out: IndexVec<BasicBlockId, FxHashSet<LocalId>>,
    /// Live sets immediately before and after each statement. The outer index
    /// is a basic block and the inner index is the statement index.
    statement_live: IndexVec<BasicBlockId, Vec<LocationLiveness>>,
    /// Live sets immediately before and after each block terminator.
    terminator_live: IndexVec<BasicBlockId, LocationLiveness>,
    /// Whole locals known to contain a fully initialized value at each
    /// statement. GC root selection intersects these sets with liveness so a
    /// future aggregate temporary or a moved-from local is never scanned.
    statement_initialized: IndexVec<BasicBlockId, Vec<LocationInitialization>>,
    /// Initialization state at each terminator. `after` is the suspended-call
    /// state after operand moves and before edge-specific destinations become
    /// initialized.
    terminator_initialized: IndexVec<BasicBlockId, LocationInitialization>,
}

#[derive(Clone, Default)]
struct LocationLiveness {
    before: FxHashSet<LocalId>,
    after: FxHashSet<LocalId>,
}

#[derive(Clone, Default)]
struct LocationInitialization {
    before: FxHashSet<LocalId>,
    after: FxHashSet<LocalId>,
}

impl LivenessResult {
    pub fn live_before(&self, location: MirLocation) -> &FxHashSet<LocalId> {
        match location {
            MirLocation::Statement { block, index } => self.live_before_statement(block, index),
            MirLocation::Terminator { block } => self.live_before_terminator(block),
        }
    }

    pub fn live_after(&self, location: MirLocation) -> &FxHashSet<LocalId> {
        match location {
            MirLocation::Statement { block, index } => self.live_after_statement(block, index),
            MirLocation::Terminator { block } => self.live_after_terminator(block),
        }
    }

    pub fn live_before_statement(
        &self,
        block: BasicBlockId,
        statement: usize,
    ) -> &FxHashSet<LocalId> {
        &self.statement_live[block][statement].before
    }

    pub fn live_after_statement(
        &self,
        block: BasicBlockId,
        statement: usize,
    ) -> &FxHashSet<LocalId> {
        &self.statement_live[block][statement].after
    }

    pub fn live_before_terminator(&self, block: BasicBlockId) -> &FxHashSet<LocalId> {
        &self.terminator_live[block].before
    }

    pub fn live_after_terminator(&self, block: BasicBlockId) -> &FxHashSet<LocalId> {
        &self.terminator_live[block].after
    }

    pub fn initialized_before(&self, location: MirLocation) -> &FxHashSet<LocalId> {
        match location {
            MirLocation::Statement { block, index } => {
                &self.statement_initialized[block][index].before
            }
            MirLocation::Terminator { block } => &self.terminator_initialized[block].before,
        }
    }

    pub fn initialized_after(&self, location: MirLocation) -> &FxHashSet<LocalId> {
        match location {
            MirLocation::Statement { block, index } => {
                &self.statement_initialized[block][index].after
            }
            MirLocation::Terminator { block } => &self.terminator_initialized[block].after,
        }
    }
}

/// Compute liveness for the given body.
/// Uses a backward dataflow analysis.
pub fn compute_liveness(body: &Body<'_>) -> LivenessResult {
    let preds = body.predecessors();
    let mut live_in = IndexVec::from(vec![FxHashSet::default(); body.basic_blocks.len()]);
    let mut live_out = IndexVec::from(vec![FxHashSet::default(); body.basic_blocks.len()]);
    let mut worklist: Vec<BasicBlockId> = body.basic_blocks.indices().collect();

    // Iterate to a predecessor-driven fixpoint.
    while let Some(bb) = worklist.pop() {
        // Compute live_out = Union(live_in(succ))
        let mut out_set = FxHashSet::default();
        if let Some(term) = &body.basic_blocks[bb].terminator {
            for succ in term.kind.successors() {
                for &local in &live_in[succ] {
                    out_set.insert(local);
                }
            }
        }
        live_out[bb] = out_set.clone();

        // Compute live_in based on live_out and block contents
        let mut in_set = out_set;

        let block = &body.basic_blocks[bb];

        // Terminator
        if let Some(term) = &block.terminator {
            transfer_terminator(body, &term.kind, &mut in_set);
        }

        // Statements
        for stmt in block.statements.iter().rev() {
            transfer_statement(&stmt.kind, &mut in_set);
        }

        if in_set != live_in[bb] {
            live_in[bb] = in_set;
            for &p in &preds[bb] {
                if !worklist.contains(&p) {
                    worklist.push(p);
                }
            }
        }
    }

    let mut statement_live = IndexVec::from(
        body.basic_blocks
            .iter()
            .map(|block| vec![LocationLiveness::default(); block.statements.len()])
            .collect::<Vec<_>>(),
    );
    let mut terminator_live =
        IndexVec::from(vec![LocationLiveness::default(); body.basic_blocks.len()]);

    // Re-run each block once from the fixed-point live-out set to retain exact
    // site-level states for code generation.
    for (bb, block) in body.basic_blocks.iter_enumerated() {
        let mut live = live_out[bb].clone();
        terminator_live[bb].after = live.clone();
        if let Some(term) = &block.terminator {
            transfer_terminator(body, &term.kind, &mut live);
        }
        terminator_live[bb].before = live.clone();
        for (index, statement) in block.statements.iter().enumerate().rev() {
            statement_live[bb][index].after = live.clone();
            transfer_statement(&statement.kind, &mut live);
            statement_live[bb][index].before = live.clone();
        }
        debug_assert_eq!(live, live_in[bb]);
    }

    let (statement_initialized, terminator_initialized) = compute_initialization(body);

    LivenessResult {
        live_in,
        live_out,
        statement_live,
        terminator_live,
        statement_initialized,
        terminator_initialized,
    }
}

fn transfer_terminator(body: &Body<'_>, term: &TerminatorKind<'_>, live: &mut FxHashSet<LocalId>) {
    match term {
        TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } => {
            if destination.projection.is_empty() {
                live.remove(&destination.local);
            } else {
                use_place(destination, live);
            }
            use_operand(func, live);
            for arg in args {
                use_operand(arg, live);
            }
        }
        TerminatorKind::SwitchInt { discr, .. } => use_operand(discr, live),
        TerminatorKind::Yield {
            value, resume_arg, ..
        } => {
            if resume_arg.projection.is_empty() {
                live.remove(&resume_arg.local);
            } else {
                use_place(resume_arg, live);
            }
            use_operand(value, live);
        }
        TerminatorKind::Return => {
            live.insert(body.return_local);
        }
        _ => {}
    }
}

fn transfer_statement(statement: &StatementKind<'_>, live: &mut FxHashSet<LocalId>) {
    match statement {
        StatementKind::StorageLive(local) => {
            live.remove(local);
        }
        StatementKind::SetInitialized(_) => {}
        StatementKind::Assign(dest, rvalue) => {
            if dest.projection.is_empty() {
                live.remove(&dest.local);
            } else {
                use_place(dest, live);
            }
            use_rvalue(rvalue, live);
        }
        StatementKind::KeepAlive(operand) => use_operand(operand, live),
        StatementKind::SetDiscriminant { place, .. } => {
            if !place.projection.is_empty() {
                use_place(place, live);
            }
        }
        StatementKind::SourceScope(_) | StatementKind::GcSafepoint(_) | StatementKind::Nop => {}
    }
}

/// Forward must-analysis for whole-local initialization.
///
/// The analysis deliberately does not attempt field-sensitive state. Direct
/// field stores leave an uninitialized aggregate uninitialized. A complete
/// assignment, `SetInitialized` after a lowered aggregate store sequence, or
/// an enum tag publication (`SetDiscriminant`) initializes the whole value. At
/// joins, a local is scannable only when every incoming edge carries an
/// initialized value.
fn compute_initialization(
    body: &Body<'_>,
) -> (
    IndexVec<BasicBlockId, Vec<LocationInitialization>>,
    IndexVec<BasicBlockId, LocationInitialization>,
) {
    let mut in_states: IndexVec<BasicBlockId, Option<FxHashSet<LocalId>>> =
        IndexVec::from(vec![None; body.basic_blocks.len()]);
    let entry_state = body
        .locals
        .iter_enumerated()
        .filter_map(|(local, declaration)| {
            matches!(declaration.kind, crate::mir::LocalKind::Param).then_some(local)
        })
        .collect();
    in_states[body.start_block] = Some(entry_state);
    let mut worklist = vec![body.start_block];

    while let Some(bb) = worklist.pop() {
        let Some(mut state) = in_states[bb].clone() else {
            continue;
        };
        let block = &body.basic_blocks[bb];
        for statement in &block.statements {
            transfer_statement_initialization(&statement.kind, &mut state);
        }
        let Some(terminator) = &block.terminator else {
            continue;
        };
        let (_, edges) = terminator_initialization_edges(&terminator.kind, state);
        for (successor, incoming) in edges {
            let changed = match &mut in_states[successor] {
                Some(existing) => {
                    let merged: FxHashSet<_> = existing.intersection(&incoming).copied().collect();
                    if *existing == merged {
                        false
                    } else {
                        *existing = merged;
                        true
                    }
                }
                slot @ None => {
                    *slot = Some(incoming);
                    true
                }
            };
            if changed && !worklist.contains(&successor) {
                worklist.push(successor);
            }
        }
    }

    let mut statements = IndexVec::from(
        body.basic_blocks
            .iter()
            .map(|block| vec![LocationInitialization::default(); block.statements.len()])
            .collect::<Vec<_>>(),
    );
    let mut terminators = IndexVec::from(vec![
        LocationInitialization::default();
        body.basic_blocks.len()
    ]);
    for (bb, block) in body.basic_blocks.iter_enumerated() {
        let Some(mut state) = in_states[bb].clone() else {
            continue;
        };
        for (index, statement) in block.statements.iter().enumerate() {
            statements[bb][index].before = state.clone();
            transfer_statement_initialization(&statement.kind, &mut state);
            statements[bb][index].after = state.clone();
        }
        terminators[bb].before = state.clone();
        if let Some(terminator) = &block.terminator {
            let (suspended, _) = terminator_initialization_edges(&terminator.kind, state);
            terminators[bb].after = suspended;
        } else {
            terminators[bb].after = state;
        }
    }
    (statements, terminators)
}

fn transfer_statement_initialization(
    statement: &StatementKind<'_>,
    initialized: &mut FxHashSet<LocalId>,
) {
    match statement {
        StatementKind::StorageLive(local) => {
            initialized.remove(local);
        }
        StatementKind::SetInitialized(local) => {
            initialized.insert(*local);
        }
        StatementKind::Assign(destination, rvalue) => {
            apply_rvalue_moves(rvalue, initialized);
            if destination.projection.is_empty() {
                initialized.insert(destination.local);
            }
        }
        StatementKind::SetDiscriminant { place, .. } => {
            if place.projection.is_empty() {
                // Enum construction writes the payload first and publishes the
                // fully initialized value by writing its tag last.
                initialized.insert(place.local);
            }
        }
        // KeepAlive is a non-consuming compiler use even if an earlier MIR
        // phase happened to encode its operand with move syntax.
        StatementKind::KeepAlive(_)
        | StatementKind::SourceScope(_)
        | StatementKind::GcSafepoint(_)
        | StatementKind::Nop => {}
    }
}

fn terminator_initialization_edges(
    terminator: &TerminatorKind<'_>,
    mut initialized: FxHashSet<LocalId>,
) -> (FxHashSet<LocalId>, Vec<(BasicBlockId, FxHashSet<LocalId>)>) {
    match terminator {
        TerminatorKind::Goto { target } => {
            let suspended = initialized.clone();
            (suspended, vec![(*target, initialized)])
        }
        TerminatorKind::SwitchInt {
            discr,
            targets,
            otherwise,
        } => {
            apply_operand_move(discr, &mut initialized);
            let suspended = initialized.clone();
            let mut edges = targets
                .iter()
                .map(|(_, target)| (*target, initialized.clone()))
                .collect::<Vec<_>>();
            edges.push((*otherwise, initialized));
            (suspended, edges)
        }
        TerminatorKind::Call {
            func,
            args,
            destination,
            target,
            unwind,
            ..
        } => {
            apply_operand_move(func, &mut initialized);
            for argument in args {
                apply_operand_move(argument, &mut initialized);
            }
            if destination.projection.is_empty() {
                initialized.remove(&destination.local);
            }
            let suspended = initialized.clone();
            let mut normal = initialized.clone();
            if destination.projection.is_empty() {
                normal.insert(destination.local);
            }
            let mut edges = vec![(*target, normal)];
            if let CallUnwindAction::Cleanup(cleanup) = unwind {
                edges.push((*cleanup, initialized));
            }
            (suspended, edges)
        }
        TerminatorKind::Yield {
            value,
            resume,
            resume_arg,
            cancel,
            unwind,
            ..
        } => {
            apply_operand_move(value, &mut initialized);
            if resume_arg.projection.is_empty() {
                initialized.remove(&resume_arg.local);
            }
            let suspended = initialized.clone();
            let mut resumed = initialized.clone();
            if resume_arg.projection.is_empty() {
                resumed.insert(resume_arg.local);
            }
            let mut edges = vec![(*resume, resumed), (*cancel, initialized.clone())];
            if let CallUnwindAction::Cleanup(cleanup) = unwind {
                edges.push((*cleanup, initialized));
            }
            (suspended, edges)
        }
        TerminatorKind::Return
        | TerminatorKind::ResumeUnwind
        | TerminatorKind::Unreachable
        | TerminatorKind::UnresolvedGoto => (initialized, Vec::new()),
    }
}

fn apply_rvalue_moves(rvalue: &Rvalue<'_>, initialized: &mut FxHashSet<LocalId>) {
    match rvalue {
        Rvalue::Use(operand)
        | Rvalue::UnaryOp { operand, .. }
        | Rvalue::Cast { operand, .. }
        | Rvalue::Repeat { operand, .. } => apply_operand_move(operand, initialized),
        Rvalue::BinaryOp { lhs, rhs, .. } => {
            apply_operand_move(lhs, initialized);
            apply_operand_move(rhs, initialized);
        }
        Rvalue::Aggregate { fields, .. } => {
            for field in fields {
                apply_operand_move(field, initialized);
            }
        }
        Rvalue::Ref { .. }
        | Rvalue::Discriminant { .. }
        | Rvalue::Alloc { .. }
        | Rvalue::Zeroed { .. } => {}
    }
}

fn apply_operand_move(operand: &Operand<'_>, initialized: &mut FxHashSet<LocalId>) {
    match operand {
        Operand::Move(place) if place.projection.is_empty() => {
            initialized.remove(&place.local);
        }
        Operand::CopyWith(place, modifiers) if modifiers.take && place.projection.is_empty() => {
            initialized.remove(&place.local);
        }
        Operand::Copy(_) | Operand::Move(_) | Operand::CopyWith(_, _) | Operand::Constant(_) => {}
    }
}

use crate::mir::{Operand, Place, Rvalue};

fn use_place(place: &Place, live: &mut FxHashSet<LocalId>) {
    live.insert(place.local);
}

fn use_operand(op: &Operand, live: &mut FxHashSet<LocalId>) {
    match op {
        Operand::Copy(p) | Operand::Move(p) | Operand::CopyWith(p, _) => use_place(p, live),
        Operand::Constant(_) => {}
    }
}

fn use_rvalue(rv: &Rvalue, live: &mut FxHashSet<LocalId>) {
    match rv {
        Rvalue::Use(op) => use_operand(op, live),
        Rvalue::UnaryOp { operand, .. } => use_operand(operand, live),
        Rvalue::BinaryOp { lhs, rhs, .. } => {
            use_operand(lhs, live);
            use_operand(rhs, live);
        }
        Rvalue::Cast { operand, .. } => use_operand(operand, live),
        Rvalue::Ref { place, .. } => use_place(place, live),
        Rvalue::Discriminant { place } => use_place(place, live),
        Rvalue::Aggregate { fields, .. } => {
            for f in fields {
                use_operand(f, live);
            }
        }
        Rvalue::Repeat { operand, .. } => use_operand(operand, live),
        Rvalue::Alloc { .. } | Rvalue::Zeroed { .. } => {}
    }
}

#[cfg(test)]
mod tests {
    use super::{MirLocation, compute_liveness};
    use crate::mir::{
        BasicBlockData, CallUnwindAction, GcSafepointKind, LocalKind, Operand, Place, PlaceElem,
        Rvalue, Statement, StatementKind, Terminator, TerminatorKind,
        test_support::{minimal_body, push_temp, with_test_gcx},
    };
    use crate::thir::{FieldIndex, VariantIndex};

    #[test]
    fn statement_liveness_tracks_storage_moves_and_keep_alive_temporally() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let span = body.locals[body.return_local].span;
            let value = push_temp(&mut body, gcx.types.uint);
            let sink = push_temp(&mut body, gcx.types.uint);
            body.basic_blocks[body.start_block].statements = vec![
                Statement {
                    kind: StatementKind::StorageLive(value),
                    span,
                },
                Statement {
                    kind: StatementKind::KeepAlive(Operand::Copy(Place::from_local(value))),
                    span,
                },
                Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(sink),
                        Rvalue::Use(Operand::Move(Place::from_local(value))),
                    ),
                    span,
                },
            ];
            body.basic_blocks[body.start_block].terminator = Some(Terminator {
                kind: TerminatorKind::Unreachable,
                span,
            });

            let result = compute_liveness(&body);
            let before_storage = result.live_before(MirLocation::Statement {
                block: body.start_block,
                index: 0,
            });
            let after_storage = result.live_after(MirLocation::Statement {
                block: body.start_block,
                index: 0,
            });
            let before_move = result.live_before(MirLocation::Statement {
                block: body.start_block,
                index: 2,
            });
            let after_move = result.live_after(MirLocation::Statement {
                block: body.start_block,
                index: 2,
            });

            assert!(!before_storage.contains(&value));
            assert!(after_storage.contains(&value));
            assert!(before_move.contains(&value));
            assert!(!after_move.contains(&value));
            assert!(!before_move.contains(&sink));
        });
    }

    #[test]
    fn branch_and_loop_liveness_reaches_a_fixpoint() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let span = body.locals[body.return_local].span;
            let condition = push_temp(&mut body, gcx.types.bool);
            let left_value = push_temp(&mut body, gcx.types.uint);
            let right_value = push_temp(&mut body, gcx.types.uint);
            let loop_block = body.basic_blocks.push(BasicBlockData {
                note: Some("loop".into()),
                statements: vec![Statement {
                    kind: StatementKind::KeepAlive(Operand::Copy(Place::from_local(left_value))),
                    span,
                }],
                terminator: None,
            });
            let exit = body.basic_blocks.push(BasicBlockData {
                note: Some("exit".into()),
                statements: vec![Statement {
                    kind: StatementKind::KeepAlive(Operand::Copy(Place::from_local(right_value))),
                    span,
                }],
                terminator: Some(Terminator {
                    kind: TerminatorKind::Unreachable,
                    span,
                }),
            });
            body.basic_blocks[body.start_block].terminator = Some(Terminator {
                kind: TerminatorKind::SwitchInt {
                    discr: Operand::Copy(Place::from_local(condition)),
                    targets: vec![(0, exit)],
                    otherwise: loop_block,
                },
                span,
            });
            body.basic_blocks[loop_block].terminator = Some(Terminator {
                kind: TerminatorKind::SwitchInt {
                    discr: Operand::Copy(Place::from_local(condition)),
                    targets: vec![(0, exit)],
                    otherwise: loop_block,
                },
                span,
            });

            let result = compute_liveness(&body);
            assert!(result.live_in[body.start_block].contains(&condition));
            assert!(result.live_in[body.start_block].contains(&left_value));
            assert!(result.live_in[body.start_block].contains(&right_value));
            assert!(result.live_in[loop_block].contains(&left_value));
            assert!(result.live_in[loop_block].contains(&right_value));
        });
    }

    #[test]
    fn call_liveness_unions_normal_and_cleanup_edges_and_kills_full_destination() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let span = body.locals[body.return_local].span;
            let function = push_temp(&mut body, gcx.types.uint);
            let argument = push_temp(&mut body, gcx.types.uint);
            let destination = push_temp(&mut body, gcx.types.uint);
            let cleanup_value = push_temp(&mut body, gcx.types.uint);
            let sink = push_temp(&mut body, gcx.types.uint);
            let normal = body.basic_blocks.push(BasicBlockData {
                note: Some("normal".into()),
                statements: vec![Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(sink),
                        Rvalue::Use(Operand::Copy(Place::from_local(destination))),
                    ),
                    span,
                }],
                terminator: Some(Terminator {
                    kind: TerminatorKind::Unreachable,
                    span,
                }),
            });
            let cleanup = body.basic_blocks.push(BasicBlockData {
                note: Some("cleanup".into()),
                statements: vec![Statement {
                    kind: StatementKind::KeepAlive(Operand::Copy(Place::from_local(cleanup_value))),
                    span,
                }],
                terminator: Some(Terminator {
                    kind: TerminatorKind::ResumeUnwind,
                    span,
                }),
            });
            body.basic_blocks[body.start_block].terminator = Some(Terminator {
                kind: TerminatorKind::Call {
                    func: Operand::Copy(Place::from_local(function)),
                    args: vec![Operand::Move(Place::from_local(argument))],
                    devirt_hint: None,
                    destination: Place::from_local(destination),
                    target: normal,
                    unwind: CallUnwindAction::Cleanup(cleanup),
                },
                span,
            });

            let result = compute_liveness(&body);
            let before = result.live_before_terminator(body.start_block);
            let after = result.live_after_terminator(body.start_block);
            assert!(before.contains(&function));
            assert!(before.contains(&argument));
            assert!(before.contains(&cleanup_value));
            assert!(!before.contains(&destination));
            assert!(after.contains(&destination));
            assert!(after.contains(&cleanup_value));
        });
    }

    #[test]
    fn future_keep_alive_distinguishes_live_across_call_from_dead_local() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let span = body.locals[body.return_local].span;
            let function = push_temp(&mut body, gcx.types.uint);
            let probe = push_temp(&mut body, gcx.types.uint);
            let live_owner = push_temp(&mut body, gcx.types.uint);
            let dead_owner = push_temp(&mut body, gcx.types.uint);
            let destination = push_temp(&mut body, gcx.types.bool);
            for local in [function, probe, live_owner, dead_owner] {
                body.locals[local].kind = LocalKind::Param;
            }
            let continuation = body.basic_blocks.push(BasicBlockData {
                note: Some("continuation".into()),
                statements: vec![Statement {
                    kind: StatementKind::KeepAlive(Operand::Copy(Place::from_local(live_owner))),
                    span,
                }],
                terminator: Some(Terminator {
                    kind: TerminatorKind::Unreachable,
                    span,
                }),
            });
            body.basic_blocks[body.start_block].terminator = Some(Terminator {
                kind: TerminatorKind::Call {
                    func: Operand::Copy(Place::from_local(function)),
                    args: vec![Operand::Copy(Place::from_local(probe))],
                    devirt_hint: None,
                    destination: Place::from_local(destination),
                    target: continuation,
                    unwind: CallUnwindAction::Terminate,
                },
                span,
            });

            let result = compute_liveness(&body);
            let before = result.live_before_terminator(body.start_block);
            let after = result.live_after_terminator(body.start_block);

            // A RuntimeSafepoint call adds the argument-only `probe` root in
            // codegen. Temporal liveness supplies only `live_owner` to the
            // live-across set; `dead_owner` must remain absent.
            assert!(before.contains(&function));
            assert!(before.contains(&probe));
            assert!(!after.contains(&probe));
            assert!(before.contains(&live_owner));
            assert!(after.contains(&live_owner));
            assert!(!before.contains(&dead_owner));
            assert!(!after.contains(&dead_owner));
            assert!(!before.contains(&destination));
        });
    }

    #[test]
    fn projected_call_destination_keeps_its_base_local_live() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let span = body.locals[body.return_local].span;
            let function = push_temp(&mut body, gcx.types.uint);
            let destination_base = push_temp(&mut body, gcx.types.uint);
            let target = body.basic_blocks.push(BasicBlockData {
                note: Some("target".into()),
                statements: Vec::new(),
                terminator: Some(Terminator {
                    kind: TerminatorKind::Unreachable,
                    span,
                }),
            });
            body.basic_blocks[body.start_block].terminator = Some(Terminator {
                kind: TerminatorKind::Call {
                    func: Operand::Copy(Place::from_local(function)),
                    args: Vec::new(),
                    devirt_hint: None,
                    destination: Place {
                        local: destination_base,
                        projection: vec![PlaceElem::Deref],
                    },
                    target,
                    unwind: CallUnwindAction::Terminate,
                },
                span,
            });

            let result = compute_liveness(&body);
            assert!(
                result
                    .live_before_terminator(body.start_block)
                    .contains(&destination_base)
            );
        });
    }

    #[test]
    fn projected_move_keeps_whole_local_conservatively_initialized() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let span = body.locals[body.return_local].span;
            let aggregate = push_temp(&mut body, gcx.types.uint);
            let moved_field = push_temp(&mut body, gcx.types.uint);
            body.locals[aggregate].kind = LocalKind::Param;
            let field = |index| Place {
                local: aggregate,
                projection: vec![PlaceElem::Field(
                    FieldIndex::from_raw(index),
                    gcx.types.uint,
                )],
            };
            body.basic_blocks[body.start_block].statements = vec![
                Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(moved_field),
                        Rvalue::Use(Operand::Move(field(0))),
                    ),
                    span,
                },
                Statement {
                    kind: StatementKind::GcSafepoint(GcSafepointKind::Loop),
                    span,
                },
                Statement {
                    kind: StatementKind::KeepAlive(Operand::Copy(field(1))),
                    span,
                },
            ];
            body.basic_blocks[body.start_block].terminator = Some(Terminator {
                kind: TerminatorKind::Unreachable,
                span,
            });

            let result = compute_liveness(&body);
            let after_move = MirLocation::Statement {
                block: body.start_block,
                index: 0,
            };
            let poll = MirLocation::Statement {
                block: body.start_block,
                index: 1,
            };
            assert!(result.initialized_after(after_move).contains(&aggregate));
            assert!(result.live_before(poll).contains(&aggregate));
            assert!(result.initialized_before(poll).contains(&aggregate));
        });
    }

    #[test]
    fn aggregate_publication_marks_the_whole_local_initialized() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let span = body.locals[body.return_local].span;
            let aggregate = push_temp(&mut body, gcx.types.uint);
            let field_value = push_temp(&mut body, gcx.types.uint);
            body.locals[field_value].kind = LocalKind::Param;
            body.basic_blocks[body.start_block].statements = vec![
                Statement {
                    kind: StatementKind::StorageLive(aggregate),
                    span,
                },
                Statement {
                    kind: StatementKind::Assign(
                        Place {
                            local: aggregate,
                            projection: vec![PlaceElem::Field(
                                FieldIndex::from_raw(0),
                                gcx.types.uint,
                            )],
                        },
                        Rvalue::Use(Operand::Copy(Place::from_local(field_value))),
                    ),
                    span,
                },
                Statement {
                    kind: StatementKind::SetInitialized(aggregate),
                    span,
                },
                Statement {
                    kind: StatementKind::GcSafepoint(GcSafepointKind::Loop),
                    span,
                },
                Statement {
                    kind: StatementKind::KeepAlive(Operand::Copy(Place::from_local(aggregate))),
                    span,
                },
            ];
            body.basic_blocks[body.start_block].terminator = Some(Terminator {
                kind: TerminatorKind::Unreachable,
                span,
            });

            let result = compute_liveness(&body);
            let location = |index| MirLocation::Statement {
                block: body.start_block,
                index,
            };
            assert!(!result.initialized_after(location(1)).contains(&aggregate));
            assert!(!result.initialized_before(location(2)).contains(&aggregate));
            assert!(result.initialized_after(location(2)).contains(&aggregate));
            assert!(result.initialized_before(location(3)).contains(&aggregate));
            assert!(result.live_before(location(3)).contains(&aggregate));
        });
    }

    #[test]
    fn initialization_excludes_future_partial_aggregates_and_moved_values() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let span = body.locals[body.return_local].span;
            let aggregate = push_temp(&mut body, gcx.types.uint);
            let field_value = push_temp(&mut body, gcx.types.uint);
            let sink = push_temp(&mut body, gcx.types.uint);
            body.locals[field_value].kind = LocalKind::Param;
            body.basic_blocks[body.start_block].statements = vec![
                Statement {
                    kind: StatementKind::GcSafepoint(GcSafepointKind::Entry),
                    span,
                },
                Statement {
                    kind: StatementKind::Assign(
                        Place {
                            local: aggregate,
                            projection: vec![PlaceElem::Field(
                                FieldIndex::from_raw(0),
                                gcx.types.uint,
                            )],
                        },
                        Rvalue::Use(Operand::Copy(Place::from_local(field_value))),
                    ),
                    span,
                },
                Statement {
                    kind: StatementKind::SetDiscriminant {
                        place: Place::from_local(aggregate),
                        variant_index: VariantIndex::from_raw(1),
                    },
                    span,
                },
                Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(sink),
                        Rvalue::Use(Operand::Move(Place::from_local(aggregate))),
                    ),
                    span,
                },
            ];
            body.basic_blocks[body.start_block].terminator = Some(Terminator {
                kind: TerminatorKind::Unreachable,
                span,
            });

            let result = compute_liveness(&body);
            let location = |index| MirLocation::Statement {
                block: body.start_block,
                index,
            };
            assert!(!result.initialized_before(location(0)).contains(&aggregate));
            assert!(!result.initialized_after(location(1)).contains(&aggregate));
            assert!(result.initialized_after(location(2)).contains(&aggregate));
            assert!(!result.initialized_after(location(3)).contains(&aggregate));
            assert!(result.initialized_after(location(3)).contains(&sink));
        });
    }

    #[test]
    fn call_initialization_distinguishes_normal_and_cleanup_edges() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let span = body.locals[body.return_local].span;
            let function = push_temp(&mut body, gcx.types.uint);
            let argument = push_temp(&mut body, gcx.types.uint);
            let destination = push_temp(&mut body, gcx.types.uint);
            body.locals[function].kind = LocalKind::Param;
            body.locals[argument].kind = LocalKind::Param;
            let normal = body.basic_blocks.push(BasicBlockData {
                note: Some("normal".into()),
                statements: vec![Statement {
                    kind: StatementKind::KeepAlive(Operand::Copy(Place::from_local(destination))),
                    span,
                }],
                terminator: Some(Terminator {
                    kind: TerminatorKind::Unreachable,
                    span,
                }),
            });
            let cleanup = body.basic_blocks.push(BasicBlockData {
                note: Some("cleanup".into()),
                statements: vec![Statement {
                    kind: StatementKind::KeepAlive(Operand::Copy(Place::from_local(destination))),
                    span,
                }],
                terminator: Some(Terminator {
                    kind: TerminatorKind::ResumeUnwind,
                    span,
                }),
            });
            body.basic_blocks[body.start_block].terminator = Some(Terminator {
                kind: TerminatorKind::Call {
                    func: Operand::Copy(Place::from_local(function)),
                    args: vec![Operand::Move(Place::from_local(argument))],
                    devirt_hint: None,
                    destination: Place::from_local(destination),
                    target: normal,
                    unwind: CallUnwindAction::Cleanup(cleanup),
                },
                span,
            });

            let result = compute_liveness(&body);
            assert!(
                result
                    .initialized_before(MirLocation::Terminator {
                        block: body.start_block
                    })
                    .contains(&argument)
            );
            assert!(
                !result
                    .initialized_after(MirLocation::Terminator {
                        block: body.start_block
                    })
                    .contains(&argument)
            );
            assert!(
                result
                    .initialized_before(MirLocation::Statement {
                        block: normal,
                        index: 0,
                    })
                    .contains(&destination)
            );
            assert!(
                !result
                    .initialized_before(MirLocation::Statement {
                        block: cleanup,
                        index: 0,
                    })
                    .contains(&destination)
            );
        });
    }
}
