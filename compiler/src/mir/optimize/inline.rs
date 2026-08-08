//! MIR Inlining Pass
//!
//! This pass inlines function bodies at call sites when profitable.
//! It supports cross-package inlining by resolving callee bodies via `Gcx`.

use super::MirPass;
use crate::compile::config::{BuildProfile, OptLevel, OptimizationMode};
use crate::compile::context::Gcx;
use crate::hir::{Abi, DefinitionID, KnownAttribute};
use crate::mir::{
    AggregateKind, BasicBlockData, BasicBlockId, Body, CallUnwindAction, Constant, ConstantKind,
    LocalDecl, LocalId, LocalKind, MirPhase, Operand, Place, PlaceElem, Rvalue, SourceScopeData,
    SourceScopeId, Statement, StatementKind, Terminator, TerminatorKind,
};
use crate::sema::models::{GenericArguments, Ty};
use crate::sema::tycheck::utils::instantiate::{
    instantiate_const_with_args, instantiate_ty_with_args,
};
use rustc_hash::FxHashSet;

/// Maximum depth of recursive inlining to prevent infinite expansion.
const MAX_INLINE_DEPTH: u32 = 8;
const FORCED_INLINE_GROWTH_LIMIT: usize = 2_000;
const O1_O2_INLINE_THRESHOLD: usize = 40;
const O3_INLINE_THRESHOLD: usize = 80;
const SIZE_INLINE_THRESHOLD: usize = 20;
const LOOP_CALLSITE_BONUS: usize = 20;
const MAX_CONSTANT_CALLSITE_BONUS: usize = 15;
const CONSTANT_ARGUMENT_BONUS: usize = 5;
const MAX_HEURISTIC_INLINE_COST: usize =
    O3_INLINE_THRESHOLD + LOOP_CALLSITE_BONUS + MAX_CONSTANT_CALLSITE_BONUS;

/// MIR pass that inlines function calls.
pub struct Inline {
    depth: u32,
    growth_used: usize,
    growth_budget: usize,
    forced_growth_used: usize,
}

impl Default for Inline {
    fn default() -> Self {
        Inline {
            depth: 0,
            growth_used: 0,
            growth_budget: 0,
            forced_growth_used: 0,
        }
    }
}

impl<'ctx> MirPass<'ctx> for Inline {
    fn name(&self) -> &'static str {
        "Inline"
    }

    fn run(&mut self, gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> crate::error::CompileResult<()> {
        // Only run inlining on freshly built or CFG-clean MIR
        if !matches!(body.phase, MirPhase::Built | MirPhase::CfgClean) {
            return Ok(());
        }
        let original_cost = body_inline_cost(gcx, body);
        let growth_percent = match gcx.config.codegen.optimization {
            OptimizationMode::Level(OptLevel::O3) => 100,
            _ => 50,
        };
        self.growth_budget = 200usize.max(original_cost.saturating_mul(growth_percent) / 100);
        // Iterate until no more inlining opportunities
        let mut changed = true;
        while changed && self.depth < MAX_INLINE_DEPTH {
            changed = self.inline_pass(gcx, body);
            self.depth += 1;
        }
        Ok(())
    }
}

impl Inline {
    /// Perform one pass of inlining. Returns true if any inlining occurred.
    fn inline_pass<'ctx>(&mut self, gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> bool {
        let mut inlined_any = false;

        // Collect call sites to inline (we can't mutate while iterating)
        let mut call_sites: Vec<_> = body
            .basic_blocks
            .iter_enumerated()
            .filter_map(|(bb_id, block)| {
                let terminator = block.terminator.as_ref()?;
                if let TerminatorKind::Call {
                    func,
                    args,
                    devirt_hint,
                    destination,
                    target,
                    unwind,
                } = &terminator.kind
                {
                    let source_scope = source_scope_at_block_end(block);
                    let logical_caller = body.source_scopes[source_scope].definition;
                    let (callee_id, gen_args) = if let Some(hint) = devirt_hint {
                        (hint.impl_def_id, hint.impl_args)
                    } else {
                        extract_callee(func)?
                    };

                    if let Some((growth, forced, normal_eligible)) = self.should_inline(
                        gcx,
                        body,
                        bb_id,
                        logical_caller,
                        callee_id,
                        gen_args,
                        args,
                    ) {
                        let callee = resolve_callee_body(gcx, callee_id)?;
                        // An unwindful callee must resume into the cleanup edge
                        // that originally belonged to the call site. A
                        // terminate-only site has no such continuation.
                        if body_has_unwind(callee)
                            && !matches!(unwind, CallUnwindAction::Cleanup(_))
                        {
                            return None;
                        }
                        return Some(CallSite {
                            caller_block: bb_id,
                            callee_id,
                            gen_args,
                            args: args.clone(),
                            destination: destination.clone(),
                            target: *target,
                            unwind: *unwind,
                            span: terminator.span,
                            source_scope,
                            growth,
                            forced,
                            normal_eligible,
                        });
                    }
                }
                None
            })
            .collect();

        // Source block order is deterministic, but it must not let incidental
        // early ordinary calls consume the budget intended for a later
        // explicit request. Keep source order within each class while
        // considering profitable `@inline` calls, forced-only `@inline`
        // calls, and ordinary candidates in that order.
        call_sites.sort_by_key(call_site_priority);

        // Perform inlining for each call site
        for site in call_sites {
            if !self.reserve_growth(&site) {
                continue;
            }
            if let Some(callee_body) = resolve_callee_body(gcx, site.callee_id) {
                self.inline_call(gcx, body, &site, callee_body);
                inlined_any = true;
            }
        }

        inlined_any
    }

    /// Determine if a callee should be inlined at this call site.
    fn should_inline<'ctx>(
        &self,
        gcx: Gcx<'ctx>,
        caller: &Body<'ctx>,
        caller_block: BasicBlockId,
        logical_caller: DefinitionID,
        callee_id: DefinitionID,
        gen_args: GenericArguments<'ctx>,
        args: &[Operand<'ctx>],
    ) -> Option<(usize, bool, bool)> {
        // Don't exceed depth limit
        if self.depth >= MAX_INLINE_DEPTH {
            return None;
        }

        // An edge within a recursive SCC is a hard stop, even for @inline.
        if call_graph_reaches(gcx, callee_id, logical_caller) {
            return None;
        }

        // Check function signature for ABI restrictions
        let sig = gcx.get_signature(callee_id);
        match sig.abi {
            Some(Abi::Intrinsic) | Some(Abi::C) | Some(Abi::Blocking) | Some(Abi::Runtime) => {
                return None;
            }
            None => {}
        }

        // Skip inlining if after substitution, the callee body would still have
        // types that need instantiation. This happens when calling methods on
        // generic types where not all type parameters are available.
        if let Some(callee_body) = resolve_callee_body(gcx, callee_id) {
            for local in callee_body.locals.iter() {
                let substituted = instantiate_mono_ty(gcx, local.ty, gen_args);
                if substituted.needs_instantiation() {
                    return None;
                }
            }
        }

        // Check attributes
        let attrs = gcx.attributes_of(callee_id);
        let mut forced = false;
        for attr in attrs.iter() {
            match attr.as_known(gcx) {
                Some(KnownAttribute::Inline) => forced = true,
                Some(KnownAttribute::NoInline) => {
                    return None;
                }
                Some(KnownAttribute::Cfg) => {} // Cfg doesn't affect inlining
                Some(_) => {} // Test, Ignore, ShouldPanic etc. don't affect inlining
                None => {}
            }
        }

        let callee = resolve_callee_body(gcx, callee_id)?;
        let cost = body_inline_cost(gcx, callee);
        let growth = cost.saturating_sub(5);
        let policy =
            inline_profitability_policy(gcx.config.profile, gcx.config.codegen.optimization);
        let loop_bonus = if block_is_cyclic(caller, caller_block) {
            LOOP_CALLSITE_BONUS
        } else {
            0
        };
        let constant_bonus = args
            .iter()
            .filter(|argument| matches!(argument, Operand::Constant(_)))
            .count()
            .saturating_mul(CONSTANT_ARGUMENT_BONUS)
            .min(MAX_CONSTANT_CALLSITE_BONUS);
        let normal_eligible = match policy {
            InlineProfitability::ExplicitOnly => false,
            InlineProfitability::SizeNeutral => growth == 0,
            InlineProfitability::Threshold(base_threshold) => {
                cost <= base_threshold + loop_bonus + constant_bonus
            }
        };
        if forced {
            return (growth <= FORCED_INLINE_GROWTH_LIMIT).then_some((
                growth,
                true,
                normal_eligible,
            ));
        }

        normal_eligible.then_some((growth, false, true))
    }

    /// Reserve this call site's contribution to caller growth.
    ///
    /// An explicit `@inline` call that is independently profitable uses the
    /// ordinary caller budget while room remains. If that budget is exhausted,
    /// or if the call needs the attribute to bypass profitability, it falls
    /// back to the separate forced-inline budget. This keeps annotations from
    /// needlessly consuming the hard override allowance without weakening the
    /// guarantee that an explicit request may bypass normal profitability.
    fn reserve_growth(&mut self, site: &CallSite<'_>) -> bool {
        if site.forced {
            if site.normal_eligible
                && self.growth_used.saturating_add(site.growth) <= self.growth_budget
            {
                self.growth_used = self.growth_used.saturating_add(site.growth);
                return true;
            }

            if self.forced_growth_used.saturating_add(site.growth) > FORCED_INLINE_GROWTH_LIMIT {
                return false;
            }
            self.forced_growth_used = self.forced_growth_used.saturating_add(site.growth);
            return true;
        }

        if self.growth_used.saturating_add(site.growth) > self.growth_budget {
            return false;
        }
        self.growth_used = self.growth_used.saturating_add(site.growth);
        true
    }

    /// Inline a call by splicing the callee's body into the caller.
    fn inline_call<'ctx>(
        &self,
        gcx: Gcx<'ctx>,
        caller: &mut Body<'ctx>,
        site: &CallSite<'ctx>,
        callee: &Body<'ctx>,
    ) {
        let gen_args = site.gen_args;
        let source_scope_map = remap_source_scopes(caller, callee, site);
        let callee_root_scope = source_scope_map[0];

        let (mapped_return_local, return_target) = prepare_inline_return(
            gcx,
            caller,
            &callee.locals[callee.return_local],
            &site.destination,
            gen_args,
            site.target,
            site.span,
            site.source_scope,
        );

        // Copy callee's locals (except return place, which maps to destination)
        // Substitute generic types with concrete types from call site
        let mut local_map: Vec<LocalId> = Vec::with_capacity(callee.locals.len());
        for (callee_local_id, local_decl) in callee.locals.iter_enumerated() {
            if callee_local_id == callee.return_local {
                local_map.push(mapped_return_local);
            } else {
                // Substitute types in the local declaration
                let substituted_ty = instantiate_mono_ty(gcx, local_decl.ty, gen_args);
                // After inlining, Param and Return locals become Temp in the caller.
                // They're no longer actual function parameters/returns.
                let inlined_kind = match local_decl.kind {
                    LocalKind::Param | LocalKind::Return => LocalKind::Temp,
                    other => other,
                };
                let new_decl = LocalDecl {
                    ty: substituted_ty,
                    kind: inlined_kind,
                    mutable: local_decl.mutable,
                    name: local_decl.name,
                    span: local_decl.span,
                };
                let new_local = caller.locals.push(new_decl);
                caller.escape_locals.push(false);
                local_map.push(new_local);
            }
        }

        // Create entry block that assigns arguments to parameters
        let callee_name = gcx.definition_ident(site.callee_id).symbol;
        let inline_entry = caller.basic_blocks.push(BasicBlockData {
            note: Some(format!("inlined: {}", callee_name)),
            statements: vec![Statement {
                kind: StatementKind::SourceScope(callee_root_scope),
                span: site.span,
            }],
            terminator: None,
        });

        // Assign call arguments to callee parameters
        let mut param_idx = 0;
        for (callee_local_id, local_decl) in callee.locals.iter_enumerated() {
            if local_decl.kind == LocalKind::Param {
                if let Some(arg) = site.args.get(param_idx) {
                    let param_local = local_map[callee_local_id.index()];
                    caller.basic_blocks[inline_entry]
                        .statements
                        .push(Statement {
                            kind: StatementKind::Assign(
                                Place::from_local(param_local),
                                Rvalue::Use(arg.clone()),
                            ),
                            span: site.span,
                        });
                }
                param_idx += 1;
            }
        }

        // Copy callee's basic blocks with remapping
        let mut block_map: Vec<BasicBlockId> = Vec::with_capacity(callee.basic_blocks.len());
        for callee_block in callee.basic_blocks.iter() {
            let new_block = caller.basic_blocks.push(BasicBlockData {
                note: callee_block.note.clone(),
                statements: Vec::new(),
                terminator: None,
            });
            block_map.push(new_block);
        }

        // Fill in the blocks with remapped content
        for (callee_bb_id, callee_block) in callee.basic_blocks.iter_enumerated() {
            let new_bb_id = block_map[callee_bb_id.index()];
            caller.basic_blocks[new_bb_id].statements.push(Statement {
                kind: StatementKind::SourceScope(callee_root_scope),
                span: site.span,
            });

            // Remap statements
            for stmt in &callee_block.statements {
                let new_stmt = remap_statement(gcx, stmt, &local_map, &source_scope_map, gen_args);
                caller.basic_blocks[new_bb_id].statements.push(new_stmt);
            }

            // Remap terminator
            if let Some(term) = &callee_block.terminator {
                let new_term = remap_terminator(
                    gcx,
                    term,
                    &local_map,
                    &block_map,
                    return_target,
                    callee.return_local,
                    gen_args,
                    site.unwind,
                );
                caller.basic_blocks[new_bb_id].terminator = Some(new_term);
            }
        }

        // Link entry block to callee's start block
        let callee_start = block_map[callee.start_block.index()];
        caller.basic_blocks[inline_entry].terminator = Some(Terminator {
            kind: TerminatorKind::Goto {
                target: callee_start,
            },
            span: site.span,
        });

        // Replace the original call terminator with a goto to inline entry
        caller.basic_blocks[site.caller_block].terminator = Some(Terminator {
            kind: TerminatorKind::Goto {
                target: inline_entry,
            },
            span: site.span,
        });
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum InlineProfitability {
    ExplicitOnly,
    SizeNeutral,
    Threshold(usize),
}

fn inline_profitability_policy(
    profile: BuildProfile,
    optimization: OptimizationMode,
) -> InlineProfitability {
    match optimization {
        OptimizationMode::Level(OptLevel::O0) => InlineProfitability::ExplicitOnly,
        OptimizationMode::Level(OptLevel::O1 | OptLevel::O2) => {
            InlineProfitability::Threshold(O1_O2_INLINE_THRESHOLD)
        }
        OptimizationMode::Level(OptLevel::O3) => {
            InlineProfitability::Threshold(O3_INLINE_THRESHOLD)
        }
        OptimizationMode::Level(OptLevel::Os) => {
            InlineProfitability::Threshold(SIZE_INLINE_THRESHOLD)
        }
        OptimizationMode::Level(OptLevel::Oz) => InlineProfitability::SizeNeutral,
        OptimizationMode::Baseline => match profile {
            BuildProfile::Debug => InlineProfitability::ExplicitOnly,
            BuildProfile::Release => InlineProfitability::Threshold(O1_O2_INLINE_THRESHOLD),
        },
    }
}

/// Prepare the place used for an inlined callee's return local.
///
/// A call may write through a projection such as `*frame.await_handle`. Mapping
/// the callee return local to only that place's base local loses the projection
/// and can overwrite the frame pointer itself. Projected destinations therefore
/// use a temporary and one continuation assignment that preserves the complete
/// original destination.
fn prepare_inline_return<'ctx>(
    gcx: Gcx<'ctx>,
    caller: &mut Body<'ctx>,
    callee_return: &LocalDecl<'ctx>,
    destination: &Place<'ctx>,
    gen_args: GenericArguments<'ctx>,
    target: BasicBlockId,
    span: crate::span::Span,
    source_scope: SourceScopeId,
) -> (LocalId, BasicBlockId) {
    if destination.projection.is_empty() {
        return (destination.local, target);
    }

    let return_local = caller.locals.push(LocalDecl {
        ty: instantiate_mono_ty(gcx, callee_return.ty, gen_args),
        kind: LocalKind::Temp,
        mutable: true,
        name: callee_return.name,
        span: callee_return.span,
    });
    caller.escape_locals.push(false);

    let return_target = caller.basic_blocks.push(BasicBlockData {
        note: Some("inlined return destination".into()),
        statements: vec![
            Statement {
                kind: StatementKind::SourceScope(source_scope),
                span,
            },
            Statement {
                kind: StatementKind::Assign(
                    destination.clone(),
                    Rvalue::Use(Operand::move_(Place::from_local(return_local))),
                ),
                span,
            },
        ],
        terminator: Some(Terminator {
            kind: TerminatorKind::Goto { target },
            span,
        }),
    });

    (return_local, return_target)
}

/// Information about a call site that may be inlined.
struct CallSite<'ctx> {
    caller_block: BasicBlockId,
    callee_id: DefinitionID,
    #[allow(dead_code)]
    gen_args: GenericArguments<'ctx>,
    args: Vec<Operand<'ctx>>,
    destination: Place<'ctx>,
    target: BasicBlockId,
    unwind: CallUnwindAction,
    span: crate::span::Span,
    source_scope: SourceScopeId,
    growth: usize,
    forced: bool,
    normal_eligible: bool,
}

fn call_site_priority(site: &CallSite<'_>) -> u8 {
    match (site.forced, site.normal_eligible) {
        (true, true) => 0,
        (true, false) => 1,
        (false, _) => 2,
    }
}

fn source_scope_at_block_end(block: &BasicBlockData<'_>) -> SourceScopeId {
    block
        .statements
        .iter()
        .rev()
        .find_map(|statement| match statement.kind {
            StatementKind::SourceScope(scope) => Some(scope),
            _ => None,
        })
        .unwrap_or_else(|| SourceScopeId::from_raw(0))
}

/// Copy the callee's logical scope tree into the caller. The callee's physical
/// root becomes a child of the logical scope containing the callsite.
fn remap_source_scopes(
    caller: &mut Body<'_>,
    callee: &Body<'_>,
    site: &CallSite<'_>,
) -> Vec<SourceScopeId> {
    debug_assert!(!callee.source_scopes.is_empty());
    let mut scope_map = Vec::with_capacity(callee.source_scopes.len());
    for (scope, data) in callee.source_scopes.iter_enumerated() {
        let mapped = if scope.index() == 0 {
            caller.source_scopes.push(SourceScopeData {
                definition: data.definition,
                callsite: Some(site.span),
                parent: Some(site.source_scope),
            })
        } else {
            let parent = data
                .parent
                .expect("non-root source scope must have a parent");
            caller.source_scopes.push(SourceScopeData {
                definition: data.definition,
                callsite: data.callsite,
                parent: Some(scope_map[parent.index()]),
            })
        };
        scope_map.push(mapped);
    }
    scope_map
}

/// Extract callee definition ID and generic args from a call operand.
fn extract_callee<'ctx>(func: &Operand<'ctx>) -> Option<(DefinitionID, GenericArguments<'ctx>)> {
    match func {
        Operand::Constant(c) => {
            if let ConstantKind::Function(def_id, gen_args, _) = c.value {
                Some((def_id, gen_args))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Resolve a callee's MIR body, potentially from another package.
fn resolve_callee_body<'ctx>(gcx: Gcx<'ctx>, callee_id: DefinitionID) -> Option<&'ctx Body<'ctx>> {
    let packages = gcx.store.inline_mir_packages.borrow();
    let package = packages.get(&callee_id.package())?;
    package.functions.get(&callee_id).cloned()
}

/// Whether any supported profitability profile and callsite bonus can select
/// this ordinary body. Dependency metadata uses the same upper bound as the
/// inliner so a cold body never disappears only because its package was cached.
pub(crate) fn is_heuristic_inline_candidate(gcx: Gcx<'_>, body: &Body<'_>) -> bool {
    body_inline_cost(gcx, body) <= MAX_HEURISTIC_INLINE_COST
}

fn body_inline_cost(gcx: Gcx<'_>, body: &Body<'_>) -> usize {
    let mut cost = body.basic_blocks.len().saturating_mul(2);
    for block in &body.basic_blocks {
        for statement in &block.statements {
            cost = cost.saturating_add(match statement.kind {
                StatementKind::Assign(_, Rvalue::Alloc { .. }) => 10,
                StatementKind::SourceScope(_)
                | StatementKind::StorageLive(_)
                | StatementKind::Assign(..)
                | StatementKind::KeepAlive(_)
                | StatementKind::GcSafepoint(_)
                | StatementKind::Nop
                | StatementKind::SetDiscriminant { .. } => 1,
            });
        }
        if let Some(terminator) = &block.terminator {
            cost = cost.saturating_add(match &terminator.kind {
                TerminatorKind::SwitchInt { targets, .. } => 1 + targets.len(),
                TerminatorKind::Call { func, .. } if call_is_panic(gcx, func) => 10,
                TerminatorKind::Call { .. } => 5,
                TerminatorKind::Return
                | TerminatorKind::ResumeUnwind
                | TerminatorKind::Unreachable => 1,
                TerminatorKind::Goto { .. }
                | TerminatorKind::Yield { .. }
                | TerminatorKind::UnresolvedGoto => 0,
            });
        }
    }
    if body
        .basic_blocks
        .indices()
        .any(|block| block_is_cyclic(body, block))
    {
        cost = cost.saturating_add(20);
    }
    cost
}

fn call_is_panic(gcx: Gcx<'_>, func: &Operand<'_>) -> bool {
    let Some((definition, _)) = extract_callee(func) else {
        return false;
    };
    let symbol = gcx.definition_symbol_or_fallback(definition);
    let name = gcx.symbol_text(symbol);
    name == "panic" || name.starts_with("__rt__panic_")
}

fn block_is_cyclic(body: &Body<'_>, block: BasicBlockId) -> bool {
    let mut pending = Vec::new();
    if let Some(terminator) = &body.basic_blocks[block].terminator {
        pending.extend(inline_successors(&terminator.kind));
    }
    let mut visited = FxHashSet::default();
    while let Some(candidate) = pending.pop() {
        if candidate == block {
            return true;
        }
        if !visited.insert(candidate) {
            continue;
        }
        if let Some(terminator) = &body.basic_blocks[candidate].terminator {
            pending.extend(inline_successors(&terminator.kind));
        }
    }
    false
}

fn inline_successors(kind: &TerminatorKind<'_>) -> Vec<BasicBlockId> {
    match kind {
        TerminatorKind::Goto { target } => vec![*target],
        TerminatorKind::SwitchInt {
            targets, otherwise, ..
        } => targets
            .iter()
            .map(|(_, target)| *target)
            .chain(std::iter::once(*otherwise))
            .collect(),
        TerminatorKind::Call { target, unwind, .. } => {
            let mut result = vec![*target];
            if let CallUnwindAction::Cleanup(cleanup) = unwind {
                result.push(*cleanup);
            }
            result
        }
        TerminatorKind::Yield {
            resume,
            cancel,
            unwind,
            ..
        } => {
            let mut result = vec![*resume, *cancel];
            if let CallUnwindAction::Cleanup(cleanup) = unwind {
                result.push(*cleanup);
            }
            result
        }
        TerminatorKind::Return
        | TerminatorKind::ResumeUnwind
        | TerminatorKind::Unreachable
        | TerminatorKind::UnresolvedGoto => Vec::new(),
    }
}

/// True when `from` can reach `target` through canonical direct calls. Testing
/// this for a proposed caller->callee edge is equivalent to rejecting edges
/// within one recursive SCC, without making pass order observable.
fn call_graph_reaches(gcx: Gcx<'_>, from: DefinitionID, target: DefinitionID) -> bool {
    let mut pending = vec![from];
    let mut visited = FxHashSet::default();
    while let Some(definition) = pending.pop() {
        if definition == target {
            return true;
        }
        if !visited.insert(definition) {
            continue;
        }
        let Some(body) = resolve_callee_body(gcx, definition) else {
            continue;
        };
        for block in &body.basic_blocks {
            let Some(terminator) = &block.terminator else {
                continue;
            };
            let TerminatorKind::Call {
                func, devirt_hint, ..
            } = &terminator.kind
            else {
                continue;
            };
            if let Some(hint) = devirt_hint {
                pending.push(hint.impl_def_id);
            } else if let Some((callee, _)) = extract_callee(func) {
                pending.push(callee);
            }
        }
    }
    false
}

fn body_has_unwind(body: &Body<'_>) -> bool {
    body.basic_blocks.iter().any(|bb| {
        bb.terminator.as_ref().is_some_and(|term| match term.kind {
            TerminatorKind::ResumeUnwind => true,
            TerminatorKind::Call {
                unwind: CallUnwindAction::Cleanup(_),
                ..
            } => true,
            _ => false,
        })
    })
}

/// Remap a statement's locals to the caller's namespace and substitute types.
fn remap_statement<'ctx>(
    gcx: Gcx<'ctx>,
    stmt: &Statement<'ctx>,
    local_map: &[LocalId],
    source_scope_map: &[SourceScopeId],
    gen_args: GenericArguments<'ctx>,
) -> Statement<'ctx> {
    Statement {
        kind: match &stmt.kind {
            StatementKind::SourceScope(scope) => {
                StatementKind::SourceScope(source_scope_map[scope.index()])
            }
            StatementKind::StorageLive(local) => {
                StatementKind::StorageLive(local_map[local.index()])
            }
            StatementKind::Assign(place, rvalue) => StatementKind::Assign(
                remap_place(gcx, place, local_map, gen_args),
                remap_rvalue(gcx, rvalue, local_map, gen_args),
            ),
            StatementKind::KeepAlive(operand) => {
                StatementKind::KeepAlive(remap_operand(gcx, operand, local_map, gen_args))
            }
            StatementKind::GcSafepoint(kind) => StatementKind::GcSafepoint(*kind),
            StatementKind::Nop => StatementKind::Nop,
            StatementKind::SetDiscriminant {
                place,
                variant_index,
            } => StatementKind::SetDiscriminant {
                place: remap_place(gcx, place, local_map, gen_args),
                variant_index: *variant_index,
            },
        },
        span: stmt.span,
    }
}

/// Remap a terminator's locals and blocks to the caller's namespace.
fn remap_terminator<'ctx>(
    gcx: Gcx<'ctx>,
    term: &Terminator<'ctx>,
    local_map: &[LocalId],
    block_map: &[BasicBlockId],
    return_target: BasicBlockId,
    _return_local: LocalId,
    gen_args: GenericArguments<'ctx>,
    caller_unwind: CallUnwindAction,
) -> Terminator<'ctx> {
    let kind = match &term.kind {
        TerminatorKind::Goto { target } => TerminatorKind::Goto {
            target: block_map[target.index()],
        },
        TerminatorKind::UnresolvedGoto => TerminatorKind::UnresolvedGoto,
        TerminatorKind::SwitchInt {
            discr,
            targets,
            otherwise,
        } => TerminatorKind::SwitchInt {
            discr: remap_operand(gcx, discr, local_map, gen_args),
            targets: targets
                .iter()
                .map(|(val, bb)| (*val, block_map[bb.index()]))
                .collect(),
            otherwise: block_map[otherwise.index()],
        },
        TerminatorKind::Return => {
            // Return becomes a goto to the call's continuation block
            TerminatorKind::Goto {
                target: return_target,
            }
        }
        TerminatorKind::Unreachable => TerminatorKind::Unreachable,
        TerminatorKind::ResumeUnwind => match caller_unwind {
            CallUnwindAction::Cleanup(target) => TerminatorKind::Goto { target },
            CallUnwindAction::Terminate => TerminatorKind::ResumeUnwind,
        },
        TerminatorKind::Call {
            func,
            args,
            devirt_hint,
            destination,
            target,
            unwind,
        } => TerminatorKind::Call {
            func: remap_operand(gcx, func, local_map, gen_args),
            args: args
                .iter()
                .map(|a| remap_operand(gcx, a, local_map, gen_args))
                .collect(),
            devirt_hint: devirt_hint.as_ref().map(|hint| crate::mir::DevirtHint {
                impl_def_id: hint.impl_def_id,
                impl_args: substitute_gen_args(gcx, hint.impl_args, gen_args),
                concrete_self_ty: instantiate_mono_ty(gcx, hint.concrete_self_ty, gen_args),
            }),
            destination: remap_place(gcx, destination, local_map, gen_args),
            target: block_map[target.index()],
            unwind: match unwind {
                CallUnwindAction::Cleanup(bb) => CallUnwindAction::Cleanup(block_map[bb.index()]),
                CallUnwindAction::Terminate => CallUnwindAction::Terminate,
            },
        },
        TerminatorKind::Yield {
            value,
            resume,
            resume_arg,
            cancel,
            cancel_complete,
            unwind,
        } => TerminatorKind::Yield {
            value: remap_operand(gcx, value, local_map, gen_args),
            resume: block_map[resume.index()],
            resume_arg: remap_place(gcx, resume_arg, local_map, gen_args),
            cancel: block_map[cancel.index()],
            cancel_complete: block_map[cancel_complete.index()],
            unwind: match unwind {
                CallUnwindAction::Cleanup(bb) => CallUnwindAction::Cleanup(block_map[bb.index()]),
                CallUnwindAction::Terminate => CallUnwindAction::Terminate,
            },
        },
    };
    Terminator {
        kind,
        span: term.span,
    }
}

fn remap_place<'ctx>(
    gcx: Gcx<'ctx>,
    place: &Place<'ctx>,
    local_map: &[LocalId],
    gen_args: GenericArguments<'ctx>,
) -> Place<'ctx> {
    Place {
        local: local_map[place.local.index()],
        projection: place
            .projection
            .iter()
            .map(|elem| remap_place_elem(gcx, elem, gen_args))
            .collect(),
    }
}

fn remap_place_elem<'ctx>(
    gcx: Gcx<'ctx>,
    elem: &PlaceElem<'ctx>,
    gen_args: GenericArguments<'ctx>,
) -> PlaceElem<'ctx> {
    match elem {
        PlaceElem::Field(idx, ty) => {
            // Substitute the type in field projections
            PlaceElem::Field(*idx, instantiate_mono_ty(gcx, *ty, gen_args))
        }
        // Other projections don't contain types that need substitution
        PlaceElem::Deref => PlaceElem::Deref,
        PlaceElem::VariantDowncast { name, index } => PlaceElem::VariantDowncast {
            name: *name,
            index: *index,
        },
    }
}

fn remap_operand<'ctx>(
    gcx: Gcx<'ctx>,
    operand: &Operand<'ctx>,
    local_map: &[LocalId],
    gen_args: GenericArguments<'ctx>,
) -> Operand<'ctx> {
    match operand {
        Operand::Copy(place) => Operand::copy(remap_place(gcx, place, local_map, gen_args)),
        Operand::Move(place) => Operand::move_(remap_place(gcx, place, local_map, gen_args)),
        Operand::CopyWith(place, modifiers) => {
            Operand::copy_with(remap_place(gcx, place, local_map, gen_args), *modifiers)
        }
        Operand::Constant(c) => Operand::Constant(remap_constant(gcx, c, gen_args)),
    }
}

fn remap_constant<'ctx>(
    gcx: Gcx<'ctx>,
    c: &Constant<'ctx>,
    gen_args: GenericArguments<'ctx>,
) -> Constant<'ctx> {
    let ty = instantiate_mono_ty(gcx, c.ty, gen_args);
    let value = match &c.value {
        // Function constants keep their def_id but substitute their generic args
        ConstantKind::Function(def_id, fn_gen_args, sig) => {
            // Substitute the function's generic args with the inlined generic args
            let substituted_args = substitute_gen_args(gcx, *fn_gen_args, gen_args);
            let substituted_sig = instantiate_mono_ty(gcx, *sig, gen_args);
            ConstantKind::Function(*def_id, substituted_args, substituted_sig)
        }
        // Const parameters need to be substituted with their concrete values
        ConstantKind::ConstParam(param) => {
            if let Some(arg) = gen_args.get(param.index) {
                match arg {
                    crate::sema::models::GenericArgument::Const(sema_const) => {
                        // Convert sema Const to MIR ConstantKind
                        match &sema_const.kind {
                            crate::sema::models::ConstKind::Value(val) => {
                                sema_const_value_to_mir(*val).unwrap_or_else(|| c.value.clone())
                            }
                            crate::sema::models::ConstKind::Param(inner_param) => {
                                // Still a param - pass it through (shouldn't happen with valid gen_args)
                                ConstantKind::ConstParam(*inner_param)
                            }
                            crate::sema::models::ConstKind::Infer(_) => {
                                // Inference should be resolved by now
                                c.value.clone()
                            }
                        }
                    }
                    crate::sema::models::GenericArgument::Type(_) => {
                        // Type argument at const param index - keep original
                        c.value.clone()
                    }
                }
            } else {
                // No substitution available - keep original
                c.value.clone()
            }
        }
        // Other constants are copied as-is (Bool, Rune, String, Integer, Float, Unit)
        other => other.clone(),
    };
    Constant { ty, value }
}

/// Convert a sema ConstValue to MIR ConstantKind
fn sema_const_value_to_mir(val: crate::sema::models::ConstValue) -> Option<ConstantKind<'static>> {
    use crate::sema::models::ConstValue;
    Some(match val {
        ConstValue::Integer(i) => ConstantKind::Integer(i as u64),
        ConstValue::Bool(b) => ConstantKind::Bool(b),
        ConstValue::Rune(r) => ConstantKind::Rune(r),
        ConstValue::String(s) => ConstantKind::String(s),
        ConstValue::Float(f) => ConstantKind::Float(f),
        ConstValue::Unit => ConstantKind::Unit,
        ConstValue::EnumUnitVariant(_) => return None,
    })
}

/// Substitute generic arguments within another set of generic arguments.
fn substitute_gen_args<'ctx>(
    gcx: Gcx<'ctx>,
    args: GenericArguments<'ctx>,
    substitution: GenericArguments<'ctx>,
) -> GenericArguments<'ctx> {
    use crate::sema::models::GenericArgument;

    if args.is_empty() || substitution.is_empty() {
        return args;
    }

    let new_args: Vec<_> = args
        .iter()
        .map(|arg| match arg {
            GenericArgument::Type(ty) => {
                GenericArgument::Type(instantiate_mono_ty(gcx, *ty, substitution))
            }
            GenericArgument::Const(c) => {
                GenericArgument::Const(instantiate_const_with_args(gcx, *c, substitution))
            }
        })
        .collect();

    gcx.store.interners.intern_generic_args(new_args)
}

fn remap_rvalue<'ctx>(
    gcx: Gcx<'ctx>,
    rvalue: &Rvalue<'ctx>,
    local_map: &[LocalId],
    gen_args: GenericArguments<'ctx>,
) -> Rvalue<'ctx> {
    match rvalue {
        Rvalue::Use(op) => Rvalue::Use(remap_operand(gcx, op, local_map, gen_args)),
        Rvalue::UnaryOp { op, operand } => Rvalue::UnaryOp {
            op: *op,
            operand: remap_operand(gcx, operand, local_map, gen_args),
        },
        Rvalue::BinaryOp { op, lhs, rhs } => Rvalue::BinaryOp {
            op: *op,
            lhs: remap_operand(gcx, lhs, local_map, gen_args),
            rhs: remap_operand(gcx, rhs, local_map, gen_args),
        },
        Rvalue::Cast { operand, ty, kind } => Rvalue::Cast {
            operand: remap_operand(gcx, operand, local_map, gen_args),
            ty: instantiate_mono_ty(gcx, *ty, gen_args),
            kind: *kind,
        },
        Rvalue::Ref { mutable, place } => Rvalue::Ref {
            mutable: *mutable,
            place: remap_place(gcx, place, local_map, gen_args),
        },
        Rvalue::Discriminant { place } => Rvalue::Discriminant {
            place: remap_place(gcx, place, local_map, gen_args),
        },
        Rvalue::Alloc { ty } => Rvalue::Alloc {
            ty: instantiate_mono_ty(gcx, *ty, gen_args),
        },
        Rvalue::Aggregate { kind, fields } => Rvalue::Aggregate {
            kind: remap_aggregate_kind(gcx, kind, gen_args),
            fields: fields
                .iter()
                .map(|f| remap_operand(gcx, f, local_map, gen_args))
                .collect(),
        },
        Rvalue::Repeat {
            operand,
            count,
            element,
        } => Rvalue::Repeat {
            operand: remap_operand(gcx, operand, local_map, gen_args),
            count: *count,
            element: instantiate_mono_ty(gcx, *element, gen_args),
        },
    }
}

fn remap_aggregate_kind<'ctx>(
    gcx: Gcx<'ctx>,
    kind: &AggregateKind<'ctx>,
    gen_args: GenericArguments<'ctx>,
) -> AggregateKind<'ctx> {
    match kind {
        AggregateKind::Tuple => AggregateKind::Tuple,
        AggregateKind::Array { len, element } => AggregateKind::Array {
            len: *len,
            element: instantiate_mono_ty(gcx, *element, gen_args),
        },
        AggregateKind::Adt {
            def_id,
            variant_index,
            generic_args: adt_gen_args,
        } => AggregateKind::Adt {
            def_id: *def_id,
            variant_index: *variant_index,
            generic_args: substitute_gen_args(gcx, *adt_gen_args, gen_args),
        },
        AggregateKind::Closure {
            def_id,
            captured_generics,
        } => AggregateKind::Closure {
            def_id: *def_id,
            captured_generics: substitute_gen_args(gcx, *captured_generics, gen_args),
        },
    }
}

#[inline]
fn instantiate_mono_ty<'ctx>(
    gcx: Gcx<'ctx>,
    ty: Ty<'ctx>,
    args: GenericArguments<'ctx>,
) -> Ty<'ctx> {
    // Inlining happens before full monomorphization. Substituting a callee body
    // into a generic caller may legitimately leave the caller's own type
    // parameters in the remapped MIR, so post-monomorphization normalization is
    // too strong here.
    instantiate_ty_with_args(gcx, ty, args)
}

#[cfg(test)]
mod tests {
    use super::{
        CallSite, FORCED_INLINE_GROWTH_LIMIT, Inline, InlineProfitability,
        MAX_HEURISTIC_INLINE_COST, body_inline_cost, call_graph_reaches, call_site_priority,
        inline_profitability_policy, is_heuristic_inline_candidate, prepare_inline_return,
        remap_source_scopes, remap_statement, remap_terminator,
    };
    use crate::PackageIndex;
    use crate::compile::config::{BuildProfile, OptLevel, OptimizationMode};
    use crate::hir::DefinitionID;
    use crate::mir::{
        BasicBlockData, CallUnwindAction, Constant, ConstantKind, LocalDecl, LocalKind, MirPackage,
        Operand, Place, PlaceElem, Rvalue, SourceScopeData, SourceScopeId, Statement,
        StatementKind, Terminator, TerminatorKind, test_support,
    };
    use crate::sema::models::GenericArguments;
    use crate::sema::resolve::models::DefinitionIndex;

    #[test]
    fn optimization_profiles_have_fixed_profitability_policies() {
        assert_eq!(
            inline_profitability_policy(BuildProfile::Debug, OptimizationMode::Level(OptLevel::O0),),
            InlineProfitability::ExplicitOnly
        );
        assert_eq!(
            inline_profitability_policy(
                BuildProfile::Release,
                OptimizationMode::Level(OptLevel::O1),
            ),
            InlineProfitability::Threshold(40)
        );
        assert_eq!(
            inline_profitability_policy(
                BuildProfile::Release,
                OptimizationMode::Level(OptLevel::O2),
            ),
            InlineProfitability::Threshold(40)
        );
        assert_eq!(
            inline_profitability_policy(
                BuildProfile::Release,
                OptimizationMode::Level(OptLevel::O3),
            ),
            InlineProfitability::Threshold(80)
        );
        assert_eq!(
            inline_profitability_policy(
                BuildProfile::Release,
                OptimizationMode::Level(OptLevel::Os),
            ),
            InlineProfitability::Threshold(20)
        );
        assert_eq!(
            inline_profitability_policy(
                BuildProfile::Release,
                OptimizationMode::Level(OptLevel::Oz),
            ),
            InlineProfitability::SizeNeutral
        );
        assert_eq!(
            inline_profitability_policy(BuildProfile::Debug, OptimizationMode::Baseline),
            InlineProfitability::ExplicitOnly
        );
        assert_eq!(
            inline_profitability_policy(BuildProfile::Release, OptimizationMode::Baseline),
            InlineProfitability::Threshold(40)
        );
    }

    #[test]
    fn metadata_candidate_bound_covers_the_largest_legal_callsite_threshold() {
        assert_eq!(MAX_HEURISTIC_INLINE_COST, 115);
        test_support::with_test_gcx(|gcx| {
            let mut body = test_support::minimal_body(gcx);
            let span = body.locals[body.return_local].span;
            while body_inline_cost(gcx, &body) <= 40 {
                body.basic_blocks[body.start_block]
                    .statements
                    .push(Statement {
                        kind: StatementKind::Nop,
                        span,
                    });
            }
            assert!(body_inline_cost(gcx, &body) <= MAX_HEURISTIC_INLINE_COST);
            assert!(is_heuristic_inline_candidate(gcx, &body));

            while body_inline_cost(gcx, &body) <= MAX_HEURISTIC_INLINE_COST {
                body.basic_blocks[body.start_block]
                    .statements
                    .push(Statement {
                        kind: StatementKind::Nop,
                        span,
                    });
            }
            assert!(!is_heuristic_inline_candidate(gcx, &body));
        });
    }

    #[test]
    fn forced_inline_uses_normal_budget_before_override_budget() {
        let mut inliner = Inline {
            growth_budget: 30,
            ..Inline::default()
        };
        let mut site = budget_test_site(20, true, true);

        assert!(inliner.reserve_growth(&site));
        assert_eq!(inliner.growth_used, 20);
        assert_eq!(inliner.forced_growth_used, 0);

        // There is not enough ordinary room for a second profitable call, so
        // the explicit request falls back to the forced-inline allowance.
        assert!(inliner.reserve_growth(&site));
        assert_eq!(inliner.growth_used, 20);
        assert_eq!(inliner.forced_growth_used, 20);

        // Calls that need the annotation never consume ordinary growth, and
        // the hard forced-growth cap remains authoritative.
        site.normal_eligible = false;
        site.growth = FORCED_INLINE_GROWTH_LIMIT - 20;
        assert!(inliner.reserve_growth(&site));
        assert_eq!(inliner.forced_growth_used, FORCED_INLINE_GROWTH_LIMIT);
        site.growth = 1;
        assert!(!inliner.reserve_growth(&site));
    }

    #[test]
    fn ordinary_inline_cannot_fall_back_to_forced_budget() {
        let mut inliner = Inline {
            growth_budget: 10,
            ..Inline::default()
        };
        let site = budget_test_site(11, false, true);

        assert!(!inliner.reserve_growth(&site));
        assert_eq!(inliner.growth_used, 0);
        assert_eq!(inliner.forced_growth_used, 0);
    }

    #[test]
    fn worklist_prioritizes_explicit_requests_over_ordinary_calls() {
        let mut sites = [
            budget_test_site(1, false, true),
            budget_test_site(1, true, false),
            budget_test_site(1, true, true),
        ];

        sites.sort_by_key(call_site_priority);

        assert!(sites[0].forced && sites[0].normal_eligible);
        assert!(sites[1].forced && !sites[1].normal_eligible);
        assert!(!sites[2].forced);
    }

    fn budget_test_site(growth: usize, forced: bool, normal_eligible: bool) -> CallSite<'static> {
        CallSite {
            caller_block: crate::mir::BasicBlockId::from_raw(0),
            callee_id: DefinitionID::new(PackageIndex::new(1), DefinitionIndex::from_raw(99)),
            gen_args: GenericArguments::empty(),
            args: Vec::new(),
            destination: Place::from_local(crate::mir::LocalId::from_raw(0)),
            target: crate::mir::BasicBlockId::from_raw(0),
            unwind: CallUnwindAction::Terminate,
            span: crate::span::Span::empty(crate::span::FileID::from_raw(0)),
            source_scope: SourceScopeId::from_raw(0),
            growth,
            forced,
            normal_eligible,
        }
    }

    #[test]
    fn direct_call_graph_detects_recursive_sccs() {
        test_support::with_test_gcx(|gcx| {
            let package = PackageIndex::new(1);
            let a = DefinitionID::new(package, DefinitionIndex::from_raw(10));
            let b = DefinitionID::new(package, DefinitionIndex::from_raw(11));
            let outside = DefinitionID::new(package, DefinitionIndex::from_raw(12));

            let make_body = |owner, callee: Option<DefinitionID>| {
                let mut body = test_support::minimal_body(gcx);
                body.owner = owner;
                body.source_scopes[SourceScopeId::from_raw(0)].definition = owner;
                if let Some(callee) = callee {
                    let span = body.locals[body.return_local].span;
                    let target = body.basic_blocks.push(BasicBlockData {
                        note: Some("return".into()),
                        statements: Vec::new(),
                        terminator: Some(Terminator {
                            kind: TerminatorKind::Return,
                            span,
                        }),
                    });
                    body.basic_blocks[body.start_block].terminator = Some(Terminator {
                        kind: TerminatorKind::Call {
                            func: Operand::Constant(Constant {
                                ty: gcx.types.uint,
                                value: ConstantKind::Function(
                                    callee,
                                    GenericArguments::empty(),
                                    gcx.types.uint,
                                ),
                            }),
                            args: Vec::new(),
                            devirt_hint: None,
                            destination: Place::from_local(body.return_local),
                            target,
                            unwind: CallUnwindAction::Terminate,
                        },
                        span,
                    });
                }
                body
            };

            let a_body = gcx.store.arenas.mir_bodies.alloc(make_body(a, Some(b)));
            let b_body = gcx.store.arenas.mir_bodies.alloc(make_body(b, Some(a)));
            let outside_body = gcx.store.arenas.mir_bodies.alloc(make_body(outside, None));
            let package_body = gcx.store.alloc_mir_package(MirPackage {
                functions: [(a, &*a_body), (b, &*b_body), (outside, &*outside_body)]
                    .into_iter()
                    .collect(),
                entry: None,
            });
            gcx.store
                .inline_mir_packages
                .borrow_mut()
                .insert(package, package_body);

            assert!(call_graph_reaches(gcx, a, b));
            assert!(call_graph_reaches(gcx, b, a));
            assert!(!call_graph_reaches(gcx, a, outside));
            assert!(!call_graph_reaches(gcx, outside, a));
        });
    }

    #[test]
    fn inlined_resume_targets_the_callers_cleanup_edge() {
        test_support::with_test_gcx(|gcx| {
            let body = test_support::minimal_body(gcx);
            let cleanup = body.start_block;
            let term = Terminator {
                kind: TerminatorKind::ResumeUnwind,
                span: body.locals[body.return_local].span,
            };
            let remapped = remap_terminator(
                gcx,
                &term,
                &[],
                &[],
                body.start_block,
                body.return_local,
                GenericArguments::empty(),
                CallUnwindAction::Cleanup(cleanup),
            );
            assert!(matches!(
                remapped.kind,
                TerminatorKind::Goto { target } if target == cleanup
            ));
        });
    }

    #[test]
    fn projected_call_destination_is_preserved_after_inlining() {
        test_support::with_test_gcx(|gcx| {
            let mut caller = test_support::minimal_body(gcx);
            let target = caller.start_block;
            let base = test_support::push_temp(&mut caller, gcx.types.void);
            let destination = Place {
                local: base,
                projection: vec![PlaceElem::Deref],
            };
            let callee_return = LocalDecl {
                ty: gcx.types.void,
                kind: LocalKind::Return,
                mutable: true,
                name: None,
                span: caller.locals[caller.return_local].span,
            };

            let (mapped_return, return_target) = prepare_inline_return(
                gcx,
                &mut caller,
                &callee_return,
                &destination,
                GenericArguments::empty(),
                target,
                callee_return.span,
                crate::mir::SourceScopeId::from_raw(0),
            );

            assert_ne!(mapped_return, destination.local);
            let block = &caller.basic_blocks[return_target];
            assert!(matches!(
                &block.statements[1].kind,
                StatementKind::Assign(place, Rvalue::Use(Operand::Move(source)))
                    if place == &destination
                        && *source == Place::from_local(mapped_return)
            ));
            assert!(matches!(
                block.terminator.as_ref().map(|term| &term.kind),
                Some(TerminatorKind::Goto { target: actual }) if *actual == target
            ));
        });
    }

    #[test]
    fn nested_inline_source_scopes_are_reparented_at_the_callsite() {
        test_support::with_test_gcx(|gcx| {
            let mut caller = test_support::minimal_body(gcx);
            let caller_inline_definition =
                DefinitionID::new(PackageIndex::new(1), DefinitionIndex::from_raw(10));
            let caller_inline_scope = caller.source_scopes.push(SourceScopeData {
                definition: caller_inline_definition,
                callsite: Some(caller.locals[caller.return_local].span),
                parent: Some(SourceScopeId::from_raw(0)),
            });

            let mut callee = test_support::minimal_body(gcx);
            let callee_definition =
                DefinitionID::new(PackageIndex::new(1), DefinitionIndex::from_raw(20));
            callee.owner = callee_definition;
            callee.source_scopes[SourceScopeId::from_raw(0)].definition = callee_definition;
            let nested_definition =
                DefinitionID::new(PackageIndex::new(2), DefinitionIndex::from_raw(30));
            let nested_scope = callee.source_scopes.push(SourceScopeData {
                definition: nested_definition,
                callsite: Some(callee.locals[callee.return_local].span),
                parent: Some(SourceScopeId::from_raw(0)),
            });

            let span = caller.locals[caller.return_local].span;
            let site = CallSite {
                caller_block: caller.start_block,
                callee_id: callee_definition,
                gen_args: GenericArguments::empty(),
                args: Vec::new(),
                destination: Place::from_local(caller.return_local),
                target: caller.start_block,
                unwind: CallUnwindAction::Terminate,
                span,
                source_scope: caller_inline_scope,
                growth: 0,
                forced: false,
                normal_eligible: true,
            };
            let scope_map = remap_source_scopes(&mut caller, &callee, &site);

            assert_eq!(
                caller.source_scopes[scope_map[0]].parent,
                Some(caller_inline_scope)
            );
            assert_eq!(
                caller.source_scopes[scope_map[nested_scope.index()]].parent,
                Some(scope_map[0])
            );
            assert_eq!(
                caller.source_scopes[scope_map[nested_scope.index()]].definition,
                nested_definition
            );

            let marker = Statement {
                kind: StatementKind::SourceScope(nested_scope),
                span,
            };
            let remapped =
                remap_statement(gcx, &marker, &[], &scope_map, GenericArguments::empty());
            assert!(matches!(
                remapped.kind,
                StatementKind::SourceScope(scope)
                    if scope == scope_map[nested_scope.index()]
            ));
        });
    }
}
