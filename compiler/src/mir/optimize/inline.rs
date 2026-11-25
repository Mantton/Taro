//! MIR Inlining Pass
//!
//! This pass inlines function bodies at call sites when profitable.
//! It supports cross-package inlining by resolving callee bodies via `Gcx`.

use super::MirPass;
use crate::compile::config::{BuildProfile, OptLevel, OptimizationMode};
use crate::compile::context::Gcx;
use crate::hir::{Abi, DefinitionID, KnownAttribute};
use crate::mir::analysis::control_flow::block_is_cyclic;
use crate::mir::{
    AggregateKind, BasicBlockData, BasicBlockId, Body, CallUnwindAction, Constant, ConstantKind,
    LocalDecl, LocalId, LocalKind, MirPhase, Operand, Place, PlaceElem, Rvalue, SourceScopeData,
    SourceScopeId, Statement, StatementKind, Terminator, TerminatorKind,
};
use crate::sema::models::{ConstKind, GenericArgument, GenericArguments, Ty};
use crate::sema::tycheck::utils::instantiate::{
    instantiate_generic_args, instantiate_ty_with_args,
};
use crate::specialize::{InstanceKind, resolve_instance};
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
const LEAF_CALLSITE_BONUS: usize = 20;
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
        self.run_body(gcx, body, GenericArguments::empty())?;
        Ok(())
    }
}

/// Generic calls skipped by shared MIR optimization become eligible once their
/// caller's arguments are concrete. Expand them on the isolated instance before
/// escape placement and safepoints, retaining the ordinary growth/recursion
/// limits. Non-generic callers have already had their opportunity.
pub(super) fn inline_instance<'ctx>(
    gcx: Gcx<'ctx>,
    body: &mut Body<'ctx>,
    args: GenericArguments<'ctx>,
) -> crate::error::CompileResult<bool> {
    if args.is_empty() {
        return Ok(false);
    }
    Inline::default().run_body(gcx, body, args)
}

impl Inline {
    fn run_body<'ctx>(
        &mut self,
        gcx: Gcx<'ctx>,
        body: &mut Body<'ctx>,
        caller_args: GenericArguments<'ctx>,
    ) -> crate::error::CompileResult<bool> {
        let original_cost = body_inline_cost(gcx, body);
        let growth_percent = match gcx.config.codegen.optimization {
            OptimizationMode::Level(OptLevel::O3) => 100,
            _ => 50,
        };
        self.growth_budget = 200usize.max(original_cost.saturating_mul(growth_percent) / 100);
        // Iterate until no more inlining opportunities
        let mut changed = true;
        let mut any_changed = false;
        while changed && self.depth < MAX_INLINE_DEPTH {
            changed = self.inline_pass(gcx, body, caller_args);
            any_changed |= changed;
            gcx.dcx().ok()?;
            self.depth += 1;
        }
        // The last ordinary expansion can expose a one-intrinsic forwarder.
        // Finish those zero-growth calls without expanding another call chain.
        if changed && self.depth == MAX_INLINE_DEPTH {
            any_changed |= self.inline_pass(gcx, body, caller_args);
            gcx.dcx().ok()?;
        }
        Ok(any_changed)
    }

    /// Perform one pass of inlining. Returns true if any inlining occurred.
    fn inline_pass<'ctx>(
        &mut self,
        gcx: Gcx<'ctx>,
        body: &mut Body<'ctx>,
        caller_args: GenericArguments<'ctx>,
    ) -> bool {
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
                    destination,
                    target,
                    unwind,
                } = &terminator.kind
                {
                    let source_scope = source_scope_at_block_end(block);
                    let (callee_id, gen_args) = extract_callee(func)?;
                    let gen_args = instantiate_generic_args(gcx, gen_args, caller_args);
                    // Instance resolution expects concrete arguments. Resolving
                    // an impl while a method parameter still belongs to the
                    // generic caller can substitute Self into that parameter.
                    if gen_args.iter().any(|arg| match arg {
                        GenericArgument::Type(ty) => {
                            ty.needs_instantiation() || ty.contains_inference()
                        }
                        GenericArgument::Const(c) => {
                            matches!(c.kind, ConstKind::Param(_) | ConstKind::Infer(_))
                                || c.ty.needs_instantiation()
                                || c.ty.contains_inference()
                        }
                    }) {
                        return None;
                    }
                    let instance = resolve_instance(gcx, callee_id, gen_args);
                    let InstanceKind::Item(callee_id) = instance.kind() else {
                        // A requirement's default body must not bypass a runtime
                        // override, even when the requirement requests @inline.
                        return None;
                    };
                    if crate::mir::analysis::class_self::validate_instance(
                        gcx,
                        callee_id,
                        instance.args(),
                    )
                    .is_err()
                    {
                        return None;
                    }
                    // Class dispatch remains dynamic even when a base body is
                    // tiny or requests inlining. Final methods remain direct.
                    if gcx.is_virtual_class_method(callee_id) {
                        return None;
                    }
                    // Opening is a dynamic choice of a real concrete generic
                    // body, not an instance whose T is the erased container.
                    if matches!(
                        crate::sema::lowering::erased_opening::plan(
                            gcx,
                            callee_id,
                            instance.args()
                        ),
                        Ok(Some(_))
                    ) {
                        return None;
                    }
                    let gen_args = instance.args();

                    if let Some((growth, forced, normal_eligible)) = self.should_inline(
                        gcx,
                        body,
                        bb_id,
                        source_scope,
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

        if gcx.dcx().has_error() {
            return false;
        }

        // Perform inlining for each call site
        for site in call_sites {
            if !self.reserve_growth(&site) {
                continue;
            }
            if let Some(callee_body) = resolve_callee_body(gcx, site.callee_id) {
                if crate::specialize::collect::validate_instance_types(
                    gcx,
                    crate::specialize::Instance::item(site.callee_id, site.gen_args),
                    callee_body,
                )
                .is_err()
                {
                    continue;
                }
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
        source_scope: SourceScopeId,
        callee_id: DefinitionID,
        gen_args: GenericArguments<'ctx>,
        args: &[Operand<'ctx>],
    ) -> Option<(usize, bool, bool)> {
        // Flatten a profitable wrapper even when its callee can call back.
        // Stop at every actual inline ancestor, including the native caller,
        // so recursive expansion retains a real call and its entry GC poll.
        if callee_in_inline_chain(caller, source_scope, callee_id) {
            return None;
        }

        if gcx.is_class_payload_factory(callee_id) {
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
        // A scalar pointer intrinsic forwarder replaces a call with address
        // arithmetic or one integer load.
        // Charging its MIR scaffolding as growth can leave managed calls in a
        // large dispatch loop even though the annotation requests expansion.
        let zero_growth_wrapper = forced
            && (crate::mir::analysis::effects::is_pointer_offset_wrapper(gcx, callee)
                || crate::mir::analysis::effects::is_scalar_pointer_read_wrapper(
                    gcx, callee, gen_args,
                )
                || crate::mir::analysis::effects::is_string_header_wrapper(gcx, callee, gen_args));
        let growth = if zero_growth_wrapper {
            0
        } else {
            cost.saturating_sub(5)
        };
        if self.depth >= MAX_INLINE_DEPTH && !zero_growth_wrapper {
            return None;
        }
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
                // A bounded leaf loses its managed call/entry overhead and
                // exposes reference loads and stores to scalar replacement.
                // Keep size-oriented profiles on their existing thresholds.
                let leaf_bonus = if base_threshold >= O1_O2_INLINE_THRESHOLD {
                    leaf_callsite_bonus(callee)
                } else {
                    0
                };
                cost <= base_threshold + loop_bonus + constant_bonus + leaf_bonus
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
                let substituted_ty = instantiate_inline_local_ty(gcx, local_decl.ty, gen_args);
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
                local_map.push(new_local);
            }
        }

        // Create entry block that assigns arguments to parameters
        let callee_name = gcx.definition_ident(site.callee_id).symbol;
        let inline_entry = caller.basic_blocks.push(BasicBlockData {
            note: Some(format!("inlined: {}", gcx.symbol_text(callee_name))),
            statements: vec![Statement {
                kind: StatementKind::SourceScope(callee_root_scope),
                span: site.span,
            }],
            terminator: None,
        });

        // Parameters and compiler temporaries without declaration markers have
        // one storage lifetime per invocation. Preserve that boundary when a
        // call is inlined into a loop: later escape placement must allocate a
        // fresh cell on each call, rather than once at the caller's entry.
        let declared: FxHashSet<_> = callee
            .basic_blocks
            .iter()
            .flat_map(|block| &block.statements)
            .filter_map(|statement| match statement.kind {
                StatementKind::StorageLive(local) => Some(local),
                _ => None,
            })
            .collect();
        for local in callee.locals.indices() {
            if local != callee.return_local && !declared.contains(&local) {
                caller.basic_blocks[inline_entry]
                    .statements
                    .push(Statement {
                        kind: StatementKind::StorageLive(local_map[local.index()]),
                        span: site.span,
                    });
            }
        }

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
    if destination.projection.is_empty() && callee_return.kind != LocalKind::ConstructorSelf {
        return (destination.local, target);
    }

    let return_local = caller.locals.push(LocalDecl {
        ty: instantiate_inline_local_ty(gcx, callee_return.ty, gen_args),
        kind: if callee_return.kind == LocalKind::ConstructorSelf {
            LocalKind::ConstructorSelf
        } else {
            LocalKind::Temp
        },
        mutable: true,
        name: callee_return.name,
        span: callee_return.span,
    });

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
                    Rvalue::Use(Operand::copy(Place::from_local(return_local))),
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
    package.functions.get(&callee_id).copied()
}

/// Whether any supported profitability profile and callsite bonus can select
/// this ordinary body. Dependency metadata uses the same upper bound as the
/// inliner so a cold body never disappears only because its package was cached.
pub(crate) fn is_heuristic_inline_candidate(gcx: Gcx<'_>, body: &Body<'_>) -> bool {
    body_inline_cost(gcx, body) <= MAX_HEURISTIC_INLINE_COST + leaf_callsite_bonus(body)
}

fn leaf_callsite_bonus(body: &Body<'_>) -> usize {
    if body.basic_blocks.len() != 1 {
        return 0;
    }
    let block = &body.basic_blocks[body.start_block];
    if !matches!(
        block.terminator.as_ref().map(|term| &term.kind),
        Some(TerminatorKind::Return)
    ) {
        return 0;
    }
    LEAF_CALLSITE_BONUS
}

fn body_inline_cost(gcx: Gcx<'_>, body: &Body<'_>) -> usize {
    let mut cost = body.basic_blocks.len().saturating_mul(2);
    for block in &body.basic_blocks {
        for statement in &block.statements {
            cost = cost.saturating_add(match statement.kind {
                StatementKind::SourceScope(_)
                | StatementKind::StorageLive(_)
                | StatementKind::StorageDead(_)
                | StatementKind::SetInitialized(_)
                | StatementKind::KeepAlive(_)
                | StatementKind::GcSafepoint(_)
                | StatementKind::Nop => 0,
                StatementKind::Assign(..) | StatementKind::SetDiscriminant { .. } => 1,
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
                | TerminatorKind::GeneratorYield { .. }
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

/// Recursion is determined by this call site's actual expansion chain, not
/// by every function reachable from the callee. Definition-based matching is
/// deliberately conservative across generic substitutions. The physical owner
/// is also checked because synthesized bodies can retain source scopes from
/// their original function.
fn callee_in_inline_chain(body: &Body<'_>, scope: SourceScopeId, callee: DefinitionID) -> bool {
    if body.owner == callee {
        return true;
    }
    let mut current = Some(scope);
    while let Some(scope) = current {
        let data = &body.source_scopes[scope];
        if data.definition == callee {
            return true;
        }
        current = data.parent;
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
            StatementKind::StorageDead(local) => {
                StatementKind::StorageDead(local_map[local.index()])
            }
            StatementKind::SetInitialized(local) => {
                StatementKind::SetInitialized(local_map[local.index()])
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
            destination,
            target,
            unwind,
        } => TerminatorKind::Call {
            func: remap_operand(gcx, func, local_map, gen_args),
            args: args
                .iter()
                .map(|a| remap_operand(gcx, a, local_map, gen_args))
                .collect(),
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
            no_result,
            cancel,
            cancel_complete,
            unwind,
        } => TerminatorKind::Yield {
            value: remap_operand(gcx, value, local_map, gen_args),
            resume: block_map[resume.index()],
            resume_arg: remap_place(gcx, resume_arg, local_map, gen_args),
            no_result: no_result.map(|block| block_map[block.index()]),
            cancel: block_map[cancel.index()],
            cancel_complete: block_map[cancel_complete.index()],
            unwind: match unwind {
                CallUnwindAction::Cleanup(bb) => CallUnwindAction::Cleanup(block_map[bb.index()]),
                CallUnwindAction::Terminate => CallUnwindAction::Terminate,
            },
        },
        TerminatorKind::GeneratorYield {
            value,
            resume,
            cancel,
            cancel_complete,
        } => TerminatorKind::GeneratorYield {
            value: remap_operand(gcx, value, local_map, gen_args),
            resume: block_map[resume.index()],
            cancel: block_map[cancel.index()],
            cancel_complete: block_map[cancel_complete.index()],
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
            PlaceElem::Field(*idx, instantiate_inline_local_ty(gcx, *ty, gen_args))
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
    if let ConstantKind::Function(def_id, fn_gen_args, sig) = &c.value {
        // The signature belongs to the referenced definition's generic index
        // space; only its arguments belong to this inlined body. Mixing those
        // spaces can substitute a caller const into a callee type parameter.
        // Use the definition template when a constant holds an instantiated snapshot.
        let template = gcx.try_get_type(*def_id).unwrap_or(*sig);
        let arguments = instantiate_generic_args(gcx, *fn_gen_args, gen_args);
        let ty = instantiate_mono_ty(gcx, template, arguments);
        return Constant {
            ty,
            value: ConstantKind::Function(*def_id, arguments, template),
        };
    }
    let ty = instantiate_mono_ty(gcx, c.ty, gen_args);
    let value = match &c.value {
        ConstantKind::Function(..) => unreachable!("function handled in its own index space"),
        ConstantKind::InterfaceConstant(id, args) => {
            ConstantKind::InterfaceConstant(*id, instantiate_generic_args(gcx, *args, gen_args))
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
        ConstValue::Bytes(s) => ConstantKind::Bytes(s),
        ConstValue::Array(arr) => ConstantKind::ConstArray(arr),
        ConstValue::Float(f) => ConstantKind::Float(f),
        ConstValue::Unit => ConstantKind::Unit,
        ConstValue::EnumUnitVariant(_) => return None,
    })
}

fn remap_rvalue<'ctx>(
    gcx: Gcx<'ctx>,
    rvalue: &Rvalue<'ctx>,
    local_map: &[LocalId],
    gen_args: GenericArguments<'ctx>,
) -> Rvalue<'ctx> {
    match rvalue {
        Rvalue::Alloc { ty } => Rvalue::Alloc {
            ty: instantiate_mono_ty(gcx, *ty, gen_args),
        },
        Rvalue::Use(op) => Rvalue::Use(remap_operand(gcx, op, local_map, gen_args)),
        Rvalue::CopyValue { source } => Rvalue::CopyValue {
            source: remap_place(gcx, source, local_map, gen_args),
        },
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
            // Checked erasure embeds its inspected type independently of the
            // result type. Inlining must substitute that annotation too.
            kind: match kind {
                crate::mir::CastKind::ExistentialTypeIs { target } => {
                    crate::mir::CastKind::ExistentialTypeIs {
                        target: instantiate_mono_ty(gcx, *target, gen_args),
                    }
                }
                crate::mir::CastKind::ExistentialTryCast { target } => {
                    crate::mir::CastKind::ExistentialTryCast {
                        target: instantiate_mono_ty(gcx, *target, gen_args),
                    }
                }
                other => *other,
            },
        },
        Rvalue::Ref { place } => Rvalue::Ref {
            place: remap_place(gcx, place, local_map, gen_args),
        },
        Rvalue::CleanupAddress { place } => Rvalue::CleanupAddress {
            place: remap_place(gcx, place, local_map, gen_args),
        },
        Rvalue::Discriminant { place } => Rvalue::Discriminant {
            place: remap_place(gcx, place, local_map, gen_args),
        },
        Rvalue::Zeroed { ty } => Rvalue::Zeroed {
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
            generic_args: instantiate_generic_args(gcx, *adt_gen_args, gen_args),
        },
        AggregateKind::Closure {
            def_id,
            captured_generics,
        } => AggregateKind::Closure {
            def_id: *def_id,
            captured_generics: instantiate_generic_args(gcx, *captured_generics, gen_args),
        },
    }
}

#[inline]
fn instantiate_mono_ty<'ctx>(
    gcx: Gcx<'ctx>,
    ty: Ty<'ctx>,
    args: GenericArguments<'ctx>,
) -> Ty<'ctx> {
    // Substitute caller-relative types without prematurely normalizing
    // projections that still depend on an outer generic caller.
    instantiate_ty_with_args(gcx, ty, args)
}

fn instantiate_inline_local_ty<'ctx>(
    gcx: Gcx<'ctx>,
    ty: Ty<'ctx>,
    args: GenericArguments<'ctx>,
) -> Ty<'ctx> {
    let ty = instantiate_ty_with_args(gcx, ty, args);
    // Substitution can make an associated projection concrete (IntBox.Item).
    // Normalize it before MIR folding/layout decisions, but leave types still
    // belonging to a generic caller for its later specialization.
    // Typed MIR has no inference variables. contains_inference() deliberately
    // treats every alias as unresolved and would suppress this normalization.
    if ty.needs_instantiation() {
        ty
    } else {
        crate::sema::tycheck::utils::normalize_post_monomorphization(gcx, ty)
    }
}

#[cfg(test)]
mod tests {
    use super::{
        CallSite, FORCED_INLINE_GROWTH_LIMIT, Inline, InlineProfitability, LEAF_CALLSITE_BONUS,
        MAX_HEURISTIC_INLINE_COST, body_inline_cost, call_site_priority, callee_in_inline_chain,
        inline_profitability_policy, is_heuristic_inline_candidate, leaf_callsite_bonus,
        prepare_inline_return, remap_source_scopes, remap_statement, remap_terminator,
    };
    use crate::PackageIndex;
    use crate::compile::config::{BuildProfile, OptLevel, OptimizationMode};
    use crate::hir::DefinitionID;
    use crate::mir::{
        CallUnwindAction, Constant, ConstantKind, LocalDecl, LocalKind, MirPackage, Operand, Place,
        PlaceElem, Rvalue, SourceScopeData, SourceScopeId, Statement, StatementKind, Terminator,
        TerminatorKind, test_support,
    };
    use crate::sema::models::GenericArguments;
    use crate::sema::resolve::models::DefinitionIndex;

    #[test]
    fn mutually_recursive_templates_are_independent_of_visit_order() {
        let source = r#"
@inline
func even(_ n: int32) -> bool { if n == 0 { return true }; odd(n - 1) }
@inline
func odd(_ n: int32) -> bool { if n == 0 { return false }; even(n - 1) }
func main() {}
"#;
        crate::test_support::analyze_script_built_mir(source, |bodies, gcx| {
            let canonical = gcx.store.alloc_mir_package(MirPackage {
                functions: bodies
                    .iter()
                    .map(|body| {
                        (
                            body.owner,
                            &*gcx.store.arenas.mir_bodies.alloc(body.clone()),
                        )
                    })
                    .collect(),
                entry: None,
            });
            gcx.store
                .inline_mir_packages
                .borrow_mut()
                .insert(gcx.package_index(), canonical);
            let snapshots: Vec<_> = bodies.iter().map(|body| format!("{body:?}")).collect();
            let mut results = Vec::new();
            for reverse in [false, true] {
                let mut ordered = bodies.clone();
                if reverse {
                    ordered.reverse();
                }
                let mut output = rustc_hash::FxHashMap::default();
                for mut body in ordered {
                    super::Inline::default()
                        .run_body(gcx, &mut body, GenericArguments::empty())
                        .unwrap_or_else(|_| panic!("inline"));
                    output.insert(body.owner, format!("{body:?}"));
                }
                results.push(output);
            }
            assert_eq!(
                results[0], results[1],
                "template visitation changes executable MIR"
            );
            for (body, before) in bodies.iter().zip(snapshots) {
                assert_eq!(
                    format!("{:?}", canonical.functions[&body.owner]),
                    before,
                    "inlining mutated shared dependency metadata"
                );
            }
        });
    }

    #[test]
    fn concrete_instances_inline_generic_helpers_without_changing_shared_mir() {
        use crate::mir::optimize::{run_global_passes, run_local_passes};
        use crate::sema::models::GenericArgument;
        use crate::specialize::Instance;

        for policy in ["inline", "noinline"] {
            let source = format!(
                "@{policy}\nfunc leaf[T](_ value: T) -> T {{ value }}\n@noinline\nfunc parent[T](_ value: T) -> T {{ leaf(value) }}\nfunc main() {{}}"
            );
            crate::test_support::analyze_script_built_mir(&source, |mut bodies, gcx| {
                for body in &mut bodies {
                    assert!(run_local_passes(gcx, body).is_ok());
                }
                let leaf = bodies
                    .iter()
                    .find(|body| gcx.symbol_text(gcx.definition_ident(body.owner).symbol).as_str() == "leaf")
                    .unwrap()
                    .owner;
                let parent = bodies
                    .iter()
                    .find(|body| gcx.symbol_text(gcx.definition_ident(body.owner).symbol).as_str() == "parent")
                    .unwrap()
                    .owner;
                let functions = bodies
                    .iter()
                    .map(|body| {
                        (
                            body.owner,
                            &*gcx.store.arenas.mir_bodies.alloc(body.clone()),
                        )
                    })
                    .collect();
                let canonical = gcx.store.alloc_mir_package(MirPackage {
                    functions,
                    entry: None,
                });
                gcx.store
                    .inline_mir_packages
                    .borrow_mut()
                    .insert(gcx.package_index(), canonical);
                for body in &mut bodies {
                    assert!(run_global_passes(gcx, body).is_ok());
                }
                let functions = bodies
                    .into_iter()
                    .map(|body| (body.owner, &*gcx.store.arenas.mir_bodies.alloc(body)))
                    .collect();
                let optimized = gcx.store.alloc_mir_package(MirPackage {
                    functions,
                    entry: None,
                });
                gcx.store
                    .mir_packages
                    .borrow_mut()
                    .insert(gcx.package_index(), optimized);
                let calls_leaf = |body: &crate::mir::Body<'_>| {
                    body.basic_blocks.iter().filter(|block| {
                        match block.terminator.as_ref().map(|terminator| &terminator.kind) {
                            Some(TerminatorKind::Call { func: Operand::Constant(constant), .. }) => {
                                matches!(constant.value, ConstantKind::Function(id, _, _) if id == leaf)
                            }
                            _ => false,
                        }
                    }).count()
                };
                assert_eq!(
                    calls_leaf(gcx.get_mir_body(parent)),
                    1,
                    "shared generic MIR retains the unresolved call"
                );
                for ty in [gcx.types.int32, gcx.types.bool] {
                    let args = gcx
                        .store
                        .interners
                        .intern_generic_args(vec![GenericArgument::Type(ty)]);
                    let instance = Instance::item(parent, args);
                    let body = gcx
                        .get_instance_mir_body(instance)
                        .unwrap_or_else(|_| panic!("instance MIR"));
                    assert_eq!(
                        calls_leaf(body),
                        usize::from(policy == "noinline"),
                        "{policy}: concrete instances should honor the inline policy"
                    );
                    assert_eq!(
                        calls_leaf(gcx.get_mir_body(parent)),
                        1,
                        "specializing one type must not change shared MIR"
                    );
                }
            });
        }
    }

    #[test]
    fn inline_pointer_intrinsic_wrapper_does_not_exhaust_caller_growth() {
        for intrinsic in ["add", "sub", "offset", "byte_add", "byte_sub"] {
            for (policy, expected) in [("inline", true), ("noinline", false)] {
                let count_ty = if intrinsic == "offset" {
                    "isize"
                } else {
                    "usize"
                };
                let source = format!(
                    r#"
extern "taro_intrinsic" {{
    func __intrinsic_ptr_{intrinsic}[T](_ ptr: *T, _ count: {count_ty}) -> *T
}}
@{policy}
func offset[T](_ ptr: *mut T, _ count: {count_ty}) -> *mut T {{
    unsafe {{ __intrinsic_ptr_{intrinsic}(ptr as *T, count) as *mut T }}
}}
func caller(_ ptr: *mut int32) -> *mut int32 {{ offset(ptr, 1 as {count_ty}) }}
func main() {{}}
"#
                );
                crate::test_support::analyze_script_built_mir(&source, |mut bodies, gcx| {
                    for body in &mut bodies {
                        assert!(crate::mir::optimize::run_local_passes(gcx, body).is_ok());
                    }
                    let functions = bodies
                        .iter()
                        .map(|body| {
                            (
                                body.owner,
                                &*gcx.store.arenas.mir_bodies.alloc(body.clone()),
                            )
                        })
                        .collect();
                    let package = gcx.store.alloc_mir_package(MirPackage {
                        functions,
                        entry: None,
                    });
                    gcx.store
                        .inline_mir_packages
                        .borrow_mut()
                        .insert(gcx.package_index(), package);
                    let mut caller = bodies
                        .into_iter()
                        .find(|body| gcx.symbol_text(gcx.definition_ident(body.owner).symbol).as_str() == "caller")
                        .unwrap();
                    let mut inliner = Inline {
                        forced_growth_used: FORCED_INLINE_GROWTH_LIMIT,
                        ..Inline::default()
                    };
                    assert_eq!(
                        inliner.inline_pass(gcx, &mut caller, GenericArguments::empty()),
                        expected,
                        "{policy} {intrinsic}: pointer wrappers must respect policy without spending growth allowance"
                    );
                    assert_eq!(inliner.growth_used, 0);
                    assert_eq!(inliner.forced_growth_used, FORCED_INLINE_GROWTH_LIMIT);
                });
            }
        }
    }

    #[test]
    fn native_subscript_inline_policy_controls_all_accessor_calls() {
        use crate::mir::optimize::MirPass;
        for (policy, should_inline) in [("inline", true), ("noinline", false)] {
            let source = format!(
                "struct Buffer {{ value: int32 }}\nextend &Buffer {{ @{policy} subscript(index: usize) -> int32 {{ address {{ &self.value }} }} }}\nfunc read(_ value: &Buffer) -> int32 {{ value[0 as usize] }}\nfunc write(_ value: &Buffer) {{ value[0 as usize] = 42 }}\nfunc address(_ value: &Buffer) -> &int32 {{ &value[0 as usize] }}\nfunc main() {{}}"
            );
            crate::test_support::analyze_script_built_mir(&source, |bodies, gcx| {
                let functions = bodies
                    .iter()
                    .map(|body| {
                        (
                            body.owner,
                            &*gcx.store.arenas.mir_bodies.alloc(body.clone()),
                        )
                    })
                    .collect();
                let package = gcx.store.alloc_mir_package(MirPackage {
                    functions,
                    entry: None,
                });
                gcx.store
                    .inline_mir_packages
                    .borrow_mut()
                    .insert(gcx.package_index(), package);
                for mut body in bodies {
                    let name = gcx.symbol_text(gcx.definition_ident(body.owner).symbol);
                    if !matches!(name.as_str(), "read" | "write" | "address") {
                        continue;
                    }
                    let expected = if should_inline || name.as_str() == "address" {
                        "__subscript_address"
                    } else if name.as_str() == "read" {
                        "__subscript_get"
                    } else {
                        "__subscript_set"
                    };
                    let callees: Vec<_> = body
                        .basic_blocks
                        .iter()
                        .filter_map(|block| {
                            let TerminatorKind::Call { func, .. } =
                                &block.terminator.as_ref()?.kind
                            else {
                                return None;
                            };
                            let (id, _) = super::extract_callee(func)?;
                            Some(gcx.symbol_text(gcx.definition_ident(id).symbol))
                        })
                        .collect();
                    assert_eq!(callees.len(), 1, "{policy} {name}: {callees:?}");
                    assert_eq!(callees[0].as_str(), expected, "{policy} {name}");
                    Inline::default().run(gcx, &mut body).unwrap_or_else(|_| {
                        panic!("inlining: {:#?}", gcx.dcx().take_recorded_diagnostics())
                    });
                    let calls = body
                        .basic_blocks
                        .iter()
                        .filter(|block| {
                            matches!(
                                block.terminator.as_ref().map(|terminator| &terminator.kind),
                                Some(TerminatorKind::Call { .. })
                            )
                        })
                        .count();
                    assert_eq!(calls == 0, should_inline, "{policy} {name}: {calls} calls");
                }
            });
        }
    }

    #[test]
    fn inlined_function_constants_keep_callee_templates_and_remap_only_caller_arguments() {
        crate::test_support::analyze_script(
            "func identity[T](_ value: T) -> T { value }\nstruct Wrapper[U] { value: U }\nfunc main() {}",
            |package, gcx| {
                use crate::sema::models::{
                    Const, ConstKind, ConstValue, GenericArgument, GenericParameter, Ty, TyKind,
                };
                use crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args;
                let function = package.root.declarations[0].id;
                let raw = gcx.get_type(function);
                let bool_args = gcx
                    .store
                    .interners
                    .intern_generic_args(vec![GenericArgument::Type(gcx.types.bool)]);
                let constant = Constant {
                    ty: raw,
                    value: ConstantKind::Function(function, bool_args, raw),
                };
                let outer = gcx
                    .store
                    .interners
                    .intern_generic_args(vec![GenericArgument::Const(Const {
                        ty: gcx.types.uint,
                        kind: ConstKind::Value(ConstValue::Integer(3)),
                    })]);
                let remapped = super::remap_constant(gcx, &constant, outer);
                assert_eq!(remapped.ty, instantiate_ty_with_args(gcx, raw, bool_args));
                assert!(
                    matches!(remapped.value, ConstantKind::Function(_, args, template) if args == bool_args && template == raw)
                );

                let caller = Ty::new(
                    TyKind::Parameter(GenericParameter {
                        index: 0,
                        name: gcx.intern_symbol("CallerU"),
                    }),
                    gcx,
                );
                let wrapper = gcx.get_type(package.root.declarations[1].id);
                let caller_args = gcx
                    .store
                    .interners
                    .intern_generic_args(vec![GenericArgument::Type(caller)]);
                let wrapped = instantiate_ty_with_args(gcx, wrapper, caller_args);
                let original_args = gcx
                    .store
                    .interners
                    .intern_generic_args(vec![GenericArgument::Type(wrapped)]);
                let snapshot = instantiate_ty_with_args(gcx, raw, original_args);
                let constant = Constant {
                    ty: snapshot,
                    value: ConstantKind::Function(function, original_args, snapshot),
                };
                let expected = instantiate_ty_with_args(gcx, snapshot, bool_args);
                let remapped = super::remap_constant(gcx, &constant, bool_args);
                assert_eq!(
                    remapped.ty, expected,
                    "an instantiated snapshot must not substitute its callee arguments twice"
                );
                assert!(
                    matches!(remapped.value, ConstantKind::Function(_, _, template) if template == raw)
                );
            },
        );
    }

    #[test]
    fn inlining_substitutes_the_inspected_type_inside_erased_casts() {
        crate::test_support::analyze_script(
            "func identity[T](_ value: T) -> T { value }\nenum Maybe[T] { case none; case some(T) }\nfunc main() {}",
            |package, gcx| {
                use crate::sema::models::{GenericArgument, Ty, TyKind};
                let parameter = gcx.get_signature(package.root.declarations[0].id).output;
                let args = gcx
                    .store
                    .interners
                    .intern_generic_args(vec![GenericArgument::Type(gcx.types.int32)]);
                let definition = gcx.get_enum_definition(package.root.declarations[1].id);
                let maybe_args = gcx
                    .store
                    .interners
                    .intern_generic_args(vec![GenericArgument::Type(parameter)]);
                let result = Ty::new(TyKind::Adt(definition.adt_def, maybe_args), gcx);
                let locals = [crate::mir::LocalId::from_usize(1)];
                for (kind, output) in [
                    (
                        crate::mir::CastKind::ExistentialTypeIs { target: parameter },
                        gcx.types.bool,
                    ),
                    (
                        crate::mir::CastKind::ExistentialTryCast { target: parameter },
                        result,
                    ),
                ] {
                    let value = Rvalue::Cast {
                        operand: Operand::Copy(Place::from_local(crate::mir::LocalId::from_usize(
                            0,
                        ))),
                        ty: output,
                        kind,
                    };
                    let remapped = super::remap_rvalue(gcx, &value, &locals, args);
                    let Rvalue::Cast { kind, operand, .. } = remapped else {
                        panic!("cast")
                    };
                    assert!(
                        matches!(kind, crate::mir::CastKind::ExistentialTypeIs { target } | crate::mir::CastKind::ExistentialTryCast { target } if target == gcx.types.int32)
                    );
                    assert!(matches!(operand, Operand::Copy(place) if place.local == locals[0]));
                }
            },
        );
    }

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
            let local = test_support::push_temp(&mut body, gcx.types.uint64);
            let assignment = StatementKind::Assign(
                Place::from_local(local),
                Rvalue::Use(Operand::Constant(Constant {
                    ty: gcx.types.uint64,
                    value: ConstantKind::Integer(1),
                })),
            );
            while body_inline_cost(gcx, &body) <= 40 {
                body.basic_blocks[body.start_block]
                    .statements
                    .push(Statement {
                        kind: assignment.clone(),
                        span,
                    });
            }
            assert!(body_inline_cost(gcx, &body) <= MAX_HEURISTIC_INLINE_COST);
            assert!(is_heuristic_inline_candidate(gcx, &body));

            while body_inline_cost(gcx, &body) <= MAX_HEURISTIC_INLINE_COST + LEAF_CALLSITE_BONUS {
                body.basic_blocks[body.start_block]
                    .statements
                    .push(Statement {
                        kind: assignment.clone(),
                        span,
                    });
            }
            assert!(!is_heuristic_inline_candidate(gcx, &body));
        });
    }

    #[test]
    fn non_executable_markers_do_not_exhaust_the_inline_budget() {
        test_support::with_test_gcx(|gcx| {
            let mut body = test_support::minimal_body(gcx);
            let local = test_support::push_temp(&mut body, gcx.types.uint64);
            let span = body.locals[local].span;
            let before = body_inline_cost(gcx, &body);
            for _ in 0..128 {
                for kind in [
                    StatementKind::SourceScope(SourceScopeId::from_raw(0)),
                    StatementKind::StorageLive(local),
                    StatementKind::SetInitialized(local),
                    StatementKind::KeepAlive(Operand::Copy(Place::from_local(local))),
                    StatementKind::Nop,
                ] {
                    body.basic_blocks[body.start_block]
                        .statements
                        .push(Statement { kind, span });
                }
            }
            assert_eq!(body_inline_cost(gcx, &body), before);
            assert!(is_heuristic_inline_candidate(gcx, &body));
        });
    }

    #[test]
    fn leaf_allowance_excludes_cyclic_bodies() {
        test_support::with_test_gcx(|gcx| {
            let mut body = test_support::minimal_body(gcx);
            assert_eq!(leaf_callsite_bonus(&body), LEAF_CALLSITE_BONUS);
            body.basic_blocks[body.start_block]
                .terminator
                .as_mut()
                .unwrap()
                .kind = TerminatorKind::Goto {
                target: body.start_block,
            };
            assert_eq!(leaf_callsite_bonus(&body), 0);
        });
    }

    #[test]
    fn string_header_forwarders_finish_after_depth_and_growth_limits() {
        let source = r#"
extern "taro_intrinsic" {
    func __intrinsic_string_len(_ value: &string) -> usize
    func __intrinsic_string_data(_ value: &string) -> *const uint8
}
@inline func length(_ value: string) -> usize { __intrinsic_string_len(&value) }
@inline func data(_ value: string) -> *const uint8 { __intrinsic_string_data(&value) }
func main() {}
"#;
        crate::test_support::analyze_script_built_mir(source, |mut bodies, gcx| {
            for body in &mut bodies {
                assert!(crate::mir::optimize::run_local_passes(gcx, body).is_ok());
            }
            let caller = bodies
                .iter()
                .find(|body| gcx.symbol_text(gcx.definition_ident(body.owner).symbol).as_str() == "main")
                .unwrap()
                .clone();
            let callees: Vec<_> = bodies
                .iter()
                .filter(|body| gcx.symbol_text(gcx.definition_ident(body.owner).symbol).as_str() != "main")
                .map(|body| body.owner)
                .collect();
            let package = gcx.store.alloc_mir_package(MirPackage {
                functions: bodies
                    .into_iter()
                    .map(|body| (body.owner, &*gcx.store.arenas.mir_bodies.alloc(body)))
                    .collect(),
                entry: None,
            });
            gcx.store
                .inline_mir_packages
                .borrow_mut()
                .insert(gcx.package_index(), package);
            let mut inliner = Inline {
                depth: super::MAX_INLINE_DEPTH,
                growth_budget: 0,
                forced_growth_used: FORCED_INLINE_GROWTH_LIMIT,
                ..Inline::default()
            };
            for callee in callees {
                let (growth, forced, normal) = inliner
                    .should_inline(
                        gcx,
                        &caller,
                        caller.start_block,
                        SourceScopeId::from_raw(0),
                        callee,
                        GenericArguments::empty(),
                        &[],
                    )
                    .expect("a single header load still qualifies at the limit");
                assert_eq!(growth, 0);
                assert!(inliner.reserve_growth(&budget_test_site(growth, forced, normal)));
            }
        });
    }

    #[test]
    fn scalar_read_forwarder_survives_an_exhausted_inline_budget() {
        use crate::mir::optimize::run_local_passes;
        use crate::sema::models::GenericArgument;
        let source = r#"
extern "taro_intrinsic" {
    unsafe func __intrinsic_ptr_read[T](_ pointer: *T) -> T
}
@inline
unsafe func read[T](_ pointer: *T) -> T {
    unsafe { __intrinsic_ptr_read(pointer) }
}
func main() {}
"#;
        crate::test_support::analyze_script_built_mir(source, |mut bodies, gcx| {
            for body in &mut bodies {
                assert!(run_local_passes(gcx, body).is_ok());
            }
            let callee = bodies
                .iter()
                .find(|body| gcx.symbol_text(gcx.definition_ident(body.owner).symbol).as_str() == "read")
                .unwrap()
                .owner;
            let caller = bodies
                .iter()
                .find(|body| gcx.symbol_text(gcx.definition_ident(body.owner).symbol).as_str() == "main")
                .unwrap()
                .clone();
            let functions = bodies
                .into_iter()
                .map(|body| (body.owner, &*gcx.store.arenas.mir_bodies.alloc(body)))
                .collect();
            let package = gcx.store.alloc_mir_package(MirPackage {
                functions,
                entry: None,
            });
            gcx.store
                .inline_mir_packages
                .borrow_mut()
                .insert(gcx.package_index(), package);
            let mut inliner = Inline {
                growth_budget: 0,
                forced_growth_used: FORCED_INLINE_GROWTH_LIMIT,
                ..Inline::default()
            };
            for (ty, expected) in [(gcx.types.uint8, true), (gcx.types.string, false)] {
                let args = gcx
                    .store
                    .interners
                    .intern_generic_args(vec![GenericArgument::Type(ty)]);
                let (growth, forced, normal_eligible) = inliner
                    .should_inline(
                        gcx,
                        &caller,
                        caller.start_block,
                        SourceScopeId::from_raw(0),
                        callee,
                        args,
                        &[],
                    )
                    .unwrap();
                let mut site = budget_test_site(growth, forced, normal_eligible);
                site.callee_id = callee;
                site.gen_args = args;
                assert_eq!(
                    inliner.reserve_growth(&site),
                    expected,
                    "{ty:?}: growth {growth}"
                );
            }
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
    fn recursive_inline_guard_checks_every_actual_ancestor() {
        test_support::with_test_gcx(|gcx| {
            let mut body = test_support::minimal_body(gcx);
            let definition =
                |index| DefinitionID::new(PackageIndex::new(1), DefinitionIndex::from_raw(index));
            let native = definition(10);
            let wrapper = definition(11);
            let nested = definition(12);
            let sibling = definition(13);
            let root = SourceScopeId::from_raw(0);
            body.owner = native;
            body.source_scopes[root].definition = native;
            let mut push = |definition, parent| {
                body.source_scopes.push(SourceScopeData {
                    definition,
                    parent: Some(parent),
                    callsite: Some(body.locals[body.return_local].span),
                })
            };
            let wrapper_scope = push(wrapper, root);
            let nested_scope = push(nested, wrapper_scope);
            let sibling_scope = push(sibling, root);
            for callee in [native, wrapper, nested] {
                assert!(callee_in_inline_chain(&body, nested_scope, callee));
            }
            assert!(!callee_in_inline_chain(&body, nested_scope, sibling));
            assert!(!callee_in_inline_chain(&body, sibling_scope, wrapper));
            assert!(!callee_in_inline_chain(&body, root, wrapper));
            // A synthesized physical function can name a different source
            // function at its root. It must still reject a call to itself.
            body.source_scopes[root].definition = definition(14);
            assert!(callee_in_inline_chain(&body, nested_scope, native));
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
                StatementKind::Assign(place, Rvalue::Use(Operand::Copy(source)))
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
