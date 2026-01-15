//! MIR Inlining Pass
//!
//! This pass inlines function bodies at call sites when profitable.
//! It supports cross-package inlining by resolving callee bodies via `Gcx`.

use super::MirPass;
use crate::compile::context::Gcx;
use crate::hir::{Abi, DefinitionID, KnownAttribute};
use crate::mir::{
    AggregateKind, BasicBlockData, BasicBlockId, Body, Constant, ConstantKind, LocalDecl, LocalId,
    LocalKind, MirPhase, Operand, Place, PlaceElem, Rvalue, Statement, StatementKind, Terminator,
    TerminatorKind,
};
use crate::sema::models::GenericArguments;
use crate::sema::tycheck::utils::instantiate::{
    instantiate_const_with_args, instantiate_ty_with_args,
};

/// Maximum number of basic blocks in a callee to consider it "small" for inlining.
const SMALL_BODY_BLOCK_LIMIT: usize = 10;
/// Maximum number of statements in a callee to consider it "small" for inlining.
const SMALL_BODY_STMT_LIMIT: usize = 30;
/// Maximum depth of recursive inlining to prevent infinite expansion.
const MAX_INLINE_DEPTH: u32 = 7;

/// MIR pass that inlines function calls.
pub struct Inline {
    /// Current inlining depth (to prevent infinite recursion)
    depth: u32,
}

impl Default for Inline {
    fn default() -> Self {
        Inline { depth: 0 }
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
        let call_sites: Vec<_> = body
            .basic_blocks
            .iter_enumerated()
            .filter_map(|(bb_id, block)| {
                let terminator = block.terminator.as_ref()?;
                if let TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    target,
                } = &terminator.kind
                {
                    let (callee_id, gen_args) = extract_callee(func)?;

                    if self.should_inline(gcx, callee_id, gen_args) {
                        return Some(CallSite {
                            caller_block: bb_id,
                            callee_id,
                            gen_args,
                            args: args.clone(),
                            destination: destination.clone(),
                            target: *target,
                            span: terminator.span,
                        });
                    }
                }
                None
            })
            .collect();

        // Perform inlining for each call site
        for site in call_sites {
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
        callee_id: DefinitionID,
        gen_args: GenericArguments<'ctx>,
    ) -> bool {
        // Don't exceed depth limit
        if self.depth >= MAX_INLINE_DEPTH {
            return false;
        }

        // Check function signature for ABI restrictions
        let sig = gcx.get_signature(callee_id);
        match sig.abi {
            Some(Abi::Intrinsic) | Some(Abi::C) | Some(Abi::Runtime) => return false,
            None => {}
        }

        // Skip inlining if after substitution, the callee body would still have
        // types that need instantiation. This happens when calling methods on
        // generic types where not all type parameters are available.
        if let Some(callee_body) = resolve_callee_body(gcx, callee_id) {
            for local in callee_body.locals.iter() {
                let substituted = instantiate_ty_with_args(gcx, local.ty, gen_args);
                if substituted.needs_instantiation() {
                    return false;
                }
            }
        }

        // Check attributes
        let attrs = gcx.attributes_of(callee_id);
        for attr in attrs.iter() {
            match attr.as_known() {
                Some(KnownAttribute::Inline) => return true,
                Some(KnownAttribute::NoInline) => return false,
                Some(KnownAttribute::Cfg) => {} // Cfg doesn't affect inlining
                None => {}
            }
        }

        // Heuristic: inline small functions (only if they passed the substitution check above)
        if let Some(callee_body) = resolve_callee_body(gcx, callee_id) {
            is_body_small(callee_body)
        } else {
            false
        }
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

        // Copy callee's locals (except return place, which maps to destination)
        // Substitute generic types with concrete types from call site
        let mut local_map: Vec<LocalId> = Vec::with_capacity(callee.locals.len());
        for (callee_local_id, local_decl) in callee.locals.iter_enumerated() {
            if callee_local_id == callee.return_local {
                // Return local maps to the destination's base local
                local_map.push(site.destination.local);
            } else {
                // Substitute types in the local declaration
                let substituted_ty = instantiate_ty_with_args(gcx, local_decl.ty, gen_args);
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
            statements: Vec::new(),
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

            // Remap statements
            for stmt in &callee_block.statements {
                let new_stmt = remap_statement(gcx, stmt, &local_map, gen_args);
                caller.basic_blocks[new_bb_id].statements.push(new_stmt);
            }

            // Remap terminator
            if let Some(term) = &callee_block.terminator {
                let new_term = remap_terminator(
                    gcx,
                    term,
                    &local_map,
                    &block_map,
                    site.target,
                    callee.return_local,
                    gen_args,
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

/// Information about a call site that may be inlined.
struct CallSite<'ctx> {
    caller_block: BasicBlockId,
    callee_id: DefinitionID,
    #[allow(dead_code)]
    gen_args: GenericArguments<'ctx>,
    args: Vec<Operand<'ctx>>,
    destination: Place<'ctx>,
    target: BasicBlockId,
    span: crate::span::Span,
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
    let packages = gcx.store.mir_packages.borrow();
    let package = packages.get(&callee_id.package())?;
    package.functions.get(&callee_id).copied()
}

/// Check if a function body is small enough to inline heuristically.
fn is_body_small(body: &Body<'_>) -> bool {
    if body.basic_blocks.len() > SMALL_BODY_BLOCK_LIMIT {
        return false;
    }

    let stmt_count: usize = body.basic_blocks.iter().map(|bb| bb.statements.len()).sum();

    stmt_count <= SMALL_BODY_STMT_LIMIT
}

/// Remap a statement's locals to the caller's namespace and substitute types.
fn remap_statement<'ctx>(
    gcx: Gcx<'ctx>,
    stmt: &Statement<'ctx>,
    local_map: &[LocalId],
    gen_args: GenericArguments<'ctx>,
) -> Statement<'ctx> {
    Statement {
        kind: match &stmt.kind {
            StatementKind::Assign(place, rvalue) => StatementKind::Assign(
                remap_place(gcx, place, local_map, gen_args),
                remap_rvalue(gcx, rvalue, local_map, gen_args),
            ),
            StatementKind::GcSafepoint => StatementKind::GcSafepoint,
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
        TerminatorKind::Call {
            func,
            args,
            destination,
            target,
        } => TerminatorKind::Call {
            func: remap_operand(gcx, func, local_map, gen_args),
            args: args
                .iter()
                .map(|a| remap_operand(gcx, a, local_map, gen_args))
                .collect(),
            destination: remap_place(gcx, destination, local_map, gen_args),
            target: block_map[target.index()],
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
            PlaceElem::Field(*idx, instantiate_ty_with_args(gcx, *ty, gen_args))
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
        Operand::Copy(place) => Operand::Copy(remap_place(gcx, place, local_map, gen_args)),
        Operand::Move(place) => Operand::Move(remap_place(gcx, place, local_map, gen_args)),
        Operand::Constant(c) => Operand::Constant(remap_constant(gcx, c, gen_args)),
    }
}

fn remap_constant<'ctx>(
    gcx: Gcx<'ctx>,
    c: &Constant<'ctx>,
    gen_args: GenericArguments<'ctx>,
) -> Constant<'ctx> {
    let ty = instantiate_ty_with_args(gcx, c.ty, gen_args);
    let value = match &c.value {
        // Function constants keep their def_id but substitute their generic args
        ConstantKind::Function(def_id, fn_gen_args, sig) => {
            // Substitute the function's generic args with the inlined generic args
            let substituted_args = substitute_gen_args(gcx, *fn_gen_args, gen_args);
            let substituted_sig = instantiate_ty_with_args(gcx, *sig, gen_args);
            ConstantKind::Function(*def_id, substituted_args, substituted_sig)
        }
        // Const parameters need to be substituted with their concrete values
        ConstantKind::ConstParam(param) => {
            if let Some(arg) = gen_args.get(param.index) {
                match arg {
                    crate::sema::models::GenericArgument::Const(sema_const) => {
                        // Convert sema Const to MIR ConstantKind
                        match sema_const.kind {
                            crate::sema::models::ConstKind::Value(val) => {
                                sema_const_value_to_mir(val)
                            }
                            crate::sema::models::ConstKind::Param(inner_param) => {
                                // Still a param - pass it through (shouldn't happen with valid gen_args)
                                ConstantKind::ConstParam(inner_param)
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
fn sema_const_value_to_mir(val: crate::sema::models::ConstValue) -> ConstantKind<'static> {
    use crate::sema::models::ConstValue;
    match val {
        ConstValue::Integer(i) => ConstantKind::Integer(i as u64),
        ConstValue::Bool(b) => ConstantKind::Bool(b),
        ConstValue::Rune(r) => ConstantKind::Rune(r),
        ConstValue::String(s) => ConstantKind::String(s),
        ConstValue::Float(f) => ConstantKind::Float(f),
        ConstValue::Unit => ConstantKind::Unit,
    }
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
                GenericArgument::Type(instantiate_ty_with_args(gcx, *ty, substitution))
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
            ty: instantiate_ty_with_args(gcx, *ty, gen_args),
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
            ty: instantiate_ty_with_args(gcx, *ty, gen_args),
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
            element: instantiate_ty_with_args(gcx, *element, gen_args),
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
            element: instantiate_ty_with_args(gcx, *element, gen_args),
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
