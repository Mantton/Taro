use super::MirPass;
use super::simplify::{
    collapse_trivial_gotos, eliminate_dead_locals, merge_consecutive_safepoints,
    merge_linear_blocks, prune_unreachable_blocks,
};
use crate::compile::context::Gcx;
use crate::error::{CompileResult, ReportedError};
use crate::hir::DefinitionKind;
use crate::mir::{
    BasicBlockData, BasicBlockId, Body, CallUnwindAction, LocalDecl, LocalId, LocalKind, MirPhase,
    Operand, Place, PlaceElem, Rvalue, Statement, StatementKind, TerminatorKind,
};
use crate::sema::models::{AdtKind, EnumVariantKind, StructDefinition, Ty, TyKind};
use crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args;
use crate::thir::FieldIndex;
use rustc_hash::FxHashSet;

pub struct SimplifyCfg;
pub struct PruneUnreachable;
pub struct LowerAggregates;
pub struct LowerKeepAlive;
pub struct LowerExistentialBoxes;
pub struct InsertSafepoints;
pub struct DeadLocalElimination;
pub struct MergeSafepoints;

impl<'ctx> MirPass<'ctx> for PruneUnreachable {
    fn name(&self) -> &'static str {
        "PruneUnreachable"
    }

    fn run(&mut self, _gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
        prune_unreachable_blocks(body);
        Ok(())
    }
}

impl<'ctx> MirPass<'ctx> for SimplifyCfg {
    fn name(&self) -> &'static str {
        "SimplifyCfg"
    }

    fn run(&mut self, _gcx: Gcx<'_>, body: &mut Body<'_>) -> CompileResult<()> {
        // 1. Merge linear chains of blocks (even with statements)
        merge_linear_blocks(body);
        // 2. Collapse remaining empty goto chains
        collapse_trivial_gotos(body);
        // 3. Remove now-unreachable blocks
        prune_unreachable_blocks(body);
        Ok(())
    }
}

impl<'ctx> MirPass<'ctx> for DeadLocalElimination {
    fn name(&self) -> &'static str {
        "DeadLocalElimination"
    }

    fn run(&mut self, _gcx: Gcx<'_>, body: &mut Body<'_>) -> CompileResult<()> {
        eliminate_dead_locals(body);
        Ok(())
    }
}

impl<'ctx> MirPass<'ctx> for MergeSafepoints {
    fn name(&self) -> &'static str {
        "MergeSafepoints"
    }

    fn run(&mut self, _gcx: Gcx<'_>, body: &mut Body<'_>) -> CompileResult<()> {
        merge_consecutive_safepoints(body);
        Ok(())
    }
}

impl<'ctx> MirPass<'ctx> for LowerAggregates {
    fn name(&self) -> &'static str {
        "LowerAggregates"
    }

    fn run(&mut self, gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
        let mut new_blocks = body.basic_blocks.clone();

        for bb in body.basic_blocks.indices() {
            let BasicBlockData {
                statements,
                terminator,
                note,
            } = body.basic_blocks[bb].clone();
            let mut lowered: Vec<Statement> = Vec::with_capacity(statements.len());

            for stmt in statements {
                let span = stmt.span;
                match stmt.kind {
                    StatementKind::Assign(dest, Rvalue::Aggregate { kind, fields }) => {
                        if matches!(kind, crate::mir::AggregateKind::Array { .. }) {
                            lowered.push(Statement {
                                kind: StatementKind::Assign(
                                    dest,
                                    Rvalue::Aggregate { kind, fields },
                                ),
                                span,
                            });
                            continue;
                        }
                        // Materialize operands into temps to preserve evaluation order.
                        let field_ops: Vec<(FieldIndex, Operand)> =
                            fields.into_iter_enumerated().collect();
                        let mut ops_with_tys = Vec::with_capacity(field_ops.len());
                        for (idx, operand) in field_ops.clone() {
                            let ty = operand_ty(body, gcx, &operand);
                            ops_with_tys.push((idx, operand, ty));
                        }

                        let mut temps: Vec<(LocalId, FieldIndex)> =
                            Vec::with_capacity(ops_with_tys.len());
                        for (idx, operand, ty) in &ops_with_tys {
                            let temp_local = body.locals.push(LocalDecl {
                                ty: *ty,
                                kind: LocalKind::Temp,
                                mutable: true,
                                name: None,
                                span,
                            });
                            body.escape_locals.push(false);
                            lowered.push(Statement {
                                kind: StatementKind::Assign(
                                    Place::from_local(temp_local),
                                    Rvalue::Use(operand.clone()),
                                ),
                                span,
                            });
                            temps.push((temp_local, *idx));
                        }

                        match kind {
                            crate::mir::AggregateKind::Tuple => {
                                let dest_ty = place_ty(body, gcx, &dest);
                                for (i, (temp_local, idx)) in temps.into_iter().enumerate() {
                                    let mut proj = dest.projection.clone();
                                    let field_ty = match dest_ty.kind() {
                                        TyKind::Tuple(items) => {
                                            items.get(i).cloned().unwrap_or(dest_ty)
                                        }
                                        _ => dest_ty,
                                    };
                                    proj.push(PlaceElem::Field(idx, field_ty));
                                    let place = Place {
                                        local: dest.local,
                                        projection: proj,
                                    };
                                    lowered.push(Statement {
                                        kind: StatementKind::Assign(
                                            place,
                                            Rvalue::Use(aggregate_field_operand(
                                                gcx,
                                                body.owner,
                                                body.locals[temp_local].ty,
                                                temp_local,
                                            )),
                                        ),
                                        span,
                                    });
                                }
                            }
                            crate::mir::AggregateKind::Array { element, .. } => {
                                for (temp_local, idx) in temps.into_iter() {
                                    let mut proj = dest.projection.clone();
                                    proj.push(PlaceElem::Field(idx, element));
                                    let place = Place {
                                        local: dest.local,
                                        projection: proj,
                                    };
                                    lowered.push(Statement {
                                        kind: StatementKind::Assign(
                                            place,
                                            Rvalue::Use(aggregate_field_operand(
                                                gcx,
                                                body.owner,
                                                body.locals[temp_local].ty,
                                                temp_local,
                                            )),
                                        ),
                                        span,
                                    });
                                }
                            }
                            crate::mir::AggregateKind::Adt {
                                def_id,
                                variant_index,
                                generic_args,
                            } => {
                                let kind = gcx.definition_kind(def_id);
                                match kind {
                                    DefinitionKind::Struct => {
                                        let StructDefinition { fields, .. } =
                                            *gcx.get_struct_definition(def_id);
                                        for ((temp_local, idx), field) in
                                            temps.into_iter().zip(fields.iter())
                                        {
                                            let mut proj = dest.projection.clone();
                                            let field_ty = instantiate_ty_with_args(
                                                gcx,
                                                field.ty,
                                                generic_args,
                                            );
                                            proj.push(PlaceElem::Field(idx, field_ty));
                                            let place = Place {
                                                local: dest.local,
                                                projection: proj,
                                            };
                                            lowered.push(Statement {
                                                kind: StatementKind::Assign(
                                                    place,
                                                    Rvalue::Use(aggregate_field_operand(
                                                        gcx,
                                                        body.owner,
                                                        body.locals[temp_local].ty,
                                                        temp_local,
                                                    )),
                                                ),
                                                span,
                                            });
                                        }
                                    }
                                    DefinitionKind::Enum => {
                                        let Some(variant_index) = variant_index else {
                                            unreachable!();
                                        };
                                        let variant_data =
                                            gcx.enum_variant_by_index(def_id, variant_index);

                                        for ((temp_local, idx), (_, _, ty)) in
                                            temps.into_iter().zip(ops_with_tys.iter())
                                        {
                                            let mut proj = dest.projection.clone();
                                            proj.push(PlaceElem::VariantDowncast {
                                                name: variant_data.name,
                                                index: variant_index,
                                            });
                                            proj.push(PlaceElem::Field(idx, *ty));
                                            let place = Place {
                                                local: dest.local,
                                                projection: proj,
                                            };
                                            lowered.push(Statement {
                                                kind: StatementKind::Assign(
                                                    place,
                                                    Rvalue::Use(aggregate_field_operand(
                                                        gcx,
                                                        body.owner,
                                                        body.locals[temp_local].ty,
                                                        temp_local,
                                                    )),
                                                ),
                                                span,
                                            });
                                        }

                                        // Publish the discriminator only after
                                        // the selected payload is completely
                                        // initialized. A tag-aware collector
                                        // must never observe a live tag paired
                                        // with stale payload storage.
                                        lowered.push(Statement {
                                            kind: StatementKind::SetDiscriminant {
                                                place: dest.clone(),
                                                variant_index,
                                            },
                                            span,
                                        });
                                    }
                                    _ => unreachable!(),
                                }
                            }
                            crate::mir::AggregateKind::Closure {
                                def_id,
                                captured_generics,
                            } => {
                                // Lower closure aggregate - each capture becomes a field assignment
                                let captures_info = gcx.get_closure_captures(def_id);
                                let capture_tys: Vec<Ty<'ctx>> = captures_info
                                    .as_ref()
                                    .map(|c| {
                                        c.captures
                                            .iter()
                                            .map(|capture| {
                                                instantiate_ty_with_args(
                                                    gcx,
                                                    capture.ty,
                                                    captured_generics,
                                                )
                                            })
                                            .collect()
                                    })
                                    .unwrap_or_default();

                                for ((temp_local, idx), field_ty) in
                                    temps.into_iter().zip(capture_tys.iter())
                                {
                                    let mut proj = dest.projection.clone();
                                    proj.push(PlaceElem::Field(idx, *field_ty));
                                    let place = Place {
                                        local: dest.local,
                                        projection: proj,
                                    };
                                    lowered.push(Statement {
                                        kind: StatementKind::Assign(
                                            place,
                                            Rvalue::Use(aggregate_field_operand(
                                                gcx,
                                                body.owner,
                                                body.locals[temp_local].ty,
                                                temp_local,
                                            )),
                                        ),
                                        span,
                                    });
                                }
                            }
                        }
                    }
                    _ => lowered.push(stmt),
                }
            }

            new_blocks[bb].statements = lowered;
            new_blocks[bb].terminator = terminator;
            new_blocks[bb].note = note;
        }

        body.basic_blocks = new_blocks;
        Ok(())
    }

    fn phase_change(&self) -> Option<MirPhase> {
        Some(MirPhase::Lowered)
    }
}

impl<'ctx> MirPass<'ctx> for LowerKeepAlive {
    fn name(&self) -> &'static str {
        "LowerKeepAlive"
    }

    fn run(&mut self, gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
        for block in body.basic_blocks.iter_mut() {
            let Some(terminator) = block.terminator.as_ref() else {
                continue;
            };
            let TerminatorKind::Call {
                func, args, target, ..
            } = &terminator.kind
            else {
                continue;
            };
            let Operand::Constant(constant) = func else {
                continue;
            };
            let crate::mir::ConstantKind::Function(def_id, _, _) = constant.value else {
                continue;
            };
            if gcx
                .symbol_text(gcx.definition_ident(def_id).symbol)
                .as_str()
                != "__rt__keep_alive"
            {
                continue;
            }
            let Some(value) = args.first().cloned() else {
                continue;
            };
            let span = terminator.span;
            let target = *target;
            block.statements.push(Statement {
                kind: StatementKind::KeepAlive(value),
                span,
            });
            block.terminator = Some(crate::mir::Terminator {
                kind: TerminatorKind::Goto { target },
                span,
            });
        }
        Ok(())
    }
}

impl<'ctx> MirPass<'ctx> for LowerExistentialBoxes {
    fn name(&self) -> &'static str {
        "LowerExistentialBoxes"
    }

    fn run(&mut self, gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
        let original = body.basic_blocks.clone();
        for block in body.basic_blocks.indices() {
            let mut lowered = Vec::with_capacity(original[block].statements.len());
            for statement in original[block].statements.iter().cloned() {
                let StatementKind::Assign(
                    destination,
                    Rvalue::Cast {
                        operand,
                        ty: target,
                        kind,
                    },
                ) = statement.kind
                else {
                    lowered.push(statement);
                    continue;
                };
                let concrete = operand_ty(body, gcx, &operand);
                let allocates = matches!(target.kind(), TyKind::BoxedExistential { .. })
                    && !matches!(concrete.kind(), TyKind::BoxedExistential { .. })
                    && matches!(
                        kind,
                        crate::mir::CastKind::BoxExistential | crate::mir::CastKind::Numeric
                    );
                if !allocates {
                    lowered.push(Statement {
                        kind: StatementKind::Assign(
                            destination,
                            Rvalue::Cast {
                                operand,
                                ty: target,
                                kind,
                            },
                        ),
                        span: statement.span,
                    });
                    continue;
                }

                let pointer_ty = gcx
                    .store
                    .interners
                    .intern_ty(TyKind::Pointer(concrete, crate::hir::Mutability::Mutable));
                let pointer = body.locals.push(LocalDecl {
                    ty: pointer_ty,
                    kind: LocalKind::Temp,
                    mutable: true,
                    name: None,
                    span: statement.span,
                });
                body.escape_locals.push(false);
                lowered.push(Statement {
                    kind: StatementKind::StorageLive(pointer),
                    span: statement.span,
                });
                lowered.push(Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(pointer),
                        Rvalue::Alloc { ty: concrete },
                    ),
                    span: statement.span,
                });
                lowered.push(Statement {
                    kind: StatementKind::Assign(
                        Place {
                            local: pointer,
                            projection: vec![PlaceElem::Deref],
                        },
                        Rvalue::Use(operand),
                    ),
                    span: statement.span,
                });
                lowered.push(Statement {
                    kind: StatementKind::Assign(
                        destination,
                        Rvalue::Cast {
                            operand: Operand::Copy(Place::from_local(pointer)),
                            ty: target,
                            kind: crate::mir::CastKind::ExistentialPack { concrete },
                        },
                    ),
                    span: statement.span,
                });
            }
            body.basic_blocks[block].statements = lowered;
        }
        Ok(())
    }
}

impl<'ctx> MirPass<'ctx> for InsertSafepoints {
    fn name(&self) -> &'static str {
        "InsertSafepoints"
    }

    fn run(&mut self, gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
        let mut targets: FxHashSet<BasicBlockId> = FxHashSet::default();
        targets.insert(body.start_block);

        // Select a deterministic feedback vertex set. Repeatedly remove one
        // block from a discovered cycle until the remaining CFG is acyclic;
        // consequently every original cycle crosses at least one poll. This
        // covers irreducible control flow as well as natural loops.
        while let Some(cycle) = find_unpolled_cycle(body, &targets) {
            let selected = cycle
                .into_iter()
                .min_by_key(|block| block.index())
                .expect("reported cycle must contain a block");
            targets.insert(selected);
        }

        let span = body.locals[body.return_local].span;
        for bb in body.basic_blocks.indices() {
            if !targets.contains(&bb) {
                continue;
            }
            let statements = &mut body.basic_blocks[bb].statements;
            let insertion_index = statements
                .iter()
                .take_while(|stmt| matches!(stmt.kind, StatementKind::SourceScope(_)))
                .count();
            let needs = statements
                .get(insertion_index)
                .map(|stmt| !matches!(stmt.kind, StatementKind::GcSafepoint(_)))
                .unwrap_or(true);
            if needs {
                let kind = if bb == body.start_block {
                    crate::mir::GcSafepointKind::Entry
                } else {
                    crate::mir::GcSafepointKind::Loop
                };
                statements.insert(
                    insertion_index,
                    Statement {
                        kind: StatementKind::GcSafepoint(kind),
                        span,
                    },
                );
            }
        }

        if let Err(cycle) = verify_safepoint_cycle_coverage(body) {
            gcx.dcx().emit_error(
                format!(
                    "internal compiler error: GC safepoint placement left an unpolled CFG cycle through {cycle:?}"
                ),
                Some(span),
            );
            return Err(ReportedError);
        }
        Ok(())
    }
}

/// Verify that removing blocks containing an actual MIR safepoint leaves an
/// acyclic CFG. This deliberately inspects the body instead of the placement
/// pass's candidate set so callers can run it after subsequent CFG rewrites.
pub(crate) fn verify_safepoint_cycle_coverage(body: &Body<'_>) -> Result<(), Vec<BasicBlockId>> {
    let polled = body
        .basic_blocks
        .iter_enumerated()
        .filter_map(|(block, data)| {
            data.statements
                .iter()
                .any(|statement| matches!(statement.kind, StatementKind::GcSafepoint(_)))
                .then_some(block)
        })
        .collect();
    match find_unpolled_cycle(body, &polled) {
        Some(cycle) => Err(cycle),
        None => Ok(()),
    }
}

fn find_unpolled_cycle(
    body: &Body<'_>,
    polled: &FxHashSet<BasicBlockId>,
) -> Option<Vec<BasicBlockId>> {
    fn visit(
        body: &Body<'_>,
        node: BasicBlockId,
        polled: &FxHashSet<BasicBlockId>,
        colors: &mut [u8],
        stack: &mut Vec<BasicBlockId>,
    ) -> Option<Vec<BasicBlockId>> {
        colors[node.index()] = 1;
        stack.push(node);
        if let Some(term) = &body.basic_blocks[node].terminator {
            for successor in terminator_successors(term) {
                if polled.contains(&successor) {
                    continue;
                }
                match colors[successor.index()] {
                    0 => {
                        if let Some(cycle) = visit(body, successor, polled, colors, stack) {
                            return Some(cycle);
                        }
                    }
                    1 => {
                        let start = stack
                            .iter()
                            .position(|candidate| *candidate == successor)
                            .expect("active DFS node must be on stack");
                        return Some(stack[start..].to_vec());
                    }
                    _ => {}
                }
            }
        }
        stack.pop();
        colors[node.index()] = 2;
        None
    }

    let mut colors = vec![0u8; body.basic_blocks.len()];
    let mut stack = Vec::new();
    for block in body.basic_blocks.indices() {
        if polled.contains(&block) || colors[block.index()] != 0 {
            continue;
        }
        if let Some(cycle) = visit(body, block, polled, &mut colors, &mut stack) {
            return Some(cycle);
        }
    }
    None
}

fn aggregate_field_operand<'ctx>(
    gcx: Gcx<'ctx>,
    owner: crate::hir::DefinitionID,
    ty: Ty<'ctx>,
    local: LocalId,
) -> Operand<'ctx> {
    let ty = crate::sema::tycheck::utils::normalize::normalize_aliases(gcx, ty);
    if gcx.is_type_copyable_in_def(ty, owner) {
        Operand::Copy(Place::from_local(local))
    } else {
        Operand::Move(Place::from_local(local))
    }
}

fn operand_ty<'a>(
    body: &Body<'a>,
    gcx: Gcx<'a>,
    operand: &Operand<'a>,
) -> crate::sema::models::Ty<'a> {
    match operand {
        Operand::Constant(c) => c.ty,
        Operand::Copy(place) | Operand::Move(place) | Operand::CopyWith(place, _) => {
            place_ty(body, gcx, place)
        }
    }
}

fn place_ty<'a>(body: &Body<'a>, gcx: Gcx<'a>, place: &Place<'a>) -> crate::sema::models::Ty<'a> {
    let mut ty = body.locals[place.local].ty;
    for elem in &place.projection {
        match elem {
            PlaceElem::Deref => {
                ty = ty
                    .dereference()
                    .unwrap_or_else(|| crate::sema::models::Ty::error(gcx));
            }
            PlaceElem::Field(_, field_ty) => ty = *field_ty,
            PlaceElem::VariantDowncast { index, .. } => {
                let def = match ty.kind() {
                    TyKind::Adt(def, _) if def.kind == AdtKind::Enum => def,
                    _ => return Ty::error(gcx),
                };
                ty = enum_variant_tuple_ty(gcx, def.id, *index);
            }
        }
    }
    ty
}

fn enum_variant_tuple_ty<'a>(
    gcx: Gcx<'a>,
    def_id: crate::hir::DefinitionID,
    variant_index: crate::thir::VariantIndex,
) -> Ty<'a> {
    let def = gcx.get_enum_definition(def_id);
    let variant = def
        .variants
        .get(variant_index.index())
        .expect("enum variant index");
    match variant.kind {
        EnumVariantKind::Unit => gcx.types.void,
        EnumVariantKind::Tuple(fields) => {
            let mut tys = Vec::with_capacity(fields.len());
            for field in fields {
                tys.push(field.ty);
            }
            let list = gcx.store.interners.intern_ty_list(tys);
            Ty::new(TyKind::Tuple(list), gcx)
        }
    }
}

fn terminator_successors(term: &crate::mir::Terminator<'_>) -> Vec<BasicBlockId> {
    match &term.kind {
        TerminatorKind::Goto { target } => vec![*target],
        TerminatorKind::SwitchInt {
            targets, otherwise, ..
        } => {
            let mut succs: Vec<_> = targets.iter().map(|(_, bb)| *bb).collect();
            succs.push(*otherwise);
            succs
        }
        TerminatorKind::Call { target, unwind, .. } => {
            let mut succs = vec![*target];
            if let CallUnwindAction::Cleanup(bb) = unwind {
                succs.push(*bb);
            }
            succs
        }
        TerminatorKind::Yield {
            resume,
            cancel,
            unwind,
            ..
        } => {
            let mut succs = vec![*resume, *cancel];
            if let CallUnwindAction::Cleanup(bb) = unwind {
                succs.push(*bb);
            }
            succs
        }
        TerminatorKind::Return
        | TerminatorKind::ResumeUnwind
        | TerminatorKind::Unreachable
        | TerminatorKind::UnresolvedGoto => vec![],
    }
}

#[cfg(test)]
mod tests {
    use super::{InsertSafepoints, LowerAggregates, verify_safepoint_cycle_coverage};
    use crate::{
        PackageIndex,
        hir::{DefinitionID, NodeID},
        mir::{
            AggregateKind, BasicBlockData, GcSafepointKind, Operand, Place, PlaceElem, Rvalue,
            Statement, StatementKind, Terminator, TerminatorKind,
            optimize::MirPass,
            test_support::{minimal_body, push_temp, with_test_gcx},
        },
        sema::{
            models::{
                CaptureAccessKind, CaptureKind, CapturedVar, ClosureCaptures, ClosureKind,
                GenericArgument, GenericParameter, Ty, TyKind,
            },
            resolve::models::DefinitionIndex,
        },
        span::{FileID, Span},
        thir::FieldIndex,
    };

    #[test]
    fn closure_aggregate_fields_use_captured_generic_arguments() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let span = Span::empty(FileID::new(0));
            let closure_id = DefinitionID::new(PackageIndex::new(1), DefinitionIndex::from_raw(10));
            let parameter = Ty::new(
                TyKind::Parameter(GenericParameter {
                    index: 0,
                    name: gcx.intern_symbol("T"),
                }),
                gcx,
            );
            gcx.cache_closure_captures(
                closure_id,
                ClosureCaptures {
                    captures: vec![CapturedVar {
                        source_id: NodeID::from_raw(0),
                        name: gcx.intern_symbol("value"),
                        ty: parameter,
                        capture_kind: CaptureKind::ByMove,
                        access_kind: CaptureAccessKind::Move,
                        field_index: FieldIndex::from_raw(0),
                    }],
                    kind: ClosureKind::FnOnce,
                },
            );

            let captured_generics = gcx
                .store
                .interners
                .intern_generic_args(vec![GenericArgument::Type(gcx.types.int32)]);
            let closure_ty = Ty::new(
                TyKind::Closure {
                    closure_def_id: closure_id,
                    kind: ClosureKind::FnOnce,
                    captured_generics,
                    inputs: gcx.store.interners.intern_ty_list(Vec::new()),
                    output: gcx.types.void,
                },
                gcx,
            );
            let destination = push_temp(&mut body, closure_ty);
            let value = push_temp(&mut body, gcx.types.int32);
            body.basic_blocks[body.start_block]
                .statements
                .push(Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(destination),
                        Rvalue::Aggregate {
                            kind: AggregateKind::Closure {
                                def_id: closure_id,
                                captured_generics,
                            },
                            fields: vec![Operand::move_(Place::from_local(value))]
                                .into_iter()
                                .collect(),
                        },
                    ),
                    span,
                });

            assert!(LowerAggregates.run(gcx, &mut body).is_ok());

            let field_ty = body.basic_blocks[body.start_block]
                .statements
                .iter()
                .find_map(|statement| match &statement.kind {
                    StatementKind::Assign(place, _)
                        if place.local == destination && !place.projection.is_empty() =>
                    {
                        match place.projection.last() {
                            Some(PlaceElem::Field(_, ty)) => Some(*ty),
                            _ => None,
                        }
                    }
                    _ => None,
                })
                .expect("lowered closure field assignment");
            assert_eq!(field_ty, gcx.types.int32);
        });
    }

    #[test]
    fn safepoint_placement_covers_entry_and_every_cfg_cycle() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let span = body.locals[body.return_local].span;
            let loop_block = body.basic_blocks.push(BasicBlockData {
                note: Some("loop".into()),
                statements: Vec::new(),
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

            assert!(InsertSafepoints.run(gcx, &mut body).is_ok());

            assert!(matches!(
                body.basic_blocks[body.start_block].statements[0].kind,
                StatementKind::GcSafepoint(GcSafepointKind::Entry)
            ));
            assert!(matches!(
                body.basic_blocks[loop_block].statements[0].kind,
                StatementKind::GcSafepoint(GcSafepointKind::Loop)
            ));
            assert!(verify_safepoint_cycle_coverage(&body).is_ok());
        });
    }

    #[test]
    fn safepoint_verifier_rejects_an_unpolled_cycle() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let span = body.locals[body.return_local].span;
            body.basic_blocks[body.start_block].terminator = Some(Terminator {
                kind: TerminatorKind::Goto {
                    target: body.start_block,
                },
                span,
            });

            assert_eq!(
                verify_safepoint_cycle_coverage(&body),
                Err(vec![body.start_block])
            );
        });
    }
}
