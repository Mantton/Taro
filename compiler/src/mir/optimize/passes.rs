use super::MirPass;
use super::simplify::{
    collapse_trivial_gotos, eliminate_dead_locals, merge_consecutive_safepoints,
    merge_linear_blocks, prune_unreachable_blocks,
};
use crate::compile::context::Gcx;
use crate::error::{CompileResult, ReportedError};
use crate::hir::DefinitionKind;
use crate::mir::{
    BasicBlockId, Body, LocalDecl, LocalId, LocalKind, MirPhase, Operand, Place, PlaceElem, Rvalue,
    Statement, StatementKind, TerminatorKind,
};
use crate::sema::models::{Ty, TyKind};
use crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args;
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
        for bb in body.basic_blocks.indices() {
            let statements = std::mem::take(&mut body.basic_blocks[bb].statements);
            let mut lowered = Vec::with_capacity(statements.len());

            for stmt in statements {
                let span = stmt.span;
                let StatementKind::Assign(dest, Rvalue::Aggregate { kind, fields }) = stmt.kind
                else {
                    lowered.push(stmt);
                    continue;
                };
                // LLVM lowers arrays directly, including empty arrays.
                if matches!(kind, crate::mir::AggregateKind::Array { .. }) {
                    lowered.push(Statement {
                        kind: StatementKind::Assign(dest, Rvalue::Aggregate { kind, fields }),
                        span,
                    });
                    continue;
                }

                let mut field_base = dest.clone();
                let mut variant_index = None;
                let field_tys: Vec<_> = match kind {
                    crate::mir::AggregateKind::Tuple => {
                        let TyKind::Tuple(items) = body.place_ty(gcx, &dest).kind() else {
                            panic!("tuple aggregate must have a tuple destination");
                        };
                        items.to_vec()
                    }
                    crate::mir::AggregateKind::Adt {
                        def_id,
                        variant_index: variant,
                        generic_args,
                    } => match gcx.definition_kind(def_id) {
                        DefinitionKind::Struct => gcx
                            .get_struct_definition(def_id)
                            .fields
                            .iter()
                            .map(|field| instantiate_ty_with_args(gcx, field.ty, generic_args))
                            .collect(),
                        DefinitionKind::Enum => {
                            let index = variant.expect("enum aggregate variant");
                            let variant = gcx.enum_variant_by_index(def_id, index);
                            field_base.projection.push(PlaceElem::VariantDowncast {
                                name: variant.name,
                                index,
                            });
                            variant_index = Some(index);
                            fields
                                .iter()
                                .map(|operand| body.operand_ty(gcx, operand))
                                .collect()
                        }
                        _ => unreachable!("aggregate must be a struct or enum"),
                    },
                    crate::mir::AggregateKind::Closure {
                        def_id,
                        captured_generics,
                    } => gcx
                        .get_closure_captures(def_id)
                        .map(|info| {
                            info.captures
                                .iter()
                                .map(|capture| {
                                    instantiate_ty_with_args(gcx, capture.ty, captured_generics)
                                })
                                .collect()
                        })
                        .unwrap_or_default(),
                    crate::mir::AggregateKind::Array { .. } => unreachable!(),
                };
                assert_eq!(fields.len(), field_tys.len(), "aggregate field count");

                // Read every operand before writing any destination field: the
                // destination may overlap an input (for example a tuple swap).
                let mut temps = Vec::with_capacity(fields.len());
                for ((index, operand), field_ty) in fields.into_iter_enumerated().zip(field_tys) {
                    let ty = body.operand_ty(gcx, &operand);
                    let local = body.locals.push(LocalDecl {
                        ty,
                        kind: LocalKind::Temp,
                        mutable: true,
                        name: None,
                        span,
                    });
                    body.escape_locals.push(false);
                    lowered.push(Statement {
                        kind: StatementKind::Assign(Place::from_local(local), Rvalue::Use(operand)),
                        span,
                    });
                    temps.push((local, index, field_ty));
                }
                for (local, index, field_ty) in temps {
                    let mut place = field_base.clone();
                    place.projection.push(PlaceElem::Field(index, field_ty));
                    lowered.push(Statement {
                        kind: StatementKind::Assign(
                            place,
                            Rvalue::Use(aggregate_field_operand(
                                gcx,
                                body.owner,
                                body.locals[local].ty,
                                local,
                            )),
                        ),
                        span,
                    });
                }

                if let Some(variant_index) = variant_index {
                    // Publish the tag only after all payload stores. A tag-aware
                    // collector must never observe stale payload storage.
                    lowered.push(Statement {
                        kind: StatementKind::SetDiscriminant {
                            place: dest,
                            variant_index,
                        },
                        span,
                    });
                } else if dest.projection.is_empty() {
                    // This safepoint-free store sequence has initialized the
                    // whole local, even when the aggregate has no fields.
                    lowered.push(Statement {
                        kind: StatementKind::SetInitialized(dest.local),
                        span,
                    });
                }
            }
            body.basic_blocks[bb].statements = lowered;
        }
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
        for block in body.basic_blocks.indices() {
            let statements = std::mem::take(&mut body.basic_blocks[block].statements);
            let mut lowered = Vec::with_capacity(statements.len());
            for statement in statements {
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
                let concrete = body.operand_ty(gcx, &operand);
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

/// A short, acyclic leaf returns to its caller without allocating or extending
/// a call chain. Its caller's polls therefore bound GC cooperation without an
/// additional entry poll (and cold poll-call frame) in every tiny helper.
fn is_bounded_safepoint_free_leaf(body: &Body<'_>) -> bool {
    if body.is_async || body.escape_locals.iter().any(|escapes| *escapes) {
        return false;
    }
    let mut budget = 64_usize;
    for block in &body.basic_blocks {
        let Some(term) = &block.terminator else {
            return false;
        };
        if !matches!(
            term.kind,
            TerminatorKind::Return | TerminatorKind::Goto { .. } | TerminatorKind::SwitchInt { .. }
        ) {
            return false;
        }
        for statement in &block.statements {
            if matches!(
                statement.kind,
                StatementKind::SourceScope(_) | StatementKind::StorageLive(_) | StatementKind::Nop
            ) {
                continue;
            }
            if let StatementKind::Assign(_, value) = &statement.kind {
                if !matches!(
                    value,
                    Rvalue::Use(_)
                        | Rvalue::UnaryOp { .. }
                        | Rvalue::BinaryOp { .. }
                        | Rvalue::Discriminant { .. }
                ) {
                    return false;
                }
            } else if !matches!(
                statement.kind,
                StatementKind::SetDiscriminant { .. }
                    | StatementKind::SetInitialized(_)
                    | StatementKind::KeepAlive(_)
            ) {
                return false;
            }
            let Some(remaining) = budget.checked_sub(1) else {
                return false;
            };
            budget = remaining;
        }
        let Some(remaining) = budget.checked_sub(1) else {
            return false;
        };
        budget = remaining;
    }
    find_unpolled_cycle(body, &FxHashSet::default()).is_none()
}

impl<'ctx> MirPass<'ctx> for InsertSafepoints {
    fn name(&self) -> &'static str {
        "InsertSafepoints"
    }

    fn run(&mut self, gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
        if is_bounded_safepoint_free_leaf(body) {
            return Ok(());
        }
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
            for successor in term.kind.successors() {
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

#[cfg(test)]
mod tests {
    use super::{
        InsertSafepoints, LowerAggregates, is_bounded_safepoint_free_leaf,
        verify_safepoint_cycle_coverage,
    };
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
    fn aggregate_lowering_reads_overlapping_fields_before_writing() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let ty = Ty::new(
                TyKind::Tuple(gcx.store.interners.intern_ty_list(vec![gcx.types.int32; 2])),
                gcx,
            );
            let local = push_temp(&mut body, ty);
            let span = body.locals[local].span;
            let field = |index| Place {
                local,
                projection: vec![PlaceElem::Field(
                    FieldIndex::from_raw(index),
                    gcx.types.int32,
                )],
            };
            body.basic_blocks[body.start_block]
                .statements
                .push(Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(local),
                        Rvalue::Aggregate {
                            kind: AggregateKind::Tuple,
                            fields: vec![
                                Operand::Move(field(1)),
                                Operand::CopyWith(
                                    field(0),
                                    crate::mir::CopyModifiers {
                                        take: false,
                                        init: true,
                                    },
                                ),
                            ]
                            .into_iter()
                            .collect(),
                        },
                    ),
                    span,
                });

            assert!(LowerAggregates.run(gcx, &mut body).is_ok());

            let statements = &body.basic_blocks[body.start_block].statements;
            assert_eq!(statements.len(), 5);
            assert!(
                matches!(&statements[0].kind, StatementKind::Assign(dest, Rvalue::Use(Operand::Move(source))) if dest.local != local && source == &field(1))
            );
            assert!(
                matches!(&statements[1].kind, StatementKind::Assign(dest, Rvalue::Use(Operand::CopyWith(source, modifiers))) if dest.local != local && source == &field(0) && modifiers.init)
            );
            for (index, statement) in statements[2..4].iter().enumerate() {
                assert!(
                    matches!(&statement.kind, StatementKind::Assign(dest, Rvalue::Use(Operand::Copy(source))) if dest == &field(index as u32) && source.projection.is_empty())
                );
            }
            assert!(matches!(statements[4].kind, StatementKind::SetInitialized(id) if id == local));
        });
    }

    #[test]
    fn enum_payload_aggregate_uses_instantiated_field_types() {
        use crate::sema::models::{
            AdtDef, AdtKind, EnumDefinition, EnumVariant, EnumVariantField, EnumVariantKind,
        };
        use crate::thir::VariantIndex;

        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let enum_id = DefinitionID::new(PackageIndex::new(1), DefinitionIndex::from_raw(10));
            let adt_def = AdtDef {
                kind: AdtKind::Enum,
                id: enum_id,
            };
            let parameter = Ty::new(
                TyKind::Parameter(GenericParameter {
                    index: 0,
                    name: gcx.intern_symbol("T"),
                }),
                gcx,
            );
            let name = gcx.intern_symbol("Some");
            let fields = gcx
                .store
                .arenas
                .global
                .alloc_slice_copy(&[EnumVariantField {
                    label: None,
                    ty: parameter,
                }]);
            let variants = gcx.store.arenas.global.alloc_slice_copy(&[EnumVariant {
                name,
                def_id: enum_id,
                ctor_def_id: enum_id,
                kind: EnumVariantKind::Tuple(fields),
                discriminant: 0,
            }]);
            gcx.cache_enum_definition(enum_id, EnumDefinition { adt_def, variants });
            let args = gcx
                .store
                .interners
                .intern_generic_args(vec![GenericArgument::Type(gcx.types.int32)]);
            let destination = push_temp(&mut body, Ty::new(TyKind::Adt(adt_def, args), gcx));
            let value = push_temp(&mut body, gcx.types.int32);
            let span = body.locals[destination].span;
            body.basic_blocks[body.start_block]
                .statements
                .push(Statement {
                    kind: StatementKind::Assign(
                        Place {
                            local: destination,
                            projection: vec![PlaceElem::VariantDowncast {
                                name,
                                index: VariantIndex::from_raw(0),
                            }],
                        },
                        Rvalue::Aggregate {
                            kind: AggregateKind::Tuple,
                            fields: vec![Operand::Copy(Place::from_local(value))]
                                .into_iter()
                                .collect(),
                        },
                    ),
                    span,
                });

            assert!(LowerAggregates.run(gcx, &mut body).is_ok());

            let StatementKind::Assign(destination, _) =
                &body.basic_blocks[body.start_block].statements[1].kind
            else {
                panic!("expected payload field assignment");
            };
            assert_eq!(
                destination.projection.last(),
                Some(&PlaceElem::Field(FieldIndex::from_raw(0), gcx.types.int32))
            );
        });
    }

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

            assert!(matches!(
                body.basic_blocks[body.start_block]
                    .statements
                    .last()
                    .map(|statement| &statement.kind),
                Some(StatementKind::SetInitialized(local)) if *local == destination
            ));

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
    fn empty_aggregate_still_publishes_initialization() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let span = body.locals[body.return_local].span;
            let tuple_ty = Ty::new(
                TyKind::Tuple(gcx.store.interners.intern_ty_list(Vec::new())),
                gcx,
            );
            let destination = push_temp(&mut body, tuple_ty);
            body.basic_blocks[body.start_block]
                .statements
                .push(Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(destination),
                        Rvalue::Aggregate {
                            kind: AggregateKind::Tuple,
                            fields: Vec::new().into_iter().collect(),
                        },
                    ),
                    span,
                });

            assert!(LowerAggregates.run(gcx, &mut body).is_ok());
            assert!(matches!(
                body.basic_blocks[body.start_block].statements.as_slice(),
                [Statement {
                    kind: StatementKind::SetInitialized(local),
                    ..
                }] if *local == destination
            ));
        });
    }

    #[test]
    fn bounded_leaf_omits_entry_poll_but_allocation_and_calls_keep_it() {
        with_test_gcx(|gcx| {
            let body = minimal_body(gcx);
            let mut leaf = body.clone();
            assert!(is_bounded_safepoint_free_leaf(&leaf));
            assert!(InsertSafepoints.run(gcx, &mut leaf).is_ok());
            assert!(leaf.basic_blocks[leaf.start_block].statements.is_empty());

            let span = body.locals[body.return_local].span;
            let mut allocating = body.clone();
            allocating.basic_blocks[body.start_block]
                .statements
                .push(Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(body.return_local),
                        Rvalue::Alloc {
                            ty: gcx.types.int32,
                        },
                    ),
                    span,
                });
            assert!(!is_bounded_safepoint_free_leaf(&allocating));
            assert!(InsertSafepoints.run(gcx, &mut allocating).is_ok());
            assert!(matches!(
                allocating.basic_blocks[body.start_block].statements[0].kind,
                StatementKind::GcSafepoint(GcSafepointKind::Entry)
            ));

            let mut calling = body.clone();
            calling.basic_blocks[body.start_block].terminator = Some(Terminator {
                kind: TerminatorKind::Call {
                    func: Operand::Copy(Place::from_local(body.return_local)),
                    args: Vec::new(),
                    devirt_hint: None,
                    destination: Place::from_local(body.return_local),
                    target: body.start_block,
                    unwind: crate::mir::CallUnwindAction::Terminate,
                },
                span,
            });
            assert!(!is_bounded_safepoint_free_leaf(&calling));
            let mut escaping = body.clone();
            escaping.escape_locals = vec![true];
            assert!(!is_bounded_safepoint_free_leaf(&escaping));
        });
    }

    #[test]
    fn leaf_poll_elision_rejects_cycles_and_large_bodies() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let span = body.locals[body.return_local].span;
            body.basic_blocks[body.start_block].statements = (0..64)
                .map(|_| Statement {
                    kind: StatementKind::SetInitialized(body.return_local),
                    span,
                })
                .collect();
            assert!(!is_bounded_safepoint_free_leaf(&body));
            body.basic_blocks[body.start_block].statements.clear();
            body.basic_blocks[body.start_block].terminator = Some(Terminator {
                kind: TerminatorKind::Goto {
                    target: body.start_block,
                },
                span,
            });
            assert!(!is_bounded_safepoint_free_leaf(&body));
            assert!(InsertSafepoints.run(gcx, &mut body).is_ok());
            assert!(verify_safepoint_cycle_coverage(&body).is_ok());
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
