use super::MirPass;
use super::simplify::{collapse_trivial_gotos, eliminate_dead_locals, merge_consecutive_safepoints, merge_linear_blocks, prune_unreachable_blocks};
use crate::compile::context::Gcx;
use crate::error::CompileResult;
use crate::hir::DefinitionKind;
use crate::mir::{
    BasicBlockData, BasicBlockId, Body, LocalDecl, LocalId, LocalKind, MirPhase, Operand, Place,
    PlaceElem, Rvalue, Statement, StatementKind, TerminatorKind,
};
use crate::sema::models::{AdtKind, EnumVariantKind, StructDefinition, Ty, TyKind};
use crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args;
use crate::thir::FieldIndex;
use rustc_hash::FxHashSet;

pub struct SimplifyCfg;
pub struct PruneUnreachable;
pub struct LowerAggregates;
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
                                            items.get(i).copied().unwrap_or(dest_ty)
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
                                            Rvalue::Use(Operand::Move(Place::from_local(
                                                temp_local,
                                            ))),
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
                                            Rvalue::Use(Operand::Move(Place::from_local(
                                                temp_local,
                                            ))),
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
                                                    Rvalue::Use(Operand::Move(Place::from_local(
                                                        temp_local,
                                                    ))),
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

                                        // Set Discriminant
                                        lowered.push(Statement {
                                            kind: StatementKind::SetDiscriminant {
                                                place: dest.clone(),
                                                variant_index,
                                            },
                                            span,
                                        });

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
                                                    Rvalue::Use(Operand::Move(Place::from_local(
                                                        temp_local,
                                                    ))),
                                                ),
                                                span,
                                            });
                                        }
                                    }
                                    _ => unreachable!(),
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

impl<'ctx> MirPass<'ctx> for InsertSafepoints {
    fn name(&self) -> &'static str {
        "InsertSafepoints"
    }

    fn run(&mut self, _gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
        let mut targets: FxHashSet<BasicBlockId> = FxHashSet::default();
        targets.insert(body.start_block);

        for (bb_id, bb) in body.basic_blocks.iter_enumerated() {
            let Some(term) = &bb.terminator else { continue };
            for succ in terminator_successors(term) {
                if succ.index() <= bb_id.index() {
                    targets.insert(succ);
                }
            }
        }

        let span = body.locals[body.return_local].span;
        for bb in body.basic_blocks.indices() {
            if !targets.contains(&bb) {
                continue;
            }
            let statements = &mut body.basic_blocks[bb].statements;
            let needs = statements
                .first()
                .map(|stmt| !matches!(stmt.kind, StatementKind::GcSafepoint))
                .unwrap_or(true);
            if needs {
                statements.insert(
                    0,
                    Statement {
                        kind: StatementKind::GcSafepoint,
                        span,
                    },
                );
            }
        }

        for bb in body.basic_blocks.iter_mut() {
            let Some(term) = &bb.terminator else { continue };
            if !matches!(term.kind, TerminatorKind::Call { .. }) {
                continue;
            }
            let needs = bb
                .statements
                .last()
                .map(|stmt| !matches!(stmt.kind, StatementKind::GcSafepoint))
                .unwrap_or(true);
            if needs {
                bb.statements.push(Statement {
                    kind: StatementKind::GcSafepoint,
                    span,
                });
            }
        }
        Ok(())
    }
}

fn operand_ty<'a>(
    body: &Body<'a>,
    gcx: Gcx<'a>,
    operand: &Operand<'a>,
) -> crate::sema::models::Ty<'a> {
    match operand {
        Operand::Constant(c) => c.ty,
        Operand::Copy(place) | Operand::Move(place) => place_ty(body, gcx, place),
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
        TerminatorKind::Call { target, .. } => vec![*target],
        TerminatorKind::Return | TerminatorKind::Unreachable | TerminatorKind::UnresolvedGoto => {
            vec![]
        }
    }
}
