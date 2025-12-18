use super::MirPass;
use super::simplify::{collapse_trivial_gotos, prune_unreachable_blocks};
use crate::compile::context::Gcx;
use crate::mir::{
    BasicBlockData, Body, LocalDecl, LocalId, LocalKind, MirPhase, Operand, Place, PlaceElem,
    Rvalue, Statement, StatementKind,
};
use crate::sema::models::{StructDefinition, TyKind};
use crate::thir::FieldIndex;

pub struct SimplifyCfg;
pub struct PruneUnreachable;
pub struct LowerAggregates;

impl<'ctx> MirPass<'ctx> for PruneUnreachable {
    fn name(&self) -> &'static str {
        "PruneUnreachable"
    }

    fn run(&mut self, _gcx: Gcx<'ctx>, body: &mut Body<'ctx>) {
        prune_unreachable_blocks(body);
    }
}

impl<'ctx> MirPass<'ctx> for SimplifyCfg {
    fn name(&self) -> &'static str {
        "SimplifyCfg"
    }

    fn run(&mut self, _gcx: Gcx<'_>, body: &mut Body<'_>) {
        collapse_trivial_gotos(body);
        prune_unreachable_blocks(body);
    }
}

impl<'ctx> MirPass<'ctx> for LowerAggregates {
    fn name(&self) -> &'static str {
        "LowerAggregates"
    }

    fn run(&mut self, gcx: Gcx<'ctx>, body: &mut Body<'ctx>) {
        let mut new_blocks = body.basic_blocks.clone();

        for bb in body.basic_blocks.indices() {
            let BasicBlockData {
                statements,
                terminator,
                note,
            } = body.basic_blocks[bb].clone();
            let mut lowered: Vec<Statement> = Vec::with_capacity(statements.len());

            for stmt in statements {
                match stmt.kind {
                    StatementKind::Assign(dest, Rvalue::Aggregate { kind, fields }) => {
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
                                name: None,
                                span: stmt.span,
                            });
                            lowered.push(Statement {
                                kind: StatementKind::Assign(
                                    Place::from_local(temp_local),
                                    Rvalue::Use(operand.clone()),
                                ),
                                span: stmt.span,
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
                                        span: stmt.span,
                                    });
                                }
                            }
                            crate::mir::AggregateKind::Adt(def_id) => {
                                let StructDefinition { fields, .. } =
                                    *gcx.get_struct_definition(def_id);
                                for ((temp_local, idx), field) in
                                    temps.into_iter().zip(fields.iter())
                                {
                                    let mut proj = dest.projection.clone();
                                    proj.push(PlaceElem::Field(idx, field.ty));
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
                                        span: stmt.span,
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
    }

    fn phase_change(&self) -> Option<MirPhase> {
        Some(MirPhase::Lowered)
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
        }
    }
    ty
}
