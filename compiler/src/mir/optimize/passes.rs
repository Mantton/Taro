use super::MirPass;
use super::simplify::{collapse_trivial_gotos, prune_unreachable_blocks};
use crate::compile::context::Gcx;
use crate::hir::{DefinitionKind, Mutability};
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
pub struct EscapeAnalysis;
pub struct ApplyEscapeAnalysis;
pub struct InsertSafepoints;

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
    }

    fn phase_change(&self) -> Option<MirPhase> {
        Some(MirPhase::Lowered)
    }
}

impl<'ctx> MirPass<'ctx> for EscapeAnalysis {
    fn name(&self) -> &'static str {
        "EscapeAnalysis"
    }

    fn run(&mut self, _gcx: Gcx<'ctx>, body: &mut Body<'ctx>) {
        let local_count = body.locals.len();
        body.escape_locals.clear();
        body.escape_locals.resize(local_count, false);

        let mut ref_bases: Vec<Vec<LocalId>> = vec![Vec::new(); local_count];
        let mut ref_sources: Vec<Vec<LocalId>> = vec![Vec::new(); local_count];
        let mut ref_escapes = vec![false; local_count];

        let is_ref_local: Vec<bool> = body
            .locals
            .iter()
            .map(|decl| matches!(decl.ty.kind(), TyKind::Reference(..)))
            .collect();

        for bb in body.basic_blocks.iter() {
            for stmt in &bb.statements {
                match &stmt.kind {
                    StatementKind::Assign(dest, Rvalue::Ref { place, .. }) => {
                        if let Some(base) = base_local_for_ref(place) {
                            if dest.projection.is_empty() && dest.local == body.return_local {
                                body.escape_locals[base.index()] = true;
                                continue;
                            }

                            if dest.projection.is_empty() && is_ref_local[dest.local.index()] {
                                if !ref_bases[dest.local.index()].contains(&base) {
                                    ref_bases[dest.local.index()].push(base);
                                }
                            } else {
                                body.escape_locals[base.index()] = true;
                            }
                        }
                    }
                    StatementKind::Assign(dest, Rvalue::Use(op)) => {
                        if let Some(src) = ref_local_operand(body, op) {
                            if dest.projection.is_empty() && is_ref_local[dest.local.index()] {
                                ref_sources[dest.local.index()].push(src);
                            } else {
                                ref_escapes[src.index()] = true;
                            }
                        }

                        if dest.projection.is_empty() && dest.local == body.return_local {
                            if let Some(src) = ref_local_operand(body, op) {
                                ref_escapes[src.index()] = true;
                            }
                        }
                    }
                    _ => {}
                }
            }

            if let Some(term) = &bb.terminator {
                if let TerminatorKind::Call { args, .. } = &term.kind {
                    for arg in args {
                        if let Some(local) = ref_local_operand(body, arg) {
                            ref_escapes[local.index()] = true;
                        }
                    }
                }
            }
        }

        let mut worklist: Vec<LocalId> = ref_escapes
            .iter()
            .enumerate()
            .filter_map(|(idx, escaped)| escaped.then(|| LocalId::from_raw(idx as u32)))
            .collect();

        while let Some(local) = worklist.pop() {
            for &src in &ref_sources[local.index()] {
                if !ref_escapes[src.index()] {
                    ref_escapes[src.index()] = true;
                    worklist.push(src);
                }
            }
        }

        for (idx, bases) in ref_bases.iter().enumerate() {
            if !ref_escapes[idx] {
                continue;
            }
            for base in bases {
                body.escape_locals[base.index()] = true;
            }
        }
    }
}

impl<'ctx> MirPass<'ctx> for ApplyEscapeAnalysis {
    fn name(&self) -> &'static str {
        "ApplyEscapeAnalysis"
    }

    fn run(&mut self, gcx: Gcx<'ctx>, body: &mut Body<'ctx>) {
        let mut heapified: Vec<Option<crate::sema::models::Ty<'ctx>>> =
            vec![None; body.locals.len()];
        let mut param_replacements: Vec<Option<LocalId>> = vec![None; body.locals.len()];
        let original_local_count = body.locals.len();

        for idx in 0..original_local_count {
            let kind = body.locals[idx].kind;
            if matches!(kind, LocalKind::Return) {
                continue;
            }
            if body.escape_locals.get(idx).copied().unwrap_or(false) {
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
            return;
        }

        for bb in body.basic_blocks.iter_mut() {
            for stmt in &mut bb.statements {
                rewrite_statement(stmt, &heapified, &param_replacements);
            }
            if let Some(term) = &mut bb.terminator {
                rewrite_terminator(term, &heapified, &param_replacements);
            }
        }

        let span = body.locals[body.return_local].span;
        let mut allocs: Vec<Statement<'ctx>> = Vec::new();
        for (idx, ty) in heapified.iter().enumerate() {
            let Some(old_ty) = ty else { continue };
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
                kind: StatementKind::Assign(heap_place, Rvalue::Use(Operand::Move(param_place))),
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
    }
}

impl<'ctx> MirPass<'ctx> for InsertSafepoints {
    fn name(&self) -> &'static str {
        "InsertSafepoints"
    }

    fn run(&mut self, _gcx: Gcx<'ctx>, body: &mut Body<'ctx>) {
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

fn base_local_for_ref(place: &Place<'_>) -> Option<LocalId> {
    if place
        .projection
        .iter()
        .any(|elem| matches!(elem, PlaceElem::Deref))
    {
        return None;
    }
    Some(place.local)
}

fn ref_local_operand<'a>(body: &Body<'a>, operand: &Operand<'a>) -> Option<LocalId> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            if !place.projection.is_empty() {
                return None;
            }
            let ty = body.locals[place.local].ty;
            matches!(ty.kind(), TyKind::Reference(..)).then_some(place.local)
        }
        Operand::Constant(_) => None,
    }
}

fn rewrite_statement<'ctx>(
    stmt: &mut Statement<'ctx>,
    heapified: &[Option<Ty<'ctx>>],
    param_replacements: &[Option<LocalId>],
) {
    if let StatementKind::Assign(place, rvalue) = &mut stmt.kind {
        rewrite_place(place, heapified, param_replacements);
        rewrite_rvalue(rvalue, heapified, param_replacements);
    }
}

fn rewrite_rvalue<'ctx>(
    rvalue: &mut Rvalue<'ctx>,
    heapified: &[Option<Ty<'ctx>>],
    param_replacements: &[Option<LocalId>],
) {
    match rvalue {
        Rvalue::Use(op) => rewrite_operand(op, heapified, param_replacements),
        Rvalue::UnaryOp { operand, .. } => rewrite_operand(operand, heapified, param_replacements),
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
        Rvalue::Alloc { .. } => {}
    }
}

fn rewrite_operand<'ctx>(
    operand: &mut Operand<'ctx>,
    heapified: &[Option<Ty<'ctx>>],
    param_replacements: &[Option<LocalId>],
) {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
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
