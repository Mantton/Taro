use crate::mir::analysis::dominators::{Dominators, compute_dominators};
use crate::{
    compile::context::Gcx,
    error::CompileResult,
    mir::{
        BasicBlockId, Body, Constant, LocalId, LocalKind, Operand, Place, Rvalue, StatementKind,
        TerminatorKind,
    },
};
use index_vec::IndexVec;

use super::MirPass;

pub struct TempCoalescing;

#[derive(Clone, Copy, PartialEq, Eq)]
enum OperandKind {
    Copy,
    Move,
}

#[derive(Clone)]
struct DefSite<'ctx> {
    block: BasicBlockId,
    stmt_index: usize,
    kind: OperandKind,
    replacement: Replacement<'ctx>,
}

#[derive(Clone, Copy)]
struct UseSite {
    block: BasicBlockId,
    stmt_index: usize,
    kind: OperandKind,
}

#[derive(Clone)]
enum Replacement<'ctx> {
    Copy(LocalId),
    Move(LocalId),
    Constant(Constant<'ctx>),
}

impl<'ctx> MirPass<'ctx> for TempCoalescing {
    fn name(&self) -> &'static str {
        "TempCoalescing"
    }

    fn run(&mut self, _gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
        let num_locals = body.locals.len();
        let dominators = compute_dominators(body);

        let mut assignment_count = vec![0usize; num_locals];
        let mut address_taken = vec![false; num_locals];
        let mut place_used = vec![false; num_locals];
        let mut use_counts = vec![0usize; num_locals];
        let mut def_sites: Vec<Option<DefSite<'ctx>>> = vec![None; num_locals];
        let mut use_sites: Vec<Option<UseSite>> = vec![None; num_locals];

        for (bb, block) in body.basic_blocks.iter_enumerated() {
            for (stmt_index, stmt) in block.statements.iter().enumerate() {
                match &stmt.kind {
                    StatementKind::Assign(dest, rv) => {
                        if dest.projection.is_empty() {
                            assignment_count[dest.local.index()] += 1;
                            if let Rvalue::Use(op) = rv {
                                if let Some((kind, replacement)) = replacement_from_operand(op) {
                                    def_sites[dest.local.index()] = Some(DefSite {
                                        block: bb,
                                        stmt_index,
                                        kind,
                                        replacement,
                                    });
                                }
                            }
                        } else {
                            place_used[dest.local.index()] = true;
                        }

                        record_rvalue_uses(
                            rv,
                            bb,
                            stmt_index,
                            &mut use_sites,
                            &mut use_counts,
                            &mut address_taken,
                            &mut place_used,
                        );
                    }
                    StatementKind::SetDiscriminant { place, .. } => {
                        place_used[place.local.index()] = true;
                        if !place.projection.is_empty() {
                            place_used[place.local.index()] = true;
                        }
                    }
                    _ => {}
                }
            }

            if let Some(term) = &block.terminator {
                let term_index = block.statements.len();
                record_terminator_uses(
                    &term.kind,
                    bb,
                    term_index,
                    &mut use_sites,
                    &mut use_counts,
                    &mut place_used,
                );
                if let TerminatorKind::Call { destination, .. } = &term.kind {
                    if destination.projection.is_empty() {
                        assignment_count[destination.local.index()] += 1;
                    } else {
                        place_used[destination.local.index()] = true;
                    }
                }
            }
        }

        let mut replace_map: Vec<Option<Replacement<'ctx>>> = vec![None; num_locals];
        let mut remove_defs: IndexVec<BasicBlockId, Vec<bool>> =
            IndexVec::from(vec![Vec::new(); body.basic_blocks.len()]);
        for (bb, block) in body.basic_blocks.iter_enumerated() {
            remove_defs[bb] = vec![false; block.statements.len()];
        }

        for (local, decl) in body.locals.iter_enumerated() {
            if !matches!(decl.kind, LocalKind::Temp) {
                continue;
            }
            if assignment_count[local.index()] != 1 {
                continue;
            }
            if address_taken[local.index()] || place_used[local.index()] {
                continue;
            }
            if use_counts[local.index()] != 1 {
                continue;
            }
            let Some(def_site) = def_sites[local.index()].as_ref() else {
                continue;
            };
            let Some(use_site) = use_sites[local.index()] else {
                continue;
            };
            if def_site.kind != use_site.kind {
                continue;
            }
            if !def_dominates_use(def_site, &use_site, &dominators) {
                continue;
            }

            let replacement = def_site.replacement.clone();
            if !replacement_is_safe(
                &replacement,
                def_site,
                &use_site,
                body,
                &assignment_count,
                &address_taken,
            ) {
                continue;
            }
            if def_site.kind == OperandKind::Move && def_site.block != use_site.block {
                continue;
            }
            if def_site.kind == OperandKind::Move && !gap_is_safe(body, def_site, &use_site) {
                continue;
            }

            replace_map[local.index()] = Some(replacement);
            remove_defs[def_site.block][def_site.stmt_index] = true;
        }

        if replace_map.iter().all(|item| item.is_none()) {
            return Ok(());
        }

        for block in body.basic_blocks.iter_mut() {
            for stmt in block.statements.iter_mut() {
                replace_stmt_operands(stmt, &replace_map);
            }
            if let Some(term) = block.terminator.as_mut() {
                replace_terminator_operands(term, &replace_map);
            }
        }

        for (bb, block) in body.basic_blocks.iter_mut_enumerated() {
            let mut idx = 0;
            block.statements.retain(|_| {
                let keep = !remove_defs[bb][idx];
                idx += 1;
                keep
            });
        }

        Ok(())
    }
}

fn def_dominates_use(def: &DefSite<'_>, use_site: &UseSite, dominators: &Dominators) -> bool {
    if def.block == use_site.block {
        def.stmt_index < use_site.stmt_index
    } else {
        dominators.dominates(def.block, use_site.block)
    }
}

fn replacement_is_safe<'ctx>(
    replacement: &Replacement<'ctx>,
    def: &DefSite<'ctx>,
    use_site: &UseSite,
    body: &Body<'ctx>,
    assignment_count: &[usize],
    address_taken: &[bool],
) -> bool {
    match replacement {
        Replacement::Constant(_) => true,
        Replacement::Copy(local) => {
            if def.block != use_site.block {
                if assignment_count[local.index()] > 1 {
                    return false;
                }
                if address_taken[local.index()] {
                    return false;
                }
                return true;
            }
            gap_is_safe_source(body, def, use_site, *local)
        }
        Replacement::Move(local) => gap_is_safe_source(body, def, use_site, *local),
    }
}

fn gap_is_safe(body: &Body<'_>, def: &DefSite<'_>, use_site: &UseSite) -> bool {
    if def.block != use_site.block {
        return false;
    }
    let block = &body.basic_blocks[def.block];
    let start = def.stmt_index + 1;
    let end = use_site.stmt_index.min(block.statements.len());
    if start >= end {
        return true;
    }
    for stmt in &block.statements[start..end] {
        match &stmt.kind {
            StatementKind::Assign(_, _) => return false,
            StatementKind::GcSafepoint
            | StatementKind::SetDiscriminant { .. }
            | StatementKind::Nop => {
                return false;
            }
        }
    }
    true
}

fn gap_is_safe_source(
    body: &Body<'_>,
    def: &DefSite<'_>,
    use_site: &UseSite,
    source: LocalId,
) -> bool {
    if def.block != use_site.block {
        return false;
    }
    let block = &body.basic_blocks[def.block];
    let start = def.stmt_index + 1;
    let end = use_site.stmt_index.min(block.statements.len());
    for stmt in &block.statements[start..end] {
        match &stmt.kind {
            StatementKind::Assign(dest, rv) => {
                if dest.local == source {
                    return false;
                }
                if rvalue_mentions_local(rv, source) {
                    return false;
                }
            }
            StatementKind::GcSafepoint
            | StatementKind::SetDiscriminant { .. }
            | StatementKind::Nop => {
                return false;
            }
        }
    }
    true
}

fn replacement_from_operand<'ctx>(op: &Operand<'ctx>) -> Option<(OperandKind, Replacement<'ctx>)> {
    match op {
        Operand::Copy(place) if place.projection.is_empty() => {
            Some((OperandKind::Copy, Replacement::Copy(place.local)))
        }
        Operand::Move(place) if place.projection.is_empty() => {
            Some((OperandKind::Move, Replacement::Move(place.local)))
        }
        Operand::Constant(c) => Some((OperandKind::Copy, Replacement::Constant(c.clone()))),
        _ => None,
    }
}

fn record_operand_use(
    op: &Operand<'_>,
    block: BasicBlockId,
    stmt_index: usize,
    use_sites: &mut [Option<UseSite>],
    use_counts: &mut [usize],
    place_used: &mut [bool],
) {
    match op {
        Operand::Copy(place) => record_place_use(
            place,
            OperandKind::Copy,
            block,
            stmt_index,
            use_sites,
            use_counts,
            place_used,
        ),
        Operand::Move(place) => record_place_use(
            place,
            OperandKind::Move,
            block,
            stmt_index,
            use_sites,
            use_counts,
            place_used,
        ),
        Operand::Constant(_) => {}
    }
}

fn record_place_use(
    place: &Place<'_>,
    kind: OperandKind,
    block: BasicBlockId,
    stmt_index: usize,
    use_sites: &mut [Option<UseSite>],
    use_counts: &mut [usize],
    place_used: &mut [bool],
) {
    if !place.projection.is_empty() {
        place_used[place.local.index()] = true;
        return;
    }
    let idx = place.local.index();
    use_counts[idx] += 1;
    if use_sites[idx].is_none() {
        use_sites[idx] = Some(UseSite {
            block,
            stmt_index,
            kind,
        });
    }
}

fn record_rvalue_uses(
    rv: &Rvalue<'_>,
    block: BasicBlockId,
    stmt_index: usize,
    use_sites: &mut [Option<UseSite>],
    use_counts: &mut [usize],
    address_taken: &mut [bool],
    place_used: &mut [bool],
) {
    match rv {
        Rvalue::Use(op)
        | Rvalue::UnaryOp { operand: op, .. }
        | Rvalue::Cast { operand: op, .. }
        | Rvalue::Repeat { operand: op, .. } => {
            record_operand_use(op, block, stmt_index, use_sites, use_counts, place_used)
        }
        Rvalue::BinaryOp { lhs, rhs, .. } => {
            record_operand_use(lhs, block, stmt_index, use_sites, use_counts, place_used);
            record_operand_use(rhs, block, stmt_index, use_sites, use_counts, place_used);
        }
        Rvalue::Ref { place, .. } => {
            address_taken[place.local.index()] = true;
            place_used[place.local.index()] = true;
        }
        Rvalue::Discriminant { place } => {
            place_used[place.local.index()] = true;
            if !place.projection.is_empty() {
                place_used[place.local.index()] = true;
            }
        }
        Rvalue::Aggregate { fields, .. } => {
            for f in fields {
                record_operand_use(f, block, stmt_index, use_sites, use_counts, place_used);
            }
        }
        Rvalue::Alloc { .. } => {}
    }
}

fn record_terminator_uses(
    term: &TerminatorKind<'_>,
    block: BasicBlockId,
    stmt_index: usize,
    use_sites: &mut [Option<UseSite>],
    use_counts: &mut [usize],
    place_used: &mut [bool],
) {
    match term {
        TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } => {
            record_operand_use(func, block, stmt_index, use_sites, use_counts, place_used);
            for arg in args {
                record_operand_use(arg, block, stmt_index, use_sites, use_counts, place_used);
            }
            if !destination.projection.is_empty() {
                place_used[destination.local.index()] = true;
            }
        }
        TerminatorKind::SwitchInt { discr, .. } => {
            record_operand_use(discr, block, stmt_index, use_sites, use_counts, place_used);
        }
        _ => {}
    }
}

fn replace_stmt_operands<'ctx>(
    stmt: &mut crate::mir::Statement<'ctx>,
    replace_map: &[Option<Replacement<'ctx>>],
) {
    match &mut stmt.kind {
        StatementKind::Assign(_, rv) => replace_rvalue_operands(rv, replace_map),
        StatementKind::SetDiscriminant { .. } => {}
        StatementKind::GcSafepoint | StatementKind::Nop => {}
    }
}

fn replace_terminator_operands<'ctx>(
    term: &mut crate::mir::Terminator<'ctx>,
    replace_map: &[Option<Replacement<'ctx>>],
) {
    match &mut term.kind {
        TerminatorKind::Call { func, args, .. } => {
            replace_operand(func, replace_map);
            for arg in args {
                replace_operand(arg, replace_map);
            }
        }
        TerminatorKind::SwitchInt { discr, .. } => replace_operand(discr, replace_map),
        _ => {}
    }
}

fn replace_rvalue_operands<'ctx>(rv: &mut Rvalue<'ctx>, replace_map: &[Option<Replacement<'ctx>>]) {
    match rv {
        Rvalue::Use(op)
        | Rvalue::UnaryOp { operand: op, .. }
        | Rvalue::Cast { operand: op, .. }
        | Rvalue::Repeat { operand: op, .. } => replace_operand(op, replace_map),
        Rvalue::BinaryOp { lhs, rhs, .. } => {
            replace_operand(lhs, replace_map);
            replace_operand(rhs, replace_map);
        }
        Rvalue::Aggregate { fields, .. } => {
            for f in fields {
                replace_operand(f, replace_map);
            }
        }
        Rvalue::Ref { .. } | Rvalue::Discriminant { .. } | Rvalue::Alloc { .. } => {}
    }
}

fn replace_operand<'ctx>(op: &mut Operand<'ctx>, replace_map: &[Option<Replacement<'ctx>>]) {
    let place = match op {
        Operand::Copy(place) | Operand::Move(place) => {
            if place.projection.is_empty() {
                Some(place.local)
            } else {
                None
            }
        }
        Operand::Constant(_) => None,
    };

    let Some(local) = place else {
        return;
    };
    let Some(replacement) = replace_map[local.index()].as_ref() else {
        return;
    };
    *op = match replacement {
        Replacement::Copy(src) => Operand::Copy(Place::from_local(*src)),
        Replacement::Move(src) => Operand::Move(Place::from_local(*src)),
        Replacement::Constant(c) => Operand::Constant(c.clone()),
    };
}

fn rvalue_mentions_local(rv: &Rvalue<'_>, local: LocalId) -> bool {
    match rv {
        Rvalue::Use(op)
        | Rvalue::UnaryOp { operand: op, .. }
        | Rvalue::Cast { operand: op, .. }
        | Rvalue::Repeat { operand: op, .. } => operand_mentions_local(op, local),
        Rvalue::BinaryOp { lhs, rhs, .. } => {
            operand_mentions_local(lhs, local) || operand_mentions_local(rhs, local)
        }
        Rvalue::Ref { place, .. } | Rvalue::Discriminant { place } => place.local == local,
        Rvalue::Aggregate { fields, .. } => fields
            .iter()
            .any(|field| operand_mentions_local(field, local)),
        Rvalue::Alloc { .. } => false,
    }
}

fn operand_mentions_local(op: &Operand<'_>, local: LocalId) -> bool {
    match op {
        Operand::Copy(place) | Operand::Move(place) => place.local == local,
        Operand::Constant(_) => false,
    }
}
