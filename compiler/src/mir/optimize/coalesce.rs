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
pub struct CallDestinationCoalescing;
pub struct RepeatFieldForwarding;

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
            if !operand_kinds_compatible(def_site.kind, use_site.kind) {
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

impl<'ctx> MirPass<'ctx> for CallDestinationCoalescing {
    fn name(&self) -> &'static str {
        "CallDestinationCoalescing"
    }

    fn run(&mut self, _gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
        let num_locals = body.locals.len();
        let mut use_counts = vec![0usize; num_locals];
        let mut address_taken = vec![false; num_locals];
        let mut pred_counts = vec![0usize; body.basic_blocks.len()];

        for (_bb, block) in body.basic_blocks.iter_enumerated() {
            for stmt in &block.statements {
                match &stmt.kind {
                    StatementKind::Assign(_, rv) => {
                        if let Rvalue::Ref { place, .. } = rv {
                            address_taken[place.local.index()] = true;
                        }
                        record_rvalue_use_counts(rv, &mut use_counts);
                    }
                    StatementKind::SetDiscriminant { place, .. } => {
                        if place.projection.is_empty() {
                            use_counts[place.local.index()] += 1;
                        }
                    }
                    StatementKind::GcSafepoint | StatementKind::Nop => {}
                }
            }

            if let Some(term) = &block.terminator {
                record_terminator_use_counts(&term.kind, &mut use_counts);
                for succ in terminator_successors(&term.kind) {
                    pred_counts[succ.index()] += 1;
                }
            }
        }

        let mut rewrites: Vec<(BasicBlockId, Place<'ctx>)> = Vec::new();
        let mut remove_first_stmt = vec![false; body.basic_blocks.len()];

        for (bb, block) in body.basic_blocks.iter_enumerated() {
            let Some(term) = &block.terminator else {
                continue;
            };
            let TerminatorKind::Call {
                destination,
                target,
                ..
            } = &term.kind
            else {
                continue;
            };
            if !destination.projection.is_empty() {
                continue;
            }
            if pred_counts[target.index()] != 1 {
                continue;
            }

            let tmp_local = destination.local;
            if address_taken[tmp_local.index()] {
                continue;
            }
            if use_counts[tmp_local.index()] != 1 {
                continue;
            }

            let target_block = &body.basic_blocks[target.index()];
            let Some(first_stmt) = target_block.statements.first() else {
                continue;
            };
            let StatementKind::Assign(new_dest, Rvalue::Use(op)) = &first_stmt.kind else {
                continue;
            };
            if !new_dest.projection.is_empty() {
                continue;
            }

            let local_from_operand = match op {
                Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                    Some(place.local)
                }
                _ => None,
            };
            if local_from_operand != Some(tmp_local) {
                continue;
            }

            rewrites.push((bb, new_dest.clone()));
            remove_first_stmt[target.index()] = true;
        }

        if rewrites.is_empty() {
            return Ok(());
        }

        for (bb, new_dest) in rewrites {
            if let Some(term) = body.basic_blocks[bb].terminator.as_mut() {
                if let TerminatorKind::Call { destination, .. } = &mut term.kind {
                    *destination = new_dest;
                }
            }
        }

        for (bb, should_remove) in remove_first_stmt.into_iter().enumerate() {
            if !should_remove {
                continue;
            }
            let block = &mut body.basic_blocks[BasicBlockId::from_raw(bb as u32)];
            if !block.statements.is_empty() {
                block.statements.remove(0);
            }
        }

        Ok(())
    }
}

#[derive(Clone)]
struct RepeatDefSite<'ctx> {
    block: BasicBlockId,
    stmt_index: usize,
    rvalue: Rvalue<'ctx>,
}

impl<'ctx> MirPass<'ctx> for RepeatFieldForwarding {
    fn name(&self) -> &'static str {
        "RepeatFieldForwarding"
    }

    fn run(&mut self, _gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
        let num_locals = body.locals.len();
        let mut assignment_count = vec![0usize; num_locals];
        let mut use_counts = vec![0usize; num_locals];
        let mut address_taken = vec![false; num_locals];
        let mut defs: Vec<Option<RepeatDefSite<'ctx>>> = vec![None; num_locals];

        for (bb, block) in body.basic_blocks.iter_enumerated() {
            for (stmt_index, stmt) in block.statements.iter().enumerate() {
                match &stmt.kind {
                    StatementKind::Assign(dest, rv) => {
                        if dest.projection.is_empty() {
                            assignment_count[dest.local.index()] += 1;
                            if matches!(body.locals[dest.local].kind, LocalKind::Temp)
                                && matches!(
                                    body.locals[dest.local].ty.kind(),
                                    crate::sema::models::TyKind::Array { .. }
                                )
                                && matches!(rv, Rvalue::Repeat { operand, .. } if repeat_operand_is_zero(operand))
                            {
                                defs[dest.local.index()] = Some(RepeatDefSite {
                                    block: bb,
                                    stmt_index,
                                    rvalue: rv.clone(),
                                });
                            }
                        }

                        if let Rvalue::Ref { place, .. } = rv {
                            address_taken[place.local.index()] = true;
                        }
                        record_rvalue_use_counts(rv, &mut use_counts);
                    }
                    StatementKind::SetDiscriminant { place, .. } => {
                        if place.projection.is_empty() {
                            use_counts[place.local.index()] += 1;
                        }
                    }
                    StatementKind::GcSafepoint | StatementKind::Nop => {}
                }
            }

            if let Some(term) = &block.terminator {
                record_terminator_use_counts(&term.kind, &mut use_counts);
            }
        }

        let mut rewrites: Vec<(BasicBlockId, usize, Rvalue<'ctx>)> = Vec::new();
        let mut remove_defs: IndexVec<BasicBlockId, Vec<bool>> =
            IndexVec::from(vec![Vec::new(); body.basic_blocks.len()]);
        for (bb, block) in body.basic_blocks.iter_enumerated() {
            remove_defs[bb] = vec![false; block.statements.len()];
        }

        for (bb, block) in body.basic_blocks.iter_enumerated() {
            for (stmt_index, stmt) in block.statements.iter().enumerate() {
                let StatementKind::Assign(dest, Rvalue::Use(op)) = &stmt.kind else {
                    continue;
                };

                // Keep this rewrite narrowly scoped to aggregate field writes.
                if dest.projection.is_empty() {
                    continue;
                }

                let local = match op {
                    Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                        place.local
                    }
                    _ => continue,
                };

                if !matches!(body.locals[local].kind, LocalKind::Temp) {
                    continue;
                }
                if assignment_count[local.index()] != 1 || use_counts[local.index()] != 1 {
                    continue;
                }
                if address_taken[local.index()] {
                    continue;
                }

                let Some(def) = defs[local.index()].as_ref() else {
                    continue;
                };
                if def.block != bb || def.stmt_index >= stmt_index {
                    continue;
                }

                rewrites.push((bb, stmt_index, def.rvalue.clone()));
                remove_defs[def.block][def.stmt_index] = true;
            }
        }

        if rewrites.is_empty() {
            return Ok(());
        }

        for (bb, stmt_index, new_rvalue) in rewrites {
            if let Some(stmt) = body.basic_blocks[bb].statements.get_mut(stmt_index) {
                if let StatementKind::Assign(dest, _) = &stmt.kind {
                    stmt.kind = StatementKind::Assign(dest.clone(), new_rvalue);
                }
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

fn operand_kinds_compatible(def_kind: OperandKind, use_kind: OperandKind) -> bool {
    // `_tmp = copy x; ...; move _tmp` is semantically equivalent to `copy x` at the use.
    // We can fold this safely for single-use temps and eliminate one aggregate hop.
    def_kind == use_kind || matches!((def_kind, use_kind), (OperandKind::Copy, OperandKind::Move))
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

fn repeat_operand_is_zero(op: &Operand<'_>) -> bool {
    let Operand::Constant(c) = op else {
        return false;
    };
    matches!(
        c.value,
        crate::mir::ConstantKind::Integer(0)
            | crate::mir::ConstantKind::Bool(false)
            | crate::mir::ConstantKind::Unit
    )
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

fn record_operand_use_count(op: &Operand<'_>, use_counts: &mut [usize]) {
    match op {
        Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
            use_counts[place.local.index()] += 1;
        }
        Operand::Copy(_) | Operand::Move(_) | Operand::Constant(_) => {}
    }
}

fn record_rvalue_use_counts(rv: &Rvalue<'_>, use_counts: &mut [usize]) {
    match rv {
        Rvalue::Use(op)
        | Rvalue::UnaryOp { operand: op, .. }
        | Rvalue::Cast { operand: op, .. }
        | Rvalue::Repeat { operand: op, .. } => record_operand_use_count(op, use_counts),
        Rvalue::BinaryOp { lhs, rhs, .. } => {
            record_operand_use_count(lhs, use_counts);
            record_operand_use_count(rhs, use_counts);
        }
        Rvalue::Aggregate { fields, .. } => {
            for f in fields {
                record_operand_use_count(f, use_counts);
            }
        }
        Rvalue::Ref { place, .. } | Rvalue::Discriminant { place } => {
            if place.projection.is_empty() {
                use_counts[place.local.index()] += 1;
            }
        }
        Rvalue::Alloc { .. } => {}
    }
}

fn record_terminator_use_counts(term: &TerminatorKind<'_>, use_counts: &mut [usize]) {
    match term {
        TerminatorKind::Call { func, args, .. } => {
            record_operand_use_count(func, use_counts);
            for arg in args {
                record_operand_use_count(arg, use_counts);
            }
        }
        TerminatorKind::SwitchInt { discr, .. } => record_operand_use_count(discr, use_counts),
        TerminatorKind::Return
        | TerminatorKind::Goto { .. }
        | TerminatorKind::UnresolvedGoto
        | TerminatorKind::ResumeUnwind
        | TerminatorKind::Unreachable => {}
    }
}

fn terminator_successors(term: &TerminatorKind<'_>) -> Vec<BasicBlockId> {
    match term {
        TerminatorKind::Goto { target } => vec![*target],
        TerminatorKind::SwitchInt {
            targets, otherwise, ..
        } => {
            let mut out = Vec::with_capacity(targets.len() + 1);
            for (_, target) in targets {
                out.push(*target);
            }
            out.push(*otherwise);
            out
        }
        TerminatorKind::Call { target, unwind, .. } => {
            let mut out = vec![*target];
            if let crate::mir::CallUnwindAction::Cleanup(bb) = unwind {
                out.push(*bb);
            }
            out
        }
        TerminatorKind::Return
        | TerminatorKind::ResumeUnwind
        | TerminatorKind::Unreachable
        | TerminatorKind::UnresolvedGoto => Vec::new(),
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
    // Resolve transitive replacement chains (e.g., _t2 -> _t1, _t1 -> _x) so we
    // don't leave stale temps after removing multiple def-sites in one pass.
    // Bound iterations to avoid infinite loops in malformed cyclic maps.
    let mut steps = 0usize;
    while steps < replace_map.len() {
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

        let next = match replacement {
            Replacement::Copy(src) => Operand::Copy(Place::from_local(*src)),
            Replacement::Move(src) => Operand::Move(Place::from_local(*src)),
            Replacement::Constant(c) => Operand::Constant(c.clone()),
        };

        *op = next;
        steps += 1;
    }
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
