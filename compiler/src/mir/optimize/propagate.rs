use crate::mir::analysis::dominators::{Dominators, compute_dominators};
use crate::{
    compile::context::Gcx,
    error::CompileResult,
    mir::{
        BasicBlockId, Body, LocalId, LocalKind, Operand, Place, Rvalue, StatementKind,
        TerminatorKind,
    },
};

use super::MirPass;

pub struct CopyPropagation;

#[derive(Clone, Copy)]
struct DefSite {
    block: BasicBlockId,
    stmt_index: usize,
}

#[derive(Clone, Copy)]
struct UseSite {
    block: BasicBlockId,
    stmt_index: usize,
}

impl<'ctx> MirPass<'ctx> for CopyPropagation {
    fn name(&self) -> &'static str {
        "CopyPropagation"
    }

    fn run(&mut self, _gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
        let num_locals = body.locals.len();
        let dominators = compute_dominators(body);

        // 1. Identify copy candidates
        let mut assignment_count = vec![0usize; num_locals];
        let mut copy_source: Vec<Option<LocalId>> = vec![None; num_locals];
        let mut address_taken = vec![false; num_locals];
        let mut complex_dest = vec![false; num_locals];
        let mut def_sites: Vec<Option<DefSite>> = vec![None; num_locals];
        let mut use_sites: Vec<Vec<UseSite>> = vec![Vec::new(); num_locals];
        let mut projection_use = vec![false; num_locals];

        for (bb, block) in body.basic_blocks.iter_enumerated() {
            for (stmt_index, stmt) in block.statements.iter().enumerate() {
                match &stmt.kind {
                    StatementKind::Assign(dest, rv) => {
                        if dest.projection.is_empty() {
                            assignment_count[dest.local.index()] += 1;
                            if def_sites[dest.local.index()].is_none() {
                                def_sites[dest.local.index()] = Some(DefSite {
                                    block: bb,
                                    stmt_index,
                                });
                            }
                            if let Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) = rv {
                                if src.projection.is_empty() {
                                    copy_source[dest.local.index()] = Some(src.local);
                                }
                            }
                        } else {
                            complex_dest[dest.local.index()] = true;
                        }

                        if let Rvalue::Ref { place, .. } = rv {
                            if place.projection.is_empty() {
                                address_taken[place.local.index()] = true;
                            }
                        }
                        record_rvalue_uses(rv, bb, stmt_index, &mut use_sites, &mut projection_use);
                    }
                    StatementKind::SetDiscriminant { place, .. } => {
                        if place.projection.is_empty() {
                            complex_dest[place.local.index()] = true;
                        }
                        if !place.projection.is_empty() {
                            projection_use[place.local.index()] = true;
                            record_place_use(place, bb, stmt_index, &mut use_sites);
                        }
                    }
                    StatementKind::KeepAlive(operand) => {
                        record_operand_use(operand, bb, stmt_index, &mut use_sites);
                    }
                    _ => {}
                }
            }
            if let Some(term) = &block.terminator {
                let term_index = block.statements.len();
                record_terminator_uses(&term.kind, bb, term_index, &mut use_sites);
                if let TerminatorKind::Call { destination, .. } = &term.kind {
                    if destination.projection.is_empty() {
                        assignment_count[destination.local.index()] += 1;
                        complex_dest[destination.local.index()] = true; // Call result is not a simple copy
                    }
                }
            }
        }

        // 2. Build propagation map
        let mut propagate: Vec<Option<LocalId>> = vec![None; num_locals];
        for (local_idx, local_decl) in body.locals.iter_enumerated() {
            if matches!(local_decl.kind, LocalKind::Param | LocalKind::Return) {
                continue;
            }
            if assignment_count[local_idx.index()] == 1
                && !address_taken[local_idx.index()]
                && !complex_dest[local_idx.index()]
                && !projection_use[local_idx.index()]
            {
                if let Some(src) = copy_source[local_idx.index()] {
                    let Some(def_site) = def_sites[local_idx.index()] else {
                        continue;
                    };
                    if !def_dominates_uses(def_site, &use_sites[local_idx.index()], &dominators) {
                        continue;
                    }
                    if !source_is_stable(
                        src,
                        body,
                        &assignment_count,
                        &address_taken,
                        &complex_dest,
                    ) {
                        continue;
                    }
                    if let Some(src_def) = def_sites[src.index()] {
                        if !dominators.dominates(src_def.block, def_site.block) {
                            continue;
                        }
                    }
                    propagate[local_idx.index()] = Some(src);
                }
            }
        }

        // 3. Resolve transitive
        let mut final_propagate: Vec<Option<LocalId>> = vec![None; num_locals];
        for i in 0..num_locals {
            if propagate[i].is_some() {
                let mut current = LocalId::from_raw(i as u32);
                let mut path = Vec::new(); // Loop detection
                while let Some(src) = propagate[current.index()] {
                    if path.contains(&current) {
                        break;
                    } // Cycle
                    path.push(current);
                    current = src;
                }
                if current.index() != i {
                    final_propagate[i] = Some(current);
                }
            }
        }

        // 4. Apply propagation to uses, preserving operand and projection metadata.
        let remap_place = |place: &mut Place<'ctx>| {
            place.local = final_propagate[place.local.index()].unwrap_or(place.local);
        };
        let remap_operand = |operand: &mut Operand<'ctx>| {
            if let Some(place) = operand.place_mut() {
                remap_place(place);
            }
        };

        for block in body.basic_blocks.iter_mut() {
            for stmt in block.statements.iter_mut() {
                match &mut stmt.kind {
                    StatementKind::Assign(dest, rv) => {
                        // A projected destination reads its base; a plain local is a definition.
                        if !dest.projection.is_empty() {
                            remap_place(dest);
                        }
                        rv.for_each_place_mut(remap_place);
                    }
                    StatementKind::SetDiscriminant { .. } => {}
                    StatementKind::KeepAlive(operand) => {
                        remap_operand(operand);
                    }
                    _ => {}
                }
            }
            if let Some(term) = block.terminator.as_mut() {
                match &mut term.kind {
                    TerminatorKind::Call {
                        func,
                        args,
                        destination,
                        ..
                    } => {
                        remap_operand(func);
                        args.iter_mut().for_each(remap_operand);
                        if !destination.projection.is_empty() {
                            remap_place(destination);
                        }
                    }
                    TerminatorKind::SwitchInt { discr, .. } => remap_operand(discr),
                    TerminatorKind::Yield {
                        value, resume_arg, ..
                    } => {
                        remap_operand(value);
                        if !resume_arg.projection.is_empty() {
                            remap_place(resume_arg);
                        }
                    }
                    _ => {}
                }
            }
        }

        Ok(())
    }
}

fn source_is_stable(
    src: LocalId,
    body: &Body<'_>,
    assignment_count: &[usize],
    address_taken: &[bool],
    complex_dest: &[bool],
) -> bool {
    if address_taken[src.index()] || complex_dest[src.index()] {
        return false;
    }
    match body.locals[src].kind {
        LocalKind::Param => assignment_count[src.index()] == 0,
        LocalKind::Temp => assignment_count[src.index()] == 1,
        LocalKind::User => assignment_count[src.index()] == 1,
        LocalKind::Return => false,
    }
}

fn def_dominates_uses(def: DefSite, uses: &[UseSite], dominators: &Dominators) -> bool {
    uses.iter().all(|use_site| {
        if def.block == use_site.block {
            def.stmt_index < use_site.stmt_index
        } else {
            dominators.dominates(def.block, use_site.block)
        }
    })
}

fn record_place_use(
    place: &Place<'_>,
    block: BasicBlockId,
    stmt_index: usize,
    uses: &mut [Vec<UseSite>],
) {
    uses[place.local.index()].push(UseSite { block, stmt_index });
}

fn record_operand_use(
    op: &Operand<'_>,
    block: BasicBlockId,
    stmt_index: usize,
    uses: &mut [Vec<UseSite>],
) {
    match op {
        Operand::Copy(place) | Operand::Move(place) | Operand::CopyWith(place, _) => {
            record_place_use(place, block, stmt_index, uses);
        }
        Operand::Constant(_) => {}
    }
}

fn record_rvalue_uses(
    rv: &Rvalue<'_>,
    block: BasicBlockId,
    stmt_index: usize,
    uses: &mut [Vec<UseSite>],
    projection_use: &mut [bool],
) {
    rv.for_each_place(|place| record_place_use(place, block, stmt_index, uses));
    if let Rvalue::Ref { place, .. } | Rvalue::Discriminant { place } = rv {
        if !place.projection.is_empty() {
            projection_use[place.local.index()] = true;
        }
    }
}

fn record_terminator_uses(
    term: &TerminatorKind<'_>,
    block: BasicBlockId,
    stmt_index: usize,
    uses: &mut [Vec<UseSite>],
) {
    match term {
        TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } => {
            record_operand_use(func, block, stmt_index, uses);
            for arg in args {
                record_operand_use(arg, block, stmt_index, uses);
            }
            if !destination.projection.is_empty() {
                record_place_use(destination, block, stmt_index, uses);
            }
        }
        TerminatorKind::SwitchInt { discr, .. } => {
            record_operand_use(discr, block, stmt_index, uses);
        }
        TerminatorKind::Yield {
            value, resume_arg, ..
        } => {
            record_operand_use(value, block, stmt_index, uses);
            if !resume_arg.projection.is_empty() {
                record_place_use(resume_arg, block, stmt_index, uses);
            }
        }
        _ => {}
    }
}
