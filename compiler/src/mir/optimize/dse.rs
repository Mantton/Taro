use crate::{
    compile::context::Gcx,
    error::CompileResult,
    mir::{
        Body, Rvalue, StatementKind,
        analysis::liveness::{compute_block_liveness, transfer_statement, transfer_terminator},
    },
};

use super::MirPass;

pub struct DeadStoreElimination;

impl<'ctx> MirPass<'ctx> for DeadStoreElimination {
    fn name(&self) -> &'static str {
        "DeadStoreElimination"
    }

    fn run(&mut self, _gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
        let liveness = compute_block_liveness(body);
        let mut address_taken = vec![false; body.locals.len()];

        for block in body.basic_blocks.iter() {
            for stmt in &block.statements {
                if let StatementKind::Assign(_, Rvalue::Ref { place, .. }) = &stmt.kind {
                    address_taken[place.local.index()] = true;
                }
            }
        }

        for (bb, data) in body.basic_blocks.iter_mut_enumerated() {
            let mut live = liveness.live_out[bb].clone();
            if let Some(term) = &data.terminator {
                transfer_terminator(body.return_local, &term.kind, &mut live);
            }

            // Walk retained statements backwards; removed stores must not make
            // their operands live. Calls are terminators, so rvalues are pure.
            data.statements.reverse();
            data.statements.retain(|statement| {
                let destination = match &statement.kind {
                    StatementKind::Assign(destination, _) => Some(destination),
                    StatementKind::SetDiscriminant { place, .. } => Some(place),
                    _ => None,
                };
                if let Some(destination) = destination {
                    if destination.projection.is_empty()
                        && !live.contains(&destination.local)
                        && !address_taken[destination.local.index()]
                    {
                        return false;
                    }
                }
                if let StatementKind::SetDiscriminant { place, .. } = &statement.kind {
                    // Tag publication conservatively preserves the value's payload.
                    live.insert(place.local);
                } else {
                    transfer_statement(&statement.kind, &mut live);
                }
                true
            });
            data.statements.reverse();
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::DeadStoreElimination;
    use crate::mir::{
        Operand, Place, Rvalue, Statement, StatementKind, Terminator, TerminatorKind,
        optimize::MirPass,
        test_support::{minimal_body, push_temp, with_test_gcx},
    };

    #[test]
    fn keep_alive_use_preserves_its_same_block_definition() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let span = body.locals[body.return_local].span;
            let source = push_temp(&mut body, gcx.types.uint);
            let value = push_temp(&mut body, gcx.types.uint);
            body.basic_blocks[body.start_block].statements = vec![
                Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(value),
                        Rvalue::Use(Operand::Copy(Place::from_local(source))),
                    ),
                    span,
                },
                Statement {
                    kind: StatementKind::KeepAlive(Operand::Copy(Place::from_local(value))),
                    span,
                },
            ];
            body.basic_blocks[body.start_block].terminator = Some(Terminator {
                kind: TerminatorKind::Unreachable,
                span,
            });

            assert!(DeadStoreElimination.run(gcx, &mut body).is_ok());

            assert!(matches!(
                body.basic_blocks[body.start_block].statements[0].kind,
                StatementKind::Assign(ref destination, _) if destination.local == value
            ));
        });
    }
}
