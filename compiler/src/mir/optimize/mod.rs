use crate::compile::context::Gcx;
use crate::error::CompileResult;
use crate::mir::{Body, MirPhase};

pub mod alloc_escape;
pub mod async_transform;
pub mod coalesce;
pub mod const_prop;
pub mod devirtualize;
pub mod dse;
pub mod escape;
pub mod inline;
pub mod passes;
pub mod propagate;
pub mod simplify;
pub mod validate;

pub trait MirPass<'ctx> {
    fn name(&self) -> &'static str;
    fn run(&mut self, gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()>;
    fn phase_change(&self) -> Option<MirPhase> {
        None
    }
}

pub fn run_passes<'ctx>(
    gcx: Gcx<'ctx>,
    body: &mut Body<'ctx>,
    passes: &mut [Box<dyn MirPass<'ctx>>],
) -> CompileResult<()> {
    for pass in passes {
        #[cfg(any(test, debug_assertions))]
        let pass_name = pass.name();
        pass.run(gcx, body)?;
        if let Some(next) = pass.phase_change() {
            body.phase = next;
        }
        #[cfg(any(test, debug_assertions))]
        validate::validate_body_structure(gcx, body, pass_name)?;
    }
    Ok(())
}

/// Local passes: run per-function during MIR building.
/// These passes don't require other function bodies to be available.
/// Includes: prune unreachable and simplify CFG.
pub fn run_local_passes<'ctx>(gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
    let validate_ownership = matches!(body.phase, MirPhase::Built);
    let mut passes: Vec<Box<dyn MirPass>> = vec![
        Box::new(validate::ValidateBodyInvariants),
        Box::new(passes::PruneUnreachable),
        Box::new(passes::SimplifyCfg),
    ];
    if validate_ownership {
        passes.push(Box::new(validate::ValidateMutability));
        passes.push(Box::new(validate::ValidateMoves));
        passes.push(Box::new(validate::ValidateBorrows));
    }
    run_passes(gcx, body, &mut passes)?;
    body.phase = MirPhase::CfgClean;
    Ok(())
}

/// Lower one source-form async body into its canonical constructor and queue
/// its synthesized poll/drop bodies. This package-wide phase must complete for
/// every function before canonical MIR is published, otherwise callers would
/// see a different callee representation depending on build order or whether
/// the dependency came from metadata.
pub fn lower_async_for_canonical_mir<'ctx>(
    gcx: Gcx<'ctx>,
    body: &mut Body<'ctx>,
) -> CompileResult<()> {
    if !body.is_async {
        return Ok(());
    }

    let mut passes: Vec<Box<dyn MirPass>> = vec![
        Box::new(escape::EscapeAnalysis),
        Box::new(escape::ApplyEscapeAnalysis),
        Box::new(async_transform::AsyncTransform),
    ];
    run_passes(gcx, body, &mut passes)?;
    // AsyncTransform builds a fresh constructor CFG. Canonical MIR always has
    // the same locally-cleaned boundary for ordinary and synthesized bodies.
    run_local_passes(gcx, body)
}

/// Shared global passes: run once per definition after all MIR bodies are built.
///
/// These passes may require access to other function bodies (e.g., inlining),
/// but must not make decisions that can differ between monomorphized instances.
/// Escape placement and safepoint insertion therefore run later on an
/// instance-local clone via [`run_instance_passes`].
///
/// Note: escape::compute_escape_summaries must be called before these passes
/// to enable interprocedural escape analysis.
pub fn run_global_passes<'ctx>(gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
    let mut passes: Vec<Box<dyn MirPass>> = vec![
        Box::new(devirtualize::DevirtualizeStaticCalls),
        Box::new(inline::Inline::default()),
        Box::new(passes::LowerKeepAlive),
        Box::new(passes::LowerExistentialBoxes),
        Box::new(const_prop::ConstantPropagation),
        Box::new(passes::SimplifyCfg), // Clean up after inlining (merges blocks, removes unreachable)
        Box::new(passes::LowerAggregates),
        Box::new(coalesce::CallDestinationCoalescing),
        // Note: LowerAggregates only expands statements, doesn't change CFG structure
        // DeadLocalElimination runs after LowerAggregates to also clean up temps it creates
        Box::new(propagate::CopyPropagation),
        Box::new(coalesce::TempCoalescing),
        Box::new(coalesce::RepeatFieldForwarding),
    ];
    run_passes(gcx, body, &mut passes)?;
    Ok(())
}

/// Finalize one concrete codegen instance.
///
/// The input is a clone of shared, globally optimized MIR. Keeping every
/// placement and safepoint mutation on this clone lets later analyses consult
/// concrete generic arguments without contaminating another instantiation of
/// the same source definition.
pub fn run_instance_passes<'ctx>(gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
    let mut passes: Vec<Box<dyn MirPass>> = vec![
        Box::new(alloc_escape::AllocEscapeAnalysis),
        Box::new(alloc_escape::StackPromoteAllocations),
        Box::new(dse::DeadStoreElimination),
        Box::new(passes::DeadLocalElimination),
        // Interprocedural escape analysis (uses precomputed summaries)
        Box::new(escape::EscapeAnalysis),
        Box::new(escape::ApplyEscapeAnalysis),
        Box::new(passes::InsertSafepoints),
        Box::new(passes::MergeSafepoints), // Clean up redundant consecutive safepoints
    ];
    run_passes(gcx, body, &mut passes)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{MirPass, run_passes};
    use crate::{
        compile::context::Gcx,
        error::CompileResult,
        mir::{
            BasicBlockData, BasicBlockId, Operand, Place, Rvalue, Statement, StatementKind,
            Terminator, TerminatorKind,
            optimize::passes::{DeadLocalElimination, PruneUnreachable},
            test_support::{minimal_body, pretty_body, push_temp, with_test_gcx},
        },
        sema::tycheck::test_support::analyze_script_mir_diagnostics,
    };
    struct CorruptEdge;

    impl<'ctx> MirPass<'ctx> for CorruptEdge {
        fn name(&self) -> &'static str {
            "CorruptEdge"
        }

        fn run(&mut self, _gcx: Gcx<'ctx>, body: &mut crate::mir::Body<'ctx>) -> CompileResult<()> {
            body.basic_blocks[body.start_block].terminator = Some(Terminator {
                kind: TerminatorKind::Goto {
                    target: BasicBlockId::from_raw(body.basic_blocks.len() as u32),
                },
                span: body.locals[body.return_local].span,
            });
            Ok(())
        }
    }

    #[test]
    fn pass_runner_reports_the_pass_that_broke_structure() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let result = run_passes(gcx, &mut body, &mut [Box::new(CorruptEdge)]);

            assert!(result.is_err());
            let diagnostics = gcx.dcx().take_recorded_diagnostics();
            assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
            assert!(
                diagnostics[0]
                    .message
                    .contains("MIR structure invalid after `CorruptEdge`")
            );
        });
    }

    #[test]
    fn prune_unreachable_remaps_surviving_edges() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let span = body.locals[body.return_local].span;
            let unreachable = body.basic_blocks.push(BasicBlockData {
                note: Some("unreachable".into()),
                statements: Vec::new(),
                terminator: Some(Terminator {
                    kind: TerminatorKind::Return,
                    span,
                }),
            });
            let destination = body.basic_blocks.push(BasicBlockData {
                note: Some("destination".into()),
                statements: Vec::new(),
                terminator: Some(Terminator {
                    kind: TerminatorKind::Return,
                    span,
                }),
            });
            body.basic_blocks[body.start_block].terminator = Some(Terminator {
                kind: TerminatorKind::Goto {
                    target: destination,
                },
                span,
            });
            let before = pretty_body(gcx, &body);

            assert!(run_passes(gcx, &mut body, &mut [Box::new(PruneUnreachable)]).is_ok());

            let after = pretty_body(gcx, &body);
            assert!(before.contains("goto -> bb2"), "{before}");
            assert!(after.contains("goto -> bb1"), "{after}");
            assert!(!after.contains("bb2"), "{after}");
            assert_eq!(unreachable.index(), 1);
            assert_eq!(body.basic_blocks.len(), 2);
            assert!(matches!(
                body.basic_blocks[body.start_block]
                    .terminator
                    .as_ref()
                    .map(|terminator| &terminator.kind),
                Some(TerminatorKind::Goto { target }) if target.index() == 1
            ));
        });
    }

    #[test]
    fn dead_local_elimination_remaps_places_and_escape_flags() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let _dead = push_temp(&mut body, gcx.types.int32);
            let used = push_temp(&mut body, gcx.types.int32);
            let span = body.locals[body.return_local].span;
            body.basic_blocks[body.start_block]
                .statements
                .push(Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(body.return_local),
                        Rvalue::Use(Operand::copy(Place::from_local(used))),
                    ),
                    span,
                });
            let before = pretty_body(gcx, &body);

            assert!(run_passes(gcx, &mut body, &mut [Box::new(DeadLocalElimination)]).is_ok());

            let after = pretty_body(gcx, &body);
            assert!(before.contains("%2"), "{before}");
            assert!(!after.contains("%2"), "{after}");
            assert!(after.contains("%0 = %1"), "{after}");
            assert_eq!(body.locals.len(), 2);
            assert_eq!(body.escape_locals.len(), body.locals.len());
            let StatementKind::Assign(_, Rvalue::Use(Operand::Copy(source))) =
                &body.basic_blocks[body.start_block].statements[0].kind
            else {
                panic!("expected remapped copy assignment");
            };
            assert_eq!(source.local.index(), 1);
        });
    }

    #[test]
    fn real_mir_pipeline_preserves_structure_across_all_passes() {
        let diagnostics = analyze_script_mir_diagnostics(
            r#"
func select(_ condition: bool, _ left: int32, _ right: int32) -> int32 {
    if condition { left } else { right }
}

func caller(_ value: int32) -> int32 {
    select(value > 0, value + 1, value - 1)
}
"#,
        );

        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }
}
