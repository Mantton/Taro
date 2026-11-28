use crate::compile::context::Gcx;
use crate::error::CompileResult;
use crate::mir::{Body, MirPhase};

pub mod async_transform;
pub mod generator_transform;
pub mod coalesce;
pub mod const_prop;
pub mod dse;
pub mod escape_graph;
pub mod gc_safepoints;
#[cfg(feature = "llvm")]
pub mod gc_storage;
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
        let started = gcx.config.debug.timings.then(std::time::Instant::now);
        #[cfg(any(test, debug_assertions))]
        let pass_name = pass.name();
        pass.run(gcx, body)?;
        if let Some(started) = started
            && started.elapsed().as_millis() >= 100
        {
            eprintln!(
                "[mir timing] {} {}: {:?} ({} locals, {} blocks)",
                gcx.symbol_text(gcx.definition_symbol_or_fallback(body.owner)),
                pass.name(),
                started.elapsed(),
                body.locals.len(),
                body.basic_blocks.len()
            );
        }
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
    let built = matches!(body.phase, MirPhase::Built);
    // Normalize value reads before structural and initialization checks.
    crate::mir::gc_lowering::lower_for_gc(body);
    let mut passes: Vec<Box<dyn MirPass>> = vec![
        Box::new(validate::ValidateBodyInvariants),
        Box::new(passes::PruneUnreachable),
        Box::new(passes::SimplifyCfg),
    ];
    if built {
        passes.push(Box::new(validate::ValidateMutability));
        passes.push(Box::new(validate::ValidateInitialization));
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
    if body.generator_element_ty.is_some() {
        {
            escape_graph::apply_async_bridge(gcx, body)?;
        }
        let mut passes: Vec<Box<dyn MirPass>> =
            vec![Box::new(generator_transform::GeneratorTransform)];
        run_passes(gcx, body, &mut passes)?;
        return run_local_passes(gcx, body);
    }

    if !body.is_async {
        return Ok(());
    }

    // Heapify escaping locals before they become coroutine frame fields;
    // afterwards a reference would name one frame slot reused by every
    // iteration rather than a fresh allocation per storage lifetime.
    {
        escape_graph::apply_async_bridge(gcx, body)?;
    }
    let mut passes: Vec<Box<dyn MirPass>> = vec![Box::new(async_transform::AsyncTransform)];
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
pub fn run_global_passes<'ctx>(gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
    inline::Inline::default().run(gcx, body)?;
    run_post_inline_passes(gcx, body)
}

/// Canonical callees may introduce aggregates and temporary scaffolding even
/// when the caller was already lowered. Use the same cleanup at both boundaries.
fn run_post_inline_passes<'ctx>(gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
    let mut passes: Vec<Box<dyn MirPass>> = vec![
        Box::new(const_prop::ConstantPropagation),
        Box::new(passes::SimplifyCfg), // Clean up after inlining (merges blocks, removes unreachable)
        Box::new(passes::LowerAggregates),
        Box::new(coalesce::CallDestinationCoalescing),
        // Note: LowerAggregates only expands statements, doesn't change CFG structure
        // DeadLocalElimination runs after LowerAggregates to also clean up temps it creates
        Box::new(propagate::CopyPropagation),
        Box::new(coalesce::TempCoalescing),
        Box::new(coalesce::RepeatFieldForwarding),
        // Instance analysis must see semantic uses, not aggregate-lowering
        // scaffolding that a later cleanup would discard. Dead value reads
        // must not obscure the real return or capture use being analyzed.
        Box::new(dse::DeadStoreElimination),
        Box::new(passes::DeadLocalElimination),
    ];
    run_passes(gcx, body, &mut passes)?;
    Ok(())
}

/// Finalize one concrete codegen instance.
///
/// The input is a clone of shared, globally optimized MIR. Keeping every
/// placement and safepoint mutation on this clone lets later analyses consult
/// concrete generic arguments without contaminating another instantiation of
/// the same source definition. Retry inlining with those arguments before
/// escape summaries and safepoints are computed.
pub fn run_instance_passes<'ctx>(
    gcx: Gcx<'ctx>,
    body: &mut Body<'ctx>,
    args: crate::sema::models::GenericArguments<'ctx>,
) -> CompileResult<()> {
    if inline::inline_instance(gcx, body, args)? {
        return run_post_inline_passes(gcx, body);
    }
    let mut passes: Vec<Box<dyn MirPass>> = vec![
        Box::new(dse::DeadStoreElimination),
        Box::new(passes::DeadLocalElimination),
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
        test_support::analyze_script_mir_diagnostics,
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
            let StatementKind::Assign(_, Rvalue::Use(Operand::Copy(source))) =
                &body.basic_blocks[body.start_block].statements[0].kind
            else {
                panic!("expected remapped copy assignment");
            };
            assert_eq!(source.local.index(), 1);
        });
    }

    #[test]
    fn enum_place_matches_only_snapshot_storage_when_guards_need_it() {
        let source = r#"
enum Choice { case number(int64); case pair(int64, int64) }
func change(_ value: &Choice) -> bool { *value = .pair(90, 91); false }
func plain(_ value: &Choice) -> int64 {
    match value {
        case .number(n) => n
        case .pair(a, b) => a + b
    }
}
func guarded(_ value: &Choice) -> int64 {
    match value {
        case .number(n) if change(value) => n
        case .number(n) => n
        case .pair(a, _) => a
    }
}
func main() {}
"#;
        crate::test_support::analyze_script_built_mir(source, |bodies, gcx| {
            for body in bodies {
                let name = gcx.symbol_text(gcx.definition_ident(body.owner).symbol);
                if !matches!(name.as_str(), "plain" | "guarded") {
                    continue;
                }
                let enum_snapshots = body
                    .locals
                    .iter()
                    .filter(|local| {
                        matches!(local.ty.kind(), crate::sema::models::TyKind::Adt(def, _)
                        if gcx.symbol_text(gcx.definition_ident(def.id).symbol).as_str() == "Choice")
                    })
                    .count();
                assert_eq!(
                    enum_snapshots == 0,
                    name.as_str() == "plain",
                    "{name}: {enum_snapshots} whole-enum temporaries"
                );
            }
        });
    }

    #[test]
    fn guarded_match_initialization_uses_the_exhaustiveness_report() {
        let diagnostics = analyze_script_mir_diagnostics(
            r#"
func select(_ flag: bool, _ enabled: bool) -> int32 {
    var result: int32
    match flag {
        case true if enabled => { result = 1 }
        case true => { result = 2 }
        case false => { result = 3 }
    }
    result
}
"#,
        );
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
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
