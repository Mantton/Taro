use crate::compile::context::Gcx;
use crate::error::CompileResult;
use crate::mir::{Body, MirPhase};

pub mod inline;
pub mod passes;
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
        pass.run(gcx, body)?;
        if let Some(next) = pass.phase_change() {
            body.phase = next;
        }
    }
    Ok(())
}

/// Local passes: run per-function during MIR building.
/// These passes don't require other function bodies to be available.
/// Includes: prune unreachable, simplify CFG, validate mutability/moves.
pub fn run_local_passes<'ctx>(gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
    let mut passes: Vec<Box<dyn MirPass>> = vec![
        Box::new(passes::PruneUnreachable),
        Box::new(passes::SimplifyCfg),
        // Validation passes - must run before inlining to catch errors in original code
        Box::new(validate::ValidateMutability),
        Box::new(validate::ValidateMoves),
    ];
    run_passes(gcx, body, &mut passes)?;
    body.phase = MirPhase::CfgClean;
    Ok(())
}

/// Global passes: run after all MIR bodies are built.
/// These passes may require access to other function bodies (e.g., inlining).
/// Includes: inlining, lower aggregates, escape analysis, safepoints.
pub fn run_global_passes<'ctx>(gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
    let mut passes: Vec<Box<dyn MirPass>> = vec![
        Box::new(inline::Inline::default()),
        Box::new(passes::SimplifyCfg), // Clean up after inlining (merges blocks, removes unreachable)
        Box::new(passes::LowerAggregates),
        // Note: LowerAggregates only expands statements, doesn't change CFG structure
        // DeadLocalElimination runs after LowerAggregates to also clean up temps it creates
        Box::new(passes::DeadLocalElimination),
        Box::new(passes::EscapeAnalysis),
        Box::new(passes::ApplyEscapeAnalysis),
        Box::new(passes::InsertSafepoints),
        Box::new(passes::MergeSafepoints), // Clean up redundant consecutive safepoints
    ];
    run_passes(gcx, body, &mut passes)?;
    Ok(())
}
