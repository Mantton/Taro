use crate::compile::context::Gcx;
use crate::mir::{Body, MirPhase};

pub mod passes;
pub mod simplify;

pub trait MirPass<'ctx> {
    fn name(&self) -> &'static str;
    fn run(&mut self, gcx: Gcx<'ctx>, body: &mut Body<'ctx>);
    fn phase_change(&self) -> Option<MirPhase> {
        None
    }
}

pub fn run_passes<'ctx>(
    gcx: Gcx<'ctx>,
    body: &mut Body<'ctx>,
    passes: &mut [Box<dyn MirPass<'ctx>>],
) {
    for pass in passes {
        pass.run(gcx, body);
        if let Some(next) = pass.phase_change() {
            body.phase = next;
        }
    }
}

/// Default pipeline: prune unreachable, simplify CFG, lower aggregates, simplify again.
pub fn run_default_passes<'ctx>(gcx: Gcx<'ctx>, body: &mut Body<'ctx>) {
    let mut passes: Vec<Box<dyn MirPass>> = vec![
        Box::new(passes::PruneUnreachable),
        Box::new(passes::SimplifyCfg),
        Box::new(passes::LowerAggregates),
        Box::new(passes::SimplifyCfg),
        Box::new(passes::EscapeAnalysis),
        Box::new(passes::ApplyEscapeAnalysis),
        Box::new(passes::InsertSafepoints),
    ];
    let (first, rest) = passes.split_at_mut(2);
    run_passes(gcx, body, first);
    body.phase = MirPhase::CfgClean;
    run_passes(gcx, body, rest);
}
