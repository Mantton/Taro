use crate::sema::models::{CandidateSource, GenericArguments, InterfaceGoal};

#[derive(Debug, Clone)]
pub(super) struct ConfirmedCandidate<'ctx> {
    pub source: CandidateSource,
    pub extension_id: Option<crate::hir::DefinitionID>,
    pub record_id: Option<crate::sema::models::ConformanceRecordId>,
    pub subst: GenericArguments<'ctx>,
    pub obligations: Vec<InterfaceGoal<'ctx>>,
}
