use crate::{
    compile::context::GlobalContext, hir::DefinitionID, sema::tycheck::solve::ConstraintSystem,
    span::Span,
};

pub fn check_conformance_implied_bounds<'ctx>(
    context: GlobalContext<'ctx>,
    def_id: DefinitionID,
    _span: Span,
    cs: &mut ConstraintSystem<'ctx>,
) {
    // Extension identity already limits this to conformances declared here.
    // Comparing the target to Nominal(def_id) would skip every conform block:
    // its declaration id differs from the type it implements the interface for.
    for record in context
        .conformance_records_for_extension(context.package_index(), def_id)
        .into_iter()
    {
        let interface_id = record.interface.id;

        // 1. Check Interface Generic Arguments WF
        cs.add_constraints_for_def(
            interface_id,
            Some(record.interface.arguments),
            record.location,
        );

        // 2. Check Associated Type Bounds
        let requirements = context.with_type_database(interface_id.package(), |db| {
            db.interface_requirements.get(&interface_id).cloned()
        });

        if let Some(reqs) = requirements
            && !reqs.types.is_empty()
        {
            let witness =
                crate::sema::tycheck::resolve_conformance_witness(context, record.interface);

            if let Some(_) = witness {
                // InterfaceReference already includes concrete Self at slot
                // zero. Prepending it again shifts every generic argument and
                // can validate the wrong associated-type requirement.
                let full_args = record.interface.arguments;

                for assoc_type in &reqs.types {
                    // Check that the witness satisfying this associated type meets the bounds defined on the associated type.
                    cs.add_constraints_for_def(assoc_type.id, Some(full_args), record.location);
                }
            }
        }
    }
}
