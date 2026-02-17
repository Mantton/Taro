use crate::{
    compile::context::GlobalContext,
    hir::DefinitionID,
    sema::{models::GenericArgument, resolve::models::TypeHead, tycheck::solve::ConstraintSystem},
    span::Span,
};

pub fn check_conformance_implied_bounds<'ctx>(
    context: GlobalContext<'ctx>,
    def_id: DefinitionID,
    _span: Span,
    cs: &mut ConstraintSystem<'ctx>,
) {
    let type_head = TypeHead::Nominal(def_id);
    let conformances = context.with_session_type_database(|db| {
        db.conformances.get(&type_head).cloned().unwrap_or_default()
    });

    // We only check conformances that are declared on THIS definition (struct, enum, impl block)
    // to avoid checking conformances defined elsewhere (e.g. in another package or impl block).
    let local_conformances = conformances.iter().filter(|rec| rec.extension == def_id);

    for record in local_conformances {
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

        if let Some(reqs) = requirements {
            let witness = context.find_in_databases(|db| {
                db.conformance_witnesses
                    .get(&(type_head, record.interface))
                    .cloned()
            });

            if let Some(_) = witness {
                // Construct the full argument list for the associated type: [Self, ...InterfaceArgs]
                let self_ty = match context.definition_kind(def_id) {
                    crate::sema::resolve::models::DefinitionKind::Impl => context
                        .get_impl_self_ty(def_id)
                        .unwrap_or_else(|| crate::sema::models::Ty::error(context)),
                    _ => context.get_type(def_id),
                };

                let mut full_args_vec = vec![GenericArgument::Type(self_ty)];
                full_args_vec.extend(record.interface.arguments.iter().cloned());
                let full_args = context.store.interners.intern_generic_args(full_args_vec);

                for assoc_type in &reqs.types {
                    // Check that the witness satisfying this associated type meets the bounds defined on the associated type.
                    cs.add_constraints_for_def(assoc_type.id, Some(full_args), record.location);
                }
            }
        }
    }
}
