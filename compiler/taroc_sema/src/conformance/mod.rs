use crate::GlobalContext;
use crate::ty::{SimpleType, UncheckedConformanceRecord};
use taroc_error::CompileResult;

pub fn run(package: &taroc_hir::Package, context: GlobalContext) -> CompileResult<()> {
    Actor::run(package, context)
}

struct Actor<'ctx> {
    context: GlobalContext<'ctx>,
}

impl<'ctx> Actor<'ctx> {
    fn new(context: GlobalContext<'ctx>) -> Actor<'ctx> {
        Actor { context }
    }

    fn run<'a>(_: &taroc_hir::Package, context: GlobalContext<'ctx>) -> CompileResult<()> {
        let actor = Actor::new(context);
        actor.resolve();
        context.diagnostics.report()
    }
}

impl<'ctx> Actor<'ctx> {
    fn resolve(&self) {
        let gcx = self.context;
        let session = gcx.session().index();
        let pending = gcx.with_type_database(session, |db| db.unchecked_conformances.clone());

        for (ty, conformances) in pending {
            self.resolve_for_type(ty, conformances);
        }
    }

    fn resolve_for_type(
        &self,
        ty: SimpleType,
        conformances: Vec<UncheckedConformanceRecord<'ctx>>,
    ) {
        let gcx = self.context;
        for conformance in conformances.into_iter() {
            conformance.extension;
            let predicates = gcx.canon_predicates_of(conformance.extension);

            // gcx.diagnostics
            //     .warn("Checking Conforamnce".into(), conformance.location);
        }
    }
}
