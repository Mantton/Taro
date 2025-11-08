use crate::{
    ast,
    error::CompileResult,
    sema::resolve::{UsageID, resolver::Resolver},
};

pub fn resolve_usages(resolver: &mut Resolver) -> CompileResult<()> {
    let mut actor = Actor { resolver };
    actor.run()
}

struct Actor<'resolver> {
    resolver: &'resolver mut Resolver,
}

impl<'r> Actor<'r> {
    fn run(mut self) -> CompileResult<()> {
        let mut changed = false;
        let mut finalize = false;

        while changed {
            let start = self.unresolved_count();
            self.resolve(false);
            let end = self.unresolved_count();
            changed |= start != end;
        }

        if self.unresolved_count() != 0 {
            self.resolve(true);
        }

        Ok(())
    }

    fn unresolved_count(&self) -> usize {
        self.resolver.unresolved_exports.len() + self.resolver.unresolved_imports.len()
    }
}

impl<'r> Actor<'r> {
    fn resolve(&mut self, finalize: bool) {
        self.resolve_exports(finalize);
        self.resolve_imports(finalize);
    }

    fn resolve_imports(&mut self, finalize: bool) {
        let imports = std::mem::take(&mut self.resolver.unresolved_imports);
        for import in imports {
            if !self.resolve_usage(import, finalize) {
                self.resolver.unresolved_imports.push(import);
            }
        }
    }
    fn resolve_exports(&mut self, finalize: bool) {
        let exports = std::mem::take(&mut self.resolver.unresolved_exports);
        for export in exports {
            if !self.resolve_usage(export, finalize) {
                self.resolver.unresolved_exports.push(export);
            }
        }
    }
}

impl<'r> Actor<'r> {
    fn resolve_usage(&mut self, usage_id: UsageID, finalize: bool) -> bool {
        let usage = self.resolver.usages.get(usage_id).unwrap();
        let module_result = self.resolver.resolve_module_path(&usage.module_path);
        false
    }
}
