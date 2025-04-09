use crate::{
    alias::TypeAliasResolver, extend::ExtensionBinder, resolver::Resolver, usage::UsageResolver,
};
use taroc_error::CompileResult;

impl Resolver<'_> {
    pub fn unresolved_usage_count(&self) -> usize {
        self.unresolved_exports.len() + self.unresolved_imports.len()
    }
}

pub struct IterativeResolver<'res, 'ctx> {
    pub resolver: &'res mut Resolver<'ctx>,
}

impl<'res, 'ctx> IterativeResolver<'res, 'ctx> {
    pub fn run(resolver: &'res mut Resolver<'ctx>) -> CompileResult<()> {
        let context = resolver.context;
        let mut actor = IterativeResolver { resolver };
        actor.fixed_point_pass();
        context.diagnostics.report()
    }

    fn fixed_point_pass(&mut self) {
        let mut changed = true;
        while changed {
            changed = false;
            changed |= self.process_imports();
            changed |= self.process_alias();
            changed |= self.process_extensions();
        }

        let unresolved_imports = self.resolver.unresolved_usage_count();
        let unresolved_extensions = self.resolver.unresolved_extensions.len();
        let unresolved_aliases = self.resolver.unresolved_aliases.len();

        // Final Pass, Finalize Errors
        if unresolved_imports != 0 {
            UsageResolver::run(self.resolver, true);
        }
        if unresolved_aliases != 0 {
            TypeAliasResolver::run(self.resolver, true);
        }
        if unresolved_extensions != 0 {
            ExtensionBinder::run(self.resolver, true);
        }
    }

    fn process_imports(&mut self) -> bool {
        let unresolved = self.resolver.unresolved_usage_count();
        UsageResolver::run(self.resolver, false);
        let updated = self.resolver.unresolved_usage_count();
        updated != unresolved
    }

    fn process_extensions(&mut self) -> bool {
        let unresolved = self.resolver.unresolved_extensions.len();
        ExtensionBinder::run(self.resolver, false);
        self.resolver.unresolved_extensions.len() != unresolved
    }

    fn process_alias(&mut self) -> bool {
        let unresolved = self.resolver.unresolved_aliases.len();
        TypeAliasResolver::run(self.resolver, false);
        self.resolver.unresolved_aliases.len() != unresolved
    }
}
