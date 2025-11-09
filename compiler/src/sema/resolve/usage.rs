use crate::{
    ast,
    error::CompileResult,
    sema::resolve::{
        models::{ScopeNamespace, UsageEntry, UsageKind},
        resolver::Resolver,
    },
};

pub fn resolve_usages(resolver: &mut Resolver) -> CompileResult<()> {
    let mut actor = Actor { resolver };
    actor.run()
}

struct Actor<'r, 'a, 'c> {
    resolver: &'r mut Resolver<'a, 'c>,
}

impl<'r, 'a, 'c> Actor<'r, 'a, 'c> {
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

impl<'r, 'a, 'c> Actor<'r, 'a, 'c> {
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

impl<'r, 'a, 'c> Actor<'r, 'a, 'c> {
    fn resolve_usage(&mut self, usage: UsageEntry<'a>, finalize: bool) -> bool {
        let module_result = self.resolver.resolve_module_path(&usage.module_path);

        let module = match module_result {
            Ok(scope) => scope,
            Err(e) => {
                if finalize {
                    todo!("report error")
                }
                return false;
            }
        };

        let binding = match &usage.kind {
            UsageKind::Single(binding) => binding,
            UsageKind::Glob { id } => {
                todo!("glob imports")
            }
        };
        let ns = [
            ScopeNamespace::Module,
            ScopeNamespace::Type,
            ScopeNamespace::Value,
        ];

        let mut resolved_holder = None;
        for ns in ns {
            let Some(holder) = self
                .resolver
                .find_holder_in_scope(&binding.source, module, ns)
                .ok()
            else {
                continue;
            };

            resolved_holder = Some((holder, ns));
            break;
        }

        let Some((holder, ns)) = resolved_holder else {
            if finalize {
                todo!("report unknown symbol")
            }
            return false;
        };

        let entries = holder.all_entries();
        for (entry) in entries.into_iter() {
            // TODO: Check if we can actually import this entry
            let entry = self
                .resolver
                .create_scope_entry_from_usage(entry, module, usage);

            let result = if usage.is_import {
                self.resolver
                    .import(usage.scope, binding.target.clone(), entry, ns)
            } else {
                self.resolver
                    .export(usage.scope, binding.target.clone(), entry, ns)
            };

            match result {
                Ok(_) => continue,
                Err(e) => {
                    if finalize {
                        // TODO: Report Error
                        todo!("report already bound symbol")
                    }
                }
            }
        }

        true
    }
}
