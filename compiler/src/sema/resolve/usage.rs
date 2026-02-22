use crate::{
    error::CompileResult,
    sema::resolve::{
        models::{Holder, ScopeEntryData, ScopeEntryKind, ScopeNamespace, UsageEntry, UsageKind},
        resolver::Resolver,
    },
};

pub fn resolve_usages(resolver: &mut Resolver) -> CompileResult<()> {
    let actor = Actor { resolver };
    actor.run();
    resolver.context.dcx.ok()
}

struct Actor<'r, 'a> {
    resolver: &'r mut Resolver<'a>,
}

impl<'r, 'a> Actor<'r, 'a> {
    fn run(mut self) {
        let mut changed = false;

        while changed {
            let start = self.unresolved_count();
            self.resolve(false);
            let end = self.unresolved_count();
            changed |= start != end;
        }

        if self.unresolved_count() != 0 {
            self.resolve(true);
        }
    }

    fn unresolved_count(&self) -> usize {
        self.resolver.unresolved_exports.len() + self.resolver.unresolved_imports.len()
    }
}

impl<'r, 'a> Actor<'r, 'a> {
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

impl<'r, 'a> Actor<'r, 'a> {
    fn resolve_usage(&mut self, usage: UsageEntry<'a>, finalize: bool) -> bool {
        let module_result = match (&usage.kind, usage.module_path.is_empty()) {
            // Handle bare imports like `import std` where module_path would otherwise be empty.
            (UsageKind::Single(binding), true) => {
                let path = vec![binding.source.clone()];
                self.resolver.resolve_module_path(&path)
            }
            _ => self.resolver.resolve_module_path(&usage.module_path),
        };

        let module = match module_result {
            Ok(scope) => scope,
            Err(e) => {
                if finalize {
                    self.resolver.dcx().emit(e.diag(self.resolver.context));
                }
                return false;
            }
        };

        usage.module_scope.set(Some(module));

        let binding = match &usage.kind {
            UsageKind::Single(binding) => binding,
            UsageKind::Glob { .. } => {
                return true;
            }
        };

        let mut resolved_holder = None;

        // If the import/export is for a module itself (e.g., `import std`), bind the module
        // resolution directly instead of looking for a member inside an empty path.
        if usage.module_path.is_empty() {
            if let Some(resolution) = module.resolution() {
                let entry = self.resolver.create_scope_entry(ScopeEntryData {
                    kind: ScopeEntryKind::Resolution(resolution),
                    span: binding.source.span,
                });
                resolved_holder = Some((Holder::Single(entry), ScopeNamespace::Type));
            }
        }

        if resolved_holder.is_none() {
            let ns = [ScopeNamespace::Type, ScopeNamespace::Value];

            for ns in ns {
                let Ok(holder) = self.resolver.resolve_in_scope(&binding.source, module, ns) else {
                    continue;
                };

                resolved_holder = Some((holder, ns));
                break;
            }
        }

        let Some((holder, ns)) = resolved_holder else {
            if finalize {
                let message = format!("unknown symbol '{}' in module", binding.source.symbol);
                self.resolver
                    .dcx()
                    .emit_error(message, Some(binding.source.span));
            }
            return false;
        };

        let entries = holder.all_entries();
        for entry in entries.into_iter() {
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
                Err(_) => {
                    if finalize {
                        self.resolver.dcx().emit_error(
                            "imported symbol is already bound in scope".into(),
                            Some(binding.target.span),
                        );
                    }
                }
            }
        }

        true
    }
}
