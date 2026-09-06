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
        loop {
            let start = self.unresolved_count();
            self.resolve(false);
            let end = self.unresolved_count();

            if end == 0 || end == start {
                break;
            }
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
                let path = vec![binding.source];
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
                self.resolver.import(usage.scope, binding.target, entry, ns)
            } else {
                self.resolver.export(usage.scope, binding.target, entry, ns)
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

#[cfg(test)]
mod tests {
    use crate::test_support::analyze_package_diagnostics;

    #[test]
    fn chained_reexports_resolve_to_a_fixed_point() {
        let diagnostics = analyze_package_diagnostics(&[
            ("a/reexport.tr", "export package.b.Value\n"),
            ("b/reexport.tr", "export package.c.Value\n"),
            ("c/value.tr", "public struct Value {}\n"),
            (
                "main.tr",
                "import package.a.Value\nfunc consume(_ value: Value) {}\n",
            ),
        ]);

        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }

    #[test]
    fn unresolved_reexport_cycle_terminates_and_reports_each_usage_once() {
        let diagnostics = analyze_package_diagnostics(&[
            ("a/reexport.tr", "export package.b.MissingFromB\n"),
            ("b/reexport.tr", "export package.a.MissingFromA\n"),
            ("main.tr", "func main() {}\n"),
        ]);

        let messages: Vec<_> = diagnostics
            .iter()
            .map(|diagnostic| diagnostic.message.as_str())
            .collect();
        assert_eq!(messages.len(), 2, "{diagnostics:#?}");
        assert!(
            messages
                .iter()
                .any(|message| message.contains("unknown symbol 'MissingFromB'")),
            "{diagnostics:#?}"
        );
        assert!(
            messages
                .iter()
                .any(|message| message.contains("unknown symbol 'MissingFromA'")),
            "{diagnostics:#?}"
        );
    }
    #[test]
    fn glob_imports_merge_function_overloads() {
        let diagnostics = analyze_package_diagnostics(&[
            (
                "a/value.tr",
                "public func value(_ x: int32) -> int32 { x }\n",
            ),
            ("b/value.tr", "public func value(_ x: bool) -> bool { x }\n"),
            (
                "main.tr",
                "import package.a.*\nimport package.b.*\nfunc exercise() { let _: int32 = value(1); let _: bool = value(true) }\n",
            ),
        ]);
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }

    #[test]
    fn glob_imports_reject_ambiguous_constants() {
        let diagnostics = analyze_package_diagnostics(&[
            ("a/value.tr", "public const VALUE: int32 = 1\n"),
            ("b/value.tr", "public const VALUE: int32 = 2\n"),
            (
                "main.tr",
                "import package.a.*\nimport package.b.*\nfunc exercise() -> int32 { VALUE }\n",
            ),
        ]);
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message.contains("ambiguous usage of `VALUE`")),
            "{diagnostics:#?}"
        );
    }
    #[test]
    fn cyclic_glob_reexports_report_missing_symbols_once() {
        let diagnostics = analyze_package_diagnostics(&[
            ("a/reexport.tr", "export package.b.*\n"),
            ("b/reexport.tr", "export package.a.*\n"),
            ("main.tr", "import package.a.Missing\nfunc main() {}\n"),
        ]);
        assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
        assert_eq!(diagnostics[0].message, "unknown symbol 'Missing' in module");
    }

    #[test]
    fn cyclic_glob_reexports_still_find_reachable_symbols() {
        let diagnostics = analyze_package_diagnostics(&[
            ("a/reexport.tr", "export package.b.*\n"),
            ("b/reexport.tr", "export package.a.*\nexport package.c.*\n"),
            ("c/value.tr", "public struct Value {}\n"),
            (
                "main.tr",
                "import package.a.Value\nfunc consume(_ value: Value) {}\n",
            ),
        ]);
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }

    #[test]
    fn glob_diamond_paths_preserve_overload_ambiguity() {
        let diagnostics = analyze_package_diagnostics(&[
            ("a/reexport.tr", "export package.c.*\n"),
            ("b/reexport.tr", "export package.c.*\n"),
            (
                "c/value.tr",
                "public func value(_ x: int32) -> int32 { x }\n",
            ),
            (
                "main.tr",
                "import package.a.*\nimport package.b.*\nfunc exercise() -> int32 { value(1) }\n",
            ),
        ]);
        assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
        assert!(
            diagnostics[0]
                .message
                .contains("ambiguous overload; unable to pick a best candidate"),
            "{diagnostics:#?}"
        );
    }
}
