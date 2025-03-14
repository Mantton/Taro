use taroc_error::CompileResult;
use taroc_resolve_models::{
    ExternalDefUsageKind, ExternalDefinitionUsage, NameBinding, NameBindingData, NameBindingKind,
};

use super::resolver::Resolver;

pub fn run(_: &taroc_hir::Package, resolver: &mut Resolver) -> CompileResult<()> {
    // Resolve
    resolver.resolve_exports()?;
    resolver.resolve_imports();
    // Finalize
    return Ok(());
}

impl Resolver<'_> {
    pub fn resolve_exports(&mut self) -> CompileResult<()> {
        // Process each exprt.
        for node in std::mem::take(&mut self.unresolved_exports) {
            if self.resolve_export(node) {
                self.resolved_exports.push(node);
            } else {
                self.unresolved_exports.push(node);
            }
        }

        self.session.context.diagnostics.report()
    }
    fn resolve_imports(&mut self) {
        while !self.unresolved_imports.is_empty() {
            let mut progress = false;
            let mut remaining = Vec::new();

            // Process each imports.
            for node in std::mem::take(&mut self.unresolved_imports) {
                if self.resolve_import(node) {
                    self.resolved_imports.push(node);
                    progress = true;
                } else {
                    remaining.push(node);
                }
            }

            // If no exports were resolved during this pass, exit the loop.
            if !progress {
                break;
            }

            self.unresolved_imports = remaining;
        }
    }
}

impl<'ctx> Resolver<'ctx> {
    fn resolve_export(&mut self, export: ExternalDefinitionUsage<'ctx>) -> bool {
        let module = self.resolve_module_path(&export.module_path);
        let Some(module) = module else {
            return false;
        };
        export.module_context.set(Some(module));

        let usage = match &export.kind {
            ExternalDefUsageKind::Single(binding) => binding,
            ExternalDefUsageKind::Glob { .. } => {
                // println!("Glob Export Tagged!");
                return true;
            }
        };

        // Set Source Binding
        let holder = module.resolutions.borrow().find(&usage.source.symbol);
        *usage.source_binding.borrow_mut() = holder;

        let parent = usage.parent;

        if holder.is_none() {
            let message = format!(
                "unable to find symbol '{}' in '{}'",
                usage.source.symbol,
                export.module_path.last().unwrap().identifier.symbol
            );
            self.session
                .context
                .diagnostics
                .error(message, usage.source.span);
            return false;
        }

        let bindings = holder.unwrap().all();

        let mut ok = true;
        for binding in bindings {
            let binding = self.convert_usage_binding(binding, export);
            // TODO: Visibility
            ok = ok && self.define(parent, usage.target, binding);
        }
        ok
    }

    fn resolve_import(&mut self, import: ExternalDefinitionUsage<'ctx>) -> bool {
        let module = self.resolve_module_path(&import.module_path);
        let Some(module) = module else {
            return false;
        };
        import.module_context.set(Some(module));

        let usage = match &import.kind {
            ExternalDefUsageKind::Single(binding) => binding,
            ExternalDefUsageKind::Glob { .. } => {
                // println!("Glob Export Tagged!");
                return true;
            }
        };

        // Set Source Binding
        let holder = module.resolutions.borrow().find(&usage.source.symbol);
        *usage.source_binding.borrow_mut() = holder;

        let parent = usage.parent;

        if holder.is_none() {
            let message = format!(
                "unable to find symbol '{}' in '{}'",
                usage.source.symbol,
                import.module_path.last().unwrap().identifier.symbol
            );
            self.session
                .context
                .diagnostics
                .error(message, usage.source.span);
            return false;
        }

        let bindings = holder.unwrap().all();

        let mut ok = true;
        for binding in bindings {
            let binding = self.convert_usage_binding(binding, import);
            // TODO: Visibility
            ok = ok && self.force_define(parent, usage.target, binding);
        }

        ok
    }

    fn convert_usage_binding(
        &mut self,
        binding: NameBinding<'ctx>,
        usage: ExternalDefinitionUsage<'ctx>,
    ) -> NameBinding<'ctx> {
        self.alloc_binding(NameBindingData {
            kind: NameBindingKind::ExternalUsage { binding, usage },
            span: usage.span,
            vis: taroc_hir::TVisibility::Public,
        })
    }
}
