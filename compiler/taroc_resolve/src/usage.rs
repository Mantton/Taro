use super::resolver::Resolver;
use taroc_error::CompileResult;
use taroc_resolve_models::{
    BindingKey, ContextOrResolutionRoot, DefContextKind, DefinitionContext, Determinacy,
    ExternalDefUsageKind, ExternalDefinitionUsage, NameBinding, PathResult,
};

impl Resolver<'_> {
    pub fn unresolved_usage_count(&self) -> usize {
        self.unresolved_exports.len() + self.unresolved_imports.len()
    }
}

pub struct UsageResolver<'res, 'ctx> {
    pub resolver: &'res mut Resolver<'ctx>,
    pub finalize: bool,
}

impl<'res, 'ctx> UsageResolver<'res, 'ctx> {
    pub fn run(resolver: &'res mut Resolver<'ctx>) -> CompileResult<()> {
        let mut actor = UsageResolver {
            resolver,
            finalize: false,
        };

        let mut changed = true;
        while changed {
            changed = false;
            changed |= actor.resolve()
        }

        let unresolved_usages = actor.resolver.unresolved_usage_count();

        // Final Pass, Finalize Errors
        if unresolved_usages != 0 {
            actor.finalize = true;
            actor.resolve();
        }

        actor.resolver.gcx.diagnostics.report()
    }
}

impl<'res, 'ctx> UsageResolver<'res, 'ctx> {
    fn resolve(&mut self) -> bool {
        let unresolved = self.resolver.unresolved_usage_count();
        self.resolve_exports();
        self.resolve_imports();
        let updated = self.resolver.unresolved_usage_count();
        updated != unresolved
    }

    fn resolve_exports(&mut self) {
        let exports = std::mem::take(&mut self.resolver.unresolved_exports);
        for export in exports {
            if self.resolve_usage(export) {
                self.resolver.resolved_exports.push(export);
            } else {
                self.resolver.unresolved_exports.push(export);
            }
        }
    }

    fn resolve_imports(&mut self) {
        let imports = std::mem::take(&mut self.resolver.unresolved_imports);
        for import in imports {
            if self.resolve_usage(import) {
                self.resolver.resolved_imports.push(import);
            } else {
                self.resolver.unresolved_imports.push(import);
            }
        }
    }
}

impl<'res, 'ctx> UsageResolver<'res, 'ctx> {
    fn resolve_usage(&mut self, usage: ExternalDefinitionUsage<'ctx>) -> bool {
        // self.resolver
        //     .context
        //     .diagnostics
        //     .warn("Resolving Usage".into(), usage.span);
        debug_assert!(
            !usage.module_path.is_empty(),
            "Module Path Must Not be Emtpy!"
        );
        debug_assert!(!usage.is_resolved.get(), "Usage Has already been resolved");

        // Resolve Module
        let module_result = self.resolver.resolve_path_with_scopes(
            &usage.module_path,
            None,
            &[],
            &usage.parent_scope,
        );

        let module = match module_result {
            PathResult::Context(ctx) => ctx,
            PathResult::NonContext(_) => {
                if self.finalize {
                    let last = usage.module_path.last().unwrap().identifier;
                    let message = format!("'{}' does not have a namespace", last.symbol);
                    self.resolver.gcx.diagnostics.error(message, last.span);
                }

                return false;
            }
            PathResult::Indeterminate => {
                if self.finalize {
                    let last = usage.module_path.last().unwrap().identifier;
                    let message = format!("ambiguous usage '{}'", last.symbol);
                    self.resolver.gcx.diagnostics.error(message, last.span);
                }
                return false;
            }
            PathResult::Failed { segment, .. } => {
                if self.finalize {
                    let message = format!("unable to locate symbol '{}'", segment.symbol);
                    self.resolver.gcx.diagnostics.error(message, segment.span);
                }
                return false;
            }
        };

        usage.module_context.set(Some(module));

        // File Imports
        let mut added_target_package = false;
        if let ContextOrResolutionRoot::Context(ctx) = module
            && let DefContextKind::Definition(id, ..) = ctx.kind
        {
            let package = id.package();
            let file = usage.span.file;
            self.resolver
                .file_to_imports
                .entry(file)
                .or_default()
                .insert(package);
            added_target_package = true;
        };

        // Resolve Imported Symbol
        let (source, source_binding, parent, target) = match &usage.kind {
            ExternalDefUsageKind::Single(def_usage_binding) => (
                def_usage_binding.source,
                &def_usage_binding.source_binding,
                def_usage_binding.parent,
                def_usage_binding.target,
            ),
            ExternalDefUsageKind::Glob { .. } => {
                usage.is_resolved.set(true);
                return true;
            }
        };

        let mut all_failed = true;
        self.resolver.per_ns(|this, ns| {
            let key = BindingKey::new(target.symbol, ns);
            // Undetermined / Unresolved usage
            if let Err(Determinacy::Undetermined) = source_binding[ns].get() {
                let result =
                    this.resolve_symbol_in_context(source, ns, module, &usage.parent_scope);
                source_binding[ns].set(result);
            } else {
                return;
            }

            // paren
            let result = source_binding[ns].get();
            let parent_context = parent.context;
            match result {
                Err(Determinacy::Undetermined) => {
                    todo!("undetermined usage")
                }
                Ok(holder) if holder.nearest().is_importable() => {
                    let bindings = holder.all();

                    for (index, binding) in bindings.into_iter().enumerate() {
                        if index == 0
                            && !added_target_package
                            && let Some(package) = binding.package_index()
                        {
                            let file = usage.span.file;
                            this.file_to_imports
                                .entry(file)
                                .or_default()
                                .insert(package);
                        }
                        let binding = this.convert_usage_binding(binding, usage);
                        if usage.is_import {
                            this.import(parent_context, key, binding);
                        } else {
                            this.export(parent_context, key, binding);
                        }
                    }
                    all_failed = false
                }
                __ @ (Ok(..) | Err(Determinacy::Determined)) => {
                    // Cannot import
                    if result.is_ok() {
                        let message = format!(
                            "cannot directly import associated symbol '{}'",
                            source.symbol
                        );
                        this.gcx.diagnostics.error(message, usage.span);
                        all_failed = false
                    }
                }
            };
        });

        if !all_failed {
            usage.is_resolved.set(true);
            return true;
        }

        if !self.finalize {
            return false;
        }

        let last = usage.module_path.last().unwrap().identifier;
        let title = if last.symbol.as_str() == "{{root}}" {
            "scope"
        } else {
            last.symbol.as_str()
        };

        let message = format!("unable to locate symbol '{}' in {}", source.symbol, title);
        self.resolver.gcx.diagnostics.error(message, source.span);

        // println!("Resolved _> {ok}, {}", self.finalize);

        // if !ok {
        //     self.resolver
        //         .context
        //         .diagnostics
        //         .warn("Failing Resolution".into(), target.span);
        // }
        return false;
    }
}

impl<'ctx> Resolver<'ctx> {
    pub fn import(
        &mut self,
        parent: DefinitionContext<'ctx>,
        key: BindingKey,
        binding: NameBinding<'ctx>,
    ) {
        let mut explict_imports = parent.explicit_imports.borrow_mut();
        let _ = self.define_in_resolution_map(key, binding, &mut explict_imports, true);
    }

    fn export(
        &mut self,
        parent: DefinitionContext<'ctx>,
        key: BindingKey,
        binding: NameBinding<'ctx>,
    ) {
        let mut explicit_exports = parent.explicit_exports.borrow_mut();
        let _ = self.define_in_resolution_map(key, binding, &mut explicit_exports, true);
    }
}
