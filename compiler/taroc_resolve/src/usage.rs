use super::resolver::Resolver;
use crate::{find::ResolutionState, models::ParentContext};
use taroc_resolve_models::{
    Determinacy, ExternalDefUsageKind, ExternalDefinitionUsage, NameBinding, NameBindingData,
    NameBindingKind, PathResult,
};

pub struct UsageResolver<'res, 'ctx> {
    pub resolver: &'res mut Resolver<'ctx>,
    pub finalize: bool,
}

impl<'res, 'ctx> UsageResolver<'res, 'ctx> {
    pub fn run(resolver: &'res mut Resolver<'ctx>, finalize: bool) {
        let mut actor = UsageResolver { resolver, finalize };
        actor.resolve_exports();
        actor.resolve_imports();
    }
}

impl<'res, 'ctx> UsageResolver<'res, 'ctx> {
    fn resolve_exports(&mut self) {
        // Process each exprt.
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
                self.resolver.unresolved_exports.push(import);
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
            usage.module_path.len() >= 1,
            "Module Path Must Not be Emtpy!"
        );
        debug_assert!(!usage.is_resolved.get(), "Usage Has already been resolved");

        let is_import = usage.is_import;
        let parent_context = if !is_import {
            Some(ParentContext {
                file: usage.file,
                module: usage.module,
            })
        } else {
            None
        };
        let result = self.resolver.resolve_path_with_scopes(
            &usage.module_path,
            &[],
            ResolutionState::Usage(parent_context),
        );

        let module = match result {
            PathResult::Context(ctx) => ctx,
            PathResult::NonContext(_) => {
                if self.finalize {
                    let last = usage.module_path.last().unwrap().identifier;
                    let message = format!("'{}' does not have a namespace", last.symbol);
                    self.resolver.context.diagnostics.error(message, last.span);
                }

                return false;
            }
            PathResult::Indeterminate => {
                if self.finalize {
                    let last = usage.module_path.last().unwrap().identifier;
                    let message = format!("ambiguous usage '{}'", last.symbol);
                    self.resolver.context.diagnostics.error(message, last.span);
                }
                return false;
            }
            PathResult::Failed { segment, .. } => {
                if self.finalize {
                    let message = format!("Unable to Resolve '{}'", segment.symbol);
                    self.resolver
                        .context
                        .diagnostics
                        .error(message, segment.span);
                }
                return false;
            }
        };

        usage.module_context.set(Some(module));

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

        let result = self.resolver.resolve_symbol_in_context(
            &source.symbol,
            module,
            ResolutionState::Usage(parent_context),
        );

        match result {
            Ok(binding) => {
                *source_binding.borrow_mut() = Some(binding);
                let binding = self.convert_usage_binding(binding, usage);
                if is_import {
                    self.resolver.force_define(parent, target, binding);
                } else {
                    self.resolver.define(parent, target, binding);
                }
            }
            Err(err) => {
                let last = usage.module_path.last().unwrap().identifier;
                match err {
                    Determinacy::Determined => {
                        if self.finalize {
                            let title = if last.symbol.as_str() == "{{root}}" {
                                "scope"
                            } else {
                                last.symbol.as_str()
                            };

                            let message =
                                format!("unable to find symbol '{}' in {}", source.symbol, title);
                            self.resolver
                                .context
                                .diagnostics
                                .error(message, source.span);
                        }
                    }
                    Determinacy::Undetermined => {
                        if self.finalize {
                            let last = usage.module_path.last().unwrap().identifier;
                            let message = format!("ambiguous usage '{}'", last.symbol);
                            self.resolver.context.diagnostics.error(message, last.span);
                        }
                    }
                }
                return false;
            }
        }

        usage.is_resolved.set(true);
        return true;
    }

    fn convert_usage_binding(
        &mut self,
        binding: NameBinding<'ctx>,
        usage: ExternalDefinitionUsage<'ctx>,
    ) -> NameBinding<'ctx> {
        self.resolver.alloc_binding(NameBindingData {
            kind: NameBindingKind::ExternalUsage { binding, usage },
            span: usage.span,
            vis: taroc_hir::TVisibility::Public,
        })
    }
}
