use taroc_constants::STD_PREFIX;
use taroc_resolve_models::{DefinitionContext, NameHolder, Segment};
use taroc_span::Symbol;

use super::resolver::Resolver;

impl<'ctx, 'arena> Resolver<'ctx, 'arena> {
    pub fn resolve_module_path(&mut self, path: &[Segment]) -> Option<DefinitionContext<'arena>> {
        let mut module = None;
        for (index, segment) in path.iter().enumerate() {
            // Resolve
            if index == 0 {
                module = self.resolve_package_root(segment.identifier.symbol);
            } else {
                let Some(next) = module else {
                    unreachable!("previous failed resolution should return");
                };
                module = self.resolve_module_in_context(next, segment.identifier.symbol)
            }

            // Validate
            if module.is_none() {
                let message = if index == 0 {
                    format!(
                        "cannot resolve package aliased '{}'",
                        segment.identifier.symbol
                    )
                } else {
                    format!(
                        "cannot resolve symbol named '{}' in '{}'",
                        segment.identifier.symbol,
                        path[index - 1].identifier.symbol
                    )
                };
                self.context
                    .diagnostics
                    .error(message, segment.identifier.span);
                return None;
            }

            // println!("Resolved {}", segment.ident.symbol);
        }

        return module;
    }

    fn resolve_package_root(&mut self, name: Symbol) -> Option<DefinitionContext<'arena>> {
        // Refering to self
        if name.as_str() == &self.context.config.package_name() {
            return self.root_context;
        }

        // Refering to STD
        if name.as_str() == STD_PREFIX {
            todo!("Load STD")
        }

        // Refering to Dependency
        if let Some(_) = self.context.config.dependency_map.get(name.as_str()) {
            todo!("Load External ^^^")
        }

        return None;
    }

    fn resolve_module_in_context(
        &mut self,
        context: DefinitionContext<'arena>,
        symbol: Symbol,
    ) -> Option<DefinitionContext<'arena>> {
        let holder = context.resolutions.borrow().find(&symbol);

        let Some(holder) = holder else {
            return None;
        };

        match holder {
            NameHolder::Single(interned) => interned.context(),
            NameHolder::Set(_) => None,
        }
    }
}
