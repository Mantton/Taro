use super::resolver::Resolver;
use taroc_constants::STD_PREFIX;
use taroc_resolve_models::{DefinitionContext, NameHolder, Segment};
use taroc_span::Symbol;

impl<'ctx> Resolver<'ctx> {
    pub fn resolve_module_path(&mut self, path: &[Segment]) -> Option<DefinitionContext<'ctx>> {
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
                self.session
                    .context
                    .diagnostics
                    .error(message, segment.identifier.span);
                return None;
            }

            // println!("Resolved {}", segment.ident.symbol);
        }

        return module;
    }

    fn resolve_package_root(&mut self, name: Symbol) -> Option<DefinitionContext<'ctx>> {
        // Refering to self
        if name.as_str() == &self.session.config.package_name() {
            return self.root_context;
        }

        // Refering to STD
        if name.as_str() == STD_PREFIX {
            let context = self
                .session
                .context
                .store
                .resolutions
                .borrow()
                .get(&0)
                .expect("std to be resolved")
                .root;
            return Some(context);
        }

        // Refering to Dependency
        if let Some(target) = self.session.config.dependency_map.get(name.as_str()) {
            let index = *self
                .session
                .context
                .store
                .package_mapping
                .borrow()
                .get(target)
                .expect("package index");
            let context = self
                .session
                .context
                .store
                .resolutions
                .borrow()
                .get(&index)
                .expect("package to be resolved")
                .root;
            return Some(context);
        }

        return None;
    }

    fn resolve_module_in_context(
        &mut self,
        context: DefinitionContext<'ctx>,
        symbol: Symbol,
    ) -> Option<DefinitionContext<'ctx>> {
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
