use crate::{
    ast::Identifier,
    compile::context::GlobalContext,
    sema::resolve::models::{
        DefinitionID, DefinitionKind, Holder, NameEntry, ResolutionOutput, Scope, ScopeNamespace,
    },
    span::Symbol,
};

pub(crate) fn resolve_package_scope<'arena>(
    gcx: GlobalContext<'arena>,
    output: &ResolutionOutput<'arena>,
    identifier: Identifier,
) -> Option<Scope<'arena>> {
    let identifier_text = gcx.symbol_text(identifier.symbol);
    if identifier_text == gcx.config.name {
        return Some(output.root_scope);
    }

    let dependency = gcx.config.dependencies.get(identifier_text.as_ref())?;
    let package = gcx
        .visible_packages()
        .into_iter()
        .find(|pkg| gcx.package_ident(*pkg).as_deref() == Some(dependency.as_str()))?;
    let output = gcx.try_resolution_output(package)?;
    Some(output.root_scope)
}

pub(crate) fn find_holder_in_scope<'arena>(
    scope: Scope<'arena>,
    symbol: Symbol,
    namespace: ScopeNamespace,
) -> Option<Holder<'arena>> {
    let table = scope.table.borrow();
    let entry = table.get(&symbol)?;
    holder_from_name_entry(entry, namespace)
}

pub(crate) fn resolve_in_scope<'arena>(
    scope: Scope<'arena>,
    identifier: Identifier,
    namespace: ScopeNamespace,
) -> Option<Holder<'arena>> {
    if let Some(holder) = find_holder_in_scope(scope, identifier.symbol, namespace) {
        return Some(holder);
    }

    let usages = match scope.kind {
        crate::sema::resolve::models::ScopeKind::File(..)
        | crate::sema::resolve::models::ScopeKind::Block(..) => &scope.glob_imports,
        crate::sema::resolve::models::ScopeKind::Definition(
            _,
            DefinitionKind::Module | DefinitionKind::Namespace,
        ) => &scope.glob_exports,
        _ => return None,
    };

    let mut candidates = Vec::new();
    for usage in usages.borrow().iter() {
        let Some(used_scope) = usage.module_scope.get() else {
            continue;
        };
        if let Some(holder) = resolve_in_scope(used_scope, identifier, namespace) {
            candidates.push(holder);
        }
    }

    match candidates.len() {
        0 => None,
        1 => candidates.into_iter().next(),
        _ if namespace == ScopeNamespace::Value => {
            let all_entries = candidates
                .into_iter()
                .flat_map(|candidate| candidate.all_entries())
                .collect();
            Some(Holder::Overloaded(all_entries))
        }
        _ => None,
    }
}

pub(crate) fn scope_for_holder<'arena>(
    gcx: GlobalContext<'arena>,
    output: &ResolutionOutput<'arena>,
    holder: &Holder<'arena>,
) -> Option<Scope<'arena>> {
    let Holder::Single(entry) = holder else {
        return None;
    };

    let resolution = entry.resolution();
    let def_id = resolution.definition_id()?;
    let kind = if def_id.is_local_to_index(gcx.package_index()) {
        *output.definition_to_kind.get(&def_id)?
    } else {
        let external = gcx.try_resolution_output(def_id.package())?;
        *external.definition_to_kind.get(&def_id)?
    };

    if !matches!(
        kind,
        DefinitionKind::Module | DefinitionKind::Namespace | DefinitionKind::Interface
    ) {
        return None;
    }

    scope_for_definition(gcx, output, def_id)
}

pub(crate) fn scope_for_definition<'arena>(
    gcx: GlobalContext<'arena>,
    output: &ResolutionOutput<'arena>,
    def_id: DefinitionID,
) -> Option<Scope<'arena>> {
    if def_id.is_local_to_index(gcx.package_index()) {
        output.definition_scope_mapping.get(&def_id).copied()
    } else {
        let external = gcx.try_resolution_output(def_id.package())?;
        external.definition_scope_mapping.get(&def_id).copied()
    }
}

fn holder_from_name_entry<'arena>(
    entry: &NameEntry<'arena>,
    namespace: ScopeNamespace,
) -> Option<Holder<'arena>> {
    match namespace {
        ScopeNamespace::Type => entry.ty.map(Holder::Single),
        ScopeNamespace::Value => {
            if entry.values.is_empty() {
                None
            } else if entry.values.len() == 1 {
                Some(Holder::Single(entry.values[0]))
            } else {
                Some(Holder::Overloaded(entry.values.clone()))
            }
        }
    }
}
