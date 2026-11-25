//! Facts the resolver records for the advisory lints: the single-name imports
//! of each file and block and which of them a name lookup went through, the
//! locals the author declared and which of them an expression reads, and, for
//! `taro vet`, declarations that shadow a binding of the same function which
//! is read after the declaration's scope ends.
//!
//! Resolution runs on the source as written, before lowering desugars `for`,
//! optional chaining or async code and before synthesized methods exist, so
//! every local recorded here is one the author wrote.
//!
//! Only the package compiled with `Config::lint_warnings` records anything.
//! The facts are moved into `CompilerStore::lint_facts` when resolution ends
//! and reported after type checking (`sema::validate::unused_names`).

use crate::{
    ast::{Identifier, NodeID},
    sema::resolve::models::{
        DefinitionKind, Holder, ImportFact, LexicalScope, LintFacts, LocalFact, Resolution,
        ScopeEntryKind, ScopeKind, UsageEntry, UsageKind,
    },
};
use rustc_hash::{FxHashMap, FxHashSet};

#[derive(Default)]
pub(crate) struct LintState {
    pub facts: LintFacts,
    /// Identifier expressions that are a whole target of `=`: a write.
    assign_targets: FxHashSet<NodeID>,
    /// Every local and parameter binding with its name and owning body.
    bindings: FxHashMap<NodeID, BindingInfo>,
    /// Outer binding -> declarations that shadow it.
    shadowers: FxHashMap<NodeID, Vec<Shadower>>,
}

#[derive(Clone, Copy)]
struct BindingInfo {
    name: Identifier,
    /// The function or closure body that declares the binding.
    owner: u32,
    is_parameter: bool,
}

struct Shadower {
    inner: NodeID,
    /// `LexicalScope::id` of the scope the shadowing declaration is in.
    scope: u32,
    reported: bool,
}

impl LintState {
    /// A name lookup returned `holder`; mark the imports it went through.
    pub fn note_lookup(&mut self, holder: &Holder<'_>) {
        let entries = match holder {
            Holder::Single(entry) => std::slice::from_ref(entry),
            Holder::Overloaded(entries) => entries.as_slice(),
        };
        for entry in entries {
            if let ScopeEntryKind::Usage { user, .. } = &entry.kind
                && user.is_import
                && let UsageKind::Single(binding) = &user.kind
            {
                self.facts.used_imports.insert(binding.node_id);
            }
        }
    }

    /// A single-name import resolved to `holder`.
    pub fn note_import(&mut self, usage: UsageEntry<'_>, holder: &Holder<'_>) {
        // A namespace's imports are members other code can reach as
        // `Namespace::Name`, possibly from another package, and globs are
        // exempt. Only file and block imports are checked.
        if !usage.is_import || !matches!(usage.scope.kind, ScopeKind::File(_) | ScopeKind::Block(_))
        {
            return;
        }
        let UsageKind::Single(binding) = &usage.kind else {
            return;
        };
        let interfaces = holder
            .all_entries()
            .iter()
            .filter_map(|entry| match entry.resolution() {
                Resolution::Definition(id, DefinitionKind::Interface) => Some(id),
                _ => None,
            })
            .collect();
        self.facts.imports.push(ImportFact {
            binding: binding.node_id,
            target: binding.target,
            interfaces,
        });
    }

    pub fn note_assign_target(&mut self, id: NodeID) {
        self.assign_targets.insert(id);
    }

    pub fn note_parameter(&mut self, id: NodeID, name: Identifier, owner: u32) {
        self.bindings.insert(
            id,
            BindingInfo {
                name,
                owner,
                is_parameter: true,
            },
        );
    }

    /// A new local `id` called `name`, bound by a pattern of the body `owner`.
    pub fn note_local(&mut self, id: NodeID, name: Identifier, owner: u32) {
        self.facts.locals.push(LocalFact { id, name });
        self.bindings.insert(
            id,
            BindingInfo {
                name,
                owner,
                is_parameter: false,
            },
        );
    }

    /// A `:=` or `var` declaration of `id` into the innermost of `scopes`.
    /// When it hides a local or parameter of the same body from an enclosing
    /// scope, remember it: a later read of the hidden binding after this
    /// scope ends suggests the declaration was meant to assign it.
    pub fn note_declaration(
        &mut self,
        id: NodeID,
        name: Identifier,
        owner: u32,
        scopes: &[LexicalScope<'_>],
    ) {
        self.note_local(id, name, owner);
        let Some((innermost, enclosing)) = scopes.split_last() else {
            return;
        };
        if innermost.table.contains_key(&name.symbol) {
            // A redeclaration in the same scope replaces the old binding.
            return;
        }
        let Some(Resolution::LocalVariable(outer)) = enclosing
            .iter()
            .rev()
            .find_map(|scope| scope.table.get(&name.symbol))
        else {
            return;
        };
        if self
            .bindings
            .get(outer)
            .is_none_or(|info| info.owner != owner)
        {
            return;
        }
        self.shadowers.entry(*outer).or_default().push(Shadower {
            inner: id,
            scope: innermost.id,
            reported: false,
        });
    }

    /// The expression `node` refers to `local` while `scopes` are open.
    pub fn note_local_reference(
        &mut self,
        names: &crate::interner::SessionInterner,
        node: NodeID,
        local: NodeID,
        scopes: &[LexicalScope<'_>],
    ) {
        if self.assign_targets.contains(&node) {
            return;
        }
        self.facts.read_locals.insert(local);

        let Some(shadowers) = self.shadowers.get_mut(&local) else {
            return;
        };
        let Some(outer) = self.bindings.get(&local).copied() else {
            return;
        };
        for shadower in shadowers.iter_mut() {
            // Reads inside the shadowing scope, before the declaration, are
            // reads of the outer binding the author can see.
            if shadower.reported || scopes.iter().any(|scope| scope.id == shadower.scope) {
                continue;
            }
            shadower.reported = true;
            let Some(inner) = self.bindings.get(&shadower.inner) else {
                continue;
            };
            let message = format!(
                "vet: '{}' shadows the {} declared on line {}, which is read after this scope ends",
                names.text(inner.name.symbol),
                if outer.is_parameter {
                    "parameter"
                } else {
                    "variable"
                },
                outer.name.span.start.line + 1,
            );
            self.facts.shadowed.push((inner.name.span, message));
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::test_support::{analyze_script, with_lint_warnings};

    /// `taro vet` shadowing findings of a script: `(line, column, message)`.
    fn shadowed(source: &str) -> Vec<(usize, usize, String)> {
        with_lint_warnings(|| {
            analyze_script(source, |_, gcx| {
                let facts = gcx.store.lint_facts.borrow();
                let mut found: Vec<_> = facts
                    .get(&gcx.package_index())
                    .map(|facts| {
                        facts
                            .shadowed
                            .iter()
                            .map(|(span, message)| {
                                (span.start.line + 1, span.start.offset, message.clone())
                            })
                            .collect()
                    })
                    .unwrap_or_default();
                found.sort();
                found
            })
        })
    }

    #[test]
    fn declarations_hiding_a_binding_read_after_their_scope_are_reported() {
        let found = shadowed(
            r#"func load(_ limit: int32, _ flag: bool) -> int32 {
    config := 1
    if flag {
        config := 2
        limit := config
        _ = limit
    }
    return config + limit
}
func main() {}
"#,
        );
        assert_eq!(
            found,
            vec![
                (
                    4,
                    8,
                    "vet: 'config' shadows the variable declared on line 2, which is read after this scope ends".to_string()
                ),
                (
                    5,
                    8,
                    "vet: 'limit' shadows the parameter declared on line 1, which is read after this scope ends".to_string()
                ),
            ]
        );
    }

    #[test]
    fn shadowing_without_a_later_read_or_across_bodies_is_not_reported() {
        let found = shadowed(
            r#"func quiet(_ flag: bool) -> int32 {
    value := 1
    total := value
    if flag {
        value := 2
        _ = value
    }
    var count = 1
    var count = count + 1
    run := () => {
        total := 5
        total
    }
    _ = run()
    return count + total
}
func main() {}
"#,
        );
        assert!(found.is_empty(), "{found:#?}");
    }

    #[test]
    fn tuple_shorthand_destructuring_reports_shadowed_outer_binding() {
        let found = shadowed(
            r#"func run(_ flag: bool) -> int32 {
    outer := 1
    if flag {
        (outer, _) := (2, 3)
        _ = outer
    }
    return outer
}
func main() {}
"#,
        );
        assert_eq!(
            found,
            vec![(
                4,
                9,
                "vet: 'outer' shadows the variable declared on line 2, which is read after this scope ends"
                    .to_string()
            )]
        );
    }
}
