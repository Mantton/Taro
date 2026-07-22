use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    compile::context::Gcx,
    error::CompileResult,
    hir::{self, DefinitionID, HirVisitor},
    sema::{
        models::InterfaceAliasDefinition,
        resolve::models::DefinitionKind,
        tycheck::lower::{DefTyLoweringCtx, TypeLowerer},
    },
    span::{Span, Symbol},
};

/// Discover interface-set aliases before interface hierarchies and generic
/// constraints are collected. The aliases are then lazily expanded by the
/// type lowerer, which lets every interface position share the same rules.
pub fn run(package: &hir::Package, context: Gcx<'_>) -> CompileResult<()> {
    let mut actor = Actor {
        context,
        candidates: FxHashMap::default(),
    };
    hir::walk_package(&mut actor, package);
    actor.register_interface_aliases();
    actor.resolve_all_interface_aliases();
    context.dcx().ok()
}

#[derive(Clone)]
struct Candidate {
    name: Symbol,
    span: Span,
    interfaces: Vec<hir::PathNode>,
    depends_on_alias: Option<DefinitionID>,
    is_interface_set: bool,
}

struct Actor<'ctx> {
    context: Gcx<'ctx>,
    candidates: FxHashMap<DefinitionID, Candidate>,
}

impl HirVisitor for Actor<'_> {
    fn visit_declaration(&mut self, node: &hir::Declaration) -> Self::Result {
        if let hir::DeclarationKind::TypeAlias(alias) = &node.kind {
            self.collect_candidate(node, alias);
        }
        hir::walk_declaration(self, node)
    }

    fn visit_assoc_declaration(
        &mut self,
        node: &hir::AssociatedDeclaration,
        context: hir::AssocContext,
    ) -> Self::Result {
        if let hir::AssociatedDeclarationKind::Type(alias) = &node.kind
            && alias.interface_set.is_some()
        {
            self.context.dcx().emit_error(
                "interface-set aliases must be standalone type declarations".into(),
                Some(node.span),
            );
        }
        hir::walk_assoc_declaration(self, node, context)
    }
}

impl Actor<'_> {
    fn collect_candidate(&mut self, node: &hir::Declaration, alias: &hir::TypeAlias) {
        if let Some(bounds) = &alias.interface_set {
            self.candidates.insert(
                node.id,
                Candidate {
                    name: node.identifier.symbol,
                    span: node.span,
                    interfaces: bounds.iter().map(|bound| bound.path.clone()).collect(),
                    depends_on_alias: None,
                    is_interface_set: true,
                },
            );
            return;
        }

        let Some(ty) = alias.ty.as_deref() else {
            return;
        };
        let Some(path_node) = nominal_path_node(ty) else {
            return;
        };
        let Some(resolution) = resolved_path_resolution(&path_node) else {
            return;
        };

        let (depends_on_alias, is_interface_set) = match resolution {
            hir::Resolution::Definition(_, DefinitionKind::Interface) => (None, true),
            hir::Resolution::Definition(id, DefinitionKind::TypeAlias) => (Some(*id), false),
            _ => return,
        };

        self.candidates.insert(
            node.id,
            Candidate {
                name: node.identifier.symbol,
                span: node.span,
                interfaces: vec![path_node],
                depends_on_alias,
                is_interface_set,
            },
        );
    }

    fn register_interface_aliases(&mut self) {
        // A single-path alias is an interface-set alias when it ultimately
        // reaches an interface or an explicit composition. Compute that
        // classification to a fixed point so declaration order is irrelevant.
        let mut known: FxHashSet<DefinitionID> = self
            .candidates
            .iter()
            .filter_map(|(&id, candidate)| candidate.is_interface_set.then_some(id))
            .collect();

        loop {
            let newly_known: Vec<_> = self
                .candidates
                .iter()
                .filter_map(|(&id, candidate)| {
                    (!known.contains(&id)
                        && candidate
                            .depends_on_alias
                            .is_some_and(|dependency| known.contains(&dependency)))
                    .then_some(id)
                })
                .collect();
            if newly_known.is_empty() {
                break;
            }
            known.extend(newly_known);
        }

        let entries: Vec<_> = known
            .into_iter()
            .filter_map(|id| {
                self.candidates
                    .get(&id)
                    .map(|candidate| InterfaceAliasDefinition {
                        id,
                        name: candidate.name,
                        span: candidate.span,
                        interfaces: candidate.interfaces.clone(),
                    })
            })
            .collect();

        self.context.with_session_type_database(|db| {
            for entry in entries {
                db.alias_table.interface_sets.insert(entry.id, entry);
            }
        });
    }

    fn resolve_all_interface_aliases(&self) {
        let mut ids: Vec<_> = self.context.with_session_type_database(|db| {
            db.alias_table.interface_sets.keys().copied().collect()
        });
        ids.sort_unstable();
        for id in ids {
            let lowerer = DefTyLoweringCtx::new(id, self.context);
            lowerer.lowerer().resolve_interface_alias(id);
        }
    }
}

fn nominal_path_node(ty: &hir::Type) -> Option<hir::PathNode> {
    let hir::TypeKind::Nominal(path) = &ty.kind else {
        return None;
    };
    Some(hir::PathNode {
        id: ty.id,
        path: path.clone(),
        span: ty.span,
    })
}

fn resolved_path_resolution(node: &hir::PathNode) -> Option<&hir::Resolution> {
    let hir::ResolvedPath::Resolved(path) = &node.path else {
        return None;
    };
    Some(&path.resolution)
}
