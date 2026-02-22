use crate::{
    compile::context::Gcx,
    error::CompileResult,
    hir::{self, DefinitionID, HirVisitor},
    sema::{
        models::{AliasDefinition, AliasKind},
        resolve::models::TypeHead,
        tycheck::lower::{DefTyLoweringCtx, TypeLowerer},
    },
    span::{Span, Symbol},
};

pub fn run(package: &hir::Package, context: Gcx) -> CompileResult<()> {
    let mut actor = Actor::new(context);

    // Phase 1: Collect all alias definitions (no lowering yet)
    hir::walk_package(&mut actor, package);
    context.dcx().ok()?;

    // Phase 2: Trigger resolution for all aliases (lowerer handles caching/cycles)
    actor.resolve_all_aliases();
    context.dcx().ok()
}

struct Actor<'ctx> {
    context: Gcx<'ctx>,
    alias_ids: Vec<DefinitionID>,
}

impl<'ctx> Actor<'ctx> {
    fn new(context: Gcx<'ctx>) -> Self {
        Self {
            context,
            alias_ids: Vec::new(),
        }
    }
}

impl<'ctx> Actor<'ctx> {
    fn register_alias(&mut self, entry: AliasDefinition) {
        let id = entry.id;

        if let Some(extension_id) = entry.extension_id {
            if let Some(head) = self.context.get_impl_type_head(extension_id) {
                self.register_in_bucket(head, entry.name, id, entry.span);
            }
        }

        self.context.with_session_type_database(|db| {
            db.alias_table.aliases.insert(id, entry);
        });

        self.alias_ids.push(id);
    }

    fn register_in_bucket(&self, head: TypeHead, name: Symbol, id: DefinitionID, span: Span) {
        self.context.with_session_type_database(|db| {
            let bucket = db.alias_table.by_type.entry(head).or_default();

            if let Some((existing_id, _)) = bucket.aliases.get(&name) {
                if *existing_id != id {
                    self.context.dcx().emit_error(
                        format!(
                            "conflicting associated type '{}' on '{}'",
                            self.context.symbol_text(name),
                            head.format(self.context)
                        ),
                        Some(span),
                    );
                    return;
                }
            }

            bucket.aliases.insert(name, (id, span));
        });
    }
}

impl HirVisitor for Actor<'_> {
    fn visit_declaration(&mut self, node: &hir::Declaration) -> Self::Result {
        let hir::DeclarationKind::TypeAlias(alias) = &node.kind else {
            return hir::walk_declaration(self, node);
        };

        let Some(ty) = &alias.ty else {
            return hir::walk_declaration(self, node);
        };

        let entry = AliasDefinition {
            id: node.id,
            name: node.identifier.symbol,
            span: node.span,
            ast_ty: ty.clone(),
            extension_id: None,
            kind: AliasKind::Weak,
        };
        self.register_alias(entry);
        hir::walk_declaration(self, node)
    }

    fn visit_assoc_declaration(
        &mut self,
        node: &hir::AssociatedDeclaration,
        context: hir::AssocContext,
    ) -> Self::Result {
        let hir::AssocContext::Impl(impl_id) = context else {
            return;
        };

        let hir::AssociatedDeclarationKind::Type(alias) = &node.kind else {
            return;
        };

        let Some(ty) = alias.ty.as_ref() else {
            return;
        };

        let entry = AliasDefinition {
            id: node.id,
            name: node.identifier.symbol,
            span: node.span,
            ast_ty: ty.clone(),
            extension_id: Some(impl_id),
            kind: AliasKind::Inherent,
        };
        self.register_alias(entry);
    }
}

impl<'ctx> Actor<'ctx> {
    fn resolve_all_aliases(&self) {
        let gcx = self.context;
        for &alias_id in &self.alias_ids {
            if gcx.try_get_alias_type(alias_id).is_some() {
                continue;
            }
            let ctx = DefTyLoweringCtx::new(alias_id, gcx);
            let lowerer: &dyn TypeLowerer = &ctx;
            let Some(def) =
                gcx.with_session_type_database(|db| db.alias_table.aliases.get(&alias_id).cloned())
            else {
                continue;
            };
            let ty = lowerer.lower_type(&def.ast_ty);
            gcx.cache_alias_type(alias_id, ty);
        }
    }
}
