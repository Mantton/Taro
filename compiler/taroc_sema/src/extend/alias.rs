use crate::GlobalContext;
use crate::ty::{AliasEntry, PackageAliasTable};
use taroc_error::CompileResult;
use taroc_hir::{DefinitionID, visitor::HirVisitor};
use taroc_span::Identifier;

use crate::lower::{ItemCtx, LoweringRequest, TypeLowerer};

pub fn run(package: &taroc_hir::Package, context: GlobalContext) -> CompileResult<()> {
    Harvestor::run(package, context)?;
    resolve(context)
}

/// Extension Binding, Maps Extension Blocks to Nominal Types
struct Harvestor<'ctx> {
    context: GlobalContext<'ctx>,
    table: PackageAliasTable,
}

impl<'ctx> Harvestor<'ctx> {
    fn new(context: GlobalContext<'ctx>) -> Harvestor<'ctx> {
        Harvestor {
            context,
            table: Default::default(),
        }
    }

    fn run<'a>(package: &taroc_hir::Package, context: GlobalContext<'ctx>) -> CompileResult<()> {
        let mut actor = Harvestor::new(context);
        taroc_hir::visitor::walk_package(&mut actor, package);
        context.with_type_database(context.session().index(), |db| {
            db.alias_table = actor.table;
        });
        context.diagnostics.report()
    }
}

impl HirVisitor for Harvestor<'_> {
    fn visit_declaration(&mut self, declaration: &taroc_hir::Declaration) -> Self::Result {
        let def_id = self.context.def_id(declaration.id);

        match &declaration.kind {
            taroc_hir::DeclarationKind::Extend(node) => {
                self.harvest_extend(def_id, node);
            }
            taroc_hir::DeclarationKind::TypeAlias(node) => {
                self.harvest(def_id, declaration.identifier, node);
            }
            _ => return,
        }
    }
}

impl<'ctx> Harvestor<'ctx> {
    fn harvest_extend(&mut self, def_id: DefinitionID, node: &taroc_hir::Extend) {
        let target_ty = self.context.extension_key(def_id);

        for declaration in &node.declarations {
            let alias = match &declaration.kind {
                taroc_hir::AssociatedDeclarationKind::Type(node) => node,
                _ => {
                    continue;
                }
            };
            let name = declaration.identifier.symbol;
            let span = declaration.identifier.span;
            let alias_id = self.context.def_id(declaration.id);

            // quick validation
            if alias.ty.is_none() {
                let message = format!("associated type must be defined");
                self.context.diagnostics.error(message, span);
                continue;
            };

            if alias.generics.type_parameters.is_some() {
                let message = format!("associated type must not have type parameters");
                self.context.diagnostics.error(message, span);
                continue;
            }

            self.harvest(alias_id, declaration.identifier, alias);

            let bucket = self
                .table
                .by_type
                .entry(target_ty)
                .or_insert(Default::default());
            match bucket.aliases.entry(name) {
                std::collections::hash_map::Entry::Occupied(entry) => {
                    let message = format!("duplicate alias definition '{name}'");
                    self.context.diagnostics.error(message, span);
                    self.context
                        .diagnostics
                        .info(format!("'{name}' is defined here"), entry.get().1);
                    continue;
                }
                std::collections::hash_map::Entry::Vacant(entry) => {
                    entry.insert((alias_id, span));
                }
            }
        }
    }

    fn harvest(&mut self, def_id: DefinitionID, ident: Identifier, node: &taroc_hir::TypeAlias) {
        // println!("Harvesting Alias '{}'", ident.symbol);
        let span = ident.span;

        // quick validation
        let Some(ty) = &node.ty else {
            let message = format!("associated type must be defined");
            self.context.diagnostics.error(message, span);
            return;
        };

        self.table.aliases.insert(
            def_id,
            AliasEntry {
                ast_type: ty.clone(),
                span,
                ext_id: None,
                alias_id: def_id,
                symbol: ident.symbol,
            },
        );
    }
}

fn resolve(context: GlobalContext) -> CompileResult<()> {
    let package = context.session().index();
    let table = context.with_type_database(package, |db| db.alias_table.clone());
    let icx = ItemCtx::new(context);

    for (_, entry) in table.aliases.iter() {
        // println!("Resolving Alias '{}'", entry.symbol);
        let ty = icx
            .lowerer()
            .lower_type(&entry.ast_type, &LoweringRequest::default());
        context.cache_type(entry.alias_id, ty);
    }

    context.diagnostics.report()
}
