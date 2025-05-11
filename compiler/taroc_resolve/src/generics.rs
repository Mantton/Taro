use rustc_hash::FxHashMap;
use std::collections::hash_map::Entry;
use taroc_error::CompileResult;
use taroc_hir::{DefinitionID, DefinitionKind, PartialResolution, Resolution, visitor::HirVisitor};
use taroc_span::{Span, Symbol};

use crate::resolver::Resolver;

pub struct GenericsCollector<'res, 'ctx> {
    pub resolver: &'res mut Resolver<'ctx>,
    pub parent: Option<DefinitionID>,
    pub table: FxHashMap<DefinitionID, Vec<(Symbol, DefinitionID)>>,
}

impl<'res, 'ctx> GenericsCollector<'res, 'ctx> {
    pub fn run(
        package: &taroc_hir::Package,
        resolver: &'res mut Resolver<'ctx>,
    ) -> CompileResult<()> {
        let mut actor = GenericsCollector {
            resolver,
            parent: None,
            table: Default::default(),
        };
        taroc_hir::visitor::walk_package(&mut actor, package);
        actor.resolver.generics_table = actor.table;
        actor.resolver.gcx.diagnostics.report()
    }
}

impl HirVisitor for GenericsCollector<'_, '_> {
    fn visit_declaration(&mut self, d: &taroc_hir::Declaration) -> Self::Result {
        let def_id = self.resolver.def_id(d.id);
        self.parent = Some(def_id);
        taroc_hir::visitor::walk_declaration(self, d);
    }

    fn visit_function_declaration(&mut self, d: &taroc_hir::FunctionDeclaration) -> Self::Result {
        let def_id = self.resolver.def_id(d.id);
        self.parent = Some(def_id);
        taroc_hir::visitor::walk_function_declaration(self, d);
    }

    fn visit_assoc_declaration(
        &mut self,
        declaration: &taroc_hir::AssociatedDeclaration,
        context: taroc_hir::visitor::AssocContext,
    ) -> Self::Result {
        let def_id = self.resolver.def_id(declaration.id);
        self.parent = Some(def_id);
        taroc_hir::visitor::walk_assoc_declaration(self, declaration, context);
    }

    fn visit_foreign_declaration(&mut self, d: &taroc_hir::ForeignDeclaration) -> Self::Result {
        let def_id = self.resolver.def_id(d.id);
        self.parent = Some(def_id);
        taroc_hir::visitor::walk_foreign_declaration(self, d);
    }

    fn visit_type_parameters(&mut self, t: &taroc_hir::TypeParameters) -> Self::Result {
        let gcx = self.resolver.gcx;
        let params = &t.parameters;
        let parent = self.parent.unwrap();

        if params.is_empty() {
            return;
        }

        let mut items = vec![];
        let mut seen_bindings: FxHashMap<Symbol, Span> = Default::default();

        for param in params.iter() {
            let def_id = self.resolver.def_id(param.id);
            let kind = DefinitionKind::TypeParameter;
            let name = param.identifier.symbol.clone();
            let entry = seen_bindings.entry(name.clone());

            match entry {
                Entry::Occupied(_) => {
                    // param has already been defined
                    let msg = format!("TypeParameter '{name}' is already defined");
                    gcx.diagnostics.error(msg, param.identifier.span);
                    continue;
                }
                Entry::Vacant(entry) => {
                    // mark as seen
                    entry.insert(param.identifier.span);
                }
            }

            items.push((name, def_id));

            let res = Resolution::Definition(def_id, kind);
            self.resolver
                .record_resolution(param.id, PartialResolution::new(res.clone()));
        }

        self.table.insert(parent, items);
    }
}
