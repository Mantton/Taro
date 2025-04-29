use super::resolver::Resolver;
use taroc_hir::{
    DefinitionID, DefinitionIndex, DefinitionKind, NodeID, PackageIndex,
    visitor::{HirVisitor, walk_declaration, walk_module, walk_package, walk_path_tree},
};
use taroc_span::Symbol;

pub struct HirNodeTagger<'res, 'ctx> {
    resolver: &'res mut Resolver<'ctx>,
    parent: DefinitionID,
}

impl<'res, 'ctx> HirNodeTagger<'res, 'ctx> {
    pub fn run(package: &taroc_hir::Package, resolver: &'res mut Resolver<'ctx>) {
        let mut actor = HirNodeTagger {
            resolver,
            parent: DefinitionID::new(PackageIndex::new(0), DefinitionIndex::new(0)),
        };
        walk_package(&mut actor, package);
    }

    fn tag(&mut self, symbol: Symbol, node: NodeID, kind: DefinitionKind) -> DefinitionID {
        self.resolver.create_def(symbol, node, kind, self.parent)
    }

    fn with_parent<F: FnOnce(&mut Self)>(&mut self, parent: DefinitionID, f: F) {
        let original = std::mem::replace(&mut self.parent, parent);
        f(self);
        self.parent = original;
    }
}

impl HirVisitor for HirNodeTagger<'_, '_> {
    fn visit_module(&mut self, m: &taroc_hir::Module) -> <Self as HirVisitor>::Result {
        self.tag(m.name, m.id, DefinitionKind::Module);
        walk_module(self, m)
    }

    fn visit_declaration(
        &mut self,
        d: &taroc_hir::Declaration,
        c: taroc_hir::DeclarationContext,
    ) -> <Self as HirVisitor>::Result {
        let kind = match &d.kind {
            taroc_hir::DeclarationKind::Function(..) => DefinitionKind::Function,
            taroc_hir::DeclarationKind::Constructor(..) => DefinitionKind::Constructor,
            taroc_hir::DeclarationKind::Variable(..) => DefinitionKind::Variable,
            taroc_hir::DeclarationKind::Import(..) => DefinitionKind::Import,
            taroc_hir::DeclarationKind::Extend(..) => DefinitionKind::Extension,
            taroc_hir::DeclarationKind::TypeAlias(..) => DefinitionKind::TypeAlias,
            taroc_hir::DeclarationKind::Extern(..) => DefinitionKind::Extern,
            taroc_hir::DeclarationKind::Namespace(..) => DefinitionKind::Namespace,
            taroc_hir::DeclarationKind::Bridge(..) => DefinitionKind::Bridged,
            taroc_hir::DeclarationKind::Export(..) => DefinitionKind::Export,
            taroc_hir::DeclarationKind::AssociatedType(..) => DefinitionKind::AssociatedType,
            taroc_hir::DeclarationKind::Constant(..) => DefinitionKind::Constant,
            taroc_hir::DeclarationKind::Operator(..) => DefinitionKind::Operator,
            taroc_hir::DeclarationKind::EnumCase(..) => DefinitionKind::EnumCase,
            taroc_hir::DeclarationKind::DefinedType(ty) => match &ty.kind {
                taroc_hir::DefinedTypeKind::Struct => DefinitionKind::Struct,
                taroc_hir::DefinedTypeKind::Enum => DefinitionKind::Enum,
                taroc_hir::DefinedTypeKind::Interface => DefinitionKind::Interface,
            },
        };

        let parent = self.tag(d.identifier.symbol, d.id, kind);

        self.with_parent(parent, |actor| {
            walk_declaration(actor, d, c);
        });
    }

    fn visit_type_parameter(
        &mut self,
        t: &taroc_hir::TypeParameter,
    ) -> <Self as HirVisitor>::Result {
        self.tag(t.identifier.symbol, t.id, DefinitionKind::TypeParameter);
    }

    fn visit_field_definition(
        &mut self,
        f: &taroc_hir::FieldDefinition,
    ) -> <Self as HirVisitor>::Result {
        self.tag(f.identifier.symbol, f.id, DefinitionKind::Field);
    }

    fn visit_variant(&mut self, v: &taroc_hir::Variant) -> <Self as HirVisitor>::Result {
        // Register Enum Variant Constructors
        self.tag(v.identifier.symbol, v.id, DefinitionKind::Variant);
    }

    fn visit_path_tree(
        &mut self,
        node: &taroc_hir::PathTree,
        id: NodeID,
        _is_nested: bool,
        is_import: bool,
    ) -> <Self as HirVisitor>::Result {
        let k = if is_import {
            DefinitionKind::Import
        } else {
            DefinitionKind::Export
        };

        self.tag(Symbol::with(""), id, k);
        walk_path_tree(self, node, id, is_import)
    }
}
