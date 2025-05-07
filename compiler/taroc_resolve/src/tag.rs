use super::resolver::Resolver;
use taroc_hir::{
    CtorKind, CtorOf, DeclarationKind, DefinitionID, DefinitionIndex, DefinitionKind,
    FunctionDeclarationKind, NodeID, PackageIndex,
    visitor::{
        self, HirVisitor, walk_declaration, walk_function_declaration, walk_module, walk_package,
        walk_path_tree,
    },
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

    fn visit_declaration(&mut self, d: &taroc_hir::Declaration) -> <Self as HirVisitor>::Result {
        let kind = match &d.kind {
            taroc_hir::DeclarationKind::Function(..) => DefinitionKind::Function,
            taroc_hir::DeclarationKind::Static(..) => DefinitionKind::StaticVariable,
            taroc_hir::DeclarationKind::Import(..) => DefinitionKind::Import,
            taroc_hir::DeclarationKind::Extend(..) => DefinitionKind::Extension,
            taroc_hir::DeclarationKind::TypeAlias(..) => DefinitionKind::TypeAlias,
            taroc_hir::DeclarationKind::Extern(..) => DefinitionKind::Extern,
            taroc_hir::DeclarationKind::Namespace(..) => DefinitionKind::Namespace,
            taroc_hir::DeclarationKind::Bridge(..) => DefinitionKind::Bridged,
            taroc_hir::DeclarationKind::Export(..) => DefinitionKind::Export,
            taroc_hir::DeclarationKind::Constant(..) => DefinitionKind::Constant,
            taroc_hir::DeclarationKind::Interface(..) => DefinitionKind::Interface,
            taroc_hir::DeclarationKind::Struct(..) => DefinitionKind::Struct,
            taroc_hir::DeclarationKind::Enum(..) => DefinitionKind::Enum,
            DeclarationKind::Malformed => unreachable!(),
        };

        let parent = self.tag(d.identifier.symbol, d.id, kind);

        self.with_parent(parent, |actor| {
            match &d.kind {
                DeclarationKind::Struct(data) => {
                    if let Some((kind, id)) = CtorKind::from_variant(&data.variant) {
                        let kind = DefinitionKind::Ctor(CtorOf::Struct, kind);
                        actor.tag(d.identifier.symbol, id, kind);
                    }
                }
                _ => {}
            }

            walk_declaration(actor, d);
        });
    }

    fn visit_function_declaration(
        &mut self,
        d: &taroc_hir::FunctionDeclaration,
    ) -> <Self as HirVisitor>::Result {
        let kind = match &d.kind {
            taroc_hir::FunctionDeclarationKind::Function(..) => DefinitionKind::Function,
            taroc_hir::FunctionDeclarationKind::Import(..) => DefinitionKind::Import,
            taroc_hir::FunctionDeclarationKind::TypeAlias(..) => DefinitionKind::TypeAlias,
            taroc_hir::FunctionDeclarationKind::Constant(..) => DefinitionKind::Constant,
            taroc_hir::FunctionDeclarationKind::Struct(..) => DefinitionKind::Struct,
            taroc_hir::FunctionDeclarationKind::Enum(..) => DefinitionKind::Enum,
        };

        let parent = self.tag(d.identifier.symbol, d.id, kind);

        self.with_parent(parent, |actor| {
            match &d.kind {
                FunctionDeclarationKind::Struct(data) => {
                    if let Some((kind, id)) = CtorKind::from_variant(&data.variant) {
                        let kind = DefinitionKind::Ctor(CtorOf::Struct, kind);
                        actor.tag(d.identifier.symbol, id, kind);
                    }
                }
                _ => {}
            }

            walk_function_declaration(actor, d);
        });
    }

    fn visit_assoc_declaration(
        &mut self,
        declaration: &taroc_hir::AssociatedDeclaration,
        context: taroc_hir::visitor::AssocContext,
    ) -> Self::Result {
        let kind = match &declaration.kind {
            taroc_hir::AssociatedDeclarationKind::Constant(..) => {
                DefinitionKind::AssociatedConstant
            }
            taroc_hir::AssociatedDeclarationKind::Function(..) => {
                DefinitionKind::AssociatedFunction
            }
            taroc_hir::AssociatedDeclarationKind::Type(..) => DefinitionKind::AssociatedType,
            taroc_hir::AssociatedDeclarationKind::Operator(..) => {
                DefinitionKind::AssociatedOperator
            }
        };

        let parent = self.tag(declaration.identifier.symbol, declaration.id, kind);

        self.with_parent(parent, |actor| {
            taroc_hir::visitor::walk_assoc_declaration(actor, declaration, context);
        });
    }

    fn visit_foreign_declaration(&mut self, d: &taroc_hir::ForeignDeclaration) -> Self::Result {
        let kind = match &d.kind {
            taroc_hir::ForeignDeclarationKind::Function(..) => DefinitionKind::Function,
            taroc_hir::ForeignDeclarationKind::Type(..) => DefinitionKind::TypeAlias,
        };

        let parent = self.tag(d.identifier.symbol, d.id, kind);

        self.with_parent(parent, |actor| {
            taroc_hir::visitor::walk_foreign_declaration(actor, d);
        });
    }

    fn visit_type_parameter(
        &mut self,
        t: &taroc_hir::TypeParameter,
    ) -> <Self as HirVisitor>::Result {
        let k = match &t.kind {
            taroc_hir::TypeParameterKind::Type { .. } => DefinitionKind::TypeParameter,
            taroc_hir::TypeParameterKind::Constant { .. } => DefinitionKind::ConstParameter,
        };
        self.tag(t.identifier.symbol, t.id, k);
    }

    fn visit_field_definition(
        &mut self,
        f: &taroc_hir::FieldDefinition,
    ) -> <Self as HirVisitor>::Result {
        self.tag(f.identifier.symbol, f.id, DefinitionKind::Field);
    }

    fn visit_variant(&mut self, v: &taroc_hir::Variant) -> <Self as HirVisitor>::Result {
        let parent = self.tag(v.identifier.symbol, v.id, DefinitionKind::Variant);

        self.with_parent(parent, |this| {
            if let Some((kind, id)) = CtorKind::from_variant(&v.kind) {
                this.tag(
                    v.identifier.symbol,
                    id,
                    DefinitionKind::Ctor(CtorOf::Variant, kind),
                );

                visitor::walk_variant(this, v)
            }
        });
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
