use crate::{
    ast::{self, AstVisitor, Identifier, NodeID, walk_package},
    error::CompileResult,
    sema::resolve::{
        models::{CtorKind, CtorOf, DefinitionID, DefinitionIndex, DefinitionKind},
        resolver::Resolver,
    },
    span::{FileID, Span},
};
use ecow::EcoString;

pub fn tag_package_symbols(package: &ast::Package, resolver: &mut Resolver) -> CompileResult<()> {
    let mut actor = Actor {
        parent: None,
        resolver,
    };
    walk_package(&mut actor, package);
    resolver.compiler.dcx.ok()
}

struct Actor<'resolver, 'arena, 'compiler> {
    parent: Option<DefinitionID>,
    resolver: &'resolver mut Resolver<'arena, 'compiler>,
}

impl<'r, 'a, 'c> AstVisitor for Actor<'r, 'a, 'c> {
    fn visit_module(&mut self, node: &ast::Module, is_root: bool) -> Self::Result {
        let name = Identifier {
            span: Span::empty(FileID::new(0)),
            symbol: node.name.clone(),
        };
        let parent = self.tag(&name, node.id, DefinitionKind::Module);
        self.with_parent(parent, |this| ast::walk_module(this, node));
    }
    fn visit_declaration(&mut self, node: &ast::Declaration) -> Self::Result {
        let kind = match &node.kind {
            ast::DeclarationKind::Interface(..) => DefinitionKind::Interface,
            ast::DeclarationKind::Struct(..) => DefinitionKind::Struct,
            ast::DeclarationKind::Enum(..) => DefinitionKind::Enum,
            ast::DeclarationKind::Function(..) => DefinitionKind::Function,
            ast::DeclarationKind::Variable(..) => DefinitionKind::ModuleVariable,
            ast::DeclarationKind::Constant(..) => DefinitionKind::Constant,
            ast::DeclarationKind::Import(..) => DefinitionKind::Import,
            ast::DeclarationKind::Export(..) => DefinitionKind::Export,
            ast::DeclarationKind::Implementation(..) => DefinitionKind::Extension,
            ast::DeclarationKind::TypeAlias(..) => DefinitionKind::TypeAlias,
            ast::DeclarationKind::Namespace(..) => DefinitionKind::Namespace,
            ast::DeclarationKind::Initializer(..) => unreachable!("top level initializer"),
        };

        let parent = self.tag(&node.identifier, node.id, kind);
        self.with_parent(parent, |this| {
            ast::walk_declaration(this, node);
        });
    }

    fn visit_function_declaration(&mut self, node: &ast::FunctionDeclaration) -> Self::Result {
        let kind = match &node.kind {
            ast::FunctionDeclarationKind::Struct(..) => DefinitionKind::Struct,
            ast::FunctionDeclarationKind::Enum(..) => DefinitionKind::Enum,
            ast::FunctionDeclarationKind::Function(..) => DefinitionKind::Function,
            ast::FunctionDeclarationKind::Constant(..) => DefinitionKind::Constant,
            ast::FunctionDeclarationKind::TypeAlias(..) => DefinitionKind::TypeAlias,
            ast::FunctionDeclarationKind::Import(..) => DefinitionKind::Import,
        };
        let parent = self.tag(&node.identifier, node.id, kind);
        self.with_parent(parent, |this| {
            ast::walk_function_declaration(this, node);
        });
    }

    fn visit_assoc_declaration(
        &mut self,
        node: &ast::AssociatedDeclaration,
        context: ast::AssocContext,
    ) -> Self::Result {
        let kind = match &node.kind {
            ast::AssociatedDeclarationKind::Constant(..) => DefinitionKind::AssociatedConstant,
            ast::AssociatedDeclarationKind::Function(..) => DefinitionKind::AssociatedFunction,
            ast::AssociatedDeclarationKind::Initializer(..) => {
                DefinitionKind::AssociatedInitializer
            }
            ast::AssociatedDeclarationKind::Type(type_alias) => DefinitionKind::AssociatedType,
        };
        let parent = self.tag(&node.identifier, node.id, kind);
        self.with_parent(parent, |this| {
            ast::walk_assoc_declaration(this, node, context);
        });
    }

    fn visit_namespace_declaration(&mut self, node: &ast::NamespaceDeclaration) -> Self::Result {
        let kind = match &node.kind {
            ast::NamespaceDeclarationKind::Struct(..) => DefinitionKind::Struct,
            ast::NamespaceDeclarationKind::Enum(..) => DefinitionKind::Enum,
            ast::NamespaceDeclarationKind::Function(..) => DefinitionKind::Function,
            ast::NamespaceDeclarationKind::Constant(..) => DefinitionKind::Constant,
            ast::NamespaceDeclarationKind::TypeAlias(..) => DefinitionKind::TypeAlias,
            ast::NamespaceDeclarationKind::Namespace(..) => DefinitionKind::Namespace,
            ast::NamespaceDeclarationKind::Interface(..) => DefinitionKind::Interface,
            ast::NamespaceDeclarationKind::Import(..) => DefinitionKind::Import,
            ast::NamespaceDeclarationKind::Export(..) => DefinitionKind::Export,
        };
        let parent = self.tag(&node.identifier, node.id, kind);
        self.with_parent(parent, |this| {
            ast::walk_namespace_declaration(this, node);
        });
    }

    fn visit_type_parameter(&mut self, node: &ast::TypeParameter) -> Self::Result {
        let kind = match &node.kind {
            ast::TypeParameterKind::Type { .. } => DefinitionKind::TypeParameter,
            ast::TypeParameterKind::Constant { .. } => DefinitionKind::ConstParameter,
        };
        self.tag(&node.identifier, node.id, kind);
    }

    fn visit_field_definition(&mut self, node: &ast::FieldDefinition) -> Self::Result {
        let kind = DefinitionKind::Field;
        self.tag(&node.identifier, node.id, kind);
    }

    fn visit_enum_variant(&mut self, node: &ast::Variant) -> Self::Result {
        let variant_id = self.tag(&node.identifier, node.id, DefinitionKind::EnumVariant);
        {
            let ctor_kind = CtorKind::from_variant(&node.kind);
            self.tag(
                &node.identifier,
                node.ctor_id,
                DefinitionKind::Ctor(CtorOf::EnumVariant, ctor_kind),
            );
        }

        self.with_parent(variant_id, |this| ast::walk_enum_variant(this, node));
    }

    fn visit_struct_definition(&mut self, node: &ast::Struct) -> Self::Result {
        let parent = self.parent.expect("struct definition node to be tagged");
        let kind = DefinitionKind::Ctor(CtorOf::Struct, CtorKind::Function);
        let identifier = self
            .resolver
            .def_to_ident
            .get(&parent)
            .expect("struct declaration to be tagged")
            .clone();
        self.tag(&identifier, node.ctor_node_id, kind);
        ast::walk_struct_definition(self, node);
    }

    fn visit_use_tree(
        &mut self,
        node: &ast::UseTree,
        context: ast::UseTreeContext,
    ) -> Self::Result {
        let (id, kind) = match context {
            ast::UseTreeContext::Import(id) => (id, DefinitionKind::Import),
            ast::UseTreeContext::Export(id) => (id, DefinitionKind::Export),
        };

        match &node.kind {
            ast::UseTreeKind::Glob => {
                // TODO: Do we want to tag glob nodes?
            }
            ast::UseTreeKind::Simple { alias } => {
                let name = if let Some(name) = alias {
                    name
                } else if let Some(name) = node.path.nodes.last() {
                    name
                } else {
                    unreachable!("malformed import path")
                };
                self.tag(name, id, kind);
            }
            ast::UseTreeKind::Nested { nodes, .. } => {
                for node in nodes {
                    let name = if let Some(name) = &node.alias {
                        name
                    } else {
                        &node.name
                    };
                    self.tag(name, id, kind);
                }
            }
        }
    }
}

impl<'r, 'a, 'c> Actor<'r, 'a, 'c> {
    fn tag(&mut self, name: &Identifier, node_id: NodeID, kind: DefinitionKind) -> DefinitionID {
        let id = self
            .resolver
            .create_definition(name, node_id, kind, self.parent);
        id
    }

    fn with_parent<F: FnOnce(&mut Self)>(&mut self, parent: DefinitionID, action: F) {
        let original = std::mem::replace(&mut self.parent, Some(parent));
        action(self);
        self.parent = original;
    }
}
