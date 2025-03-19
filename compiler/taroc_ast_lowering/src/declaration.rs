use taroc_ast::{self, DeclarationContext};
use taroc_span::{Span, Symbol};

use super::package::Actor;

impl Actor<'_> {
    pub fn lower_declaration(
        &mut self,
        declaration: taroc_ast::Declaration,
        context: DeclarationContext,
    ) -> taroc_hir::Declaration {
        taroc_hir::Declaration {
            id: self.next(),
            span: declaration.span,
            identifier: declaration.identifier,
            kind: self.lower_declaration_kind(declaration.kind, context),
            attributes: self.lower_attributes(declaration.attributes),
            visibility: self.lower_visibility(declaration.visibility),
        }
    }

    fn lower_declaration_kind(
        &mut self,
        kind: taroc_ast::DeclarationKind,
        _: DeclarationContext,
    ) -> taroc_hir::DeclarationKind {
        match kind {
            taroc_ast::DeclarationKind::Function(function) => {
                taroc_hir::DeclarationKind::Function(self.lower_function(function))
            }
            taroc_ast::DeclarationKind::Constructor(function, is_optional) => {
                taroc_hir::DeclarationKind::Constructor(self.lower_function(function), is_optional)
            }
            taroc_ast::DeclarationKind::Variable(local) => {
                taroc_hir::DeclarationKind::Variable(self.lower_local(local))
            }
            taroc_ast::DeclarationKind::Interface(interface) => {
                taroc_hir::DeclarationKind::Interface(self.lower_interface(interface))
            }
            taroc_ast::DeclarationKind::Extend(extend) => {
                taroc_hir::DeclarationKind::Extend(self.lower_extend(extend))
            }
            taroc_ast::DeclarationKind::Conform(conform) => {
                taroc_hir::DeclarationKind::Conform(self.lower_conform(conform))
            }
            taroc_ast::DeclarationKind::TypeAlias(type_alias) => {
                taroc_hir::DeclarationKind::TypeAlias(self.lower_type_alias(type_alias))
            }
            taroc_ast::DeclarationKind::Struct(s) => {
                taroc_hir::DeclarationKind::Struct(self.lower_struct(s))
            }
            taroc_ast::DeclarationKind::Enum(value) => {
                taroc_hir::DeclarationKind::Enum(self.lower_enum(value))
            }
            taroc_ast::DeclarationKind::Namespace(ns) => {
                taroc_hir::DeclarationKind::Namespace(self.lower_namspace(ns))
            }
            taroc_ast::DeclarationKind::Extern(extrn) => {
                taroc_hir::DeclarationKind::Extern(self.lower_extern(extrn))
            }
            taroc_ast::DeclarationKind::Bridge(..) => todo!(),
            taroc_ast::DeclarationKind::Import(tree) => {
                taroc_hir::DeclarationKind::Import(self.lower_path_tree(tree))
            }
            taroc_ast::DeclarationKind::Export(tree) => {
                taroc_hir::DeclarationKind::Export(self.lower_path_tree(tree))
            }
            taroc_ast::DeclarationKind::Computed(node) => {
                taroc_hir::DeclarationKind::Computed(self.lower_computed_var(node))
            }
        }
    }
}

impl Actor<'_> {
    fn lower_type_alias(&mut self, alias: taroc_ast::TypeAlias) -> taroc_hir::TypeAlias {
        let ty = self.lower_optional(alias.ty, |a, ty| a.lower_type(ty));
        let generics = self.lower_generics(alias.generics);

        taroc_hir::TypeAlias { ty, generics }
    }

    fn lower_namspace(&mut self, namespace: taroc_ast::Namespace) -> taroc_hir::Namespace {
        taroc_hir::Namespace {
            declarations: self.lower_sequence(namespace.declarations, |a, d| {
                a.lower_declaration(d, DeclarationContext::Namespace)
            }),
        }
    }

    fn lower_interface(&mut self, e: taroc_ast::Interface) -> taroc_hir::Interface {
        taroc_hir::Interface {
            declarations: self.lower_sequence(e.declarations, |a, d| {
                a.lower_declaration(d, DeclarationContext::Interface)
            }),
            extensions: self.lower_optional(e.extensions, |a1, paths| {
                a1.lower_sequence(paths, |a2, path| a2.lower_path(path))
            }),
            generics: self.lower_generics(e.generics),
        }
    }

    fn lower_conform(&mut self, e: taroc_ast::Conform) -> taroc_hir::Conform {
        taroc_hir::Conform {
            declarations: self.lower_sequence(e.declarations, |a, d| {
                a.lower_declaration(d, DeclarationContext::Conform)
            }),
            ty: self.lower_path(e.ty),
            interface: self.lower_path(e.interface),
            generics: self.lower_generics(e.generics),
            ty_ref_id: self.next(),
            interface_ref_id: self.next(),
        }
    }

    fn lower_extend(&mut self, e: taroc_ast::Extend) -> taroc_hir::Extend {
        taroc_hir::Extend {
            declarations: self.lower_sequence(e.declarations, |a, d| {
                a.lower_declaration(d, DeclarationContext::Extern)
            }),
            ty: self.lower_path(e.ty),
            generics: self.lower_generics(e.generics),
            ty_ref_id: self.next(),
        }
    }
}

impl Actor<'_> {
    fn lower_extern(&mut self, e: taroc_ast::Extern) -> taroc_hir::Extern {
        taroc_hir::Extern {
            abi: self.lower_abi(e.abi, e.span),
            declarations: self.lower_sequence(e.declarations, |a, d| {
                a.lower_declaration(d, DeclarationContext::Extern)
            }),
        }
    }

    fn lower_abi(&mut self, abi: Symbol, span: Span) -> taroc_hir::Abi {
        match abi.as_str() {
            "c" | "C" => taroc_hir::Abi::C,
            "taro-intrinsic" => taroc_hir::Abi::TaroInstrinsic,
            _ => {
                self.context.diagnostics.error("unknown abi".into(), span);
                taroc_hir::Abi::Error
            }
        }
    }
}

impl Actor<'_> {
    fn lower_computed_var(
        &mut self,
        node: taroc_ast::ComputedVariable,
    ) -> taroc_hir::ComputedProperty {
        taroc_hir::ComputedProperty {
            id: self.next(),
            ty: self.lower_type(node.ty),
            block: self.lower_optional(node.block, |this, node| this.lower_block(node)),
        }
    }
}

impl Actor<'_> {
    fn lower_path_tree(&mut self, tree: taroc_ast::PathTree) -> taroc_hir::PathTree {
        taroc_hir::PathTree {
            root: self.lower_path(tree.root),
            node: self.lower_path_tree_node(tree.node),
            span: tree.span,
        }
    }
    fn lower_path_tree_node(&mut self, node: taroc_ast::PathTreeNode) -> taroc_hir::PathTreeNode {
        match node {
            taroc_ast::PathTreeNode::Simple { alias } => taroc_hir::PathTreeNode::Simple { alias },
            taroc_ast::PathTreeNode::Glob => taroc_hir::PathTreeNode::Glob,
            taroc_ast::PathTreeNode::Nested { nodes, span } => {
                let nodes = nodes
                    .into_iter()
                    .map(|node| (self.lower_path_tree(node), self.next()))
                    .collect();

                taroc_hir::PathTreeNode::Nested { nodes, span }
            }
        }
    }
}
