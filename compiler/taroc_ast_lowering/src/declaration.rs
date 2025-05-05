use super::package::Actor;
use taroc_hir::TypeKind;
use taroc_span::{Identifier, Span, Symbol};

impl Actor<'_> {
    pub fn lower_declaration(
        &mut self,
        declaration: taroc_ast::Declaration,
    ) -> taroc_hir::Declaration {
        taroc_hir::Declaration {
            id: self.next(),
            span: declaration.span,
            identifier: declaration.identifier,
            kind: self.lower_declaration_kind(declaration.kind),
            attributes: self.lower_attributes(declaration.attributes),
            visibility: self.lower_visibility(declaration.visibility),
        }
    }

    pub fn lower_associated_declaration(
        &mut self,
        declaration: taroc_ast::AssociatedDeclaration,
    ) -> taroc_hir::AssociatedDeclaration {
        taroc_hir::AssociatedDeclaration {
            id: self.next(),
            span: declaration.span,
            identifier: declaration.identifier,
            kind: self.lower_assoc_declaration_kind(declaration.kind),
            attributes: self.lower_attributes(declaration.attributes),
            visibility: self.lower_visibility(declaration.visibility),
        }
    }

    pub fn lower_foreign_declaration(
        &mut self,
        declaration: taroc_ast::ForeignDeclaration,
    ) -> taroc_hir::ForeignDeclaration {
        taroc_hir::ForeignDeclaration {
            id: self.next(),
            span: declaration.span,
            identifier: declaration.identifier,
            kind: self.lower_foreign_declaration_kind(declaration.kind),
            attributes: self.lower_attributes(declaration.attributes),
            visibility: self.lower_visibility(declaration.visibility),
        }
    }

    pub fn lower_function_declaration(
        &mut self,
        declaration: taroc_ast::FunctionDeclaration,
    ) -> taroc_hir::FunctionDeclaration {
        taroc_hir::FunctionDeclaration {
            id: self.next(),
            span: declaration.span,
            identifier: declaration.identifier,
            kind: self.lower_function_declaration_kind(declaration.kind),
            attributes: self.lower_attributes(declaration.attributes),
            visibility: self.lower_visibility(declaration.visibility),
        }
    }
}
impl Actor<'_> {
    fn lower_declaration_kind(
        &mut self,
        kind: taroc_ast::DeclarationKind,
    ) -> taroc_hir::DeclarationKind {
        match kind {
            taroc_ast::DeclarationKind::Function(function) => {
                taroc_hir::DeclarationKind::Function(self.lower_function(function))
            }
            taroc_ast::DeclarationKind::Variable(local) => {
                taroc_hir::DeclarationKind::Static(self.lower_local_to_static(local))
            }
            taroc_ast::DeclarationKind::Extend(extend) => {
                taroc_hir::DeclarationKind::Extend(self.lower_extend(extend))
            }
            taroc_ast::DeclarationKind::TypeAlias(type_alias) => {
                taroc_hir::DeclarationKind::TypeAlias(self.lower_type_alias(type_alias))
            }
            taroc_ast::DeclarationKind::Namespace(ns) => {
                taroc_hir::DeclarationKind::Namespace(self.lower_namspace(ns))
            }
            taroc_ast::DeclarationKind::Extern(extrn) => {
                taroc_hir::DeclarationKind::Extern(self.lower_extern(extrn))
            }
            taroc_ast::DeclarationKind::Import(tree) => {
                taroc_hir::DeclarationKind::Import(self.lower_path_tree(tree))
            }
            taroc_ast::DeclarationKind::Export(tree) => {
                taroc_hir::DeclarationKind::Export(self.lower_path_tree(tree))
            }
            taroc_ast::DeclarationKind::Constant(node) => {
                taroc_hir::DeclarationKind::Constant(self.lower_constant_decl(node))
            }
            taroc_ast::DeclarationKind::Interface(node) => {
                taroc_hir::DeclarationKind::Interface(self.lower_interface_definition(node))
            }
            taroc_ast::DeclarationKind::Struct(node) => {
                taroc_hir::DeclarationKind::Struct(self.lower_struct_definition(node))
            }
            taroc_ast::DeclarationKind::Enum(node) => {
                taroc_hir::DeclarationKind::Enum(self.lower_enum_definition(node))
            }
            taroc_ast::DeclarationKind::Bridge(..) => todo!("bridge declaration"),
            taroc_ast::DeclarationKind::Operator(..) => {
                unreachable!("top level operators must be caught by")
            }
        }
    }

    fn lower_assoc_declaration_kind(
        &mut self,
        kind: taroc_ast::AssociatedDeclarationKind,
    ) -> taroc_hir::AssociatedDeclarationKind {
        match kind {
            taroc_ast::AssociatedDeclarationKind::Constant(node) => {
                taroc_hir::AssociatedDeclarationKind::Constant(self.lower_constant_decl(node))
            }
            taroc_ast::AssociatedDeclarationKind::Function(node) => {
                taroc_hir::AssociatedDeclarationKind::Function(self.lower_function(node))
            }
            taroc_ast::AssociatedDeclarationKind::Type(node) => {
                taroc_hir::AssociatedDeclarationKind::Type(self.lower_type_alias(node))
            }
            taroc_ast::AssociatedDeclarationKind::Operator(operator_kind, function) => {
                taroc_hir::AssociatedDeclarationKind::Operator(
                    operator_kind,
                    self.lower_function(function),
                )
            }
        }
    }

    fn lower_foreign_declaration_kind(
        &mut self,
        kind: taroc_ast::ForeignDeclarationKind,
    ) -> taroc_hir::ForeignDeclarationKind {
        match kind {
            taroc_ast::ForeignDeclarationKind::Function(node) => {
                taroc_hir::ForeignDeclarationKind::Function(self.lower_function(node))
            }
            taroc_ast::ForeignDeclarationKind::Type(node) => {
                taroc_hir::ForeignDeclarationKind::Type(self.lower_type_alias(node))
            }
        }
    }

    fn lower_function_declaration_kind(
        &mut self,
        kind: taroc_ast::FunctionDeclarationKind,
    ) -> taroc_hir::FunctionDeclarationKind {
        match kind {
            taroc_ast::FunctionDeclarationKind::Function(node) => {
                taroc_hir::FunctionDeclarationKind::Function(self.lower_function(node))
            }
            taroc_ast::FunctionDeclarationKind::Struct(node) => {
                taroc_hir::FunctionDeclarationKind::Struct(self.lower_struct_definition(node))
            }
            taroc_ast::FunctionDeclarationKind::Enum(node) => {
                taroc_hir::FunctionDeclarationKind::Enum(self.lower_enum_definition(node))
            }
            taroc_ast::FunctionDeclarationKind::Constant(node) => {
                taroc_hir::FunctionDeclarationKind::Constant(self.lower_constant_decl(node))
            }
            taroc_ast::FunctionDeclarationKind::Import(node) => {
                taroc_hir::FunctionDeclarationKind::Import(self.lower_path_tree(node))
            }
            taroc_ast::FunctionDeclarationKind::TypeAlias(node) => {
                taroc_hir::FunctionDeclarationKind::TypeAlias(self.lower_type_alias(node))
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
            declarations: self
                .lower_sequence(namespace.declarations, |a, d| a.lower_declaration(d)),
        }
    }

    fn lower_extend(&mut self, e: taroc_ast::Extend) -> taroc_hir::Extend {
        taroc_hir::Extend {
            declarations: self
                .lower_sequence(e.declarations, |a, d| a.lower_associated_declaration(d)),
            ty: self.lower_type(e.ty),
            generics: self.lower_generics(e.generics),
        }
    }
}

impl Actor<'_> {
    fn lower_extern(&mut self, e: taroc_ast::Extern) -> taroc_hir::Extern {
        taroc_hir::Extern {
            abi: taroc_span::Spanned {
                span: e.abi.span,
                value: self.lower_abi(e.abi.value, e.abi.span),
            },
            declarations: self
                .lower_sequence(e.declarations, |a, d| a.lower_foreign_declaration(d)),
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

impl Actor<'_> {
    fn lower_constant_decl(
        &mut self,
        node: taroc_ast::ConstantDeclaration,
    ) -> taroc_hir::ConstantDeclaration {
        taroc_hir::ConstantDeclaration {
            identifier: node.identifier,
            ty: self.lower_type(node.ty),
            expr: self.lower_optional(node.expr, |this, expr| this.lower_expression(expr)),
        }
    }
}

impl Actor<'_> {
    fn lower_struct_definition(
        &mut self,
        node: taroc_ast::StructDefinition,
    ) -> taroc_hir::StructDefinition {
        taroc_hir::StructDefinition {
            generics: self.lower_generics(node.generics),
            variant: self.lower_variant_kind(node.variant),
        }
    }

    fn lower_enum_definition(
        &mut self,
        node: taroc_ast::EnumDefinition,
    ) -> taroc_hir::EnumDefinition {
        taroc_hir::EnumDefinition {
            generics: self.lower_generics(node.generics),
            variants: self
                .lower_sequence(node.variants, |this, variant| this.lower_variant(variant)),
        }
    }

    fn lower_interface_definition(
        &mut self,
        node: taroc_ast::InterfaceDefinition,
    ) -> taroc_hir::InterfaceDefinition {
        taroc_hir::InterfaceDefinition {
            generics: self.lower_generics(node.generics),
            declarations: self.lower_sequence(node.declarations, |this, variant| {
                this.lower_associated_declaration(variant)
            }),
        }
    }
}

impl Actor<'_> {
    fn lower_local_to_static(&mut self, local: taroc_ast::Local) -> taroc_hir::StaticDeclaration {
        let identifier = match local.pattern.kind {
            taroc_ast::BindingPatternKind::Identifier(identifier) => identifier,
            _ => {
                self.context.diagnostics.error(
                    "static variables must be an identifier binding".into(),
                    local.pattern.span,
                );
                Identifier::emtpy(local.pattern.span.file)
            }
        };
        let ty = if let Some(ty) = local.ty {
            self.lower_type(ty)
        } else {
            self.mk_ty(TypeKind::Malformed, local.pattern.span)
        };

        let expr = self.lower_optional(local.initializer, |this, expr| this.lower_expression(expr));

        taroc_hir::StaticDeclaration {
            identifier,
            ty,
            expr,
        }
    }
}
