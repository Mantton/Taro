use std::cell::Cell;

use crate::{
    ast::{self, AssocContext, AstVisitor, Identifier, NodeID, UseTree, UseTreeKind, walk_package},
    error::CompileResult,
    sema::resolve::{
        models::{
            ActiveScope, DefinitionKind, Resolution, Scope, ScopeData, ScopeKind, ScopeNamespace,
            UsageBinding, UsageEntryData, UsageKind,
        },
        resolver::Resolver,
    },
    span::{FileID, Span},
};

pub fn define_package_symbols(
    package: &ast::Package,
    resolver: &mut Resolver,
) -> CompileResult<()> {
    let mut actor = Actor::new(resolver);
    walk_package(&mut actor, package);
    resolver.context.dcx.ok()
}

pub struct Actor<'r, 'a> {
    resolver: &'r mut Resolver<'a>,
    scopes: ActiveScope<'a>,
}

impl<'r, 'a> Actor<'r, 'a> {
    fn new(resolver: &'r mut Resolver<'a>) -> Actor<'r, 'a> {
        Actor {
            resolver,
            scopes: ActiveScope {
                current: None,
                file: None,
            },
        }
    }
}

impl<'r, 'a> AstVisitor for Actor<'r, 'a> {
    fn visit_module(&mut self, node: &ast::Module, is_root: bool) -> Self::Result {
        let id = self.resolver.definition_id(node.id);
        let kind = ScopeKind::Definition(id, DefinitionKind::Module);
        let parent = self.scopes.current;
        let scope = ScopeData::new(kind, parent);
        let scope = self.create_scope(scope);

        if is_root {
            self.resolver.root_module_scope = Some(scope)
        } else {
            self.define(
                &Identifier {
                    span: Span::empty(FileID::new(0)),
                    symbol: node.name,
                },
                ScopeNamespace::Type,
                Resolution::Definition(id, DefinitionKind::Module),
                0,
            );
        }

        self.with_scope(scope, |this| ast::walk_module(this, node));
    }

    fn visit_file(&mut self, node: &ast::File) -> Self::Result {
        let kind = ScopeKind::File(node.id);
        let scope = ScopeData::new(kind, None);
        let scope = self.create_scope(scope);
        self.resolver.file_scope_mapping.insert(node.id, scope);

        self.scopes.file = Some(scope);
        ast::walk_file(self, node);
        self.scopes.file = None
    }

    fn visit_declaration(&mut self, node: &ast::Declaration) -> Self::Result {
        if matches!(node.kind, ast::DeclarationKind::ExternBlock(..)) {
            ast::walk_declaration(self, node);
            return;
        }
        let scope = self.define_module_declaration(node);
        if let Some(scope) = scope {
            self.with_scope(scope, |this| ast::walk_declaration(this, node));
        } else {
            ast::walk_declaration(self, node)
        }
    }

    fn visit_namespace_declaration(&mut self, node: &ast::NamespaceDeclaration) -> Self::Result {
        let scope = self.define_namespace_declaration(node);
        if let Some(scope) = scope {
            self.with_scope(scope, |this| ast::walk_namespace_declaration(this, node));
        } else {
            ast::walk_namespace_declaration(self, node)
        }
    }

    fn visit_function_declaration(&mut self, node: &ast::FunctionDeclaration) -> Self::Result {
        let scope = self.define_function_declaration(node);
        if let Some(scope) = scope {
            self.with_scope(scope, |this| ast::walk_function_declaration(this, node));
        } else {
            ast::walk_function_declaration(self, node)
        }
    }

    fn visit_assoc_declaration(
        &mut self,
        node: &ast::AssociatedDeclaration,
        context: ast::AssocContext,
    ) -> Self::Result {
        if !matches!(context, AssocContext::Interface(..)) {
            return;
        }

        let scope = self.define_assoc_declaration(node);
        if let Some(scope) = scope {
            self.with_scope(scope, |this| {
                ast::walk_assoc_declaration(this, node, context)
            });
        } else {
            ast::walk_assoc_declaration(self, node, context)
        }
    }

    fn visit_extern_declaration(&mut self, node: &ast::ExternDeclaration) -> Self::Result {
        let def_id = self.resolver.definition_id(node.id);
        let def_kind = self.resolver.definition_kind(def_id);
        let resolution = Resolution::Definition(def_id, def_kind);
        let visibility = 0;

        match &node.kind {
            ast::ExternDeclarationKind::Function(..) => {
                self.define(&node.identifier, ScopeNamespace::Value, resolution, visibility);
            }
        }

        ast::walk_extern_declaration(self, node)
    }

    fn visit_block(&mut self, node: &ast::Block) -> Self::Result {
        if node.has_declarations {
            let scope = self.create_scope(ScopeData::new(
                ScopeKind::Block(node.id),
                self.scopes.current,
            ));

            self.resolver.block_scope_mapping.insert(node.id, scope);
            self.with_scope(scope, |this| ast::walk_block(this, node));
        } else {
            ast::walk_block(self, node);
        }
    }
}

impl<'r, 'a> Actor<'r, 'a> {
    fn create_scope(&mut self, scope: ScopeData<'a>) -> Scope<'a> {
        let def_id = if let ScopeKind::Definition(id, _) = &scope.kind {
            Some(*id)
        } else {
            None
        };
        let id = self.resolver.create_scope(scope);

        if let Some(def_id) = def_id {
            self.resolver.definition_scope_mapping.insert(def_id, id);
        }
        id
    }

    fn with_scope<F: FnOnce(&mut Self)>(&mut self, scope: Scope<'a>, action: F) {
        let previous = self.scopes.current;
        self.scopes.current = Some(scope);
        action(self);
        self.scopes.current = previous;
    }
}

impl<'r, 'a> Actor<'r, 'a> {
    fn define_module_declaration(&mut self, declaration: &ast::Declaration) -> Option<Scope<'a>> {
        let def_id = self.resolver.definition_id(declaration.id);
        let def_kind = self.resolver.definition_kind(def_id);
        let resolution = Resolution::Definition(def_id, def_kind);
        let identifier = &declaration.identifier;
        let visibility = 0;

        match &declaration.kind {
            ast::DeclarationKind::Struct(_) => {
                self.define(identifier, ScopeNamespace::Type, resolution, visibility);
            }
            ast::DeclarationKind::Enum(..) | ast::DeclarationKind::TypeAlias(..) => {
                self.define(identifier, ScopeNamespace::Type, resolution, visibility);
            }
            ast::DeclarationKind::Function(..)
            | ast::DeclarationKind::Variable(..)
            | ast::DeclarationKind::Constant(..) => {
                self.define(identifier, ScopeNamespace::Value, resolution, visibility);
            }
            ast::DeclarationKind::ExternBlock(..) => return None,
            ast::DeclarationKind::Extension(_) => return None,
            ast::DeclarationKind::Interface(..) => {
                let scope = ScopeData::new(
                    ScopeKind::Definition(def_id, DefinitionKind::Interface),
                    self.scopes.current,
                );
                let scope = self.create_scope(scope);
                self.define(identifier, ScopeNamespace::Type, resolution, visibility);
                return Some(scope);
            }
            ast::DeclarationKind::Namespace(..) => {
                let scope = ScopeData::new(
                    ScopeKind::Definition(def_id, DefinitionKind::Namespace),
                    self.scopes.current,
                );
                let scope = self.create_scope(scope);
                self.define(identifier, ScopeNamespace::Type, resolution, visibility);
                return Some(scope);
            }

            ast::DeclarationKind::Import(node) => {
                self.define_use_tree(declaration.id, node, true);
            }
            ast::DeclarationKind::Export(node) => {
                self.define_use_tree(declaration.id, node, false);
            }
            ast::DeclarationKind::Initializer(..) => {
                unreachable!("top level initializer")
            }
            ast::DeclarationKind::Operator(..) => {
                unreachable!("top level operator")
            }
        }

        return None;
    }

    fn define_namespace_declaration(
        &mut self,
        declaration: &ast::NamespaceDeclaration,
    ) -> Option<Scope<'a>> {
        let def_id = self.resolver.definition_id(declaration.id);
        let def_kind = self.resolver.definition_kind(def_id);
        let resolution = Resolution::Definition(def_id, def_kind);
        let identifier = &declaration.identifier;
        let visibility = 0;

        match &declaration.kind {
            ast::NamespaceDeclarationKind::Struct(..)
            | ast::NamespaceDeclarationKind::Enum(..)
            | ast::NamespaceDeclarationKind::TypeAlias(..) => {
                self.define(identifier, ScopeNamespace::Type, resolution, visibility);
            }

            ast::NamespaceDeclarationKind::Function(..)
            | ast::NamespaceDeclarationKind::Constant(..) => {
                self.define(identifier, ScopeNamespace::Value, resolution, visibility);
            }

            ast::NamespaceDeclarationKind::Namespace(..) => {
                let scope = ScopeData::new(
                    ScopeKind::Definition(def_id, DefinitionKind::Namespace),
                    self.scopes.current,
                );
                let scope = self.create_scope(scope);
                self.define(identifier, ScopeNamespace::Type, resolution, visibility);
                return Some(scope);
            }
            ast::NamespaceDeclarationKind::Interface(..) => {
                let scope = ScopeData::new(
                    ScopeKind::Definition(def_id, DefinitionKind::Interface),
                    self.scopes.current,
                );
                let scope = self.create_scope(scope);
                self.define(identifier, ScopeNamespace::Type, resolution, visibility);
                return Some(scope);
            }
            ast::NamespaceDeclarationKind::Import(node) => {
                self.define_use_tree(declaration.id, node, true);
            }
            ast::NamespaceDeclarationKind::Export(node) => {
                self.define_use_tree(declaration.id, node, false);
            }
        }

        return None;
    }

    fn define_function_declaration(
        &mut self,
        declaration: &ast::FunctionDeclaration,
    ) -> Option<Scope<'a>> {
        let def_id = self.resolver.definition_id(declaration.id);
        let def_kind = self.resolver.definition_kind(def_id);
        let resolution = Resolution::Definition(def_id, def_kind);
        let identifier = &declaration.identifier;
        let visibility = 0;
        match &declaration.kind {
            ast::FunctionDeclarationKind::Struct(..)
            | ast::FunctionDeclarationKind::Enum(..)
            | ast::FunctionDeclarationKind::TypeAlias(..) => {
                self.define(identifier, ScopeNamespace::Type, resolution, visibility);
            }

            ast::FunctionDeclarationKind::Function(..)
            | ast::FunctionDeclarationKind::Constant(..) => {
                self.define(identifier, ScopeNamespace::Value, resolution, visibility);
            }
            ast::FunctionDeclarationKind::Import(node) => {
                self.define_use_tree(declaration.id, node, true);
            }
        }

        return None;
    }

    fn define_assoc_declaration(
        &mut self,
        declaration: &ast::AssociatedDeclaration,
    ) -> Option<Scope<'a>> {
        let def_id = self.resolver.definition_id(declaration.id);
        let def_kind = self.resolver.definition_kind(def_id);
        let resolution = Resolution::Definition(def_id, def_kind);
        let identifier = &declaration.identifier;
        let visibility = 0;

        match &declaration.kind {
            ast::AssociatedDeclarationKind::Constant(..)
            | ast::AssociatedDeclarationKind::Function(..) => {
                self.define(identifier, ScopeNamespace::Value, resolution, visibility);
            }
            ast::AssociatedDeclarationKind::AssociatedType(..) => {
                self.define(identifier, ScopeNamespace::Type, resolution, visibility);
            }
            ast::AssociatedDeclarationKind::Initializer(..)
            | ast::AssociatedDeclarationKind::Operator(..) => {
                // do nothing
            }
        }

        return None;
    }
}
impl<'r, 'a> Actor<'r, 'a> {
    fn define(
        &mut self,
        identifier: &Identifier,
        namespace: ScopeNamespace,
        resolution: Resolution,
        _visibility: usize,
    ) {
        let Some(current_scope) = self.scopes.current else {
            return;
        };

        let current_scope_kind = &current_scope.kind;
        // If defining in module, define in file
        let file_result = if matches!(
            current_scope_kind,
            ScopeKind::Definition(_, DefinitionKind::Module)
        ) && let Some(file_scope) = self.scopes.file
        {
            self.resolver
                .define_in_scope(file_scope, identifier, namespace, resolution.clone())
        } else {
            Ok(())
        };

        // Define in current scope
        let module_result =
            self.resolver
                .define_in_scope(current_scope, identifier, namespace, resolution);

        let result = file_result.and(module_result);
        if let Err(err) = result {
            let message = format!("Duplicate Symbol {}", identifier.symbol);
            self.resolver
                .dcx()
                .emit_error(message, Some(identifier.span));

            let message = format!("'{}' is defined here.", identifier.symbol);
            self.resolver.dcx().emit_info(message, Some(err.span));
        }
    }
}

impl<'r, 'a> Actor<'r, 'a> {
    fn define_use_tree(&mut self, id: NodeID, tree: &UseTree, is_import: bool) {
        let scope = if let Some(scope) = self.scopes.current {
            match &scope.kind {
                ScopeKind::Block(_) if is_import => Some(scope),
                ScopeKind::Definition(_, kind) if matches!(kind, DefinitionKind::Namespace) => {
                    Some(scope)
                }
                ScopeKind::Definition(_, kind)
                    if matches!(kind, DefinitionKind::Module) && !is_import =>
                {
                    Some(scope)
                }
                _ => self.scopes.file,
            }
        } else {
            None
        };

        let scope = scope.expect("non-nil scope id");
        match &tree.kind {
            UseTreeKind::Glob => {
                let kind = UsageKind::Glob { id };
                self.define_usage(
                    id,
                    scope,
                    tree.path.nodes.clone(),
                    kind,
                    is_import,
                    tree.span,
                );
            }
            UseTreeKind::Simple { alias } => {
                let mut module_path = tree.path.nodes.clone();
                assert!(!module_path.is_empty(), "non-empty module path");
                let target = if let Some(alias) = alias {
                    alias.clone()
                } else {
                    module_path.last().expect("non-empty module path").clone()
                };
                let source = module_path.pop().expect("non-empty module path");
                let binding = UsageBinding {
                    node_id: id,
                    source,
                    target,
                };
                let kind = UsageKind::Single(binding);
                self.define_usage(id, scope, module_path, kind, is_import, tree.span);
            }
            UseTreeKind::Nested { nodes, span } => {
                if nodes.is_empty() {
                    self.resolver
                        .dcx()
                        .emit_error("empty nested import".into(), Some(*span));
                }
                for node in nodes {
                    let module_path = tree.path.nodes.clone();
                    let target = if let Some(alias) = node.alias {
                        alias
                    } else {
                        node.name
                    };
                    let source = node.name;
                    let binding = UsageBinding {
                        node_id: node.id,
                        source,
                        target,
                    };
                    let kind = UsageKind::Single(binding);
                    self.define_usage(id, scope, module_path, kind, is_import, *span);
                }
            }
        }
    }

    fn define_usage(
        &mut self,
        _node_id: NodeID,
        scope: Scope<'a>,
        module_path: Vec<Identifier>,
        kind: UsageKind,
        is_import: bool,
        span: Span,
    ) {
        let usage = UsageEntryData {
            span,
            module_path,
            kind,
            is_import,
            scope,
            module_scope: Cell::new(None),
        };

        let is_glob = matches!(&usage.kind, UsageKind::Glob { .. });
        let usage = self.resolver.create_usage(usage);

        // for later passes
        if is_import {
            self.resolver.unresolved_imports.push(usage);
            if is_glob {
                scope.glob_imports.borrow_mut().push(usage);
            }
        } else {
            self.resolver.unresolved_exports.push(usage);
            if is_glob {
                scope.glob_exports.borrow_mut().push(usage);
            }
        }
    }
}
