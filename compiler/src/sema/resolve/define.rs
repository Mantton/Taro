use crate::{
    ast::{
        self, AstVisitor, DeclarationKind, Identifier, NodeID, UseTree, UseTreeKind,
        VisibilityLevel, walk_package,
    },
    error::CompileResult,
    sema::resolve::{
        ActiveScope, DefinitionKind, Resolution, Scope, ScopeID, ScopeKind, ScopeNamespace,
        UsageBinding, UsageEntry, UsageKind, resolver::Resolver,
    },
    span::Span,
};

pub fn define_package_symbols(
    package: &ast::Package,
    resolver: &mut Resolver,
) -> CompileResult<()> {
    let mut actor = Actor::new(resolver);
    walk_package(&mut actor, package);
    Ok(())
}

pub struct Actor<'resolver> {
    resolver: &'resolver mut Resolver,
    scopes: ActiveScope,
}

impl<'r> Actor<'r> {
    fn new(resolver: &'r mut Resolver) -> Actor<'r> {
        Actor {
            resolver,
            scopes: ActiveScope {
                current: None,
                file: None,
            },
        }
    }
}

impl<'r> AstVisitor for Actor<'r> {
    fn visit_module(&mut self, node: &ast::Module, is_root: bool) -> Self::Result {
        let kind = ScopeKind::Module(0);
        let parent = self.scopes.current;
        let scope = Scope::new(kind, parent);
        let scope_id = self.create_scope(scope);

        if is_root {
            self.resolver.root_module_scope = Some(scope_id)
        }

        self.with_scope(scope_id, |this| ast::walk_module(this, node));
    }

    fn visit_file(&mut self, node: &ast::File) -> Self::Result {
        let kind = ScopeKind::File(node.id);
        let scope = Scope::new(kind, None);
        let scope_id = self.create_scope(scope);

        self.scopes.file = Some(scope_id);
        ast::walk_file(self, node);
        self.scopes.file = None
    }

    fn visit_declaration(&mut self, node: &ast::Declaration) -> Self::Result {
        let scope_id = self.define_module_declaration(node);
        if let Some(scope_id) = scope_id {
            self.with_scope(scope_id, |this| ast::walk_declaration(this, node));
        } else {
            ast::walk_declaration(self, node)
        }
    }

    fn visit_namespace_declaration(&mut self, node: &ast::NamespaceDeclaration) -> Self::Result {
        let scope_id = self.define_namespace_declaration(node);
        if let Some(scope_id) = scope_id {
            self.with_scope(scope_id, |this| ast::walk_namespace_declaration(this, node));
        } else {
            ast::walk_namespace_declaration(self, node)
        }
    }

    fn visit_function_declaration(&mut self, node: &ast::FunctionDeclaration) -> Self::Result {
        let scope_id = self.define_function_declaration(node);
        if let Some(scope_id) = scope_id {
            self.with_scope(scope_id, |this| ast::walk_function_declaration(this, node));
        } else {
            ast::walk_function_declaration(self, node)
        }
    }

    fn visit_assoc_declaration(
        &mut self,
        node: &ast::AssociatedDeclaration,
        context: ast::AssocContext,
    ) -> Self::Result {
        let scope_id = self.define_assoc_declaration(node);
        if let Some(scope_id) = scope_id {
            self.with_scope(scope_id, |this| {
                ast::walk_assoc_declaration(this, node, context)
            });
        } else {
            ast::walk_assoc_declaration(self, node, context)
        }
    }
}

impl<'r> Actor<'r> {
    fn create_scope(&mut self, scope: Scope) -> ScopeID {
        self.resolver.create_scope(scope)
    }

    fn with_scope<F: FnOnce(&mut Self)>(&mut self, scope: ScopeID, action: F) {
        let previous = self.scopes.current;
        self.scopes.current = Some(scope);
        action(self);
        self.scopes.current = previous;
    }
}

impl<'r> Actor<'r> {
    fn define_module_declaration(&mut self, declaration: &ast::Declaration) -> Option<ScopeID> {
        let def_id = self.resolver.def_id(declaration.id);
        let def_kind = self.resolver.def_kind(def_id);
        let resolution = Resolution::Definition(def_id, def_kind);
        let identifier = &declaration.identifier;
        let visibility = 0;

        match &declaration.kind {
            ast::DeclarationKind::Struct(node) => {
                self.define(identifier, ScopeNamespace::Type, resolution, visibility);

                // Constructor
                let ctor_def_id = self.resolver.def_id(node.ctor_node_id);
                let ctor_def_kind = self.resolver.def_kind(ctor_def_id);
                self.define(
                    identifier,
                    ScopeNamespace::Value,
                    Resolution::Definition(ctor_def_id, ctor_def_kind),
                    visibility,
                );
            }
            ast::DeclarationKind::Enum(..) | ast::DeclarationKind::TypeAlias(..) => {
                self.define(identifier, ScopeNamespace::Type, resolution, visibility);
            }
            ast::DeclarationKind::Function(..)
            | ast::DeclarationKind::Variable(..)
            | ast::DeclarationKind::Constant(..) => {
                self.define(identifier, ScopeNamespace::Value, resolution, visibility);
            }
            ast::DeclarationKind::Extend(node) => {
                let scope = Scope::new(ScopeKind::Definition(def_id), self.scopes.current);
                let scope = self.create_scope(scope);
                return Some(scope);
            }
            ast::DeclarationKind::Interface(..) => {
                let scope = Scope::new(ScopeKind::Definition(def_id), self.scopes.current);
                let scope = self.create_scope(scope);
                self.define(identifier, ScopeNamespace::Type, resolution, visibility);
                return Some(scope);
            }
            ast::DeclarationKind::Namespace(..) => {
                let scope = Scope::new(ScopeKind::Definition(def_id), self.scopes.current);
                let scope = self.create_scope(scope);
                self.define(identifier, ScopeNamespace::Module, resolution, visibility);
                return Some(scope);
            }

            ast::DeclarationKind::Import(node) => {
                self.define_use_tree(declaration.id, node, true);
            }
            ast::DeclarationKind::Export(node) => {
                self.define_use_tree(declaration.id, node, false);
            }
            ast::DeclarationKind::Initializer(node) => {
                // do nothing
            }
        }

        return None;
    }

    fn define_namespace_declaration(
        &mut self,
        declaration: &ast::NamespaceDeclaration,
    ) -> Option<ScopeID> {
        let def_id = self.resolver.def_id(declaration.id);
        let def_kind = self.resolver.def_kind(def_id);
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
                let scope = Scope::new(ScopeKind::Definition(def_id), self.scopes.current);
                let scope = self.create_scope(scope);
                self.define(identifier, ScopeNamespace::Module, resolution, visibility);
                return Some(scope);
            }
            ast::NamespaceDeclarationKind::Interface(..) => {
                let scope = Scope::new(ScopeKind::Definition(def_id), self.scopes.current);
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
    ) -> Option<ScopeID> {
        let def_id = self.resolver.def_id(declaration.id);
        let def_kind = self.resolver.def_kind(def_id);
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
    ) -> Option<ScopeID> {
        let def_id = self.resolver.def_id(declaration.id);
        let def_kind = self.resolver.def_kind(def_id);
        let resolution = Resolution::Definition(def_id, def_kind);
        let identifier = &declaration.identifier;
        let visibility = 0;

        match &declaration.kind {
            ast::AssociatedDeclarationKind::Constant(..)
            | ast::AssociatedDeclarationKind::Function(..) => {
                self.define(identifier, ScopeNamespace::Value, resolution, visibility);
            }
            ast::AssociatedDeclarationKind::Type(..) => {
                self.define(identifier, ScopeNamespace::Type, resolution, visibility);
            }
            ast::AssociatedDeclarationKind::Initializer(..) => {
                // do nothing
            }
        }

        return None;
    }
}
impl<'r> Actor<'r> {
    fn define(
        &mut self,
        identifier: &Identifier,
        namespace: ScopeNamespace,
        resolution: Resolution,
        visibility: usize,
    ) {
        let Some(current_scope_id) = self.scopes.current else {
            return;
        };

        let current_scope_kind = &self.resolver.get_scope(current_scope_id).kind;
        // If defining in module, define in file
        let file_result = if matches!(current_scope_kind, ScopeKind::Module(..))
            && let Some(file_scope) = self.scopes.file
        {
            self.resolver
                .define_in_scope(file_scope, identifier, namespace, resolution.clone())
        } else {
            Ok(())
        };

        // Define in current scope
        let module_result =
            self.resolver
                .define_in_scope(current_scope_id, identifier, namespace, resolution);

        let result = file_result.and(module_result);
        if let Err(err) = result {
            println!("todo - Duplicate Symbol {}", identifier.symbol)
            // TODO: Report Error
        }
    }
}

impl<'r> Actor<'r> {
    fn define_use_tree(&mut self, id: NodeID, tree: &UseTree, is_import: bool) {
        let scope_id = if let Some(scope_id) = self.scopes.current {
            let scope = self.resolver.get_scope(scope_id);
            match scope.kind {
                ScopeKind::Block(_) if is_import => Some(scope_id),
                ScopeKind::Definition(def_id)
                    if matches!(self.resolver.def_kind(def_id), DefinitionKind::Namespace) =>
                {
                    Some(scope_id)
                }
                ScopeKind::Module(_) if !is_import => Some(scope_id),
                _ => self.scopes.file,
            }
        } else {
            None
        };

        let scope_id = scope_id.expect("non-nil scope id");
        match &tree.kind {
            UseTreeKind::Glob => {
                let kind = UsageKind::Glob { id };
                self.define_usage(
                    id,
                    scope_id,
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
                self.define_usage(id, scope_id, module_path, kind, is_import, tree.span);
            }
            UseTreeKind::Nested { nodes, span } => {
                if nodes.is_empty() {
                    todo!("report error – empty nested import")
                }
                for node in nodes {
                    let module_path = tree.path.nodes.clone();
                    let target = if let Some(alias) = &node.alias {
                        alias.clone()
                    } else {
                        node.name.clone()
                    };
                    let source = node.name.clone();
                    let binding = UsageBinding {
                        node_id: node.id,
                        source,
                        target,
                    };
                    let kind = UsageKind::Single(binding);
                    self.define_usage(id, scope_id, module_path, kind, is_import, *span);
                }
            }
        }
    }

    fn define_usage(
        &mut self,
        node_id: NodeID,
        scope_id: ScopeID,
        module_path: Vec<Identifier>,
        kind: UsageKind,
        is_import: bool,
        span: Span,
    ) {
        let usage = UsageEntry {
            span,
            module_path,
            kind,
            is_import,
            scope_id,
            is_resolved: false,
        };

        let is_glob = matches!(&usage.kind, UsageKind::Glob { .. });
        let usage_id = self.resolver.create_usage(usage);

        let target_scope = self
            .resolver
            .scopes
            .get_mut(scope_id)
            .expect("no scope matching id");

        // for later passes
        if is_import {
            self.resolver.unresolved_imports.push(usage_id);
            if is_glob {
                target_scope.glob_imports.borrow_mut().push(usage_id);
            }
        } else {
            self.resolver.unresolved_exports.push(usage_id);
            if is_glob {
                target_scope.glob_exports.borrow_mut().push(usage_id);
            }
        }
    }
}
