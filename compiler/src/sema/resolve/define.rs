use std::cell::Cell;

use crate::{
    ast::{self, AssocContext, AstVisitor, Identifier, NodeID, UseTree, UseTreeKind, walk_package},
    error::CompileResult,
    sema::resolve::{
        models::{
            ActiveScope, DefinitionKind, LexicalScope, LexicalScopeBinding, LexicalScopeSource,
            Resolution, Scope, ScopeData, ScopeKind, ScopeNamespace, UsageBinding, UsageEntryData,
            UsageKind,
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
    actor.define_nested_types(&package.root);
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
    // An extension may precede its owner, or reach it through an import.
    // Install these definitions after the ordinary module and file scopes exist.
    fn visit_nested_types(&mut self, _: &[ast::Declaration]) {}

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
        self.define_function_declaration(node);
        ast::walk_function_declaration(self, node)
    }

    fn visit_assoc_declaration(
        &mut self,
        node: &ast::AssociatedDeclaration,
        context: ast::AssocContext,
    ) -> Self::Result {
        if !matches!(context, AssocContext::Interface(..)) {
            return;
        }
        // Native descriptors have no callable value name. Their accessor
        // methods form ordinary overload groups in the interface scope.
        if matches!(&node.kind, ast::AssociatedDeclarationKind::Subscript(_)) {
            ast::walk_assoc_declaration(self, node, context);
            return;
        }

        self.define_named_declaration(node.id, &node.identifier);
        ast::walk_assoc_declaration(self, node, context)
    }

    fn visit_extern_declaration(&mut self, node: &ast::ExternDeclaration) -> Self::Result {
        self.define_named_declaration(node.id, &node.identifier);
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
    fn define_nested_types(&mut self, root: &ast::Module) {
        fn extensions<'p>(
            module: &'p ast::Module,
            pending: &mut Vec<(&'p ast::Impl, NodeID, FileID)>,
        ) {
            for file in &module.files {
                for declaration in &file.declarations {
                    if let ast::DeclarationKind::Impl(block) = &declaration.kind
                        && !block.nested_types.is_empty()
                    {
                        pending.push((block, module.id, file.id));
                    }
                }
            }
            for child in &module.submodules {
                extensions(child, pending);
            }
        }
        let mut pending = Vec::new();
        extensions(root, &mut pending);
        while !pending.is_empty() {
            super::usage::resolve_available(self.resolver);
            let before = pending.len();
            pending
                .retain(|&(block, module, file)| !self.install_nested_types(block, module, file));
            if pending.len() == before {
                for (block, _, _) in pending {
                    self.resolver.dcx().emit_error(
                        "could not resolve the owner of nested type declarations".into(),
                        Some(block.target.span),
                    );
                }
                break;
            }
        }
    }

    /// Returns false while an owner may still be introduced by another
    /// extension or an import. Diagnostics consume the invalid extension.
    fn install_nested_types(&mut self, block: &ast::Impl, module: NodeID, file: FileID) -> bool {
        let enclosing = self
            .resolver
            .get_definition_scope(self.resolver.definition_id(module));
        let file = self.resolver.file_scope_mapping[&file];
        let scopes = [enclosing, file].map(|s| LexicalScope::new(LexicalScopeSource::Scoped(s)));
        let ast::TypeKind::Nominal(path) = &block.target.kind else {
            self.resolver.dcx().emit_error(
                "nested types require a nominal extension target".into(),
                Some(block.target.span),
            );
            return true;
        };
        if !unrestricted_owner(block, path) {
            self.resolver.dcx().emit_error(
                "nested types require an unspecialized owner".into(),
                Some(block.target.span),
            );
            return true;
        }
        let Some((first, rest)) = path.segments.split_first() else {
            return false;
        };
        let Ok(LexicalScopeBinding::Declaration(mut holder)) = self
            .resolver
            .resolve_in_lexical_scopes(&first.identifier, ScopeNamespace::Type, &scopes)
        else {
            return false;
        };
        for part in rest {
            let Some(scope) = holder
                .resolution()
                .definition_id()
                .and_then(|id| self.resolver.nested_scope(id))
            else {
                return false;
            };
            let Ok(found) =
                self.resolver
                    .resolve_in_scope(&part.identifier, scope, ScopeNamespace::Type)
            else {
                return false;
            };
            holder = found;
        }
        let Resolution::Definition(owner, kind @ (DefinitionKind::Struct | DefinitionKind::Enum)) =
            holder.resolution()
        else {
            self.resolver.dcx().emit_error(
                "nested types require a struct, class or enum owner".into(),
                Some(block.target.span),
            );
            return true;
        };
        if !owner.is_local_to_index(self.resolver.package_index()) {
            self.resolver.dcx().emit_error(
                "nested types must be declared in the owner's package".into(),
                Some(block.target.span),
            );
            return true;
        }
        let scope = self.resolver.nested_scope(owner).unwrap_or_else(|| {
            self.create_scope(ScopeData::new(
                ScopeKind::Definition(owner, kind),
                Some(enclosing),
            ))
        });
        self.scopes.file = Some(file);
        self.with_scope(scope, |this| {
            for nested in &block.nested_types {
                this.resolver
                    .attach_nested_type(this.resolver.definition_id(nested.id), owner);
                this.visit_declaration(nested);
            }
        });
        self.scopes.file = None;
        true
    }

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
        match &declaration.kind {
            ast::DeclarationKind::Import(tree) => self.define_use_tree(declaration.id, tree, true),
            ast::DeclarationKind::Export(tree) => self.define_use_tree(declaration.id, tree, false),
            ast::DeclarationKind::Impl(_) | ast::DeclarationKind::ExternBlock(_) => {}
            _ => return self.define_named_declaration(declaration.id, &declaration.identifier),
        }
        None
    }

    fn define_namespace_declaration(
        &mut self,
        declaration: &ast::NamespaceDeclaration,
    ) -> Option<Scope<'a>> {
        match &declaration.kind {
            ast::NamespaceDeclarationKind::Import(tree) => {
                self.define_use_tree(declaration.id, tree, true)
            }
            ast::NamespaceDeclarationKind::Export(tree) => {
                self.define_use_tree(declaration.id, tree, false)
            }
            _ => return self.define_named_declaration(declaration.id, &declaration.identifier),
        }
        None
    }

    fn define_function_declaration(&mut self, declaration: &ast::FunctionDeclaration) {
        if let ast::FunctionDeclarationKind::Import(tree) = &declaration.kind {
            self.define_use_tree(declaration.id, tree, true);
        } else {
            self.define_named_declaration(declaration.id, &declaration.identifier);
        }
    }

    fn define_named_declaration(
        &mut self,
        node: NodeID,
        identifier: &Identifier,
    ) -> Option<Scope<'a>> {
        let def_id = self.resolver.definition_id(node);
        let kind = self.resolver.definition_kind(def_id);
        let (namespace, scoped) = match kind {
            DefinitionKind::Struct
            | DefinitionKind::Enum
            | DefinitionKind::TypeAlias
            | DefinitionKind::AssociatedType
            | DefinitionKind::OpaqueType => (ScopeNamespace::Type, false),
            DefinitionKind::Interface | DefinitionKind::Namespace => (ScopeNamespace::Type, true),
            DefinitionKind::Function
            | DefinitionKind::ModuleVariable
            | DefinitionKind::Constant
            | DefinitionKind::AssociatedFunction
            | DefinitionKind::AssociatedConstant
            | DefinitionKind::AssociatedProperty => (ScopeNamespace::Value, false),
            _ => unreachable!("non-declaration kind in named declaration: {kind:?}"),
        };
        let scope = scoped.then(|| {
            self.create_scope(ScopeData::new(
                ScopeKind::Definition(def_id, kind),
                self.scopes.current,
            ))
        });
        self.define(identifier, namespace, Resolution::Definition(def_id, kind));
        scope
    }
}
impl<'r, 'a> Actor<'r, 'a> {
    fn define(
        &mut self,
        identifier: &Identifier,
        namespace: ScopeNamespace,
        resolution: Resolution,
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
                self.define_usage(scope, tree.path.nodes.clone(), kind, is_import, tree.span);
            }
            UseTreeKind::Simple { alias } => {
                let mut module_path = tree.path.nodes.clone();
                assert!(!module_path.is_empty(), "non-empty module path");
                let target = if let Some(alias) = alias {
                    *alias
                } else {
                    *module_path.last().expect("non-empty module path")
                };
                let source = module_path.pop().expect("non-empty module path");
                let binding = UsageBinding {
                    node_id: id,
                    source,
                    target,
                };
                let kind = UsageKind::Single(binding);
                self.define_usage(scope, module_path, kind, is_import, tree.span);
            }
            UseTreeKind::Nested { nodes, span } => {
                if nodes.is_empty() {
                    self.resolver
                        .dcx()
                        .emit_error("empty nested import".into(), Some(*span));
                }
                for node in nodes {
                    let module_path = tree.path.nodes.clone();
                    let target = if let Some(alias) = &node.alias {
                        *alias
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
                    self.define_usage(scope, module_path, kind, is_import, *span);
                }
            }
        }
    }

    fn define_usage(
        &mut self,
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

/// A nested name belongs to the whole owner. An explicit generic header can
/// repeat independent parameters, but a concrete argument or bound narrows it.
fn unrestricted_owner(block: &ast::Impl, path: &ast::Path) -> bool {
    let Some((last, prefix)) = path.segments.split_last() else {
        return false;
    };
    if block.generics.where_clause.is_some() || prefix.iter().any(|part| part.arguments.is_some()) {
        return false;
    }
    match (&last.arguments, &block.generics.type_parameters) {
        (None, None) => true,
        (Some(args), Some(params)) if args.arguments.len() == params.parameters.len() => {
            let mut names: rustc_hash::FxHashSet<_> = params
                .parameters
                .iter()
                .map(|p| p.identifier.symbol)
                .collect();
            params.parameters.iter().all(|p| p.bounds.is_none()) && args.arguments.iter().all(|arg| {
                let ast::TypeArgument::Type(ty) = arg else { return false };
                let ast::TypeKind::Nominal(path) = &ty.kind else { return false };
                matches!(path.segments.as_slice(), [part] if part.arguments.is_none() && names.remove(&part.identifier.symbol))
            })
        }
        _ => false,
    }
}
