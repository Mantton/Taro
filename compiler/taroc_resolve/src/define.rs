use super::resolver::Resolver;
use crate::{arena::alloc_binding, models::ToNameBinding};
use std::cell::Cell;
use taroc_sema::GlobalContext;
use taroc_error::CompileResult;
use taroc_hir::{
    self, Declaration, DeclarationKind, NodeID, PathTree, PathTreeNode, Resolution,
    SymbolNamespace,
    visitor::{self, AssocContext, HirVisitor, walk_package},
};
use taroc_resolve_models::{DefContextKind, Determinacy, ParentScope, PerNS};
use taroc_resolve_models::{
    DefUsageBinding, DefinitionContext, ExternalDefUsageData, ExternalDefUsageKind, NameBinding,
    NameBindingData, NameBindingKind, Segment,
};
use taroc_span::{Identifier, Span, Symbol};

pub struct DefinitionCollector<'res, 'ctx> {
    pub resolver: &'res mut Resolver<'ctx>,
    pub parent_scope: ParentScope<'ctx>,
}

impl<'res, 'ctx> DefinitionCollector<'res, 'ctx> {
    pub fn run(
        package: &taroc_hir::Package,
        resolver: &'res mut Resolver<'ctx>,
    ) -> CompileResult<()> {
        let context = resolver.gcx;
        let root_context = resolver.root_context;
        let mut actor = DefinitionCollector {
            resolver,
            parent_scope: ParentScope {
                context: root_context,
            },
        };

        walk_package(&mut actor, package);
        context.diagnostics.report()
    }
}

impl HirVisitor for DefinitionCollector<'_, '_> {
    fn visit_module(&mut self, m: &taroc_hir::Module) -> Self::Result {
        let id = self.resolver.def_id(m.id);

        let context = if m.id != NodeID::from(0) {
            let context = self.resolver.new_context(
                None,
                DefContextKind::Definition(id, taroc_hir::DefinitionKind::Module, Some(m.name)),
                Span::module(),
            );
            let def = (context, taroc_hir::TVisibility::Public, Span::module());

            self.resolver.define(
                self.parent_scope.context,
                taroc_span::Identifier {
                    span: Span::module(),
                    symbol: m.name,
                },
                taroc_hir::SymbolNamespace::Type,
                def,
            );

            context
        } else {
            self.parent_scope.context
        };
        let previous_context = self.parent_scope.context;
        self.parent_scope.context = context;
        visitor::walk_module(self, m);
        self.parent_scope.context = previous_context;
    }

    fn visit_file(&mut self, f: &taroc_hir::File) -> Self::Result {
        let file_context = self.resolver.new_context(
            Some(self.parent_scope.context),
            DefContextKind::File,
            Span::empty(f.id),
        );
        self.resolver.file_map.insert(f.id, file_context);
        self.resolver
            .file_to_imports
            .entry(f.id)
            .or_default()
            .insert(self.resolver.gcx.session().index());

        let previous = self.parent_scope.context;
        self.parent_scope.context = file_context;
        visitor::walk_file(self, f);
        self.parent_scope.context = previous
    }

    fn visit_declaration(&mut self, d: &taroc_hir::Declaration) -> Self::Result {
        let previous = self.parent_scope;
        self.define_declaration(d);
        visitor::walk_declaration(self, d);
        self.parent_scope = previous;
    }

    fn visit_assoc_declaration(
        &mut self,
        declaration: &taroc_hir::AssociatedDeclaration,
        context: visitor::AssocContext,
    ) -> Self::Result {
        let ns = match &declaration.kind {
            taroc_hir::AssociatedDeclarationKind::Constant(..)
            | taroc_hir::AssociatedDeclarationKind::Function(..)
            | taroc_hir::AssociatedDeclarationKind::Operator(..) => SymbolNamespace::Value,
            taroc_hir::AssociatedDeclarationKind::Type(..) => SymbolNamespace::Type,
        };

        if context == AssocContext::Interface
            && !matches!(
                declaration.kind,
                taroc_hir::AssociatedDeclarationKind::Operator(..)
            )
        {
            let parent = self.parent_scope.context;
            let id = self.resolver.def_id(declaration.id);
            let kind = self.resolver.def_kind(id);
            let res = Resolution::Definition(id, kind);
            let vis = taroc_hir::TVisibility::Public; // TODO: Visibility
            let def = (res, vis, declaration.span);
            self.resolver
                .define(parent, declaration.identifier, ns, def);
        }
    }

    fn visit_block(&mut self, b: &taroc_hir::Block) -> Self::Result {
        let previous = self.parent_scope.context;
        self.define_block(b);
        visitor::walk_block(self, b);
        self.parent_scope.context = previous;
    }
    fn visit_variant(&mut self, v: &taroc_hir::Variant) -> Self::Result {
        let id = self.resolver.def_id(v.id);
        let kind = self.resolver.def_kind(id);
        let res = Resolution::Definition(id, kind);
        let vis = taroc_hir::TVisibility::Public; // TODO: Visibility
        let span = v.identifier.span;
        let parent = self.parent_scope.context;
        let def = (res, vis, span);

        // Define Variant in Type Namespace
        self.resolver
            .define(parent, v.identifier, SymbolNamespace::Type, def);

        // Constructor
        //
        if let Some(ctor_node_id) = v.kind.ctor_node_id() {
            let id = self.resolver.def_id(ctor_node_id);
            let kind = self.resolver.def_kind(id);
            let res = Resolution::Definition(id, kind);
            self.resolver.define(
                parent,
                v.identifier,
                SymbolNamespace::Value,
                (res, vis, span),
            );
        }
    }
}

impl DefinitionCollector<'_, '_> {
    fn define_declaration(&mut self, decl: &taroc_hir::Declaration) {
        let id = self.resolver.def_id(decl.id);
        let kind = self.resolver.def_kind(id);
        let name = decl.identifier.symbol;
        let res = Resolution::Definition(id, kind);
        let vis = taroc_hir::TVisibility::Public; // TODO: Visibility
        let span = decl.identifier.span;
        let parent = if matches!(self.parent_scope.context.kind, DefContextKind::File) {
            self.parent_scope.context.parent.unwrap()
        } else {
            self.parent_scope.context
        };
        let def = (res, vis, span);

        match &decl.kind {
            DeclarationKind::Struct(node) => {
                self.resolver
                    .define(parent, decl.identifier, SymbolNamespace::Type, def);

                // Define Constructor in Value NS
                if let Some(ctor_id) = node.variant.ctor_node_id() {
                    let ctor_def_id = self.resolver.def_id(ctor_id);
                    let kind = self.resolver.def_kind(id);
                    let def = (Resolution::Definition(ctor_def_id, kind), vis, span);
                    self.resolver.define(
                        parent,
                        decl.identifier,
                        taroc_hir::SymbolNamespace::Value,
                        def,
                    );
                }
            }
            DeclarationKind::Function(..)
            | DeclarationKind::Static(..)
            | DeclarationKind::Constant(..) => {
                self.resolver.define(
                    parent,
                    decl.identifier,
                    taroc_hir::SymbolNamespace::Value,
                    def,
                );
            }
            DeclarationKind::TypeAlias(_) => {
                self.resolver.define(
                    parent,
                    decl.identifier,
                    taroc_hir::SymbolNamespace::Type,
                    def,
                );
            }
            DeclarationKind::Namespace(..)
            | DeclarationKind::Bridge(..)
            | DeclarationKind::Enum(..)
            | DeclarationKind::Interface(..) => {
                let ctx_k = DefContextKind::Definition(id, kind, Some(name));
                let context = self.resolver.new_context(Some(parent), ctx_k, span);
                let def = (context, vis, span);
                self.resolver.define(
                    parent,
                    decl.identifier,
                    taroc_hir::SymbolNamespace::Type,
                    def,
                );
                self.parent_scope.context = context;
            }
            DeclarationKind::Import(node) => self.define_external_symbol_usage(
                node,
                decl.id,
                &[],
                false,
                &decl,
                self.parent_scope,
            ),
            DeclarationKind::Export(node) => self.define_external_symbol_usage(
                node,
                decl.id,
                &[],
                false,
                &decl,
                self.parent_scope,
            ),
            DeclarationKind::Extend(_) => {
                let ctx_k = DefContextKind::Definition(id, kind, None);
                let context = self.resolver.new_context(Some(parent), ctx_k, span);
                self.parent_scope.context = context;
            }
            DeclarationKind::Extern(..) => {}
            DeclarationKind::Malformed => unreachable!(),
        }
    }
}

impl<'arena, 'context> DefinitionCollector<'arena, 'context> {
    fn define_external_symbol_usage(
        &mut self,
        tree: &PathTree,
        id: NodeID,
        prefix: &[Segment],
        is_nested: bool,
        decl: &Declaration,
        parent_scope: ParentScope<'context>,
    ) {
        let mut prefix_iter = prefix
            .iter()
            .cloned()
            .chain(tree.root.segments.iter().map(|v| v.into()))
            .peekable();

        let is_glob = matches!(tree.node, PathTreeNode::Glob);
        let package_root = match prefix_iter.peek() {
            Some(segment) if !segment.identifier.is_path_segment_keyword() => {
                Some(segment.identifier.span)
            }
            None if is_glob => Some(tree.span),
            _ => None,
        }
        .map(|span| Segment::from_ident(Identifier::new(Symbol::with("{{root}}"), span)));

        let prefix: Vec<Segment> = package_root.into_iter().chain(prefix_iter).collect();

        match &tree.node {
            taroc_hir::PathTreeNode::Simple { alias } => {
                let target = if let Some(alias) = alias {
                    *alias
                } else {
                    tree.root.segments.last().unwrap().identifier
                };

                let mut module_path = prefix;
                let source = module_path.pop().unwrap();
                if is_nested {
                    if source.identifier.symbol == Symbol::with("self") {
                        todo!("self import")
                    }
                }

                // If Import, use either block or file scope to register as parent

                let parent = self.parent_scope;
                let binding = DefUsageBinding {
                    id,
                    source: source.identifier,
                    target,
                    source_binding: PerNS {
                        value_ns: Cell::new(Err(Determinacy::Undetermined)),
                        type_ns: Cell::new(Err(Determinacy::Undetermined)),
                    },
                    target_binding: PerNS {
                        value_ns: Cell::new(None),
                        type_ns: Cell::new(None),
                    },
                    is_nested,
                    parent,
                };

                let kind = ExternalDefUsageKind::Single(binding);
                self.add_extenal_symbol_usage(module_path, kind, tree.span, decl, parent_scope);
            }
            taroc_hir::PathTreeNode::Nested { nodes, span } => {
                if nodes.is_empty() {
                    self.resolver
                        .gcx
                        .diagnostics
                        .warn("Unused Import, Path is Empty".into(), *span);
                    return;
                }

                for (node, id) in nodes {
                    self.define_external_symbol_usage(node, *id, &prefix, true, decl, parent_scope);
                }
            }
            taroc_hir::PathTreeNode::Glob => {
                let kind = ExternalDefUsageKind::Glob { id };
                self.add_extenal_symbol_usage(prefix, kind, tree.span, decl, parent_scope);
            }
        }
    }
}

impl<'res, 'ctx> DefinitionCollector<'res, 'ctx> {
    fn add_extenal_symbol_usage(
        &mut self,
        module_path: Vec<Segment>,
        kind: ExternalDefUsageKind<'ctx>,
        span: Span,
        decl: &Declaration,
        parent_scope: ParentScope<'ctx>,
    ) {
        let is_import = matches!(&decl.kind, DeclarationKind::Import(..));
        let root_span = match &decl.kind {
            DeclarationKind::Import(node) | DeclarationKind::Export(node) => node.root.span,
            _ => unreachable!("must be import or export node"),
        };

        let root_id = decl.id;
        let data = ExternalDefUsageData {
            file: span.file,
            span,
            module_path,
            kind,
            root_id,
            root_span,
            is_import,
            module_context: Cell::new(None),
            is_resolved: Cell::new(false),
            parent_scope,
        };
        let ptr = self.resolver.alloc_external_usage(data);

        if is_import {
            self.resolver.unresolved_imports.push(ptr);
        } else {
            self.resolver.unresolved_exports.push(ptr);
        }

        if !is_import {
            match &ptr.0.kind {
                ExternalDefUsageKind::Single(..) => {}
                ExternalDefUsageKind::Glob { .. } => self
                    .parent_scope
                    .context
                    .glob_exports
                    .borrow_mut()
                    .push(ptr),
            };
        } else {
            match &ptr.0.kind {
                ExternalDefUsageKind::Single(..) => {}
                ExternalDefUsageKind::Glob { .. } => {
                    parent_scope.context.glob_imports.borrow_mut().push(ptr)
                }
            };
        }
    }
}

impl DefinitionCollector<'_, '_> {
    fn define_block(&mut self, block: &taroc_hir::Block) {
        if block.has_declarations {
            let parent = self.parent_scope.context;
            let context =
                self.resolver
                    .new_context(Some(parent), DefContextKind::Block, block.span);
            self.resolver.block_map.insert(block.id, context);
            self.parent_scope.context = parent;
        }
    }
}

impl<'ctx> ToNameBinding<'ctx> for (DefinitionContext<'ctx>, taroc_hir::TVisibility, Span) {
    fn to_name_binding(self, arena: GlobalContext<'ctx>) -> NameBinding<'ctx> {
        let binding = NameBindingData {
            kind: NameBindingKind::Context(self.0),
            span: self.2,
            vis: self.1,
        };
        alloc_binding(arena, binding)
    }
}

impl<'ctx> ToNameBinding<'ctx> for (Resolution, taroc_hir::TVisibility, Span) {
    fn to_name_binding(self, arena: GlobalContext<'ctx>) -> NameBinding<'ctx> {
        let binding = NameBindingData {
            kind: NameBindingKind::Resolution(self.0),
            span: self.2,
            vis: self.1,
        };
        alloc_binding(arena, binding)
    }
}
