use crate::models::ToNameBinding;

use super::{arena::ResolverArena, resolver::Resolver};
use std::cell::{Cell, RefCell};
use taroc_error::CompileResult;
use taroc_hir::{
    self, Declaration, DeclarationContext, DeclarationKind, NodeID, PathTree, Resolution,
    visitor::{self, HirVisitor, walk_package},
};
use taroc_resolve_models::DefContextKind;
use taroc_resolve_models::{
    DefUsageBinding, DefinitionContext, ExternalDefUsageData, ExternalDefUsageKind, NameBinding,
    NameBindingData, NameBindingKind, Segment,
};
use taroc_span::{FileID, Span, Symbol};

pub fn run(package: &taroc_hir::Package, r: &mut Resolver) -> CompileResult<()> {
    let actor = Actor::new(r);
    actor.run(package);
    r.context.diagnostics.report()
}

struct Actor<'res, 'ctx, 'arena> {
    pub resolver: &'res mut Resolver<'ctx, 'arena>,
    pub parent_context: Option<DefinitionContext<'arena>>,
    pub import_context: Option<DefinitionContext<'arena>>,
}

impl Actor<'_, '_, '_> {
    fn new<'res, 'ctx, 'arena>(
        resolver: &'res mut Resolver<'ctx, 'arena>,
    ) -> Actor<'res, 'ctx, 'arena> {
        Actor {
            resolver,
            parent_context: None,
            import_context: None,
        }
    }

    fn run(mut self, package: &taroc_hir::Package) {
        walk_package(&mut self, package);
    }
}

impl HirVisitor for Actor<'_, '_, '_> {
    fn visit_module(&mut self, m: &taroc_hir::Module, id: NodeID) -> Self::Result {
        // Create Context Scope for root module
        if id == NodeID::from(0) {
            let id = self.resolver.def_id(id);
            let context = self.resolver.new_context(
                None,
                DefContextKind::Definition(id, taroc_hir::DefinitionKind::Module, m.name),
                Span::empty(FileID::new(0)),
            );
            self.parent_context = Some(context);
            self.resolver.root_context = Some(context);
        }

        visitor::walk_module(self, m)
    }

    fn visit_file(&mut self, f: &taroc_hir::File) -> Self::Result {
        let file_context =
            self.resolver
                .new_context(self.parent_context, DefContextKind::File, Span::empty(f.id));
        self.resolver.file_map.insert(f.id, file_context);
        self.import_context = Some(file_context);
        visitor::walk_file(self, f);
        self.import_context = None;
    }

    fn visit_declaration(
        &mut self,
        d: &taroc_hir::Declaration,
        c: taroc_hir::DeclarationContext,
    ) -> Self::Result {
        let previous = self.parent_context;
        self.define_declaration(d, c);
        visitor::walk_declaration(self, d, c);
        self.parent_context = previous;
    }

    fn visit_block(&mut self, b: &taroc_hir::Block) -> Self::Result {
        let previous = self.parent_context;
        self.define_block(b);
        visitor::walk_block(self, b);
        self.parent_context = previous;
    }
    fn visit_variant(&mut self, v: &taroc_hir::Variant) -> Self::Result {
        let id = self.resolver.def_id(v.id);
        let kind = self.resolver.def_kind(id);
        let res = Resolution::Definition(id, kind);
        let vis = taroc_hir::TVisibility::Public; // TODO: Visibility
        let span = v.identifier.span;
        let parent = self.parent_context.unwrap();
        let def = (res, vis, span);

        // Define Variant in Type Namespace
        self.resolver.define(parent, v.identifier, def);

        // Define Ctor in Value Namespace
        // let (_, ctor_id) = v.kind.ctor();
        // let ctor_res = self.res(ctor_id);
        // let ctor_def = (ctor_res, vis, span);
        // self.resolver.define(parent, v.identifier, ctor_def);
    }
}

impl Actor<'_, '_, '_> {
    fn define_declaration(&mut self, decl: &taroc_hir::Declaration, context: DeclarationContext) {
        if matches!(
            context,
            DeclarationContext::Extend | DeclarationContext::Conform
        ) {
            return;
        }

        let id = self.resolver.def_id(decl.id);
        let kind = self.resolver.def_kind(id);
        let name = decl.identifier.symbol;
        let res = Resolution::Definition(id, kind);
        let vis = taroc_hir::TVisibility::Public; // TODO: Visibility
        let span = decl.identifier.span;
        let parent = self.parent_context.unwrap();
        let def = (res, vis, span);

        match &decl.kind {
            DeclarationKind::Function(..)
            | DeclarationKind::Variable(..)
            | DeclarationKind::Computed(..) => {
                self.resolver.define(parent, decl.identifier, def);
            }
            DeclarationKind::TypeAlias(_) => {
                self.resolver.define(parent, decl.identifier, def);
            }
            DeclarationKind::Struct(..) => {
                let ctx_k = DefContextKind::Definition(id, kind, name);
                let context = self.resolver.new_context(Some(parent), ctx_k, span);
                let def = (context, vis, span);
                self.resolver.define(parent, decl.identifier, def);

                // Non-Builtin
                // if !attributes_contain(&decl.attributes, Symbol::with("builtin")) {
                //     let (_, ctor_id) = node.variant.ctor();
                //     let ctor_res = self.res(ctor_id);
                //     let ctor_def = (ctor_res, vis, span);
                //     self.resolver.define(
                //         parent,
                //         decl.identifier,
                //         taroc_hir::SymbolNamespace::Value,
                //         ctor_def,
                //     );
                // }
            }
            DeclarationKind::Interface(..)
            | DeclarationKind::Enum(..)
            | DeclarationKind::Namespace(..)
            | DeclarationKind::Bridge(..)
            | DeclarationKind::Module(..) => {
                let ctx_k = DefContextKind::Definition(id, kind, name);
                let context = self.resolver.new_context(Some(parent), ctx_k, span);
                let def = (context, vis, span);
                self.resolver.define(parent, decl.identifier, def);
                self.parent_context = Some(context);
            }
            DeclarationKind::Import(node) => {
                self.define_external_symbol_usage(node, decl.id, &[], false, &decl)
            }
            DeclarationKind::Export(node) => {
                self.define_external_symbol_usage(node, decl.id, &[], false, &decl)
            }
            DeclarationKind::Extern(..)
            | DeclarationKind::Constructor(..)
            | DeclarationKind::Extend(..)
            | DeclarationKind::Conform(..) => {}
        }
    }
}

impl Actor<'_, '_, '_> {
    fn define_external_symbol_usage(
        &mut self,
        tree: &PathTree,
        id: NodeID,
        prefix: &[Segment],
        is_nested: bool,
        decl: &Declaration,
    ) {
        let prefix: Vec<Segment> = prefix
            .iter()
            .cloned()
            .chain(tree.root.segments.iter().map(|v| v.into()))
            .collect();

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
                let parent = if matches!(decl.kind, DeclarationKind::Import(..)) {
                    if let Some(context) = self.parent_context
                        && matches!(context.kind, DefContextKind::Block)
                    {
                        context
                    } else {
                        self.import_context.unwrap()
                    }
                } else {
                    self.parent_context.unwrap()
                };

                let binding = DefUsageBinding {
                    id,
                    source: source.identifier,
                    target,
                    source_binding: RefCell::new(None),
                    target_binding: RefCell::new(None),
                    is_nested,
                    parent,
                };

                let kind = ExternalDefUsageKind::Single(binding);
                self.add_extenal_symbol_usage(module_path, kind, tree.span, decl);
            }
            taroc_hir::PathTreeNode::Nested { nodes, span } => {
                if nodes.is_empty() {
                    self.resolver
                        .context
                        .diagnostics
                        .warn("Unused Import, Path is Empty".into(), *span);
                    return;
                }

                for (node, id) in nodes {
                    self.define_external_symbol_usage(node, *id, &prefix, true, decl);
                }
            }
            taroc_hir::PathTreeNode::Glob => {
                let kind = ExternalDefUsageKind::Glob { id };
                self.add_extenal_symbol_usage(prefix, kind, tree.span, decl);
            }
        }
    }
}

impl<'a, 'b, 'arena> Actor<'_, '_, 'arena> {
    fn add_extenal_symbol_usage(
        &mut self,
        module_path: Vec<Segment>,
        kind: ExternalDefUsageKind<'arena>,
        span: Span,
        decl: &Declaration,
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
        };
        let ptr = self.resolver.arena.alloc_external_usage(data);

        if is_import {
            self.resolver.unresolved_imports.push(ptr);
        } else {
            self.resolver.unresolved_exports.push(ptr);
        }

        if !is_import {
            match &ptr.0.kind {
                ExternalDefUsageKind::Single(..) => {}
                ExternalDefUsageKind::Glob { .. } => self
                    .parent_context
                    .unwrap()
                    .glob_exports
                    .borrow_mut()
                    .push(ptr),
            };
        } else {
            let context = if let Some(context) = self.parent_context
                && matches!(context.kind, DefContextKind::Block)
            {
                context
            } else {
                self.import_context.unwrap()
            };

            match &ptr.0.kind {
                ExternalDefUsageKind::Single(..) => {}
                ExternalDefUsageKind::Glob { .. } => context.glob_imports.borrow_mut().push(ptr),
            };
        }
    }
}

impl Actor<'_, '_, '_> {
    fn define_block(&mut self, block: &taroc_hir::Block) {
        if block.has_declarations {
            let parent = self.parent_context;
            let context = self
                .resolver
                .new_context(parent, DefContextKind::Block, block.span);
            self.resolver.block_map.insert(block.id, context);
            self.parent_context = Some(context);
        }
    }
}

impl<'arena> ToNameBinding<'arena> for (DefinitionContext<'arena>, taroc_hir::TVisibility, Span) {
    fn to_name_binding(self, arena: &'arena ResolverArena<'arena>) -> NameBinding<'arena> {
        let binding = NameBindingData {
            kind: NameBindingKind::Context(self.0),
            span: self.2,
            vis: self.1,
        };
        arena.alloc_binding(binding)
    }
}

impl<'arena> ToNameBinding<'arena> for (Resolution, taroc_hir::TVisibility, Span) {
    fn to_name_binding(self, arena: &'arena ResolverArena<'arena>) -> NameBinding<'arena> {
        let binding = NameBindingData {
            kind: NameBindingKind::Resolution(self.0),
            span: self.2,
            vis: self.1,
        };
        arena.alloc_binding(binding)
    }
}
