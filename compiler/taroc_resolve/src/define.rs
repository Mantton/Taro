use super::resolver::Resolver;
use crate::models::{DefinitionExtensionData, ToNameBinding, UnresolvedAlias};
use std::cell::{Cell, RefCell};
use taroc_error::CompileResult;
use taroc_hir::{
    self, Declaration, DeclarationContext, DeclarationKind, DefinitionID, NodeID, PathTree,
    PathTreeNode, Resolution,
    visitor::{self, HirVisitor, walk_package},
};
use taroc_resolve_models::DefContextKind;
use taroc_resolve_models::{
    DefUsageBinding, DefinitionContext, ExternalDefUsageData, ExternalDefUsageKind, NameBinding,
    NameBindingData, NameBindingKind, Segment,
};
use taroc_span::{FileID, Identifier, Span, Symbol};

pub struct DefinitionCollector<'res, 'ctx> {
    pub resolver: &'res mut Resolver<'ctx>,
    pub parent_context: Option<DefinitionContext<'ctx>>,
    pub import_context: Option<DefinitionContext<'ctx>>,
    pub file_id: Option<FileID>,
    pub module_id: Option<DefinitionID>,
}

impl<'res, 'ctx> DefinitionCollector<'res, 'ctx> {
    pub fn run(
        package: &taroc_hir::Package,
        resolver: &'res mut Resolver<'ctx>,
    ) -> CompileResult<()> {
        let context = resolver.context;
        let mut actor = DefinitionCollector {
            resolver,
            parent_context: None,
            import_context: None,
            file_id: None,
            module_id: None,
        };

        walk_package(&mut actor, package);
        context.diagnostics.report()
    }
}

impl HirVisitor for DefinitionCollector<'_, '_> {
    fn visit_module(&mut self, m: &taroc_hir::Module) -> Self::Result {
        let id = self.resolver.def_id(m.id);
        let context = self.resolver.new_context(
            None,
            DefContextKind::Definition(id, taroc_hir::DefinitionKind::Module, m.name),
            Span::module(),
        );

        if m.id == NodeID::from(0) {
            self.resolver.packages_root = Some(self.resolver.new_context(
                None,
                DefContextKind::Root,
                Span::module(),
            ));
            self.resolver.root_context = Some(context);
            self.parent_context = Some(context);
        } else {
            let def = (context, taroc_hir::TVisibility::Public, Span::module());

            self.resolver.define(
                self.parent_context.unwrap(),
                taroc_span::Identifier {
                    span: Span::module(),
                    symbol: m.name,
                },
                def,
            );
        }
        let previous = self.parent_context;
        let previous_module = self.module_id;
        self.parent_context = Some(context);
        self.module_id = Some(id);
        visitor::walk_module(self, m);
        self.parent_context = previous;
        self.module_id = previous_module
    }

    fn visit_file(&mut self, f: &taroc_hir::File) -> Self::Result {
        let file_context =
            self.resolver
                .new_context(self.parent_context, DefContextKind::File, Span::empty(f.id));
        self.resolver.file_map.insert(f.id, file_context);
        self.import_context = Some(file_context);
        self.file_id = Some(f.id);
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
    }
}

impl DefinitionCollector<'_, '_> {
    fn define_declaration(&mut self, decl: &taroc_hir::Declaration, _: DeclarationContext) {
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
            | DeclarationKind::Constant(..)
            | DeclarationKind::Computed(..)
            | DeclarationKind::AssociatedType(..) => {
                self.resolver.define(parent, decl.identifier, def);
            }
            DeclarationKind::TypeAlias(alias) => {
                self.resolver.define(parent, decl.identifier, def);

                if alias.ty.is_some() {
                    let node = UnresolvedAlias {
                        _name: decl.identifier,
                        span,
                        alias: alias.clone(),
                        parent,
                    };
                    self.resolver.unresolved_aliases.insert(id, node);
                }
            }
            DeclarationKind::DefinedType(..)
            | DeclarationKind::Namespace(..)
            | DeclarationKind::Bridge(..) => {
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
            DeclarationKind::Extend(node) => {
                let ctx_k = DefContextKind::Definition(id, kind, name);
                let context = self.resolver.new_context(Some(parent), ctx_k, span);
                let data = DefinitionExtensionData {
                    ty: *node.ty.clone(),
                    extension_context: context,
                    module_id: self.module_id.unwrap(),
                    file_id: self.file_id.unwrap(),
                };
                self.resolver.unresolved_extensions.insert(id, data);
                self.parent_context = Some(context);
            }
            DeclarationKind::Extern(..) | DeclarationKind::Constructor(..) => {}
            DeclarationKind::EnumCase(..) => {}
            DeclarationKind::Operator(..) => {}
        }
    }
}

impl DefinitionCollector<'_, '_> {
    fn define_external_symbol_usage(
        &mut self,
        tree: &PathTree,
        id: NodeID,
        prefix: &[Segment],
        is_nested: bool,
        decl: &Declaration,
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

impl<'res, 'ctx> DefinitionCollector<'res, 'ctx> {
    fn add_extenal_symbol_usage(
        &mut self,
        module_path: Vec<Segment>,
        kind: ExternalDefUsageKind<'ctx>,
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
            module: self.module_id.unwrap(),
            span,
            module_path,
            kind,
            root_id,
            root_span,
            is_import,
            module_context: Cell::new(None),
            is_resolved: Cell::new(false),
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

impl DefinitionCollector<'_, '_> {
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

impl<'ctx> ToNameBinding<'ctx> for (DefinitionContext<'ctx>, taroc_hir::TVisibility, Span) {
    fn to_name_binding(self, arena: &Resolver<'ctx>) -> NameBinding<'ctx> {
        let binding = NameBindingData {
            kind: NameBindingKind::Context(self.0),
            span: self.2,
            vis: self.1,
        };
        arena.alloc_binding(binding)
    }
}

impl<'ctx> ToNameBinding<'ctx> for (Resolution, taroc_hir::TVisibility, Span) {
    fn to_name_binding(self, arena: &Resolver<'ctx>) -> NameBinding<'ctx> {
        let binding = NameBindingData {
            kind: NameBindingKind::Resolution(self.0),
            span: self.2,
            vis: self.1,
        };
        arena.alloc_binding(binding)
    }
}
