use rustc_hash::FxHashMap;
use taroc_context::GlobalContext;
use taroc_hir::{DefinitionID, DefinitionIndex, DefinitionKind, NodeID, PackageIndex, PartialRes};
use taroc_resolve_models::{
    DefContextKind, DefinitionContext, ExternalDefinitionUsage, NameBinding, NameHolder,
    ResolverOutput,
};
use taroc_span::{FileID, Identifier, Span, Symbol};

use crate::models::ToNameBinding;

use super::arena::ResolverArena;

pub struct Resolver<'ctx, 'arena> {
    pub context: GlobalContext<'ctx>,
    pub arena: &'arena ResolverArena<'arena>,
    node_to_def: FxHashMap<NodeID, DefinitionID>,
    def_to_kind: FxHashMap<DefinitionID, DefinitionKind>,
    def_to_context: FxHashMap<DefinitionID, DefinitionContext<'arena>>,
    pub block_map: FxHashMap<NodeID, DefinitionContext<'arena>>,
    pub file_map: FxHashMap<FileID, DefinitionContext<'arena>>,
    pub unresolved_exports: Vec<ExternalDefinitionUsage<'arena>>,
    pub unresolved_imports: Vec<ExternalDefinitionUsage<'arena>>,
    pub resolved_exports: Vec<ExternalDefinitionUsage<'arena>>,
    pub resolved_imports: Vec<ExternalDefinitionUsage<'arena>>,
    pub root_context: Option<DefinitionContext<'arena>>,
    pub next_index: u32,
    partial_resolution_map: FxHashMap<NodeID, PartialRes>,
}

impl Resolver<'_, '_> {
    pub fn new<'ctx, 'arena>(
        context: GlobalContext<'ctx>,
        arena: &'arena ResolverArena<'arena>,
    ) -> Resolver<'ctx, 'arena> {
        Resolver {
            context,
            arena,
            node_to_def: Default::default(),
            def_to_kind: Default::default(),
            def_to_context: Default::default(),
            block_map: Default::default(),
            file_map: Default::default(),
            unresolved_exports: Vec::new(),
            unresolved_imports: Vec::new(),
            resolved_exports: Vec::new(),
            resolved_imports: Vec::new(),
            root_context: None,
            partial_resolution_map: Default::default(),
            next_index: 0,
        }
    }
}

impl<'ctx, 'arena> Resolver<'_, 'arena> {
    pub fn new_context(
        &mut self,
        parent: Option<DefinitionContext<'arena>>,
        kind: DefContextKind,
        span: Span,
    ) -> DefinitionContext<'arena> {
        let context = self.arena.new_context(parent, kind, span);

        match kind {
            DefContextKind::Block => {}
            DefContextKind::File => {}
            DefContextKind::Definition(id, ..) => {
                self.def_to_context.insert(id, context);
            }
        }

        context
    }

    pub fn create_def(
        &mut self,
        _symbol: Symbol,
        node: NodeID,
        kind: DefinitionKind,
        _parent: DefinitionID,
    ) -> DefinitionID {
        let index = DefinitionID::new(
            PackageIndex::new(0),
            DefinitionIndex::from_raw(self.next_index),
        );
        self.node_to_def.insert(node, index);
        self.def_to_kind.insert(index, kind);
        self.next_index += 1;
        index
    }

    pub fn def_id(&self, id: NodeID) -> DefinitionID {
        *self.node_to_def.get(&id).expect("bug! node not tagged")
    }

    pub fn def_kind(&self, id: DefinitionID) -> DefinitionKind {
        if id.is_local() {
            return *self.def_to_kind.get(&id).expect("bug! node not tagged");
        }

        todo!("non-local definition, requesting kind")
    }

    pub fn get_context(&self, id: &DefinitionID) -> Option<DefinitionContext<'arena>> {
        if !id.is_local() {
            todo!("non local id")
        };

        let x = self.def_to_context.get(id).cloned();
        return x;
    }
    pub fn get_block_context(&self, id: &NodeID) -> Option<DefinitionContext<'arena>> {
        self.block_map.get(id).cloned()
    }

    pub fn get_file_context(&self, id: &FileID) -> DefinitionContext<'arena> {
        self.file_map
            .get(id)
            .cloned()
            .expect("file must always produce it's own def context")
    }
}

impl<'ctx, 'arena> Resolver<'ctx, 'arena> {
    pub fn define<T>(
        &mut self,
        parent: DefinitionContext<'arena>,
        identifier: Identifier,
        definition: T,
    ) -> bool
    where
        T: ToNameBinding<'arena>,
    {
        let binding = definition.to_name_binding(&self.arena);
        self.define_in_parent(parent, identifier, binding, false)
    }

    pub fn force_define<T>(
        &mut self,
        parent: DefinitionContext<'arena>,
        identifier: Identifier,
        definition: T,
    ) -> bool
    where
        T: ToNameBinding<'arena>,
    {
        let binding = definition.to_name_binding(&self.arena);
        self.define_in_parent(parent, identifier, binding, true)
    }

    pub fn define_in_parent(
        &mut self,
        parent: DefinitionContext<'arena>,
        identifier: Identifier,
        binding: NameBinding<'arena>,
        force: bool,
    ) -> bool {
        let result = self.define_in_context(parent, identifier.symbol, binding, force);

        match result {
            Ok(..) => {
                // println!("Defined {}", identifier.symbol);
                return true;
            }
            Err(previous_binding) => {
                let message = format!(
                    "Duplicate Definition, '{}' is already defined in this scope",
                    identifier.symbol
                );
                self.context.diagnostics.error(message, identifier.span);

                let message = format!("'{}' is defined here.", identifier.symbol);
                self.context
                    .diagnostics
                    .info(message, previous_binding.nearest().span);
                return false;
            }
        }
    }

    pub fn define_in_context(
        &self,
        context: DefinitionContext<'arena>,
        symbol: Symbol,
        binding: NameBinding<'arena>,
        force: bool,
    ) -> Result<Option<NameHolder<'arena>>, NameHolder<'arena>> {
        // if forcing a new binding
        if force {
            let old = context
                .resolutions
                .borrow_mut()
                .bindings
                .insert(symbol, NameHolder::Single(binding));
            return Ok(old);
        }

        let mut resolutions = context.resolutions.borrow_mut();

        if resolutions.contains(&symbol) {
            let current_binding = resolutions
                .bindings
                .get(&symbol)
                .expect("symbol must be contained");

            // Not a function, Duplicate Definition
            if !binding.is_function() || !current_binding.nearest().is_function() {
                let target = resolutions
                    .bindings
                    .get(&symbol)
                    .cloned()
                    .expect("symbol should be defined");

                return Err(target);
            };

            // Overloaded Function

            let bindings: &[NameBinding<'arena>] = match current_binding {
                NameHolder::Single(interned) => &[*interned],
                NameHolder::Set(interneds) => *interneds,
            };

            let total = 1 + bindings.len();
            let mut combined = Vec::with_capacity(total);
            combined.push(binding);
            combined.extend_from_slice(bindings);
            let new_bindings = self.arena.alloc_slice_copy(&combined);
            let new_holder = NameHolder::Set(new_bindings);
            resolutions.bindings.insert(symbol, new_holder);
            return Ok(None);
        } else {
            resolutions
                .bindings
                .insert(symbol, NameHolder::Single(binding));
            return Ok(None);
        }
    }
}

impl<'ctx, 'arena> Resolver<'ctx, 'arena> {
    pub fn record_paratial_resolution(&mut self, node: NodeID, resolution: PartialRes) {
        if let Some(_) = self.partial_resolution_map.insert(node, resolution) {
            panic!("multiple resolutions recorded for node {node:?}")
        }
    }
}

impl<'ctx, 'arena> Resolver<'_, 'arena> {
    pub fn produce(self) -> ResolverOutput {
        ResolverOutput {
            node_to_def: self.node_to_def,
            def_to_kind: self.def_to_kind,
            partial_resolution_map: self.partial_resolution_map,
        }
    }
}
