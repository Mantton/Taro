use rustc_hash::FxHashMap;
use std::rc::Rc;
use taroc_context::{CompilerSession, ResolutionData};
use taroc_hir::{DefinitionID, DefinitionIndex, DefinitionKind, NodeID, PackageIndex, PartialRes};
use taroc_resolve_models::{
    DefContextKind, DefinitionContext, ExternalDefinitionUsage, NameBinding, NameHolder,
};
use taroc_span::{FileID, Identifier, Span, Symbol};

use crate::models::ToNameBinding;

pub struct Resolver<'ctx> {
    pub session: Rc<CompilerSession<'ctx>>,
    node_to_def: FxHashMap<NodeID, DefinitionID>,
    def_to_kind: FxHashMap<DefinitionID, DefinitionKind>,
    def_to_context: FxHashMap<DefinitionID, DefinitionContext<'ctx>>,
    pub block_map: FxHashMap<NodeID, DefinitionContext<'ctx>>,
    pub file_map: FxHashMap<FileID, DefinitionContext<'ctx>>,
    pub unresolved_exports: Vec<ExternalDefinitionUsage<'ctx>>,
    pub unresolved_imports: Vec<ExternalDefinitionUsage<'ctx>>,
    pub resolved_exports: Vec<ExternalDefinitionUsage<'ctx>>,
    pub resolved_imports: Vec<ExternalDefinitionUsage<'ctx>>,
    pub root_context: Option<DefinitionContext<'ctx>>,
    pub next_index: u32,
    partial_resolution_map: FxHashMap<NodeID, PartialRes>,
}

impl Resolver<'_> {
    pub fn new<'ctx>(session: Rc<CompilerSession<'ctx>>) -> Resolver<'ctx> {
        Resolver {
            session,
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

impl<'ctx> Resolver<'ctx> {
    pub fn new_context(
        &mut self,
        parent: Option<DefinitionContext<'ctx>>,
        kind: DefContextKind,
        span: Span,
    ) -> DefinitionContext<'ctx> {
        let context = self.alloc_context(parent, kind, span);

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
            PackageIndex::new(self.session.index),
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
        if id.is_local(self.session.index) {
            return *self.def_to_kind.get(&id).expect("bug! node not tagged");
        }

        let resolutions = self.session.context.store.resolutions.borrow();
        let data = resolutions
            .get(&id.package().index())
            .expect("resolution data");
        let kind = *data.def_to_kind.get(&id).expect("def to kind");
        kind
    }

    pub fn get_context(&self, id: &DefinitionID) -> Option<DefinitionContext<'ctx>> {
        if !id.is_local(self.session.index) {
            todo!("non local id")
        };

        let x = self.def_to_context.get(id).cloned();
        return x;
    }
    pub fn get_block_context(&self, id: &NodeID) -> Option<DefinitionContext<'ctx>> {
        self.block_map.get(id).cloned()
    }

    pub fn get_file_context(&self, id: &FileID) -> DefinitionContext<'ctx> {
        self.file_map
            .get(id)
            .cloned()
            .expect("file must always produce it's own def context")
    }
}

impl<'ctx> Resolver<'ctx> {
    pub fn define<T>(
        &mut self,
        parent: DefinitionContext<'ctx>,
        identifier: Identifier,
        definition: T,
    ) -> bool
    where
        T: ToNameBinding<'ctx>,
    {
        let binding = definition.to_name_binding(&self);
        self.define_in_parent(parent, identifier, binding, false)
    }

    pub fn force_define<T>(
        &mut self,
        parent: DefinitionContext<'ctx>,
        identifier: Identifier,
        definition: T,
    ) -> bool
    where
        T: ToNameBinding<'ctx>,
    {
        let binding = definition.to_name_binding(&self);
        self.define_in_parent(parent, identifier, binding, true)
    }

    pub fn define_in_parent(
        &mut self,
        parent: DefinitionContext<'ctx>,
        identifier: Identifier,
        binding: NameBinding<'ctx>,
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
                self.session
                    .context
                    .diagnostics
                    .error(message, identifier.span);

                let message = format!("'{}' is defined here.", identifier.symbol);
                self.session
                    .context
                    .diagnostics
                    .info(message, previous_binding.nearest().span);
                return false;
            }
        }
    }

    pub fn define_in_context(
        &self,
        context: DefinitionContext<'ctx>,
        symbol: Symbol,
        binding: NameBinding<'ctx>,
        force: bool,
    ) -> Result<Option<NameHolder<'ctx>>, NameHolder<'ctx>> {
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

            let bindings: &[NameBinding<'ctx>] = match current_binding {
                NameHolder::Single(interned) => &[*interned],
                NameHolder::Set(interneds) => *interneds,
            };

            let total = 1 + bindings.len();
            let mut combined = Vec::with_capacity(total);
            combined.push(binding);
            combined.extend_from_slice(bindings);
            let new_bindings = self.alloc_slice_copy(&combined);
            let new_holder: NameHolder<'ctx> = NameHolder::Set(new_bindings);
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

impl<'ctx> Resolver<'ctx> {
    pub fn record_paratial_resolution(&mut self, node: NodeID, resolution: PartialRes) {
        if let Some(_) = self.partial_resolution_map.insert(node, resolution) {
            // panic!("multiple resolutions recorded for node {node:?}")
        }
    }
}

impl<'ctx> Resolver<'ctx> {
    pub fn produce(self) -> ResolutionData<'ctx> {
        ResolutionData {
            node_to_def: self.node_to_def,
            def_to_kind: self.def_to_kind,
            partial_resolution_map: self.partial_resolution_map,
            root: self.root_context.unwrap(),
        }
    }
}
