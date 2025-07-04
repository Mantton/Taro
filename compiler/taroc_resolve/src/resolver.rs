use crate::{
    arena::{alloc_binding, alloc_context},
    models::ToNameBinding,
};
use rustc_hash::{FxHashMap, FxHashSet};
use taroc_hir::{
    DefinitionID, DefinitionIndex, DefinitionKind, NodeID, PackageIndex, PartialResolution,
    PrimaryType, Resolution, SymbolNamespace, TVisibility,
};
use taroc_resolve_models::{
    BindingKey, DefContextKind, DefinitionContext, ExternalDefinitionUsage, NameBinding,
    NameBindingData, NameBindingKind, NameHolder, ResolutionMap,
};
use taroc_sema::{CompilerSession, GlobalContext, ResolutionData};
use taroc_span::{FileID, Identifier, Span, Symbol};

pub struct Resolver<'ctx> {
    pub gcx: GlobalContext<'ctx>,
    pub root_context: DefinitionContext<'ctx>,
    node_to_def: FxHashMap<NodeID, DefinitionID>,
    def_to_kind: FxHashMap<DefinitionID, DefinitionKind>,
    def_to_ident: FxHashMap<DefinitionID, Identifier>,
    def_to_context: FxHashMap<DefinitionID, DefinitionContext<'ctx>>,
    def_to_parent: FxHashMap<DefinitionID, DefinitionID>,
    pub block_map: FxHashMap<NodeID, DefinitionContext<'ctx>>,
    pub file_map: FxHashMap<FileID, DefinitionContext<'ctx>>,
    pub unresolved_exports: Vec<ExternalDefinitionUsage<'ctx>>,
    pub unresolved_imports: Vec<ExternalDefinitionUsage<'ctx>>,
    pub resolved_exports: Vec<ExternalDefinitionUsage<'ctx>>,
    pub resolved_imports: Vec<ExternalDefinitionUsage<'ctx>>,
    pub next_index: u32,
    pub resolution_map: FxHashMap<NodeID, PartialResolution>,
    pub builin_types_bindings: FxHashMap<Symbol, NameHolder<'ctx>>,
    pub generics_table: FxHashMap<DefinitionID, Vec<(Symbol, DefinitionID)>>,
    pub file_to_imports: FxHashMap<FileID, FxHashSet<PackageIndex>>,
}

impl Resolver<'_> {
    pub fn new<'ctx>(context: GlobalContext<'ctx>) -> Resolver<'ctx> {
        let root_id = DefinitionID::new(
            PackageIndex::new(context.session().package_index),
            DefinitionIndex::new(0),
        );
        let root_context = alloc_context(
            context,
            None,
            DefContextKind::Definition(root_id, DefinitionKind::Module, None),
            Span::module(),
        );

        Resolver {
            gcx: context,
            root_context,
            node_to_def: Default::default(),
            def_to_kind: Default::default(),
            def_to_context: Default::default(),
            def_to_ident: Default::default(),
            def_to_parent: Default::default(),
            block_map: Default::default(),
            file_map: Default::default(),
            unresolved_exports: Vec::new(),
            unresolved_imports: Vec::new(),
            resolved_exports: Vec::new(),
            resolved_imports: Vec::new(),
            resolution_map: Default::default(),
            next_index: 0,
            generics_table: Default::default(),
            file_to_imports: Default::default(),
            builin_types_bindings: PrimaryType::ALL
                .iter()
                .map(|ty| {
                    let binding = (
                        Resolution::PrimaryType(*ty),
                        TVisibility::Public,
                        Span::empty(FileID::from_raw(0)),
                    )
                        .to_name_binding(context);
                    (Symbol::with(ty.name_str()), NameHolder::Single(binding))
                })
                .collect(),
        }
    }
}

impl<'ctx> Resolver<'ctx> {
    pub fn session(&self) -> CompilerSession {
        self.gcx.session()
    }

    pub fn new_context(
        &mut self,
        parent: Option<DefinitionContext<'ctx>>,
        kind: DefContextKind,
        span: Span,
    ) -> DefinitionContext<'ctx> {
        let context = alloc_context(self.gcx, parent, kind, span);

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
        ident: Identifier,
        node: NodeID,
        kind: DefinitionKind,
        parent: DefinitionID,
    ) -> DefinitionID {
        let index = DefinitionID::new(
            PackageIndex::new(self.session().package_index),
            DefinitionIndex::from_raw(self.next_index),
        );
        self.node_to_def.insert(node, index);
        self.def_to_kind.insert(index, kind);
        self.def_to_ident.insert(index, ident);
        self.def_to_parent.insert(index, parent);
        self.next_index += 1;
        index
    }

    pub fn def_id(&self, id: NodeID) -> DefinitionID {
        *self.node_to_def.get(&id).expect("bug! node not tagged")
    }

    pub fn def_kind(&self, id: DefinitionID) -> DefinitionKind {
        if id.is_local(self.session().package_index) {
            return *self.def_to_kind.get(&id).expect("bug! node not tagged");
        }

        let resolutions = self.gcx.store.resolutions.borrow();
        let data = resolutions.get(&id.package()).expect("resolution data");
        let kind = *data.def_to_kind.get(&id).expect("def to kind");
        kind
    }

    #[track_caller]
    pub fn get_context(&self, id: &DefinitionID) -> Option<DefinitionContext<'ctx>> {
        if !id.is_local(self.session().package_index) {
            return self.gcx.def_context(*id);
        };
        self.def_to_context.get(id).cloned()
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
        namespace: SymbolNamespace,
        definition: T,
    ) -> bool
    where
        T: ToNameBinding<'ctx>,
    {
        let binding = definition.to_name_binding(self.gcx);
        self.define_in_parent(parent, identifier, binding, namespace)
    }

    pub fn define_in_parent(
        &mut self,
        parent: DefinitionContext<'ctx>,
        identifier: Identifier,
        binding: NameBinding<'ctx>,
        ns: SymbolNamespace,
    ) -> bool {
        let key = BindingKey::new(identifier.symbol, ns);
        let result = self.define_in_context(parent, key, binding);

        match result {
            Ok(..) => {
                return true;
            }
            Err(previous_binding) => {
                let message = format!(
                    "Duplicate Definition, '{}' is already defined in this scope",
                    identifier.symbol
                );
                self.gcx.diagnostics.error(message, identifier.span);

                let message = format!("'{}' is defined here.", identifier.symbol);
                self.gcx
                    .diagnostics
                    .info(message, previous_binding.nearest().span);
                return false;
            }
        }
    }

    pub fn define_in_context(
        &self,
        context: DefinitionContext<'ctx>,
        key: BindingKey,
        binding: NameBinding<'ctx>,
    ) -> Result<Option<NameHolder<'ctx>>, NameHolder<'ctx>> {
        let mut resolutions = context.namespace.borrow_mut();
        self.define_in_resolution_map(key, binding, &mut resolutions)
    }

    pub fn define_in_resolution_map(
        &self,
        key: BindingKey,
        binding: NameBinding<'ctx>,
        map: &mut ResolutionMap<'ctx>,
    ) -> Result<Option<NameHolder<'ctx>>, NameHolder<'ctx>> {
        let resolutions = &mut map.data;

        if resolutions.contains_key(&key) {
            let current_binding = resolutions.get(&key).expect("symbol must be contained");

            // Not a function, Duplicate Definition
            if !binding.is_function() || !current_binding.nearest().is_function() {
                let target = resolutions
                    .get(&key)
                    .cloned()
                    .expect("symbol should be defined");

                return Err(target);
            };

            // Overloaded Function

            let bindings: &[NameBinding<'ctx>] = match current_binding {
                NameHolder::Single(interned) => &[*interned],
                NameHolder::Set(interneds) => interneds,
            };

            let total = 1 + bindings.len();
            let mut combined = Vec::with_capacity(total);
            combined.push(binding);
            combined.extend_from_slice(bindings);
            let new_bindings = self.alloc_slice_copy(&combined);
            let new_holder: NameHolder<'ctx> = NameHolder::Set(new_bindings);
            let prev = resolutions.insert(key, new_holder);
            return Ok(prev);
        } else {
            let prev = resolutions.insert(key, NameHolder::Single(binding));
            return Ok(prev);
        }
    }
}

impl<'ctx> Resolver<'ctx> {
    pub fn record_resolution(&mut self, node: NodeID, resolution: PartialResolution) {
        if let Some(_) = self.resolution_map.insert(node, resolution) {
            // panic!("multiple resolutions recorded for node {node:?}")
        }
    }

    pub fn per_ns<F: FnMut(&mut Self, SymbolNamespace)>(&mut self, mut f: F) {
        f(self, SymbolNamespace::Type);
        f(self, SymbolNamespace::Value);
    }

    pub fn convert_usage_binding(
        &mut self,
        binding: NameBinding<'ctx>,
        usage: ExternalDefinitionUsage<'ctx>,
    ) -> NameBinding<'ctx> {
        alloc_binding(
            self.gcx,
            NameBindingData {
                kind: NameBindingKind::ExternalUsage { binding, usage },
                span: usage.span,
                vis: taroc_hir::TVisibility::Public,
            },
        )
    }
}

impl<'ctx> Resolver<'ctx> {
    pub fn produce(self) -> ResolutionData<'ctx> {
        ResolutionData {
            root: self.root_context,
            node_to_def: self.node_to_def,
            def_to_kind: self.def_to_kind,
            def_to_context: self.def_to_context,
            def_to_ident: self.def_to_ident,
            def_to_parent: self.def_to_parent,
            resolution_map: self.resolution_map,
            generics_map: self.generics_table,
            file_to_imports: self.file_to_imports,
        }
    }
}
