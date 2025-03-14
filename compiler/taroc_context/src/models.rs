use std::{cell::RefCell, marker::PhantomData};

use bumpalo::Bump;
use rustc_hash::FxHashMap;
use taroc_hir::{DefinitionID, DefinitionKind, NodeID, PartialRes};
use taroc_resolve_models::DefinitionContext;

pub struct ContextStore<'ctx> {
    pub interners: ContextInterners<'ctx>,
    pub resolutions: RefCell<FxHashMap<usize, ResolutionData<'ctx>>>,
    pub package_mapping: RefCell<FxHashMap<String, usize>>,
}

impl<'ctx> ContextStore<'ctx> {
    pub fn new() -> ContextStore<'ctx> {
        ContextStore {
            interners: ContextInterners::new(),
            resolutions: RefCell::default(),
            package_mapping: RefCell::default(),
        }
    }
}

pub struct ContextInterners<'ctx> {
    pub resolve: Bump,
    _data: PhantomData<DefinitionContext<'ctx>>,
}

impl<'ctx> ContextInterners<'ctx> {
    pub fn new() -> ContextInterners<'ctx> {
        ContextInterners {
            resolve: Bump::new(),
            _data: PhantomData::default(),
        }
    }
}

pub struct ResolutionData<'ctx> {
    pub root: DefinitionContext<'ctx>,
    pub node_to_def: FxHashMap<NodeID, DefinitionID>,
    pub def_to_kind: FxHashMap<DefinitionID, DefinitionKind>,
    pub partial_resolution_map: FxHashMap<NodeID, PartialRes>,
}
