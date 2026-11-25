//! Field-sensitive initialized storage. A place's identity is independent of
//! projection type annotations. Pointee initialization is not guessed from a
//! pointer slot: indirect accesses separately require an initialized access path.
//!
//! Definite initialization tracks uninitialized reads, partial construction
//! and conditional initialization. Reading a GC value never consumes storage.
use super::places::{PlaceKey, ProjectionKey};
use crate::{
    compile::context::Gcx,
    mir::{Body, LocalId, Operand, Place, PlaceElem, Rvalue, StatementKind, TerminatorKind},
    sema::{
        models::{AdtKind, Ty, TyKind},
        tycheck::utils::{instantiate::instantiate_ty_with_args, normalize_aliases},
    },
    thir::{FieldIndex, VariantIndex},
};
use rustc_hash::FxHashMap;

pub type PathId = usize;

#[derive(Debug)]
struct PathNode<'ctx> {
    key: PlaceKey,
    ty: Ty<'ctx>,
    parent: Option<PathId>,
    children: Vec<PathId>,
    expanded: bool,
    complete_children: bool,
    is_enum: bool,
}

/// The finite set of directly owned paths used by a body, including all inline
/// siblings at each projected level. Expanding only observed levels avoids
/// recursively enumerating unused large/recursive aggregate types.
pub struct InitializationPaths<'ctx> {
    nodes: Vec<PathNode<'ctx>>,
    by_key: FxHashMap<PlaceKey, PathId>,
    roots: Vec<PathId>,
}

impl<'ctx> InitializationPaths<'ctx> {
    pub fn build(gcx: Gcx<'ctx>, body: &Body<'ctx>) -> Self {
        let mut paths = Self {
            nodes: vec![],
            by_key: FxHashMap::default(),
            roots: vec![],
        };
        for (local, declaration) in body.locals.iter_enumerated() {
            let root = paths.insert(gcx, PlaceKey::local(local), declaration.ty, None);
            paths.roots.push(root);
            if declaration.kind == crate::mir::LocalKind::ConstructorSelf {
                // Missing fields must remain visible even when source code
                // never mentions them before the initializer's return.
                paths.expand(gcx, root);
            }
        }
        for block in &body.basic_blocks {
            for statement in &block.statements {
                match &statement.kind {
                    StatementKind::Assign(place, value) => {
                        paths.include(gcx, place);
                        value.for_each_place(|place| paths.include(gcx, place));
                    }

                    StatementKind::KeepAlive(operand) => {
                        if let Some(place) = operand.place() {
                            paths.include(gcx, place);
                        }
                    }
                    StatementKind::SetDiscriminant {
                        place,
                        variant_index,
                    } => {
                        paths.include(gcx, place);
                        if !place.projection.contains(&PlaceElem::Deref) {
                            let parent = paths.access_path(place);
                            paths.expand(gcx, parent);
                            if let Some(child) = paths.variant_child(parent, *variant_index) {
                                paths.expand(gcx, child);
                            }
                        }
                    }
                    StatementKind::SetInitialized(local) => {
                        paths.expand(gcx, paths.root(*local));
                    }
                    _ => {}
                }
            }
            if let Some(terminator) = &block.terminator {
                match &terminator.kind {
                    TerminatorKind::Call {
                        func,
                        args,
                        destination,
                        ..
                    } => {
                        if let Some(place) = func.place() {
                            paths.include(gcx, place);
                        }
                        for argument in args {
                            if let Some(place) = argument.place() {
                                paths.include(gcx, place);
                            }
                        }
                        paths.include(gcx, destination);
                    }
                    TerminatorKind::Yield {
                        value, resume_arg, ..
                    } => {
                        if let Some(place) = value.place() {
                            paths.include(gcx, place);
                        }
                        paths.include(gcx, resume_arg);
                    }
                    TerminatorKind::GeneratorYield { value, .. } => {
                        if let Some(place) = value.place() {
                            paths.include(gcx, place);
                        }
                    }
                    TerminatorKind::SwitchInt { discr, .. } => {
                        if let Some(place) = discr.place() {
                            paths.include(gcx, place);
                        }
                    }
                    _ => {}
                }
            }
        }
        paths
    }

    fn insert(
        &mut self,
        gcx: Gcx<'ctx>,
        key: PlaceKey,
        ty: Ty<'ctx>,
        parent: Option<PathId>,
    ) -> PathId {
        if let Some(&id) = self.by_key.get(&key) {
            return id;
        }
        let id = self.nodes.len();
        self.by_key.insert(key.clone(), id);
        self.nodes.push(PathNode {
            key,
            ty,
            parent,
            children: vec![],
            expanded: false,
            complete_children: false,
            is_enum: matches!(normalize_aliases(gcx, ty).kind(), TyKind::Adt(def, _) if def.kind == AdtKind::Enum),
        });
        if let Some(parent) = parent {
            self.nodes[parent].children.push(id);
        }
        id
    }

    pub(crate) fn expand(&mut self, gcx: Gcx<'ctx>, parent: PathId) {
        if self.nodes[parent].expanded {
            return;
        }
        self.nodes[parent].expanded = true;
        let fields: Option<Vec<(ProjectionKey, Ty<'ctx>)>> =
            match normalize_aliases(gcx, self.nodes[parent].ty).kind() {
                TyKind::Tuple(fields) => Some(
                    fields
                        .iter()
                        .enumerate()
                        .map(|(index, ty)| {
                            (
                                ProjectionKey::Field(FieldIndex::from_raw(index as u32)),
                                *ty,
                            )
                        })
                        .collect(),
                ),
                TyKind::Adt(_, _) if gcx.is_class_type(self.nodes[parent].ty) => {
                    // This place owns one initialized handle. Logical payload
                    // fields live in the separate object allocation.
                    None
                }
                TyKind::Adt(def, args) if def.kind == AdtKind::Struct => {
                    gcx.try_get_struct_definition(def.id).map(|definition| {
                        definition
                            .fields
                            .iter()
                            .enumerate()
                            .map(|(index, field)| {
                                (
                                    ProjectionKey::Field(FieldIndex::from_raw(index as u32)),
                                    instantiate_ty_with_args(gcx, field.ty, args),
                                )
                            })
                            .collect()
                    })
                }
                TyKind::Adt(def, args) if def.kind == AdtKind::Enum => {
                    gcx.try_get_enum_definition(def.id).map(|definition| {
                        definition
                            .variants
                            .iter()
                            .enumerate()
                            .map(|(index, _)| {
                                let index = VariantIndex::from_raw(index as u32);
                                (
                                    ProjectionKey::Variant(index),
                                    crate::mir::enum_variant_tuple_ty(gcx, def.id, index, args),
                                )
                            })
                            .collect()
                    })
                }
                TyKind::Closure {
                    closure_def_id,
                    captured_generics,
                    ..
                } => gcx.get_closure_captures(closure_def_id).map(|captures| {
                    captures
                        .captures
                        .iter()
                        .map(|capture| {
                            (
                                ProjectionKey::Field(capture.field_index),
                                capture.storage_ty(gcx, captured_generics),
                            )
                        })
                        .collect()
                }),
                _ => None,
            };
        if let Some(fields) = fields {
            self.nodes[parent].complete_children = true;
            for (projection, ty) in fields {
                let mut key = self.nodes[parent].key.clone();
                key.projection.push(projection);
                self.insert(gcx, key, ty, Some(parent));
            }
        }
    }

    fn include(&mut self, gcx: Gcx<'ctx>, place: &Place<'ctx>) {
        let mut parent = self.roots[place.local.index()];
        for projection in &place.projection {
            let (projection, annotation) = match projection {
                PlaceElem::Deref => break,
                PlaceElem::Field(index, ty) => (ProjectionKey::Field(*index), Some(*ty)),
                PlaceElem::VariantDowncast { index, .. } => (ProjectionKey::Variant(*index), None),
            };
            self.expand(gcx, parent);
            let mut key = self.nodes[parent].key.clone();
            key.projection.push(projection);
            parent = match self.by_key.get(&key) {
                Some(&id) => id,
                None => self.insert(gcx, key, annotation.unwrap_or(gcx.types.void), Some(parent)),
            };
        }
    }

    /// The slot that must be initialized to access this place. At indirection,
    /// this is the pointer/handle prefix, not the separately owned pointee.
    pub fn access_path(&self, place: &Place<'ctx>) -> PathId {
        let mut key = PlaceKey::from(place);
        if let Some(index) = key
            .projection
            .iter()
            .position(|projection| *projection == ProjectionKey::Deref)
        {
            key.projection.truncate(index);
        }
        *self
            .by_key
            .get(&key)
            .expect("all MIR paths were catalogued")
    }

    pub fn root(&self, local: LocalId) -> PathId {
        self.roots[local.index()]
    }
    pub fn children(&self, path: PathId) -> &[PathId] {
        &self.nodes[path].children
    }
    pub fn empty_state(&self) -> PathState {
        PathState {
            initialized: vec![false; self.nodes.len()],
            remainder: vec![false; self.nodes.len()],
            tags: vec![false; self.nodes.len()],
            active_variant: vec![None; self.nodes.len()],
            constructed: vec![false; self.nodes.len()],
        }
    }

    pub fn write(&self, state: &mut PathState, place: &Place<'ctx>) {
        if place.projection.contains(&PlaceElem::Deref) {
            return;
        }
        let path = self.access_path(place);
        let mut child = path;
        while let Some(parent) = self.nodes[child].parent {
            if self.nodes[parent].is_enum {
                // Other cases overlap this storage. Stores establishing one
                // case cannot reuse stale construction facts from another.
                for sibling in &self.nodes[parent].children {
                    if *sibling != child {
                        self.clear_construction(state, *sibling);
                    }
                }
            }
            child = parent;
        }
        self.set(state, path, true);
    }

    pub fn clear(&self, state: &mut PathState, local: LocalId) {
        self.set(state, self.root(local), false);
    }
    pub fn initialize_local(&self, state: &mut PathState, local: LocalId) {
        self.set(state, self.root(local), true);
    }

    fn variant_child(&self, parent: PathId, index: VariantIndex) -> Option<PathId> {
        self.nodes[parent].children.iter().copied().find(|child| {
            self.nodes[*child].key.projection.last() == Some(&ProjectionKey::Variant(index))
        })
    }

    /// A completion marker proves existing stores; it does not write a value.
    /// Empty, fully known aggregates need no stores, but opaque/scalar storage
    /// cannot be initialized merely by asserting that construction finished.
    pub(super) fn construction_ready(&self, state: &PathState, path: PathId) -> bool {
        state.initialized[path]
            || (!self.nodes[path].is_enum
                && self.nodes[path].complete_children
                && self.nodes[path]
                    .children
                    .iter()
                    .all(|child| state.initialized[*child]))
    }

    fn recompute(&self, state: &mut PathState, path: PathId) {
        let node = &self.nodes[path];
        state.initialized[path] = if node.is_enum {
            state.tags[path]
                && match state.active_variant[path] {
                    Some(index) => self
                        .variant_child(path, index)
                        .is_some_and(|child| state.initialized[child]),
                    None => {
                        (node.complete_children || state.remainder[path])
                            && node.children.iter().all(|child| state.initialized[*child])
                    }
                }
        } else {
            (node.complete_children || state.remainder[path])
                && node.children.iter().all(|child| state.initialized[*child])
        };
        state.constructed[path] = if node.is_enum {
            state.initialized[path]
                && state.active_variant[path]
                    .and_then(|index| self.variant_child(path, index))
                    .is_some_and(|child| state.constructed[child])
        } else {
            node.complete_children && node.children.iter().all(|child| state.constructed[*child])
        };
    }

    fn recompute_ancestors(&self, state: &mut PathState, path: PathId) {
        let mut parent = self.nodes[path].parent;
        while let Some(id) = parent {
            self.recompute(state, id);
            parent = self.nodes[id].parent;
        }
    }

    fn set_tag(&self, state: &mut PathState, place: &Place<'ctx>, index: VariantIndex) {
        if place.projection.contains(&PlaceElem::Deref) {
            return;
        }
        let path = self.access_path(place);
        state.tags[path] = self.payload_ready(state, path, index);
        state.active_variant[path] = Some(index);
        if let Some(child) = self.variant_child(path, index) {
            for sibling in &self.nodes[path].children {
                if *sibling != child {
                    self.clear_construction(state, *sibling);
                }
            }
            // A unit case's payload is an empty tuple, with no bytes to write.
            if self.nodes[child].complete_children && self.nodes[child].children.is_empty() {
                self.set_descendants(state, child, true);
            }
        }
        self.recompute(state, path);
        self.recompute_ancestors(state, path);
    }

    fn set(&self, state: &mut PathState, path: PathId, initialized: bool) {
        self.set_descendants(state, path, initialized);
        self.recompute_ancestors(state, path);
    }
    fn set_descendants(&self, state: &mut PathState, path: PathId, initialized: bool) {
        self.set_contents(state, path, initialized, initialized);
    }
    fn clear_construction(&self, state: &mut PathState, path: PathId) {
        state.constructed[path] = false;
        for child in &self.nodes[path].children {
            self.clear_construction(state, *child);
        }
    }
    fn payload_ready(&self, state: &PathState, path: PathId, index: VariantIndex) -> bool {
        self.nodes[path].is_enum
            && self.variant_child(path, index).is_some_and(|child| {
                state.constructed[child]
                    || (self.nodes[child].complete_children
                        && self.nodes[child].children.is_empty())
            })
    }
    fn set_contents(
        &self,
        state: &mut PathState,
        path: PathId,
        initialized: bool,
        constructed: bool,
    ) {
        state.initialized[path] = initialized;
        state.remainder[path] = initialized;
        state.constructed[path] = constructed;
        if self.nodes[path].is_enum {
            state.tags[path] = initialized;
            state.active_variant[path] = None;
        }
        for child in &self.nodes[path].children {
            // A complete enum value proves a valid active payload, not that
            // every alternative's bytes exist or have just been written.
            self.set_contents(
                state,
                *child,
                initialized,
                constructed && !self.nodes[path].is_enum,
            );
        }
    }
}

/// Must-initialized bits intersect at joins. `remainder`
/// preserves opaque/unobserved storage, preventing a write of the only observed
/// child from initializing an otherwise unknown/uninitialized aggregate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PathState {
    initialized: Vec<bool>,
    remainder: Vec<bool>,
    tags: Vec<bool>,
    active_variant: Vec<Option<VariantIndex>>,
    /// Stores establishing a new case, independently of conditional validity
    /// when projecting an already complete enum through its checked tag.
    constructed: Vec<bool>,
}
impl PathState {
    pub fn is_initialized(&self, path: PathId) -> bool {
        self.initialized[path]
    }

    pub fn merge(&mut self, other: &Self) -> bool {
        let mut changed = false;
        for index in 0..self.initialized.len() {
            let initialized = self.initialized[index] && other.initialized[index];
            let remainder = self.remainder[index] && other.remainder[index];
            let tag = self.tags[index] && other.tags[index];
            let active = if self.active_variant[index] == other.active_variant[index] {
                self.active_variant[index]
            } else {
                None
            };
            let constructed = self.constructed[index] && other.constructed[index];
            changed |= self.constructed[index] != constructed;
            self.constructed[index] = constructed;
            changed |= self.tags[index] != tag || self.active_variant[index] != active;
            self.tags[index] = tag;
            self.active_variant[index] = active;
            changed |= self.initialized[index] != initialized || self.remainder[index] != remainder;
            self.initialized[index] = initialized;
            self.remainder[index] = remainder;
        }
        changed
    }
}

/// Incoming states are solved to a fixed point before diagnostics are emitted.
/// A first traversal through a loop/branch is not a proof of initialization.
pub struct Initialization<'ctx> {
    pub paths: InitializationPaths<'ctx>,
    pub incoming: Vec<Option<PathState>>,
}
impl<'ctx> Initialization<'ctx> {
    pub fn compute(gcx: Gcx<'ctx>, body: &Body<'ctx>) -> Self {
        let paths = InitializationPaths::build(gcx, body);
        let mut initial = paths.empty_state();
        for (local, declaration) in body.locals.iter_enumerated() {
            if declaration.kind == crate::mir::LocalKind::Param {
                paths.initialize_local(&mut initial, local);
            }
        }
        let mut incoming = vec![None; body.basic_blocks.len()];
        incoming[body.start_block.index()] = Some(initial);
        let mut pending = vec![body.start_block];
        while let Some(block) = pending.pop() {
            let mut state = incoming[block.index()].clone().unwrap();
            let data = &body.basic_blocks[block];
            for statement in &data.statements {
                paths.transfer_statement(&mut state, &statement.kind);
            }
            let Some(terminator) = &data.terminator else {
                continue;
            };
            for (successor, state) in paths.terminator_edges(state, &terminator.kind) {
                let changed = match &mut incoming[successor.index()] {
                    Some(existing) => existing.merge(&state),
                    slot @ None => {
                        *slot = Some(state);
                        true
                    }
                };
                if changed && !pending.contains(&successor) {
                    pending.push(successor);
                }
            }
        }
        Self { paths, incoming }
    }
}

impl<'ctx> InitializationPaths<'ctx> {
    pub fn transfer_statement(&self, state: &mut PathState, statement: &StatementKind<'ctx>) {
        match statement {
            StatementKind::StorageLive(local) | StatementKind::StorageDead(local) => {
                self.clear(state, *local)
            }
            StatementKind::SetInitialized(local) => {
                let path = self.root(*local);
                if self.construction_ready(state, path) {
                    // This marker emits no stores: preserve active-case and
                    // payload facts instead of inventing every alternative.
                    state.initialized[path] = true;
                    state.remainder[path] = true;
                    state.constructed[path] = true;
                }
            }
            StatementKind::Assign(destination, _) => {
                self.write(state, destination);
            }

            StatementKind::SetDiscriminant {
                place,
                variant_index,
            } => self.set_tag(state, place, *variant_index),
            StatementKind::SourceScope(_)
            | StatementKind::KeepAlive(_)
            | StatementKind::GcSafepoint(_)
            | StatementKind::Nop => {}
        }
    }
    pub fn terminator_edges(
        &self,
        state: PathState,
        terminator: &TerminatorKind<'ctx>,
    ) -> Vec<(crate::mir::BasicBlockId, PathState)> {
        use crate::mir::CallUnwindAction;
        match terminator {
            TerminatorKind::Call {
                destination,
                target,
                unwind,
                ..
            } => {
                let mut normal = state.clone();
                self.write(&mut normal, destination);
                let mut edges = vec![(*target, normal)];
                if let CallUnwindAction::Cleanup(cleanup) = unwind {
                    edges.push((*cleanup, state));
                }
                edges
            }
            TerminatorKind::Yield {
                resume_arg,
                resume,
                cancel,
                no_result,
                unwind,
                ..
            } => {
                let mut normal = state.clone();
                self.write(&mut normal, resume_arg);
                let mut edges = vec![(*resume, normal), (*cancel, state.clone())];

                if let CallUnwindAction::Cleanup(cleanup) = unwind {
                    edges.push((*cleanup, state.clone()));
                }
                if let Some(failed) = no_result {
                    edges.push((*failed, state));
                }
                edges
            }

            TerminatorKind::SwitchInt { discr: _, .. } => terminator
                .successors()
                .into_iter()
                .map(|successor| (successor, state.clone()))
                .collect(),
            _ => terminator
                .successors()
                .into_iter()
                .map(|successor| (successor, state.clone()))
                .collect(),
        }
    }
}

use crate::{
    error::{CompileResult, ReportedError},
    span::Span,
};

/// Check direct ownership and address-path reads. Loan conflicts and dynamic
/// pointee access are separate checks; pointer-slot initialization proves neither.
pub fn validate_initialization<'ctx>(gcx: Gcx<'ctx>, body: &Body<'ctx>) -> CompileResult<()> {
    let analysis = Initialization::compute(gcx, body);
    let paths = &analysis.paths;
    let check_read = |state: &PathState, place: &Place<'ctx>, span: Span| -> CompileResult<()> {
        let path = paths.access_path(place);
        if state.is_initialized(path) {
            return Ok(());
        }
        let name = body.locals[place.local]
            .name
            .map(|name| format!("'{}'", name))
            .unwrap_or_else(|| "<temporary>".to_string());
        let message = format!("use of uninitialized value {name}");
        gcx.dcx().emit_error(message, Some(span));
        Err(ReportedError)
    };
    let check_address = |state: &PathState, place: &Place<'ctx>, span: Span| -> CompileResult<()> {
        if place.projection.contains(&PlaceElem::Deref) {
            check_read(state, place, span)?;
        }
        Ok(())
    };
    let check_operand =
        |state: &mut PathState, operand: &Operand<'ctx>, span: Span| -> CompileResult<()> {
            if let Some(place) = operand.place() {
                check_read(state, place, span)?;
            }
            Ok(())
        };
    let check_rvalue =
        |state: &mut PathState, value: &Rvalue<'ctx>, span: Span| -> CompileResult<()> {
            if let Rvalue::CopyValue { source: place }
            | Rvalue::Ref { place, .. }
            | Rvalue::Discriminant { place } = value
            {
                check_read(state, place, span)?;
            }
            let mut result = Ok(());
            value.for_each_operand(|operand| {
                if result.is_ok() {
                    result = check_operand(state, operand, span);
                }
            });
            result
        };
    for (block, data) in body.basic_blocks.iter_enumerated() {
        let Some(mut state) = analysis.incoming[block.index()].clone() else {
            continue;
        };
        for statement in &data.statements {
            let span = statement.span;
            match &statement.kind {
                StatementKind::Assign(destination, value) => {
                    check_rvalue(&mut state, value, span)?;
                    check_address(&state, destination, span)?;
                }

                StatementKind::KeepAlive(operand) => {
                    if let Some(place) = operand.place() {
                        check_read(&state, place, span)?;
                    }
                }
                StatementKind::SetDiscriminant {
                    place,
                    variant_index,
                } => {
                    check_address(&state, place, span)?;
                    if !place.projection.contains(&PlaceElem::Deref)
                        && !paths.payload_ready(&state, paths.access_path(place), *variant_index)
                    {
                        gcx.dcx().emit_error(
                            "internal error: enum tag publication requires initialized case storage".into(),
                            Some(span),
                        );
                        return Err(ReportedError);
                    }
                }
                StatementKind::SetInitialized(local) => {
                    if !paths.construction_ready(&state, paths.root(*local)) {
                        gcx.dcx().emit_error(
                            "internal error: construction completion has uninitialized storage"
                                .into(),
                            Some(span),
                        );
                        return Err(ReportedError);
                    }
                }
                _ => {}
            }
            // Apply the write only after every input and destination address
            // has been validated.
            paths.transfer_statement(&mut state, &statement.kind);
        }
        let Some(terminator) = &data.terminator else {
            continue;
        };
        let span = terminator.span;
        match &terminator.kind {
            TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } => {
                check_operand(&mut state, func, span)?;
                for argument in args {
                    check_operand(&mut state, argument, span)?;
                }
                check_address(&state, destination, span)?;
            }
            TerminatorKind::Yield {
                value, resume_arg, ..
            } => {
                check_operand(&mut state, value, span)?;
                check_address(&state, resume_arg, span)?;
            }
            TerminatorKind::GeneratorYield { value, .. } => {
                check_operand(&mut state, value, span)?;
            }

            TerminatorKind::SwitchInt { discr, .. } => check_operand(&mut state, discr, span)?,
            TerminatorKind::Return => {
                if normalize_aliases(gcx, body.locals[body.return_local].ty) != gcx.types.void {
                    check_read(&state, &Place::from_local(body.return_local), span)?;
                }
            }
            _ => {}
        }
    }
    gcx.dcx().ok()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mir::{
        BasicBlockData, CallUnwindAction, Constant, ConstantKind, LocalKind, Statement, Terminator,
        test_support::{minimal_body, push_temp, with_test_gcx},
    };

    fn field<'ctx>(local: LocalId, indices: &[(u32, Ty<'ctx>)]) -> Place<'ctx> {
        Place {
            local,
            projection: indices
                .iter()
                .map(|(index, ty)| PlaceElem::Field(FieldIndex::from_raw(*index), *ty))
                .collect(),
        }
    }

    #[test]
    fn completion_markers_require_all_known_fields_or_a_previously_initialized_value() {
        for written in 0..=2 {
            with_test_gcx(|gcx| {
                let mut body = minimal_body(gcx);
                let pair = Ty::new(
                    TyKind::Tuple(
                        gcx.store
                            .interners
                            .intern_ty_list(vec![gcx.types.int, gcx.types.int]),
                    ),
                    gcx,
                );
                let local = push_temp(&mut body, pair);
                let span = body.locals[local].span;
                for index in 0..written {
                    body.basic_blocks[body.start_block]
                        .statements
                        .push(Statement {
                            span,
                            kind: StatementKind::Assign(
                                field(local, &[(index, gcx.types.int)]),
                                Rvalue::Zeroed { ty: gcx.types.int },
                            ),
                        });
                }
                body.basic_blocks[body.start_block]
                    .statements
                    .push(Statement {
                        span,
                        kind: StatementKind::SetInitialized(local),
                    });
                assert_eq!(validate_initialization(gcx, &body).is_ok(), written == 2);
            });
        }
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let local = push_temp(&mut body, gcx.types.int);
            body.basic_blocks[body.start_block]
                .statements
                .push(Statement {
                    span: body.locals[local].span,
                    kind: StatementKind::SetInitialized(local),
                });
            assert!(
                validate_initialization(gcx, &body).is_err(),
                "a marker cannot invent an initialized scalar"
            );
        });
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let empty = Ty::new(
                TyKind::Tuple(gcx.store.interners.intern_ty_list(vec![])),
                gcx,
            );
            let local = push_temp(&mut body, empty);
            body.basic_blocks[body.start_block]
                .statements
                .push(Statement {
                    span: body.locals[local].span,
                    kind: StatementKind::SetInitialized(local),
                });
            assert!(
                validate_initialization(gcx, &body).is_ok(),
                "a known empty aggregate has no missing field stores"
            );
        });
    }

    #[test]
    fn enum_tag_publication_does_not_initialize_missing_payload_storage() {
        for written in 0..=2 {
            crate::test_support::analyze_script(
                "enum State {\ncase empty\ncase pair(int32, int32)\n}\nfunc main() {}",
                |package, gcx| {
                    let definition = gcx.get_enum_definition(package.root.declarations[0].id);
                    let mut body = minimal_body(gcx);
                    let ty = Ty::new(
                        TyKind::Adt(
                            definition.adt_def,
                            crate::sema::models::GenericArguments::empty(),
                        ),
                        gcx,
                    );
                    let local = push_temp(&mut body, ty);
                    let span = body.locals[local].span;
                    let payload_field = |index| Place {
                        local,
                        projection: vec![
                            PlaceElem::VariantDowncast {
                                name: gcx.intern_symbol("pair"),
                                index: VariantIndex::from_raw(1),
                            },
                            PlaceElem::Field(FieldIndex::from_raw(index), gcx.types.int32),
                        ],
                    };
                    for index in 0..written {
                        body.basic_blocks[body.start_block]
                            .statements
                            .push(Statement {
                                span,
                                kind: StatementKind::Assign(
                                    payload_field(index),
                                    Rvalue::Zeroed {
                                        ty: gcx.types.int32,
                                    },
                                ),
                            });
                    }
                    // Catalog both payload fields, including an unwritten one.
                    body.basic_blocks[body.start_block]
                        .statements
                        .push(Statement {
                            span,
                            kind: StatementKind::SetDiscriminant {
                                place: Place::from_local(local),
                                variant_index: VariantIndex::from_raw(1),
                            },
                        });
                    body.basic_blocks[body.start_block]
                        .statements
                        .push(Statement {
                            span,
                            kind: StatementKind::SetDiscriminant {
                                place: Place::from_local(local),
                                variant_index: VariantIndex::from_raw(0),
                            },
                        });
                    let paths = InitializationPaths::build(gcx, &body);
                    let mut state = paths.empty_state();
                    let statements = &body.basic_blocks[body.start_block].statements;
                    for statement in &statements[..statements.len() - 1] {
                        paths.transfer_statement(&mut state, &statement.kind);
                    }
                    assert_eq!(
                        state.is_initialized(paths.root(local)),
                        written == 2,
                        "installing a tag must not initialize its payload"
                    );
                    if written == 2 {
                        paths.set(&mut state, paths.access_path(&payload_field(0)), false);
                        assert!(!state.is_initialized(paths.root(local)));
                        paths.write(&mut state, &payload_field(0));
                        assert!(
                            state.is_initialized(paths.root(local)),
                            "restoring a payload repairs the still-valid active case"
                        );
                    }
                    paths.transfer_statement(
                        &mut state,
                        &StatementKind::SetDiscriminant {
                            place: Place::from_local(local),
                            variant_index: VariantIndex::from_raw(0),
                        },
                    );
                    assert!(
                        state.is_initialized(paths.root(local)),
                        "a unit case needs only its tag"
                    );
                    paths.transfer_statement(
                        &mut state,
                        &StatementKind::SetDiscriminant {
                            place: Place::from_local(local),
                            variant_index: VariantIndex::from_raw(1),
                        },
                    );
                    assert!(
                        !state.is_initialized(paths.root(local)),
                        "switching back cannot resurrect an old payload's construction facts"
                    );
                    paths.initialize_local(&mut state, local);
                    assert!(state.is_initialized(paths.root(local)));
                    paths.transfer_statement(
                        &mut state,
                        &StatementKind::SetDiscriminant {
                            place: Place::from_local(local),
                            variant_index: VariantIndex::from_raw(1),
                        },
                    );
                    assert!(
                        !state.is_initialized(paths.root(local)),
                        "a complete value with an unknown active case cannot manufacture another payload"
                    );
                },
            );
        }
    }

    #[test]
    fn nested_siblings_remain_initialized_and_restoring_the_hole_repairs_parents() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let pair = Ty::new(
                TyKind::Tuple(
                    gcx.store
                        .interners
                        .intern_ty_list(vec![gcx.types.int, gcx.types.int]),
                ),
                gcx,
            );
            let outer = Ty::new(
                TyKind::Tuple(
                    gcx.store
                        .interners
                        .intern_ty_list(vec![pair, gcx.types.int]),
                ),
                gcx,
            );
            let local = push_temp(&mut body, outer);
            let left = field(local, &[(0, pair), (0, gcx.types.int)]);
            let right = field(local, &[(0, pair), (1, gcx.types.int)]);
            let span = body.locals[local].span;
            body.basic_blocks[body.start_block].statements = vec![left.clone(), right.clone()]
                .into_iter()
                .map(|place| Statement {
                    kind: StatementKind::KeepAlive(Operand::Copy(place)),
                    span,
                })
                .collect();
            let paths = InitializationPaths::build(gcx, &body);
            let mut state = paths.empty_state();
            paths.initialize_local(&mut state, local);
            paths.set(&mut state, paths.access_path(&left), false);
            assert!(!state.is_initialized(paths.root(local)));
            assert!(state.is_initialized(paths.access_path(&right)));
            paths.write(&mut state, &right);
            assert!(!state.is_initialized(paths.root(local)));
            paths.write(&mut state, &left);
            assert!(state.is_initialized(paths.root(local)));
            paths.clear(&mut state, local);
            paths.write(&mut state, &left);
            paths.write(&mut state, &right);
            assert!(
                !state.is_initialized(paths.root(local)),
                "unwritten tag sibling must stay uninitialized"
            );
            let tag = field(local, &[(1, gcx.types.int)]);
            paths.write(&mut state, &tag);
            assert!(state.is_initialized(paths.root(local)));
        });
    }

    #[test]
    fn gc_value_copies_preserve_initialization_across_loop_backedges() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let source = push_temp(&mut body, gcx.types.int);
            body.locals[source].kind = LocalKind::Param;
            let target = push_temp(&mut body, gcx.types.int);
            let span = body.locals[source].span;
            let loop_block = body.basic_blocks.push(BasicBlockData {
                note: None,
                statements: vec![Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(target),
                        Rvalue::Use(Operand::Copy(Place::from_local(source))),
                    ),
                    span,
                }],
                terminator: None,
            });
            body.basic_blocks[body.start_block].terminator = Some(Terminator {
                kind: TerminatorKind::Goto { target: loop_block },
                span,
            });
            body.basic_blocks[loop_block].terminator = Some(Terminator {
                kind: TerminatorKind::Goto { target: loop_block },
                span,
            });
            let analysis = Initialization::compute(gcx, &body);
            let state = analysis.incoming[loop_block.index()].as_ref().unwrap();
            assert!(
                state.is_initialized(analysis.paths.root(source)),
                "copying a value on a backedge must not consume its input"
            );
            assert!(validate_initialization(gcx, &body).is_ok());
        });
    }

    #[test]
    fn a_join_does_not_publish_a_value_initialized_on_only_one_branch() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let local = push_temp(&mut body, gcx.types.int);
            let span = body.locals[local].span;
            let join = body.basic_blocks.push(BasicBlockData {
                note: None,
                statements: vec![Statement {
                    kind: StatementKind::KeepAlive(Operand::Copy(Place::from_local(local))),
                    span,
                }],
                terminator: Some(Terminator {
                    kind: TerminatorKind::Return,
                    span,
                }),
            });
            let initialized = body.basic_blocks.push(BasicBlockData {
                note: None,
                statements: vec![Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(local),
                        Rvalue::Zeroed { ty: gcx.types.int },
                    ),
                    span,
                }],
                terminator: Some(Terminator {
                    kind: TerminatorKind::Goto { target: join },
                    span,
                }),
            });
            body.basic_blocks[body.start_block].terminator = Some(Terminator {
                kind: TerminatorKind::SwitchInt {
                    discr: Operand::Constant(Constant {
                        ty: gcx.types.bool,
                        value: ConstantKind::Bool(true),
                    }),
                    targets: vec![(1, initialized)],
                    otherwise: join,
                },
                span,
            });
            let analysis = Initialization::compute(gcx, &body);
            assert!(
                !analysis.incoming[join.index()]
                    .as_ref()
                    .unwrap()
                    .is_initialized(analysis.paths.root(local))
            );
            assert!(validate_initialization(gcx, &body).is_err());
        });
    }

    #[test]
    fn calls_preserve_arguments_but_only_initialize_normal_results() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let source = push_temp(&mut body, gcx.types.int);
            body.locals[source].kind = LocalKind::Param;
            let output = push_temp(&mut body, gcx.types.int);
            let span = body.locals[source].span;
            let normal = body.basic_blocks.push(BasicBlockData {
                note: None,
                statements: vec![],
                terminator: Some(Terminator {
                    kind: TerminatorKind::Return,
                    span,
                }),
            });
            let cleanup = body.basic_blocks.push(BasicBlockData {
                note: None,
                statements: vec![],
                terminator: Some(Terminator {
                    kind: TerminatorKind::ResumeUnwind,
                    span,
                }),
            });
            body.basic_blocks[body.start_block].terminator = Some(Terminator {
                kind: TerminatorKind::Call {
                    func: Operand::Constant(Constant {
                        ty: gcx.types.void,
                        value: ConstantKind::Unit,
                    }),
                    args: vec![Operand::Copy(Place::from_local(source))],
                    destination: Place::from_local(output),
                    target: normal,
                    unwind: CallUnwindAction::Cleanup(cleanup),
                },
                span,
            });
            let analysis = Initialization::compute(gcx, &body);
            let normal_state = analysis.incoming[normal.index()].as_ref().unwrap();
            let cleanup_state = analysis.incoming[cleanup.index()].as_ref().unwrap();
            assert!(normal_state.is_initialized(analysis.paths.root(source)));
            assert!(cleanup_state.is_initialized(analysis.paths.root(source)));
            assert!(normal_state.is_initialized(analysis.paths.root(output)));
            assert!(!cleanup_state.is_initialized(analysis.paths.root(output)));
        });
    }

    #[test]
    fn a_write_through_an_uninitialized_pointer_does_not_initialize_the_pointer() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let pointer_ty = Ty::new(
                TyKind::Pointer(gcx.types.int, crate::hir::Mutability::Mutable),
                gcx,
            );
            let pointer = push_temp(&mut body, pointer_ty);
            let span = body.locals[pointer].span;
            let pointee = Place {
                local: pointer,
                projection: vec![PlaceElem::Deref],
            };
            body.basic_blocks[body.start_block]
                .statements
                .push(Statement {
                    kind: StatementKind::Assign(
                        pointee.clone(),
                        Rvalue::Zeroed { ty: gcx.types.int },
                    ),
                    span,
                });
            let analysis = Initialization::compute(gcx, &body);
            let mut state = analysis.paths.empty_state();
            analysis.paths.write(&mut state, &pointee);
            assert!(!state.is_initialized(analysis.paths.root(pointer)));
            assert!(validate_initialization(gcx, &body).is_err());
        });
    }

    #[test]
    fn nested_moves_and_restoration_work_in_source() {
        let diagnostics = crate::test_support::analyze_script_mir_diagnostics(
            "struct Token { id: int32 }\nstruct Pair { left: Token; right: Token }\nstruct Outer { pair: Pair; tag: int32 }\nfunc consume(_ value: Token) {}\nfunc consumeOuter(_ value: Outer) {}\nfunc main() {\nvar outer = Outer { pair: Pair { left: Token { id: 1 }, right: Token { id: 2 } }, tag: 3 }\nleft := outer.pair.left\nconsume(outer.pair.right)\nouter.pair.left = left\nouter.pair.right = Token { id: 4 }\nconsumeOuter(outer)\n}",
        );
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
    }

    #[test]
    fn nested_mutation_rejects_readonly_ancestors() {
        for source in [
            "struct Inner { count: int32 }\nstruct Outer { readonly inner: Inner }\nfunc main() { var outer = Outer { inner: Inner { count: 1 } }; outer.inner.count = 2 }",
        ] {
            let diagnostics = crate::test_support::analyze_script_mir_diagnostics(source);
            assert!(
                diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.message.contains("immutable")),
                "{diagnostics:?}"
            );
        }
    }

    #[test]
    fn failed_guards_leave_noncopyable_payloads_for_later_arms() {
        let diagnostics = crate::test_support::analyze_script_mir_diagnostics(
            "struct Token { id: int32 }\nenum State {\ncase token(Token)\n}\nfunc inspect(_ token: &Token) -> bool { token.id < 0 }\nfunc read(_ state: State) -> int32 { match state {\ncase .token(token) if inspect(&token) => token.id\ncase .token(token) => token.id\n} }\nfunc main() {}",
        );
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
    }

    #[test]
    fn guards_pass_payloads_by_value_without_consuming_later_arms() {
        let diagnostics = crate::test_support::analyze_script_mir_diagnostics(
            "struct Token { id: int32 }\nenum State {\ncase token(Token)\n}\nfunc consume(_ token: Token) -> bool { true }\nfunc read(_ state: State) -> int32 { match state {\ncase .token(token) if consume(token) => 1\ncase .token(token) => token.id\n} }\nfunc main() {}",
        );
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
    }

    #[test]
    fn guards_can_use_writable_payload_copies() {
        let diagnostics = crate::test_support::analyze_script_mir_diagnostics(
            "struct Token { id: int32 }\nenum State {\ncase token(Token)\n}\nfunc mutate(_ token: &Token) -> bool { token.id = 3; true }\nfunc read(_ state: &State) -> int32 { match *state {\ncase .token(token) if mutate(&token) => token.id\ncase .token(token) => token.id\n} }\nfunc main() {}",
        );
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
    }

    #[test]
    fn binding_conditions_keep_success_initialization_on_the_actual_success_edge() {
        for body in [
            "if case .some(value) = maybe && value > 0 { value } else { 0 }",
            "guard case .some(value) = maybe else { return 0 }; value",
        ] {
            let source = format!(
                "enum Maybe {{\ncase some(int32)\ncase none\n}}\nfunc read(_ maybe: Maybe) -> int32 {{ {body} }}\nfunc main() {{}}"
            );
            let diagnostics = crate::test_support::analyze_script_mir_diagnostics(&source);
            assert!(diagnostics.is_empty(), "{diagnostics:?}");
        }
    }

    #[test]
    fn never_returning_cleanup_does_not_reach_an_uninitialized_return_slot() {
        let diagnostics = crate::test_support::analyze_script_mir_diagnostics(
            "func diverge() -> ! { loop {} }\nfunc result() -> int32 { defer { diverge() } }\nfunc main() {}",
        );
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
    }

    #[test]
    fn unit_alias_returns_do_not_require_a_runtime_value_slot() {
        let diagnostics = crate::test_support::analyze_script_mir_diagnostics(
            "type Unit = ()\nfunc nothing() -> Unit {}\nfunc relay() -> Unit { nothing() }\nfunc main() { relay() }",
        );
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }

    #[test]
    fn repetition_copies_any_value() {
        for count in [0, 1, 2] {
            let diagnostics = crate::test_support::analyze_script_mir_diagnostics(&format!(
                "struct Owned {{ value: int32 }}\nfunc main() {{ owner := Owned {{ value: 7 }}; var repeated: [Owned; {count}] = [owner; {count}] }}"
            ));
            assert!(diagnostics.is_empty(), "{diagnostics:#?}");
        }
    }

    #[test]
    fn symbolic_repeat_count_is_diagnosed_before_concrete_mir_lowering() {
        let diagnostics = crate::test_support::analyze_script_mir_diagnostics(
            "func fill[const N: usize](_ value: int32) -> [int32; N] { [value; N] }\nfunc main() {}",
        );
        assert!(
            diagnostics
                .iter()
                .any(|d| d.message.contains("const-generic repeat counts")),
            "{diagnostics:#?}"
        );
        assert!(
            !diagnostics
                .iter()
                .any(|d| d.message.contains("internal error")),
            "{diagnostics:#?}"
        );
    }
}
