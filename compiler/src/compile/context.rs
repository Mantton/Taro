use crate::span::Symbol;
use crate::{
    PackageIndex,
    codegen::target::TargetLayout,
    compile::config::{BuildProfile, Config, StdMode},
    diagnostics::DiagCtx,
    error::CompileResult,
    hir::{self, DefinitionID, StdItem},
    mir::{self, Body, EscapeSummary},
    sema::std_items::{StdItemEntry, StdItemRegistry},
    sema::{
        models::{
            AliasKind, CanonicalGoalKey, ClosureCaptures, ConformanceRecord, ConformanceRecordId,
            ConformanceWitness, Const, Constraint, EnumDefinition, EnumVariant, FloatTy,
            GenericArgument, GenericArguments, GenericParameter, Generics, GoalResult, IntTy,
            InterfaceDefinition, InterfaceGoal, InterfaceRequirements, LabeledFunctionSignature,
            SelectionMode, SelectionResult, StructDefinition, StructField, Ty, TyKind, TyList,
            UIntTy,
        },
        resolve::models::{
            DefinitionKind, PrimaryType, ResolutionOutput, ScopeData, ScopeEntryData, TypeHead,
            UsageEntryData, Visibility,
        },
    },
    specialize::Instance,
    thir::VariantIndex,
    utils::intern::{Interned, InternedInSet, InternedSet, List},
};
use bumpalo::Bump;
use ecow::EcoString;
use rustc_hash::{FxHashMap, FxHashSet};
use std::rc::Rc;
use std::{cell::RefCell, ops::Deref, path::PathBuf};

pub type Gcx<'gcx> = GlobalContext<'gcx>;

#[derive(Clone, Copy)]
pub struct GlobalContext<'arena> {
    context: &'arena CompilerContext<'arena>,
    pub config: &'arena Config,
}

impl<'arena> Deref for GlobalContext<'arena> {
    type Target = &'arena CompilerContext<'arena>;
    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &self.context
    }
}

impl<'arena> GlobalContext<'arena> {
    pub fn new(
        context: &'arena CompilerContext<'arena>,
        config: &'arena Config,
    ) -> GlobalContext<'arena> {
        GlobalContext { context, config }
    }

    pub fn package_index(self) -> PackageIndex {
        self.config.index
    }

    pub fn cache_package_ident(self, ident: EcoString) {
        self.context
            .store
            .package_idents
            .borrow_mut()
            .insert(self.package_index(), ident);
    }

    pub fn package_ident(self, pkg: PackageIndex) -> Option<EcoString> {
        self.context
            .store
            .package_idents
            .borrow()
            .get(&pkg)
            .cloned()
    }

    pub fn intern_symbol(self, text: &str) -> Symbol {
        Symbol::new(text)
    }

    pub fn symbol_eq(self, symbol: impl AsRef<str>, text: &str) -> bool {
        symbol.as_ref() == text
    }

    pub fn symbol_text(self, symbol: impl AsRef<str>) -> EcoString {
        symbol.as_ref().into()
    }
}

impl<'arena> GlobalContext<'arena> {
    pub fn cache_type(self, id: DefinitionID, ty: Ty<'arena>) {
        let mut cache = self.context.store.type_databases.borrow_mut();
        let package_index = id.package();
        let database = cache.entry(package_index).or_insert_with(Default::default);
        database.def_to_ty.insert(id, ty);
    }

    pub fn cache_const(self, id: DefinitionID, value: Const<'arena>) {
        let mut cache = self.context.store.type_databases.borrow_mut();
        let package_index = id.package();
        let database = cache.entry(package_index).or_insert_with(Default::default);
        database.def_to_const.insert(id, value);
    }

    pub fn cache_static_mutability(self, id: DefinitionID, mutability: hir::Mutability) {
        let mut cache = self.context.store.type_databases.borrow_mut();
        let package_index = id.package();
        let database = cache.entry(package_index).or_insert_with(Default::default);
        database.def_to_static_mutability.insert(id, mutability);
    }

    pub fn cache_static_initializer(self, id: DefinitionID, value: Const<'arena>) {
        let mut cache = self.context.store.type_databases.borrow_mut();
        let package_index = id.package();
        let database = cache.entry(package_index).or_insert_with(Default::default);
        database.def_to_static_init.insert(id, value);
    }

    /// Updates the constraints for a definition, overwriting any existing entry.
    ///
    /// This is used during multi-pass constraint collection where bounds are collected first
    /// and committed to the database so that subsequent constraint generation (e.g., for
    /// associated type projections) can resolve against them.
    ///
    /// Also invalidates the canonical constraints cache to ensure re-computation.
    pub fn update_constraints(
        self,
        id: DefinitionID,
        constraints: Vec<crate::span::Spanned<Constraint<'arena>>>,
    ) {
        let mut cache = self.context.store.type_databases.borrow_mut();
        let package_index = id.package();
        let database = cache.entry(package_index).or_insert_with(Default::default);
        database.def_to_constraints.insert(id, constraints);
        // Invalidate canonical constraints cache to ensure re-computation
        database.def_to_canon_constraints.remove(&id);
    }

    pub fn cache_constraints(
        self,
        id: DefinitionID,
        constraints: Vec<crate::span::Spanned<Constraint<'arena>>>,
    ) {
        let mut cache = self.context.store.type_databases.borrow_mut();
        let package_index = id.package();
        let database = cache.entry(package_index).or_insert_with(Default::default);
        database.def_to_constraints.insert(id, constraints);
    }

    pub fn constraints_of(self, id: DefinitionID) -> Vec<crate::span::Spanned<Constraint<'arena>>> {
        self.with_type_database(id.package(), |db| {
            db.def_to_constraints.get(&id).cloned().unwrap_or_default()
        })
    }

    pub fn cache_canonical_constraints(
        self,
        id: DefinitionID,
        constraints: Vec<crate::span::Spanned<Constraint<'arena>>>,
    ) {
        let mut cache = self.context.store.type_databases.borrow_mut();
        let package_index = id.package();
        let database = cache.entry(package_index).or_insert_with(Default::default);
        database.def_to_canon_constraints.insert(id, constraints);
    }

    pub fn canonical_constraints_of(
        self,
        id: DefinitionID,
    ) -> Vec<crate::span::Spanned<Constraint<'arena>>> {
        self.with_type_database(id.package(), |db| {
            db.def_to_canon_constraints
                .get(&id)
                .cloned()
                .unwrap_or_default()
        })
    }

    pub fn cache_alias_type(self, id: DefinitionID, ty: Ty<'arena>) {
        self.with_type_database(id.package(), |db| {
            db.resolved_aliases.insert(id, ty);
        });
    }

    pub fn cache_signature(self, id: DefinitionID, sig: LabeledFunctionSignature<'arena>) {
        let mut cache = self.context.store.type_databases.borrow_mut();
        let package_index = id.package();
        let database = cache.entry(package_index).or_insert_with(Default::default);
        let alloc = self.context.store.arenas.function_signatures.alloc(sig);
        database.def_to_fn_sig.insert(id, alloc);
    }

    pub fn cache_async_body_output(self, id: DefinitionID, ty: Ty<'arena>) {
        self.with_type_database(id.package(), |db| {
            db.def_to_async_body_output.insert(id, ty);
        });
    }

    pub fn cache_struct_definition(self, id: DefinitionID, def: StructDefinition<'arena>) {
        let mut cache = self.context.store.type_databases.borrow_mut();
        let package_index = id.package();
        let database = cache.entry(package_index).or_insert_with(Default::default);
        let alloc = self.context.store.arenas.struct_definitions.alloc(def);
        database.def_to_struct_def.insert(id, alloc);
    }

    pub fn cache_enum_definition(self, id: DefinitionID, def: EnumDefinition<'arena>) {
        let mut cache = self.context.store.type_databases.borrow_mut();
        let package_index = id.package();
        let database = cache.entry(package_index).or_insert_with(Default::default);
        let alloc = self.context.store.arenas.enum_definitions.alloc(def);
        database.def_to_enum_def.insert(id, alloc);
    }

    pub fn cache_impl_type_head(self, impl_id: DefinitionID, head: TypeHead) {
        self.with_type_database(impl_id.package(), |db| {
            db.impl_to_type_head.insert(impl_id, head);
            db.type_head_to_impls.entry(head).or_default().push(impl_id);
        });
    }

    pub fn cache_impl_target_ty(self, impl_id: DefinitionID, ty: Ty<'arena>) {
        self.with_type_database(impl_id.package(), |db| {
            db.impl_to_target_ty.insert(impl_id, ty);
        });
    }

    pub fn insert_conformance_record(
        self,
        record: ConformanceRecord<'arena>,
    ) -> ConformanceRecordId {
        let package = self.package_index();
        self.with_session_type_database(|db| {
            let id = ConformanceRecordId::new(package, db.next_conformance_record_index);
            db.next_conformance_record_index += 1;
            db.conformance_records.insert(id, record);
            db.conformance_by_interface_head
                .entry((record.interface.id, record.target))
                .or_default()
                .push(id);
            db.conformance_by_interface
                .entry(record.interface.id)
                .or_default()
                .push(id);
            db.conformance_by_head
                .entry(record.target)
                .or_default()
                .push(id);
            db.conformance_by_extension
                .entry(record.extension)
                .or_default()
                .push(id);
            // New impls can change selection/witness answers for already-cached goals.
            db.selection_cache.clear();
            db.witness_cache.clear();
            id
        })
    }

    pub fn conformance_record(self, id: ConformanceRecordId) -> Option<ConformanceRecord<'arena>> {
        self.with_type_database(id.package, |db| db.conformance_records.get(&id).cloned())
    }

    pub fn conformance_records_for_interface_head(
        self,
        package: PackageIndex,
        interface_id: DefinitionID,
        head: TypeHead,
    ) -> Vec<ConformanceRecord<'arena>> {
        self.with_type_database(package, |db| {
            db.conformance_by_interface_head
                .get(&(interface_id, head))
                .into_iter()
                .flat_map(|ids| ids.iter())
                .filter_map(|id| db.conformance_records.get(id).cloned())
                .collect()
        })
    }

    pub fn conformance_record_entries_for_interface_head(
        self,
        package: PackageIndex,
        interface_id: DefinitionID,
        head: TypeHead,
    ) -> Vec<(ConformanceRecordId, ConformanceRecord<'arena>)> {
        self.with_type_database(package, |db| {
            db.conformance_by_interface_head
                .get(&(interface_id, head))
                .into_iter()
                .flat_map(|ids| ids.iter())
                .filter_map(|id| db.conformance_records.get(id).map(|record| (*id, *record)))
                .collect()
        })
    }

    pub fn conformance_records_for_interface(
        self,
        package: PackageIndex,
        interface_id: DefinitionID,
    ) -> Vec<ConformanceRecord<'arena>> {
        self.with_type_database(package, |db| {
            db.conformance_by_interface
                .get(&interface_id)
                .into_iter()
                .flat_map(|ids| ids.iter())
                .filter_map(|id| db.conformance_records.get(id).cloned())
                .collect()
        })
    }

    pub fn conformance_records_for_head(
        self,
        package: PackageIndex,
        head: TypeHead,
    ) -> Vec<ConformanceRecord<'arena>> {
        self.with_type_database(package, |db| {
            db.conformance_by_head
                .get(&head)
                .into_iter()
                .flat_map(|ids| ids.iter())
                .filter_map(|id| db.conformance_records.get(id).cloned())
                .collect()
        })
    }

    pub fn conformance_records_for_extension(
        self,
        package: PackageIndex,
        extension: DefinitionID,
    ) -> Vec<ConformanceRecord<'arena>> {
        self.with_type_database(package, |db| {
            db.conformance_by_extension
                .get(&extension)
                .into_iter()
                .flat_map(|ids| ids.iter())
                .filter_map(|id| db.conformance_records.get(id).cloned())
                .collect()
        })
    }

    pub fn all_conformance_records(self, package: PackageIndex) -> Vec<ConformanceRecord<'arena>> {
        self.with_type_database(package, |db| {
            db.conformance_records.values().copied().collect()
        })
    }

    pub fn get_selection_cache(
        self,
        package: PackageIndex,
        key: CanonicalGoalKey<'arena>,
    ) -> Option<SelectionResult<'arena>> {
        self.with_type_database(package, |db| db.selection_cache.get(&key).cloned())
    }

    pub fn put_selection_cache(
        self,
        package: PackageIndex,
        key: CanonicalGoalKey<'arena>,
        value: SelectionResult<'arena>,
    ) {
        self.with_type_database(package, |db| {
            db.selection_cache.insert(key, value);
        });
    }

    pub fn get_witness_cache(
        self,
        package: PackageIndex,
        key: CanonicalGoalKey<'arena>,
    ) -> Option<ConformanceWitness<'arena>> {
        self.with_type_database(package, |db| db.witness_cache.get(&key).cloned())
    }

    pub fn put_witness_cache(
        self,
        package: PackageIndex,
        key: CanonicalGoalKey<'arena>,
        value: ConformanceWitness<'arena>,
    ) {
        self.with_type_database(package, |db| {
            db.witness_cache.insert(key, value);
        });
    }

    pub fn select_interface_impl(
        self,
        goal: InterfaceGoal<'arena>,
        mode: SelectionMode,
    ) -> SelectionResult<'arena> {
        crate::sema::impl_engine::select_interface_impl(self, goal, mode)
    }

    pub fn prove_interface_goal(
        self,
        goal: InterfaceGoal<'arena>,
        mode: SelectionMode,
    ) -> GoalResult {
        crate::sema::impl_engine::prove_interface_goal(self, goal, mode)
    }

    pub fn build_conformance_witness(
        self,
        goal: InterfaceGoal<'arena>,
        mode: SelectionMode,
    ) -> Result<ConformanceWitness<'arena>, crate::sema::models::SelectionError<'arena>> {
        crate::sema::impl_engine::build_conformance_witness(self, goal, mode)
    }

    pub fn cache_generics(self, id: DefinitionID, generics: Generics) {
        let mut cache = self.context.store.type_databases.borrow_mut();
        let package_index = id.package();
        let database = cache.entry(package_index).or_insert_with(Default::default);
        let generics = self.context.store.arenas.generics.alloc(generics);
        let ok = database.def_to_generics.insert(id, generics).is_none();
        debug_assert!(ok, "duplicated generic information")
    }

    pub fn cache_generic_type_default(self, param_id: DefinitionID, ty: Ty<'arena>) {
        self.with_type_database(param_id.package(), |db| {
            db.generic_type_defaults.insert(param_id, ty);
        });
    }

    pub fn try_generic_type_default(self, param_id: DefinitionID) -> Option<Ty<'arena>> {
        self.with_type_database(param_id.package(), |db| {
            db.generic_type_defaults.get(&param_id).copied()
        })
    }

    pub fn cache_generic_const_param_ty(self, param_id: DefinitionID, ty: Ty<'arena>) {
        self.with_type_database(param_id.package(), |db| {
            db.generic_const_param_tys.insert(param_id, ty);
        });
    }

    pub fn try_generic_const_param_ty(self, param_id: DefinitionID) -> Option<Ty<'arena>> {
        self.with_type_database(param_id.package(), |db| {
            db.generic_const_param_tys.get(&param_id).copied()
        })
    }

    pub fn cache_generic_const_default(self, param_id: DefinitionID, value: Const<'arena>) {
        self.with_type_database(param_id.package(), |db| {
            db.generic_const_defaults.insert(param_id, value);
        });
    }

    pub fn try_generic_const_default(self, param_id: DefinitionID) -> Option<Const<'arena>> {
        self.with_type_database(param_id.package(), |db| {
            db.generic_const_defaults.get(&param_id).copied()
        })
    }

    pub fn cache_attributes(self, id: DefinitionID, attributes: hir::AttributeList) {
        let mut cache = self.context.store.type_databases.borrow_mut();
        let package_index = id.package();
        let database = cache.entry(package_index).or_insert_with(Default::default);
        let attributes = self.context.store.arenas.global.alloc(attributes);
        let ok = database.def_to_attributes.insert(id, attributes).is_none();
        debug_assert!(ok, "duplicated attribute information")
    }

    pub fn cache_definition_unsafe(self, id: DefinitionID, is_unsafe: bool) {
        self.with_type_database(id.package(), |db| {
            if is_unsafe {
                db.def_to_unsafe.insert(id);
            } else {
                db.def_to_unsafe.remove(&id);
            }
        });
    }

    pub fn allocate_synthetic_id(self, package: PackageIndex) -> DefinitionID {
        let store = &self.context.store;
        let id = store.next_synthetic_id.get();
        store.next_synthetic_id.set(id + 1);
        // Offset to avoid collision with low IDs
        let index = 0xF000_0000 + id;
        DefinitionID::new(
            package,
            crate::sema::resolve::models::DefinitionIndex::from_raw(index),
        )
    }

    pub fn register_synthetic_definition(
        self,
        id: DefinitionID,
        def: crate::sema::models::SyntheticDefinition<'arena>,
    ) {
        self.context
            .store
            .synthetic_definitions
            .borrow_mut()
            .insert(id, def);
    }

    pub fn register_default_value_expr(self, id: DefinitionID, expr: &'arena hir::Expression) {
        self.context
            .store
            .default_value_exprs
            .borrow_mut()
            .insert(id, expr);
    }

    pub fn queue_synthetic_mir_body(self, id: DefinitionID, body: Body<'arena>) {
        self.context
            .store
            .queued_mir_bodies
            .borrow_mut()
            .insert(id, body);
    }

    pub fn take_queued_mir_bodies(self) -> FxHashMap<DefinitionID, Body<'arena>> {
        std::mem::take(&mut *self.context.store.queued_mir_bodies.borrow_mut())
    }
}

impl<'arena> GlobalContext<'arena> {
    #[track_caller]
    #[inline]
    pub fn with_type_database<F, T>(self, index: PackageIndex, func: F) -> T
    where
        F: FnOnce(&mut TypeDatabase<'arena>) -> T,
    {
        let mut cache = self.context.store.type_databases.borrow_mut();
        let database = cache.entry(index).or_insert_with(Default::default);
        func(database)
    }

    #[track_caller]
    #[inline]
    pub fn with_session_type_database<F, T>(self, func: F) -> T
    where
        F: FnOnce(&mut TypeDatabase<'arena>) -> T,
    {
        self.with_type_database(self.package_index(), func)
    }
}

// Package iteration helpers
impl<'arena> GlobalContext<'arena> {
    /// Returns package indices for all dependencies plus std (if available).
    /// Does NOT include the current session package.
    pub fn visible_packages(self) -> Vec<PackageIndex> {
        let mapping = self.store.package_mapping.borrow();
        let mut deps: Vec<_> = self
            .config
            .dependencies
            .values()
            .filter_map(|ident| mapping.get(ident.as_str()).cloned())
            .collect();
        drop(mapping);

        // Always include std for Foundation type lookups
        if let Some(std_pkg) = self.std_package_index() {
            if !deps.contains(&std_pkg) {
                deps.push(std_pkg);
            }
        }
        deps
    }

    /// Search session first, then all visible packages. Returns first Some result.
    pub fn find_in_databases<F, T>(self, func: F) -> Option<T>
    where
        F: Fn(&mut TypeDatabase<'arena>) -> Option<T>,
    {
        // Check session first
        if let Some(result) = self.with_session_type_database(&func) {
            return Some(result);
        }

        // Check dependencies
        for index in self.visible_packages() {
            if let Some(result) = self.with_type_database(index, &func) {
                return Some(result);
            }
        }
        None
    }

    /// Collect from session first, then from all visible packages.
    pub fn collect_from_databases<F, T>(self, mut func: F) -> Vec<T>
    where
        F: FnMut(&mut TypeDatabase<'arena>) -> Vec<T>,
    {
        let mut results = self.with_session_type_database(&mut func);
        for index in self.visible_packages() {
            results.extend(self.with_type_database(index, &mut func));
        }
        results
    }
}

impl<'arena> GlobalContext<'arena> {
    #[inline]
    pub fn get_type(self, id: DefinitionID) -> Ty<'arena> {
        self.with_type_database(id.package(), |db| {
            *db.def_to_ty.get(&id).expect("type of definition")
        })
    }

    pub fn try_get_const(self, id: DefinitionID) -> Option<Const<'arena>> {
        self.with_type_database(id.package(), |db| db.def_to_const.get(&id).cloned())
    }

    pub fn try_get_static_mutability(self, id: DefinitionID) -> Option<hir::Mutability> {
        self.with_type_database(id.package(), |db| {
            db.def_to_static_mutability.get(&id).copied()
        })
    }

    pub fn get_static_mutability(self, id: DefinitionID) -> hir::Mutability {
        self.with_type_database(id.package(), |db| {
            *db.def_to_static_mutability
                .get(&id)
                .expect("static mutability")
        })
    }

    pub fn try_get_static_initializer(self, id: DefinitionID) -> Option<Const<'arena>> {
        self.with_type_database(id.package(), |db| db.def_to_static_init.get(&id).cloned())
    }

    pub fn get_static_initializer(self, id: DefinitionID) -> Const<'arena> {
        self.with_type_database(id.package(), |db| {
            *db.def_to_static_init.get(&id).expect("static initializer")
        })
    }

    #[inline]
    pub fn get_const(self, id: DefinitionID) -> Const<'arena> {
        self.with_type_database(id.package(), |db| {
            *db.def_to_const.get(&id).expect("const value")
        })
    }

    pub fn try_get_alias_type(self, id: DefinitionID) -> Option<Ty<'arena>> {
        self.with_type_database(id.package(), |db| db.resolved_aliases.get(&id).cloned())
    }

    #[inline]
    pub fn get_alias_type(self, id: DefinitionID) -> Ty<'arena> {
        self.with_type_database(id.package(), |db| {
            *db.resolved_aliases
                .get(&id)
                .expect("alias type of definition")
        })
    }

    pub fn get_signature(self, id: DefinitionID) -> &'arena LabeledFunctionSignature<'arena> {
        self.try_get_signature(id)
            .expect("fn signature of definition")
    }

    pub fn try_get_signature(
        self,
        id: DefinitionID,
    ) -> Option<&'arena LabeledFunctionSignature<'arena>> {
        let synthetic_sig = {
            let defs = self.context.store.synthetic_definitions.borrow();
            defs.get(&id).map(|def| def.signature)
        };
        if let Some(signature) = synthetic_sig {
            return Some(signature);
        }

        self.with_type_database(id.package(), |db| db.def_to_fn_sig.get(&id).copied())
    }

    pub fn function_body_output(self, id: DefinitionID) -> Ty<'arena> {
        if let Some(ty) = self.with_type_database(id.package(), |db| {
            db.def_to_async_body_output.get(&id).copied()
        }) {
            ty
        } else {
            self.get_signature(id).output
        }
    }

    pub fn definition_is_async(self, id: DefinitionID) -> bool {
        self.with_type_database(id.package(), |db| {
            db.def_to_async_body_output.contains_key(&id)
        })
    }

    pub fn async_handle_ty(self) -> Ty<'arena> {
        self.store
            .interners
            .intern_ty(TyKind::Pointer(self.types.uint8, hir::Mutability::Mutable))
    }

    /// Get the escape summary for a function, if one has been computed.
    pub fn get_escape_summary(self, id: DefinitionID) -> Option<EscapeSummary> {
        self.with_type_database(id.package(), |db| {
            db.def_to_escape_summary.get(&id).cloned()
        })
    }

    /// Store an escape summary for a function.
    pub fn set_escape_summary(self, id: DefinitionID, summary: EscapeSummary) {
        self.with_type_database(id.package(), |db| {
            db.def_to_escape_summary.insert(id, summary);
        });
    }

    /// Get closure capture information for a closure definition.
    pub fn get_closure_captures(self, id: DefinitionID) -> Option<ClosureCaptures<'arena>> {
        self.with_type_database(id.package(), |db| db.closure_captures.get(&id).cloned())
    }

    /// Store closure capture information.
    pub fn cache_closure_captures(self, id: DefinitionID, captures: ClosureCaptures<'arena>) {
        self.with_type_database(id.package(), |db| {
            db.closure_captures.insert(id, captures);
        });
    }

    #[track_caller]
    pub fn get_struct_definition(self, id: DefinitionID) -> &'arena StructDefinition<'arena> {
        self.with_type_database(id.package(), |db| db.def_to_struct_def.get(&id).cloned())
            .expect("struct definition of definition")
    }

    pub fn try_get_struct_definition(
        self,
        id: DefinitionID,
    ) -> Option<&'arena StructDefinition<'arena>> {
        self.with_type_database(id.package(), |db| db.def_to_struct_def.get(&id).cloned())
    }

    pub fn lookup_field_in_type_head(
        self,
        head: TypeHead,
        name: Symbol,
    ) -> Option<StructField<'arena>> {
        let TypeHead::Nominal(def_id) = head else {
            return None;
        };

        if self.definition_kind(def_id) != DefinitionKind::Struct {
            return None;
        }

        let def = self.get_struct_definition(def_id);
        def.fields.iter().find(|field| field.name == name).copied()
    }

    pub fn get_enum_definition(self, id: DefinitionID) -> &'arena EnumDefinition<'arena> {
        self.with_type_database(id.package(), |db| {
            *db.def_to_enum_def
                .get(&id)
                .expect("enum definition of definition")
        })
    }

    pub fn try_get_enum_definition(
        self,
        id: DefinitionID,
    ) -> Option<&'arena EnumDefinition<'arena>> {
        self.with_type_database(id.package(), |db| db.def_to_enum_def.get(&id).cloned())
    }

    pub fn enum_variant_by_index(
        self,
        enum_id: DefinitionID,
        index: VariantIndex,
    ) -> EnumVariant<'arena> {
        let def = self.get_enum_definition(enum_id);
        *def.variants.get(index.index()).expect("enum variant index")
    }

    pub fn get_interface_requirements(
        self,
        id: DefinitionID,
    ) -> Option<&'arena InterfaceRequirements<'arena>> {
        self.with_type_database(id.package(), |db| {
            db.interface_requirements.get(&id).cloned()
        })
    }

    pub fn get_interface_definition(
        self,
        id: DefinitionID,
    ) -> Option<&'arena InterfaceDefinition<'arena>> {
        self.with_type_database(id.package(), |db| db.def_to_iface_def.get(&id).cloned())
    }

    pub fn interface_has_associated_property(self, interface_id: DefinitionID) -> bool {
        let output = self.resolution_output(interface_id.package());
        output.definition_to_kind.iter().any(|(candidate, kind)| {
            *kind == DefinitionKind::AssociatedProperty
                && output
                    .definition_to_parent
                    .get(candidate)
                    .copied()
                    .is_some_and(|parent| parent == interface_id)
        })
    }

    pub fn get_impl_type_head(self, impl_id: DefinitionID) -> Option<TypeHead> {
        self.with_type_database(impl_id.package(), |db| {
            db.impl_to_type_head.get(&impl_id).cloned()
        })
    }

    pub fn get_impl_target_ty(self, impl_id: DefinitionID) -> Option<Ty<'arena>> {
        self.with_type_database(impl_id.package(), |db| {
            db.impl_to_target_ty.get(&impl_id).cloned()
        })
    }

    /// Get the Self type for an impl block.
    /// - For struct/enum impls: returns the concrete type
    /// - For interface impls: returns the Self type parameter
    pub fn get_impl_self_ty(self, impl_id: DefinitionID) -> Option<Ty<'arena>> {
        let head = self.get_impl_type_head(impl_id)?;
        match head {
            TypeHead::Nominal(target_id) => match self.definition_kind(target_id) {
                DefinitionKind::Interface => {
                    // For interface impls, Self is the abstract Self parameter
                    Some(self.types.self_type_parameter)
                }
                DefinitionKind::Struct | DefinitionKind::Enum => self
                    .get_impl_target_ty(impl_id)
                    .or_else(|| Some(self.get_type(target_id))),
                _ => None,
            },
            TypeHead::Primary(p) => self.get_impl_target_ty(impl_id).or_else(|| {
                Some(match p {
                    PrimaryType::Int(k) => Ty::new_int(self, k),
                    PrimaryType::UInt(k) => Ty::new_uint(self, k),
                    PrimaryType::Float(k) => Ty::new_float(self, k),
                    PrimaryType::String => self.types.string,
                    PrimaryType::Bool => self.types.bool,
                    PrimaryType::Rune => self.types.rune,
                })
            }),
            TypeHead::Tuple(_)
            | TypeHead::Reference(_)
            | TypeHead::Pointer(_)
            | TypeHead::Array
            | TypeHead::Closure(_) => self.get_impl_target_ty(impl_id),
        }
    }

    pub fn get_mir_body(self, id: DefinitionID) -> &'arena mir::Body<'arena> {
        let packages = self.context.store.mir_packages.borrow();
        let package = packages.get(&id.package()).expect("mir package");
        *package.functions.get(&id).expect("mir body")
    }

    pub fn resolution_output(self, pkg: PackageIndex) -> &'arena ResolutionOutput<'arena> {
        let outputs = self.context.store.resolution_outputs.borrow();
        *outputs.get(&pkg).expect("resolution output")
    }

    pub fn try_resolution_output(
        self,
        pkg: PackageIndex,
    ) -> Option<&'arena ResolutionOutput<'arena>> {
        let outputs = self.context.store.resolution_outputs.borrow();
        outputs.get(&pkg).copied()
    }

    pub fn definition_ident(self, id: DefinitionID) -> crate::span::Identifier {
        if let Some(def) = self.context.store.synthetic_definitions.borrow().get(&id) {
            return crate::span::Identifier {
                symbol: def.name,
                span: def.span,
            };
        }

        let output = self.resolution_output(id.package());
        *output
            .definition_to_ident
            .get(&id)
            .expect("identifier for definition")
    }

    pub fn try_definition_ident(self, id: DefinitionID) -> Option<crate::span::Identifier> {
        if let Some(def) = self.context.store.synthetic_definitions.borrow().get(&id) {
            return Some(crate::span::Identifier {
                symbol: def.name,
                span: def.span,
            });
        }

        let output = self.try_resolution_output(id.package())?;
        output.definition_to_ident.get(&id).copied()
    }

    pub fn definition_symbol_or_fallback(self, id: DefinitionID) -> Symbol {
        self.try_definition_ident(id)
            .map(|ident| ident.symbol)
            .unwrap_or_else(|| {
                self.intern_symbol(&format!(
                    "missing_p{}_d{}",
                    id.package().raw(),
                    id.index().raw()
                ))
            })
    }

    pub fn definition_kind(self, id: DefinitionID) -> DefinitionKind {
        if self
            .context
            .store
            .synthetic_definitions
            .borrow()
            .contains_key(&id)
        {
            // Synthetic definitions are currently only used for methods (Clone etc)
            return DefinitionKind::AssociatedFunction;
        }

        let output = self.resolution_output(id.package());
        *output.definition_to_kind.get(&id).expect("definition kind")
    }

    pub fn try_definition_kind(self, id: DefinitionID) -> Option<DefinitionKind> {
        if self
            .context
            .store
            .synthetic_definitions
            .borrow()
            .contains_key(&id)
        {
            return Some(DefinitionKind::AssociatedFunction);
        }

        let output = self.try_resolution_output(id.package())?;
        output.definition_to_kind.get(&id).copied()
    }

    fn is_current_package_std(self) -> bool {
        self.config.is_std_provider
    }

    pub fn is_std_package(self, pkg: PackageIndex) -> bool {
        if pkg == self.package_index() {
            return self.is_current_package_std();
        }

        self.context.store.std_provider_index.get() == Some(pkg)
    }

    pub fn std_package_index(self) -> Option<PackageIndex> {
        if self.is_current_package_std() {
            return Some(self.package_index());
        }

        if let Some(provider) = self.context.store.std_provider_index.get() {
            return Some(provider);
        }

        if matches!(self.config.std_mode, StdMode::BootstrapStd) {
            return None;
        }

        None
    }

    /// Returns the stored language item entry for the active std provider.
    pub fn std_item_entry(self, item: StdItem) -> Option<StdItemEntry> {
        let std_pkg = self.std_package_index()?;
        let std_items = self.context.store.std_items.borrow();
        let (cached_pkg, registry) = std_items.as_ref()?;
        if *cached_pkg != std_pkg {
            return None;
        }
        registry.get(item)
    }

    /// Returns the DefinitionID for a well-known language item, if available.
    pub fn std_item_def(self, item: StdItem) -> Option<DefinitionID> {
        self.std_item_entry(item).map(|entry| entry.def_id)
    }

    pub fn visible_traits(self, def_id: DefinitionID) -> Rc<FxHashSet<DefinitionID>> {
        if let Some(cached) = self.with_type_database(def_id.package(), |db| {
            db.visible_traits.get(&def_id).cloned()
        }) {
            return cached;
        }

        use crate::sema::resolve::models::{DefinitionKind, Resolution, ScopeEntryKind};

        let mut visible = FxHashSet::default();
        let pkg = def_id.package();
        let resolution_output = self.resolution_output(pkg);

        let mut collect_entry =
            |entry: crate::sema::resolve::models::ScopeEntry<'arena>| match &entry.kind {
                ScopeEntryKind::Resolution(Resolution::Definition(id, kind)) => {
                    if *kind == DefinitionKind::Interface {
                        visible.insert(*id);
                    }
                }
                ScopeEntryKind::Usage { used_entry, .. } => {
                    if let ScopeEntryKind::Resolution(Resolution::Definition(id, kind)) =
                        &used_entry.kind
                        && *kind == DefinitionKind::Interface
                    {
                        visible.insert(*id);
                    }
                }
                _ => {}
            };

        let mut collect_scope = |scope: crate::sema::resolve::models::Scope<'arena>| {
            let table = scope.table.borrow();
            for name_entry in table.values() {
                if let Some(type_entry) = name_entry.ty {
                    collect_entry(type_entry);
                }
                for value_entry in &name_entry.values {
                    collect_entry(*value_entry);
                }
            }
        };

        let mut collect_scope_tree = |root: crate::sema::resolve::models::Scope<'arena>| {
            let mut queue = std::collections::VecDeque::new();
            let mut seen_scopes: FxHashSet<*const crate::sema::resolve::models::ScopeData<'arena>> =
                FxHashSet::default();
            queue.push_back(root);

            while let Some(scope) = queue.pop_front() {
                let scope_ptr = scope.0 as *const crate::sema::resolve::models::ScopeData<'arena>;
                if !seen_scopes.insert(scope_ptr) {
                    continue;
                }

                collect_scope(scope);

                for usage in scope.glob_imports.borrow().iter() {
                    if let Some(module_scope) = usage.module_scope.get() {
                        queue.push_back(module_scope);
                    }
                }

                for usage in scope.glob_exports.borrow().iter() {
                    if let Some(module_scope) = usage.module_scope.get() {
                        queue.push_back(module_scope);
                    }
                }
            }
        };

        // Some nested definitions (especially associated declarations) are not
        // mapped directly. Walk parents until we find the nearest mapped scope.
        let mut scope_owner = Some(def_id);
        let mut current_scope = None;
        while let Some(owner) = scope_owner {
            if let Some(scope) = resolution_output
                .definition_scope_mapping
                .get(&owner)
                .cloned()
            {
                current_scope = Some(scope);
                break;
            }

            scope_owner = resolution_output.definition_to_parent.get(&owner).cloned();
        }

        if current_scope.is_none() {
            current_scope = Some(resolution_output.root_scope);
        }

        while let Some(scope) = current_scope {
            collect_scope_tree(scope);
            current_scope = scope.parent;
        }

        let file_id = self.definition_ident(def_id).span.file;
        if let Some(file_scope) = resolution_output.file_scope_mapping.get(&file_id).cloned() {
            collect_scope_tree(file_scope);
        }

        // The std prelude is implicitly in scope for user packages.
        // Pull interface exports from `std.prelude` so prelude traits are treated as visible.
        if let Some(std_pkg) = self.std_package_index()
            && let Some(std_output) = self.try_resolution_output(std_pkg)
        {
            let prelude_scope = {
                let prelude_symbol = self.intern_symbol("prelude");
                let table = std_output.root_scope.table.borrow();
                table
                    .get(&prelude_symbol)
                    .and_then(|entry| entry.ty)
                    .and_then(|scope_entry| match scope_entry.resolution() {
                        Resolution::Definition(id, DefinitionKind::Module) => {
                            std_output.definition_scope_mapping.get(&id).cloned()
                        }
                        _ => None,
                    })
            };

            if let Some(prelude_scope) = prelude_scope {
                collect_scope_tree(prelude_scope);
            }
        }

        let rc_visible = Rc::new(visible);
        self.with_type_database(def_id.package(), |db| {
            db.visible_traits.insert(def_id, rc_visible.clone());
        });

        rc_visible
    }

    /// Checks whether a type is intrinsically copyable without consulting interface selection.
    ///
    /// This is used for the builtin `Copy` candidate and must not call back into trait
    /// resolution, otherwise `Copy` selection immediately recurses on itself.
    pub fn is_type_builtin_copyable(self, ty: Ty<'arena>) -> bool {
        match ty.kind() {
            TyKind::Int(_)
            | TyKind::UInt(_)
            | TyKind::Float(_)
            | TyKind::Bool
            | TyKind::Rune
            | TyKind::String
            | TyKind::Reference(..)
            | TyKind::Pointer(..)
            | TyKind::FnPointer { .. }
            | TyKind::Never => true,
            TyKind::Tuple(elements) => elements.iter().all(|elem| self.is_type_copyable(*elem)),
            TyKind::Array { element, .. } => self.is_type_copyable(element),
            TyKind::Adt(def, _) => self.std_item_def(StdItem::Span) == Some(def.id),
            TyKind::BoxedExistential { .. } => false,
            TyKind::Parameter(_) => false,
            TyKind::Alias { kind, .. } if kind != AliasKind::Projection => {
                let normalized = crate::sema::tycheck::utils::normalize_aliases(self, ty);
                if normalized == ty {
                    false
                } else {
                    self.is_type_builtin_copyable(normalized)
                }
            }
            TyKind::Alias { .. } => false,
            TyKind::Closure { .. } => false,
            TyKind::Opaque(_) | TyKind::Error | TyKind::Infer(_) => false,
        }
    }

    /// Checks if a type implements the `Copy` interface.
    /// Primitives, references, pointers, function pointers, spans, and never are
    /// implicitly copyable. Structs/enums must explicitly implement `Copy`.
    /// Type parameters are conservatively non-Copy; use `is_type_copyable_in_def`
    /// when a definition context is available to check constraints.
    pub fn is_type_copyable(self, ty: Ty<'arena>) -> bool {
        if self.is_type_builtin_copyable(ty) {
            return true;
        }

        match ty.kind() {
            TyKind::Adt(def, _) => {
                let Some(copy_def) = self.std_item_def(StdItem::Copy) else {
                    return false;
                };
                if self.std_item_def(StdItem::Span) == Some(def.id) {
                    return true;
                }
                let goal = InterfaceGoal {
                    interface_id: copy_def,
                    self_ty: ty,
                    interface_args: GenericArguments::empty(),
                    bindings: &[],
                    param_env: &[],
                };
                matches!(
                    self.prove_interface_goal(goal, SelectionMode::Typecheck),
                    GoalResult::Proven
                )
            }
            TyKind::Alias { kind, .. } if kind != AliasKind::Projection => {
                let normalized = crate::sema::tycheck::utils::normalize_aliases(self, ty);
                if normalized == ty {
                    false
                } else {
                    self.is_type_copyable(normalized)
                }
            }
            TyKind::Tuple(elements) => elements.iter().all(|elem| self.is_type_copyable(*elem)),
            TyKind::Array { element, .. } => self.is_type_copyable(element),
            TyKind::Int(_)
            | TyKind::UInt(_)
            | TyKind::Float(_)
            | TyKind::Bool
            | TyKind::Rune
            | TyKind::String
            | TyKind::Reference(..)
            | TyKind::Pointer(..)
            | TyKind::FnPointer { .. }
            | TyKind::Never => true,
            TyKind::BoxedExistential { .. } => false,
            TyKind::Parameter(_) => false,
            TyKind::Alias { .. } => false,
            TyKind::Closure { .. } => false,
            TyKind::Opaque(_) | TyKind::Error | TyKind::Infer(_) => false,
        }
    }

    /// Checks if a type implements `Copy` in the context of a specific definition,
    /// consulting the definition's constraints for type parameter bounds.
    pub fn is_type_copyable_in_def(self, ty: Ty<'arena>, owner: hir::DefinitionID) -> bool {
        let TyKind::Parameter(param) = ty.kind() else {
            return self.is_type_copyable(ty);
        };

        let Some(copy_def) = self.std_item_def(StdItem::Copy) else {
            return false;
        };

        let param_ty = Ty::new(TyKind::Parameter(param), self);
        self.canonical_constraints_of(owner)
            .iter()
            .any(|constraint| match constraint.value {
                Constraint::Bound { ty, interface } => {
                    if ty != param_ty {
                        return false;
                    }
                    self.interface_transitively_requires(interface.id, copy_def)
                }
                Constraint::TypeEquality(_, _) => false,
            })
    }

    /// Returns true if `interface_id` is `target_id` or transitively extends it.
    fn interface_transitively_requires(
        self,
        interface_id: hir::DefinitionID,
        target_id: hir::DefinitionID,
    ) -> bool {
        let mut visited = FxHashSet::default();
        self.interface_transitively_requires_inner(interface_id, target_id, &mut visited)
    }

    fn interface_transitively_requires_inner(
        self,
        interface_id: hir::DefinitionID,
        target_id: hir::DefinitionID,
        visited: &mut FxHashSet<hir::DefinitionID>,
    ) -> bool {
        if interface_id == target_id {
            return true;
        }
        if !visited.insert(interface_id) {
            return false;
        }
        let Some(def) = self.get_interface_definition(interface_id) else {
            return false;
        };
        def.superfaces.iter().any(|super_iface| {
            self.interface_transitively_requires_inner(super_iface.value.id, target_id, visited)
        })
    }

    /// Checks if a type is safe to move across executor workers.
    /// This powers the builtin `Sendable` marker and async task scheduling.
    pub fn is_type_sendable(self, ty: Ty<'arena>) -> bool {
        let mut visited = FxHashSet::default();
        self.is_type_sendable_inner(ty, &mut visited)
    }

    fn is_type_sendable_inner(self, ty: Ty<'arena>, visited: &mut FxHashSet<Ty<'arena>>) -> bool {
        let ty = crate::sema::tycheck::utils::normalize_aliases(self, ty);
        if ty == self.async_handle_ty() {
            return false;
        }
        if !visited.insert(ty) {
            return true;
        }

        let sendable = match ty.kind() {
            TyKind::Bool
            | TyKind::Rune
            | TyKind::String
            | TyKind::Int(_)
            | TyKind::UInt(_)
            | TyKind::Float(_)
            | TyKind::Never
            | TyKind::FnPointer { .. } => true,
            TyKind::Pointer(..)
            | TyKind::Reference(..)
            | TyKind::BoxedExistential { .. }
            | TyKind::Parameter(_)
            | TyKind::Opaque(_)
            | TyKind::Infer(_)
            | TyKind::Error => false,
            TyKind::Alias { .. } => false,
            TyKind::Array { element, .. } => self.is_type_sendable_inner(element, visited),
            TyKind::Tuple(items) => items
                .iter()
                .copied()
                .all(|item| self.is_type_sendable_inner(item, visited)),
            TyKind::Closure { closure_def_id, .. } => self
                .get_closure_captures(closure_def_id)
                .map(|captures| {
                    captures.captures.iter().all(|capture| {
                        !matches!(
                            capture.capture_kind,
                            crate::sema::models::CaptureKind::ByRef { .. }
                        ) && self.is_type_sendable_inner(capture.ty, visited)
                    })
                })
                .unwrap_or(true),
            TyKind::Adt(def, args) => {
                if self.std_item_def(StdItem::Task) == Some(def.id) {
                    true
                } else {
                    match def.kind {
                        crate::sema::models::AdtKind::Struct => self
                            .get_struct_definition(def.id)
                            .fields
                            .iter()
                            .all(|field| {
                                let field_ty =
                                    crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args(
                                        self,
                                        field.ty,
                                        args,
                                    );
                                self.is_type_sendable_inner(field_ty, visited)
                            }),
                        crate::sema::models::AdtKind::Enum => self
                            .get_enum_definition(def.id)
                            .variants
                            .iter()
                            .all(|variant| match variant.kind {
                                crate::sema::models::EnumVariantKind::Unit => true,
                                crate::sema::models::EnumVariantKind::Tuple(fields) => fields
                                    .iter()
                                    .all(|field| {
                                        let field_ty =
                                            crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args(
                                                self,
                                                field.ty,
                                                args,
                                            );
                                        self.is_type_sendable_inner(field_ty, visited)
                                    }),
                            }),
                    }
                }
            }
        };

        visited.remove(&ty);
        sendable
    }

    pub fn definition_visibility(self, id: DefinitionID) -> Visibility {
        let output = self.resolution_output(id.package());
        output
            .definition_to_visibility
            .get(&id)
            .cloned()
            .unwrap_or(Visibility::Public)
    }

    pub fn definition_parent(self, id: DefinitionID) -> Option<DefinitionID> {
        let output = self.resolution_output(id.package());
        output.definition_to_parent.get(&id).cloned()
    }

    pub fn is_visibility_allowed(self, visibility: Visibility, from: DefinitionID) -> bool {
        match visibility {
            Visibility::Public => true,
            Visibility::FilePrivate(file) => self.definition_ident(from).span.file == file,
            Visibility::Private(owner) => self.is_within_definition(from, owner),
        }
    }

    pub fn is_definition_visible(self, target: DefinitionID, from: DefinitionID) -> bool {
        let visibility = self.definition_visibility(target);
        self.is_visibility_allowed(visibility, from)
    }

    fn is_within_definition(self, mut current: DefinitionID, owner: DefinitionID) -> bool {
        if current == owner {
            return true;
        }
        while let Some(parent) = self.definition_parent(current) {
            if parent == owner {
                return true;
            }
            current = parent;
        }
        false
    }

    pub fn cache_object_file(self, path: PathBuf) {
        self.context
            .store
            .object_files
            .borrow_mut()
            .insert(self.package_index(), path);
    }

    pub fn get_object_file(self, pkg: PackageIndex) -> Option<PathBuf> {
        self.context.store.object_files.borrow().get(&pkg).cloned()
    }

    pub fn cache_specializations(self, pkg: PackageIndex, instances: FxHashSet<Instance<'arena>>) {
        self.context
            .store
            .specialization_instances
            .borrow_mut()
            .insert(pkg, instances);
    }

    pub fn cache_emitted_instances(
        self,
        pkg: PackageIndex,
        instances: FxHashSet<Instance<'arena>>,
    ) {
        self.context
            .store
            .emitted_instances
            .borrow_mut()
            .insert(pkg, instances);
    }

    pub fn emitted_instances_of(self, pkg: PackageIndex) -> Vec<Instance<'arena>> {
        let cache = self.context.store.emitted_instances.borrow();
        match cache.get(&pkg) {
            Some(instances) => instances.iter().cloned().collect(),
            None => Vec::new(),
        }
    }

    pub fn specializations_of(self, pkg: PackageIndex) -> Vec<Instance<'arena>> {
        let cache = self.context.store.specialization_instances.borrow();
        match cache.get(&pkg) {
            Some(instances) => instances.iter().cloned().collect(),
            None => Vec::new(),
        }
    }

    /// Mark an instance as compiled (to avoid duplicate compilation).
    pub fn mark_instance_compiled(self, instance: Instance<'arena>) {
        self.context
            .store
            .compiled_instances
            .borrow_mut()
            .insert(instance);
    }

    /// Check if an instance has already been compiled.
    pub fn is_instance_compiled(self, instance: Instance<'arena>) -> bool {
        self.context
            .store
            .compiled_instances
            .borrow()
            .contains(&instance)
    }

    pub fn all_object_files(self) -> Vec<PathBuf> {
        let mut inputs: Vec<PathBuf> = self
            .context
            .store
            .object_files
            .borrow()
            .values()
            .cloned()
            .collect();
        inputs.extend(self.context.store.all_link_inputs());
        inputs
    }

    pub fn output_root(self) -> &'arena PathBuf {
        &self.context.store.output_root
    }

    pub fn generics_of(self, id: DefinitionID) -> &'arena Generics {
        if let Some(def) = self.context.store.synthetic_definitions.borrow().get(&id) {
            return def.generics;
        }

        let mut database = self.context.store.type_databases.borrow_mut();
        let database = database.entry(id.package()).or_default();

        if let Some(x) = database.def_to_generics.get(&id) {
            x
        } else if let Some(empty) = database.empty_generics {
            empty
        } else {
            let generics = self.context.store.arenas.generics.alloc(Generics {
                parameters: vec![],
                has_self: false,
                parent: None,
                parent_count: 0,
            });
            database.empty_generics = Some(generics);
            generics
        }
    }

    pub fn empty_generics_for_package(self, package: PackageIndex) -> &'arena Generics {
        let mut database = self.context.store.type_databases.borrow_mut();
        let database = database.entry(package).or_default();

        if let Some(empty) = database.empty_generics {
            empty
        } else {
            let generics = self.context.store.arenas.generics.alloc(Generics {
                parameters: vec![],
                has_self: false,
                parent: None,
                parent_count: 0,
            });
            database.empty_generics = Some(generics);
            generics
        }
    }

    pub fn attributes_of(self, id: DefinitionID) -> &'arena hir::AttributeList {
        let mut database = self.context.store.type_databases.borrow_mut();
        let database = database.entry(id.package()).or_default();

        if let Some(attrs) = database.def_to_attributes.get(&id) {
            *attrs
        } else if let Some(empty) = database.empty_attributes {
            empty
        } else {
            let empty = self.context.store.arenas.global.alloc(Vec::new());
            database.empty_attributes = Some(empty);
            empty
        }
    }

    pub fn definition_has_known_attribute(
        self,
        id: DefinitionID,
        attr: hir::KnownAttribute,
    ) -> bool {
        self.attributes_of(id)
            .iter()
            .any(|item| item.as_known(self) == Some(attr))
    }

    pub fn definition_is_unsafe(self, id: DefinitionID) -> bool {
        self.with_type_database(id.package(), |db| db.def_to_unsafe.contains(&id))
    }
}

pub struct CompilerContext<'arena> {
    pub dcx: Rc<DiagCtx>,
    pub store: CompilerStore<'arena>,
    pub types: CommonTypes<'arena>,
}

impl<'arena> CompilerContext<'arena> {
    pub fn new(dcx: Rc<DiagCtx>, store: CompilerStore<'arena>) -> CompilerContext<'arena> {
        let self_symbol = Symbol::new("Self");
        let types = CommonTypes::new(&store.interners, self_symbol);
        CompilerContext { dcx, store, types }
    }

    pub fn dcx(&self) -> &DiagCtx {
        &self.dcx
    }
}

pub struct CompilerStore<'arena> {
    pub arenas: &'arena CompilerArenas<'arena>,
    pub interners: CompilerInterners<'arena>,
    pub resolution_outputs: RefCell<FxHashMap<PackageIndex, &'arena ResolutionOutput<'arena>>>,
    pub package_mapping: RefCell<FxHashMap<EcoString, PackageIndex>>,
    pub package_idents: RefCell<FxHashMap<PackageIndex, EcoString>>,
    pub type_databases: RefCell<FxHashMap<PackageIndex, TypeDatabase<'arena>>>,
    pub mir_packages: RefCell<FxHashMap<PackageIndex, &'arena mir::MirPackage<'arena>>>,
    pub queued_mir_bodies: RefCell<FxHashMap<DefinitionID, Body<'arena>>>,
    pub llvm_modules: RefCell<FxHashMap<PackageIndex, String>>,
    pub object_files: RefCell<FxHashMap<PackageIndex, PathBuf>>,
    pub link_inputs: RefCell<Vec<PathBuf>>,
    pub output_root: PathBuf,
    pub specialization_instances: RefCell<FxHashMap<PackageIndex, FxHashSet<Instance<'arena>>>>,
    /// Per-package set of instances emitted into that package object file.
    pub emitted_instances: RefCell<FxHashMap<PackageIndex, FxHashSet<Instance<'arena>>>>,
    /// Global set of instances that have been compiled (to avoid duplicate work)
    pub compiled_instances: RefCell<FxHashSet<Instance<'arena>>>,
    /// Target-specific layout information (shared between MIR and codegen).
    pub target_layout: TargetLayout,
    /// The std provider package index selected by the driver.
    pub std_provider_index: std::cell::Cell<Option<PackageIndex>>,
    /// Cached standard library language items collected from std.
    pub std_items: RefCell<Option<(PackageIndex, StdItemRegistry)>>,

    // Synthetic definitions (for method synthesis linkage)
    pub synthetic_definitions:
        RefCell<FxHashMap<DefinitionID, crate::sema::models::SyntheticDefinition<'arena>>>,
    pub next_synthetic_id: std::cell::Cell<u32>,

    // Default value expressions (mapped by provider ID)
    pub default_value_exprs: RefCell<FxHashMap<DefinitionID, &'arena hir::Expression>>,
}

impl<'arena> CompilerStore<'arena> {
    pub fn new(
        arenas: &'arena CompilerArenas<'arena>,
        output_root: PathBuf,
        dcx: &DiagCtx,
        target_override: Option<String>,
        profile: BuildProfile,
    ) -> CompileResult<CompilerStore<'arena>> {
        let target_layout = TargetLayout::new(dcx, target_override.as_deref(), profile)?;
        Ok(CompilerStore {
            arenas,
            interners: CompilerInterners::new(arenas),
            package_mapping: Default::default(),
            package_idents: Default::default(),
            resolution_outputs: Default::default(),
            type_databases: Default::default(),
            mir_packages: Default::default(),
            queued_mir_bodies: Default::default(),
            llvm_modules: Default::default(),
            object_files: Default::default(),
            link_inputs: Default::default(),
            output_root,
            specialization_instances: Default::default(),
            emitted_instances: Default::default(),
            compiled_instances: Default::default(),
            target_layout,
            std_provider_index: std::cell::Cell::new(None),
            std_items: Default::default(),
            synthetic_definitions: Default::default(),
            next_synthetic_id: std::cell::Cell::new(0),
            default_value_exprs: Default::default(),
        })
    }

    pub fn add_link_input(&self, path: PathBuf) {
        self.link_inputs.borrow_mut().push(path);
    }

    pub fn all_link_inputs(&self) -> Vec<PathBuf> {
        self.link_inputs.borrow().clone()
    }
}

impl<'arena> CompilerStore<'arena> {
    pub fn alloc_mir_package(
        &self,
        package: mir::MirPackage<'arena>,
    ) -> &'arena mir::MirPackage<'arena> {
        self.arenas.mir_packages.alloc(package)
    }
}
pub struct CompilerInterners<'arena> {
    arenas: &'arena CompilerArenas<'arena>,
    types: InternedSet<'arena, TyKind<'arena>>,
    type_lists: InternedSet<'arena, Vec<Ty<'arena>>>,
    generic_arguments: InternedSet<'arena, Vec<GenericArgument<'arena>>>,
}
impl<'arena> CompilerInterners<'arena> {
    pub fn new(arenas: &'arena CompilerArenas<'arena>) -> CompilerInterners<'arena> {
        CompilerInterners {
            arenas,
            types: InternedSet::new(),
            type_lists: InternedSet::new(),
            generic_arguments: InternedSet::new(),
        }
    }

    pub fn intern_ty(&self, k: TyKind<'arena>) -> Ty<'arena> {
        let ptr = self
            .types
            .intern(k, |k| {
                let k = self.arenas.types.alloc(k);
                return InternedInSet(k);
            })
            .0;

        Ty::with_kind(Interned::new_unchecked(ptr))
    }

    pub fn intern_ty_list(&self, items: Vec<Ty<'arena>>) -> TyList<'arena> {
        let ik = self
            .type_lists
            .intern(items, |k| {
                let k = self.arenas.type_lists.alloc(k);
                return InternedInSet(k);
            })
            .0;

        List::from_interned_slice(ik)
    }

    pub fn intern_ty_list_slice(&self, items: &[Ty<'arena>]) -> TyList<'arena> {
        let list = self
            .type_lists
            .intern_ref(items, || {
                let owned = items.to_vec();
                let stored = self.arenas.type_lists.alloc(owned);
                InternedInSet(stored)
            })
            .0;

        List::from_interned_slice(list)
    }

    pub fn intern_generic_args(
        &self,
        items: Vec<GenericArgument<'arena>>,
    ) -> GenericArguments<'arena> {
        let ik = self
            .generic_arguments
            .intern(items, |k| {
                let k = self.arenas.generic_arguments.alloc(k);
                return InternedInSet(k);
            })
            .0;
        List::from_interned_slice(ik)
    }

    pub fn intern_generic_args_slice(
        &self,
        items: &[GenericArgument<'arena>],
    ) -> GenericArguments<'arena> {
        let list = self
            .generic_arguments
            .intern_ref(items, || {
                let owned = items.to_vec();
                let stored = self.arenas.generic_arguments.alloc(owned);
                InternedInSet(stored)
            })
            .0;

        List::from_interned_slice(list)
    }
}

pub struct CompilerArenas<'arena> {
    pub configs: typed_arena::Arena<Config>,
    pub scopes: typed_arena::Arena<ScopeData<'arena>>,
    pub scope_entries: typed_arena::Arena<ScopeEntryData<'arena>>,
    pub usage_entries: typed_arena::Arena<UsageEntryData<'arena>>,
    pub resolution_outputs: typed_arena::Arena<ResolutionOutput<'arena>>,
    pub types: typed_arena::Arena<TyKind<'arena>>,
    pub type_lists: typed_arena::Arena<Vec<Ty<'arena>>>,
    pub function_signatures: typed_arena::Arena<LabeledFunctionSignature<'arena>>,
    pub struct_definitions: typed_arena::Arena<StructDefinition<'arena>>,
    pub enum_definitions: typed_arena::Arena<EnumDefinition<'arena>>,
    pub mir_bodies: typed_arena::Arena<Body<'arena>>,
    pub mir_packages: typed_arena::Arena<mir::MirPackage<'arena>>,
    pub generics: typed_arena::Arena<Generics>,
    pub generic_arguments: typed_arena::Arena<Vec<GenericArgument<'arena>>>,
    pub interface_definitions: typed_arena::Arena<InterfaceDefinition<'arena>>,
    pub interface_requirements: typed_arena::Arena<InterfaceRequirements<'arena>>,

    pub global: Bump,
}

impl<'arena> CompilerArenas<'arena> {
    pub fn new() -> CompilerArenas<'arena> {
        CompilerArenas {
            configs: Default::default(),
            scopes: Default::default(),
            scope_entries: Default::default(),
            usage_entries: Default::default(),
            resolution_outputs: Default::default(),
            types: Default::default(),
            type_lists: Default::default(),
            function_signatures: Default::default(),
            struct_definitions: Default::default(),
            enum_definitions: Default::default(),
            mir_bodies: Default::default(),
            mir_packages: Default::default(),
            generics: Default::default(),
            generic_arguments: Default::default(),
            interface_definitions: Default::default(),
            interface_requirements: Default::default(),
            global: Bump::new(),
        }
    }
}

pub struct CommonTypes<'arena> {
    pub bool: Ty<'arena>,
    pub rune: Ty<'arena>,
    pub string: Ty<'arena>,
    pub void: Ty<'arena>,

    pub uint: Ty<'arena>,
    pub uint8: Ty<'arena>,
    pub uint16: Ty<'arena>,
    pub uint32: Ty<'arena>,
    pub uint64: Ty<'arena>,

    pub int: Ty<'arena>,
    pub int8: Ty<'arena>,
    pub int16: Ty<'arena>,
    pub int32: Ty<'arena>,
    pub int64: Ty<'arena>,

    pub float32: Ty<'arena>,
    pub float64: Ty<'arena>,

    pub self_type_parameter: Ty<'arena>,

    pub error: Ty<'arena>,
}

impl<'a> CommonTypes<'a> {
    pub fn new(interner: &CompilerInterners<'a>, self_symbol: Symbol) -> CommonTypes<'a> {
        let mk = |ty| interner.intern_ty(ty);

        CommonTypes {
            bool: mk(TyKind::Bool),
            rune: mk(TyKind::Rune),
            string: mk(TyKind::String),
            void: {
                let list = interner.intern_ty_list(vec![]);
                mk(TyKind::Tuple(list))
            },

            uint: mk(TyKind::UInt(UIntTy::USize)),
            uint8: mk(TyKind::UInt(UIntTy::U8)),
            uint16: mk(TyKind::UInt(UIntTy::U16)),
            uint32: mk(TyKind::UInt(UIntTy::U32)),
            uint64: mk(TyKind::UInt(UIntTy::U64)),

            int: mk(TyKind::Int(IntTy::ISize)),
            int8: mk(TyKind::Int(IntTy::I8)),
            int16: mk(TyKind::Int(IntTy::I16)),
            int32: mk(TyKind::Int(IntTy::I32)),
            int64: mk(TyKind::Int(IntTy::I64)),

            float32: mk(TyKind::Float(FloatTy::F32)),
            float64: mk(TyKind::Float(FloatTy::F64)),

            self_type_parameter: {
                let parameter = GenericParameter {
                    index: 0,
                    name: self_symbol,
                };

                let kind = TyKind::Parameter(parameter);
                mk(kind)
            },

            error: mk(TyKind::Error),
        }
    }
}

#[derive(Debug, Default)]
pub struct TypeDatabase<'arena> {
    pub def_to_ty: FxHashMap<DefinitionID, Ty<'arena>>,
    pub def_to_const: FxHashMap<DefinitionID, Const<'arena>>,
    pub def_to_static_mutability: FxHashMap<DefinitionID, hir::Mutability>,
    pub def_to_static_init: FxHashMap<DefinitionID, Const<'arena>>,
    pub def_to_fn_sig: FxHashMap<DefinitionID, &'arena LabeledFunctionSignature<'arena>>,
    pub def_to_async_body_output: FxHashMap<DefinitionID, Ty<'arena>>,
    pub def_to_struct_def: FxHashMap<DefinitionID, &'arena StructDefinition<'arena>>,
    pub def_to_enum_def: FxHashMap<DefinitionID, &'arena EnumDefinition<'arena>>,
    pub def_to_constraints: FxHashMap<DefinitionID, Vec<crate::span::Spanned<Constraint<'arena>>>>,
    pub def_to_canon_constraints:
        FxHashMap<DefinitionID, Vec<crate::span::Spanned<Constraint<'arena>>>>,
    pub impl_to_type_head: FxHashMap<DefinitionID, TypeHead>,
    pub impl_to_target_ty: FxHashMap<DefinitionID, Ty<'arena>>,
    pub type_head_to_impls: FxHashMap<TypeHead, Vec<DefinitionID>>,
    pub type_head_to_members: FxHashMap<TypeHead, TypeMemberIndex>,
    pub type_head_to_properties:
        FxHashMap<TypeHead, FxHashMap<Symbol, ComputedPropertyEntry<'arena>>>,
    pub def_to_generics: FxHashMap<DefinitionID, &'arena Generics>,
    /// Lowered default type for a generic type parameter (keyed by parameter DefinitionID).
    pub generic_type_defaults: FxHashMap<DefinitionID, Ty<'arena>>,
    /// Lowered expected type of a generic const parameter (keyed by parameter DefinitionID).
    pub generic_const_param_tys: FxHashMap<DefinitionID, Ty<'arena>>,
    /// Lowered default value of a generic const parameter (keyed by parameter DefinitionID).
    pub generic_const_defaults: FxHashMap<DefinitionID, Const<'arena>>,
    pub def_to_attributes: FxHashMap<DefinitionID, &'arena hir::AttributeList>,
    pub def_to_unsafe: FxHashSet<DefinitionID>,
    pub def_to_iface_def: FxHashMap<DefinitionID, &'arena InterfaceDefinition<'arena>>,
    pub interface_to_supers: FxHashMap<DefinitionID, FxHashSet<DefinitionID>>,
    pub conformance_records: FxHashMap<ConformanceRecordId, ConformanceRecord<'arena>>,
    pub conformance_by_interface_head:
        FxHashMap<(DefinitionID, TypeHead), Vec<ConformanceRecordId>>,
    pub conformance_by_interface: FxHashMap<DefinitionID, Vec<ConformanceRecordId>>,
    pub conformance_by_head: FxHashMap<TypeHead, Vec<ConformanceRecordId>>,
    pub conformance_by_extension: FxHashMap<DefinitionID, Vec<ConformanceRecordId>>,
    pub next_conformance_record_index: u32,
    pub interface_requirements: FxHashMap<DefinitionID, &'arena InterfaceRequirements<'arena>>,
    pub selection_cache: FxHashMap<CanonicalGoalKey<'arena>, SelectionResult<'arena>>,
    pub witness_cache: FxHashMap<CanonicalGoalKey<'arena>, ConformanceWitness<'arena>>,
    /// Revised alias table
    pub alias_table: crate::sema::models::PackageAliasTable,
    /// Resolved alias types (cached after lowering)
    pub resolved_aliases: FxHashMap<DefinitionID, Ty<'arena>>,
    /// Escape summaries for functions (computed during MIR optimization)
    pub def_to_escape_summary: FxHashMap<DefinitionID, EscapeSummary>,
    /// Closure capture information keyed by closure definition ID
    pub closure_captures: FxHashMap<DefinitionID, ClosureCaptures<'arena>>,
    pub empty_generics: Option<&'arena Generics>,
    pub empty_attributes: Option<&'arena hir::AttributeList>,
    /// Registered synthetic methods for THIR generation
    pub synthetic_methods: FxHashMap<
        (TypeHead, DefinitionID),
        crate::sema::tycheck::derive::SyntheticMethodInfo<'arena>,
    >,
    pub visible_traits: FxHashMap<DefinitionID, Rc<FxHashSet<DefinitionID>>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ComputedPropertyEntry<'arena> {
    pub property_id: DefinitionID,
    pub ty: Ty<'arena>,
    pub getter_id: DefinitionID,
    pub setter_id: Option<DefinitionID>,
    pub visibility: crate::sema::resolve::models::Visibility,
}

#[derive(Default, Debug, Clone)]
pub struct MemberSet {
    pub members: Vec<DefinitionID>,
    pub fingerprints: FxHashMap<u64, DefinitionID>,
}

#[derive(Default, Debug, Clone)]
pub struct TypeMemberIndex {
    // Inherent methods from `impl Type {}`
    pub inherent_static: FxHashMap<Symbol, MemberSet>,
    pub inherent_instance: FxHashMap<Symbol, MemberSet>,

    // Trait methods from `impl Trait for Type {}`
    // Key: (trait_id, method_name) to group overloads per trait
    pub trait_methods: FxHashMap<(DefinitionID, Symbol), MemberSet>,
    // Fast lookup for all trait methods by symbol, regardless of trait.
    pub trait_methods_by_name: FxHashMap<Symbol, Vec<DefinitionID>>,

    pub operators: FxHashMap<hir::OperatorKind, MemberSet>,
}

impl<'arena> GlobalContext<'arena> {
    pub fn lookup_computed_property(
        self,
        head: TypeHead,
        name: Symbol,
    ) -> Option<ComputedPropertyEntry<'arena>> {
        self.find_in_databases(|db| {
            db.type_head_to_properties
                .get(&head)
                .and_then(|properties| properties.get(&name).copied())
        })
    }
}

impl<'arena> GlobalContext<'arena> {
    /// Register a synthetic method for later THIR generation.
    pub fn register_synthetic_method(
        self,
        type_head: TypeHead,
        method_id: DefinitionID,
        name: Symbol,
        info: crate::sema::tycheck::derive::SyntheticMethodInfo<'arena>,
    ) {
        self.with_session_type_database(|db| {
            db.synthetic_methods.insert((type_head, method_id), info);

            // Also register as a member so lookup finds it
            let members = db.type_head_to_members.entry(type_head).or_default();
            let member_set = members.inherent_instance.entry(name).or_default();
            if !member_set.members.contains(&method_id) {
                member_set.members.push(method_id);
            }
        });
    }

    /// Get all registered synthetic methods for THIR generation.
    pub fn get_synthetic_methods(
        self,
    ) -> Vec<(
        (TypeHead, DefinitionID),
        crate::sema::tycheck::derive::SyntheticMethodInfo<'arena>,
    )> {
        self.with_session_type_database(|db| {
            db.synthetic_methods.iter().map(|(k, v)| (*k, *v)).collect()
        })
    }

    /// Get a specific registered synthetic method info.
    pub fn get_synthetic_method(
        self,
        type_head: TypeHead,
        method_id: DefinitionID,
    ) -> Option<crate::sema::tycheck::derive::SyntheticMethodInfo<'arena>> {
        self.with_session_type_database(|db| {
            db.synthetic_methods.get(&(type_head, method_id)).cloned()
        })
    }
}
