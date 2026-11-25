use crate::{
    PackageIndex,
    compile::context::Gcx,
    error::CompileResult,
    hir::{self, DefinitionID, DefinitionKind, HirVisitor, StdItem},
    sema::{
        models::{ConformanceRecord, Constraint, GenericArgument, InterfaceReference, Ty},
        resolve::models::TypeHead,
        tycheck::{
            infer::InferCtx,
            lower::{DefTyLoweringCtx, TypeLowerer},
            utils::{
                ParamEnv,
                instantiate::{
                    instantiate_constraint_with_args, instantiate_interface_ref_with_args,
                    instantiate_ty_with_args,
                },
                normalize_ty,
                unify::TypeUnifier,
            },
        },
    },
    span::Span,
};
use std::rc::Rc;

#[cfg(test)]
#[path = "g31_tests.rs"]
mod g31_tests;

/// Retain only header syntax until selection needs a record. A conformance
/// target can itself contain an array length supplied by a later declaration.
pub(crate) enum Header {
    Inline(hir::Conformances),
    Explicit {
        target: hir::Type,
        interface: hir::Type,
    },
}

impl Header {
    fn mentions(&self, gcx: Gcx<'_>, interface: DefinitionID) -> bool {
        let matches = |path: &hir::ResolvedPath| {
            let resolution = match path {
                hir::ResolvedPath::Resolved(path) => &path.resolution,
                hir::ResolvedPath::Relative(_, segment) => &segment.resolution,
            };
            resolution.definition_id().is_some_and(|id| {
                id == interface
                    || gcx.try_get_interface_alias(id).is_some_and(|expanded| {
                        expanded.iter().any(|reference| reference.id == interface)
                    })
            })
        };
        match self {
            Self::Inline(interfaces) => interfaces.bounds.iter().any(|bound| matches(&bound.path)),
            Self::Explicit { interface, .. } => {
                matches!(&interface.kind, hir::TypeKind::Nominal(path) if matches(path))
            }
        }
    }
}

pub fn register(package: &hir::Package, gcx: Gcx<'_>) -> Vec<DefinitionID> {
    struct Register<'ctx> {
        gcx: Gcx<'ctx>,
        order: Vec<DefinitionID>,
    }
    impl HirVisitor for Register<'_> {
        fn visit_declaration(&mut self, declaration: &hir::Declaration) {
            let id = declaration.id;
            let (head, header, generics) = match &declaration.kind {
                hir::DeclarationKind::Impl(node) => {
                    let (Some(interface), Some(head)) =
                        (&node.interface, self.gcx.get_impl_type_head(id))
                    else {
                        return;
                    };
                    (
                        head,
                        Header::Explicit {
                            target: (*node.target).clone(),
                            interface: (**interface).clone(),
                        },
                        &node.generics,
                    )
                }
                hir::DeclarationKind::Struct(node) => {
                    let Some(mut interfaces) = node.conformances.clone() else {
                        return;
                    };
                    if node.class_header.is_some() {
                        self.gcx
                            .store
                            .pending_class_bases
                            .borrow_mut()
                            .insert(id, interfaces.clone());
                        interfaces.bounds.retain(|b| {
                            super::class_hierarchy::is_interface_bound(self.gcx, &b.path)
                        });
                    }
                    (
                        TypeHead::Nominal(id),
                        Header::Inline(interfaces),
                        &node.generics,
                    )
                }
                hir::DeclarationKind::Enum(node) => {
                    let Some(interfaces) = node.conformances.clone() else {
                        return;
                    };
                    (
                        TypeHead::Nominal(id),
                        Header::Inline(interfaces),
                        &node.generics,
                    )
                }
                _ => return,
            };
            self.order.push(id);
            self.gcx
                .store
                .pending_conformances
                .borrow_mut()
                .insert(id, (head, header, generics.clone()));
        }
    }
    let mut visitor = Register {
        gcx,
        order: Vec::new(),
    };
    hir::walk_package(&mut visitor, package);
    visitor.order
}

pub fn finish(order: Vec<DefinitionID>, gcx: Gcx<'_>) -> CompileResult<()> {
    for id in order {
        collect_header(gcx, id);
    }
    gcx.dcx().ok()
}

fn collect_header(gcx: Gcx<'_>, id: DefinitionID) {
    let Some((_, header, generics)) = gcx.store.pending_conformances.borrow_mut().remove(&id)
    else {
        return;
    };
    if !gcx.with_type_database(id.package(), |db| db.def_to_constraints.contains_key(&id)) {
        super::constraints::collect_header_constraints(gcx, id, &generics);
    }
    let mut actor = Actor { context: gcx };
    match header {
        Header::Inline(interfaces) => actor.collect_inline_conformance(id, &interfaces),
        Header::Explicit { target, interface } => {
            if gcx.get_impl_target_ty(id).is_none() {
                super::super::impls::target::cache_target(gcx, id, &target);
            }
            actor.collect_impl_conformance(id, &interface);
        }
    }
}

/// Supply declarations of this interface that can apply to the receiver, in
/// source order. Taking the pending header before lowering its target guards
/// recursive requests without caching a partially built record.
pub(crate) fn ensure_candidates<'ctx>(gcx: Gcx<'ctx>, receiver: Ty<'ctx>, interface: DefinitionID) {
    if gcx.store.pending_conformances.borrow().is_empty() {
        return;
    }
    let heads: Vec<_> = gcx
        .class_ancestry(receiver)
        .into_iter()
        .chain([receiver])
        .filter_map(super::super::utils::type_head_from_value_ty)
        .collect();
    let mut owners: Vec<_> = gcx
        .store
        .pending_conformances
        .borrow()
        .iter()
        .filter(|(_, (head, header, _))| {
            (heads.contains(head) || head.is_blanket()) && header.mentions(gcx, interface)
        })
        .map(|(&owner, _)| owner)
        .collect();
    owners.sort_unstable();
    for owner in owners {
        collect_header(gcx, owner);
    }
}

struct Actor<'ctx> {
    context: Gcx<'ctx>,
}

impl<'ctx> Actor<'ctx> {
    /// Collect explicit conformances; compiler-derived Tuple membership stays reserved.
    fn collect_impl_conformance(&mut self, impl_id: DefinitionID, interface_ty: &hir::Type) {
        // Extract the path from the interface type (must be a nominal type)
        let hir::TypeKind::Nominal(resolved_path) = &interface_ty.kind else {
            // Interface must be a nominal type path
            return;
        };

        // Construct a PathNode from the Type for use with lower_interface_reference
        let interface_path = hir::PathNode {
            id: interface_ty.id,
            path: resolved_path.clone(),
            span: interface_ty.span,
        };
        if self.reject_interface_alias_implementation(&interface_path) {
            return;
        }

        // Get type head and self type for the impl
        let Some(ty_key) = self.context.get_impl_type_head(impl_id) else {
            return;
        };

        let Some(self_ty) = self.context.get_impl_self_ty(impl_id) else {
            return;
        };

        let icx = DefTyLoweringCtx::new(impl_id, self.context);
        let impl_pkg = impl_id.package();

        let reference = icx
            .lowerer()
            .lower_interface_reference(self_ty, &interface_path);

        // Reject compiler-only capability claims.
        if self.is_compiler_only_interface(reference.id) {
            self.emit_compiler_only_error(interface_ty.span, reference);
            return;
        }

        if self.reject_task_clone_claim(self_ty, reference.id, interface_ty.span) {
            return;
        }

        if let Err(reason) =
            crate::sema::tycheck::utils::coherence::check_orphan(self.context, reference, impl_pkg)
        {
            self.emit_orphan_error(interface_ty.span, self_ty, reference, reason);
            return;
        }

        // Check for duplicate conformances
        if let Some(prev) = self.find_conflicting_conformance(ty_key, reference, impl_id) {
            self.emit_redundant(interface_ty.span, &prev);
            return;
        }

        // Register the conformance
        let is_conditional = !self.context.canonical_constraints_of(impl_id).is_empty();
        let record = ConformanceRecord {
            target: ty_key,
            interface: reference,
            extension: impl_id,
            location: interface_ty.span,
            is_conditional,
            is_inline: false, // Impl-based conformance
        };

        self.context.insert_conformance_record(record);
    }

    /// Collect conformances from inline syntax on struct/enum definitions.
    /// This allows auto-derivation of derivable interfaces like Clone, Hashable and PartialEq.
    fn collect_inline_conformance(
        &mut self,
        type_id: DefinitionID,
        conformances: &hir::Conformances,
    ) {
        let interfaces = &conformances.bounds;
        if interfaces.is_empty() {
            return;
        }

        let ty_key = TypeHead::Nominal(type_id);
        let self_ty = self.context.get_type(type_id);

        let icx = DefTyLoweringCtx::new(type_id, self.context);

        for interface in interfaces {
            for reference in icx.lowerer().lower_interface_references(self_ty, interface) {
                // Check for duplicate conformances
                if let Some(prev) = self.find_conflicting_conformance(ty_key, reference, type_id) {
                    self.emit_redundant(interface.span, &prev);
                    continue;
                }

                // Reject compiler-only capability claims.
                if self.is_compiler_only_interface(reference.id) {
                    self.emit_compiler_only_error(interface.span, reference);
                    continue;
                }

                if self.reject_task_clone_claim(self_ty, reference.id, interface.span) {
                    continue;
                }

                // Register the conformance
                let is_conditional = !self.context.canonical_constraints_of(type_id).is_empty()
                    || (!self.context.generics_of(type_id).is_empty()
                        && StdItem::ALL_INTERFACES.iter().any(|item| {
                            item.is_derivable()
                                && self.context.std_item_def(*item) == Some(reference.id)
                        }));
                let record = ConformanceRecord {
                    target: ty_key,
                    interface: reference,
                    extension: type_id, // For inline conformance, the "extension" is the type itself
                    location: interface.span,
                    is_conditional,
                    is_inline: true, // Inline conformance allows auto-synthesis
                };

                self.context.insert_conformance_record(record);
            }
        }
    }

    fn reject_task_clone_claim(&self, ty: Ty<'ctx>, interface: DefinitionID, span: Span) -> bool {
        let task_handle = matches!(
            crate::sema::tycheck::utils::normalize_aliases(self.context, ty).kind(),
            crate::sema::models::TyKind::Adt(def, _) if self.context.std_item_def(StdItem::Task) == Some(def.id)
        );
        if task_handle && self.context.std_item_def(StdItem::Clone) == Some(interface) {
            self.context
                .dcx()
                .emit_error("Task handles cannot conform to Clone".into(), Some(span));
            return true;
        }
        false
    }

    fn reject_interface_alias_implementation(&self, node: &hir::PathNode) -> bool {
        let hir::ResolvedPath::Resolved(path) = &node.path else {
            return false;
        };
        let hir::Resolution::Definition(alias_id, DefinitionKind::TypeAlias) = path.resolution
        else {
            return false;
        };

        let name = self
            .context
            .symbol_text(self.context.definition_ident(alias_id).symbol);
        let message = if self.context.is_interface_alias(alias_id) {
            format!(
                "interface-set alias '{name}' cannot be used as an implementation target; implement each constituent interface separately"
            )
        } else {
            format!("type alias '{name}' does not name an interface")
        };
        self.context.dcx().emit_error(message, Some(node.span));
        true
    }

    /// Check if an interface is compiler-only (cannot be implemented by user code).
    fn is_compiler_only_interface(&self, interface_id: DefinitionID) -> bool {
        // Tuple membership is compiler-derived.
        self.context.std_item_def(StdItem::Tuple) == Some(interface_id)
    }

    fn emit_compiler_only_error(&self, span: Span, interface: InterfaceReference<'ctx>) {
        let interface_name = interface.format(self.context);
        self.context.dcx().emit_error(
            format!(
                "'{}' is a compiler-internal interface and cannot be implemented by user types",
                interface_name
            ),
            Some(span),
        );
    }

    /// Find a conflicting conformance across all visible packages.
    fn find_conflicting_conformance(
        &self,
        ty_key: TypeHead,
        interface: InterfaceReference<'ctx>,
        new_extension_id: DefinitionID,
    ) -> Option<ConformanceRecord<'ctx>> {
        for package in self.context.conformance_ownership_packages(
            interface.id,
            interface.self_ty().expect("conformance Self"),
            interface.arguments,
        ) {
            if let Some(previous) =
                self.find_conformance_in_package(package, ty_key, interface, new_extension_id)
            {
                return Some(previous);
            }
        }

        None
    }

    fn find_conformance_in_package(
        &self,
        package_id: PackageIndex,
        ty_key: TypeHead,
        interface: InterfaceReference<'ctx>,
        new_extension_id: DefinitionID,
    ) -> Option<ConformanceRecord<'ctx>> {
        // Universal impls have no concrete constructor head. Scan the
        // interface bucket and cheaply reject unrelated concrete heads before
        // performing the full overlap proof.
        let candidates = self
            .context
            .conformance_records_for_interface(package_id, interface.id);

        for candidate in candidates {
            if candidate.target != ty_key && !candidate.target.is_blanket() && !ty_key.is_blanket()
            {
                continue;
            }

            if !self.overlaps(candidate, interface, new_extension_id) {
                continue;
            }

            return Some(candidate);
        }

        None
    }

    fn overlaps(
        &self,
        existing: ConformanceRecord<'ctx>,
        new_interface: InterfaceReference<'ctx>,
        new_extension_id: DefinitionID,
    ) -> bool {
        if existing.interface.id != new_interface.id {
            return false;
        }

        let icx = Rc::new(InferCtx::new(self.context));
        let span = Span::empty(crate::span::FileID::from_usize(0));
        let unifier = TypeUnifier::new(icx.clone());

        let existing_extension_args = icx.fresh_args_for_def(existing.extension, span);
        let existing_iface = instantiate_interface_ref_with_args(
            self.context,
            existing.interface,
            existing_extension_args,
        );
        let new_extension_args = icx.fresh_args_for_def(new_extension_id, span);
        let new_iface =
            instantiate_interface_ref_with_args(self.context, new_interface, new_extension_args);

        let existing_iface =
            crate::sema::tycheck::utils::normalize_aliases(self.context, existing_iface);
        let new_iface = crate::sema::tycheck::utils::normalize_aliases(self.context, new_iface);

        let Some(existing_self) = self.conformance_self_ty(existing.extension) else {
            return false;
        };
        let Some(new_self) = self.conformance_self_ty(new_extension_id) else {
            return false;
        };
        let existing_self =
            instantiate_ty_with_args(self.context, existing_self, existing_extension_args);
        let new_self = instantiate_ty_with_args(self.context, new_self, new_extension_args);
        let existing_self =
            crate::sema::tycheck::utils::normalize_aliases(self.context, existing_self);
        let new_self = crate::sema::tycheck::utils::normalize_aliases(self.context, new_self);
        if unifier.unify(existing_self, new_self).is_err() {
            return false;
        }

        if existing_iface.id != new_iface.id
            || existing_iface.arguments.len() != new_iface.arguments.len()
        {
            return false;
        }

        for (lhs, rhs) in existing_iface
            .arguments
            .iter()
            .zip(new_iface.arguments.iter())
        {
            match (lhs, rhs) {
                (GenericArgument::Type(lhs_ty), GenericArgument::Type(rhs_ty)) => {
                    if unifier.unify(*lhs_ty, *rhs_ty).is_err() {
                        return false;
                    }
                }
                (GenericArgument::Const(lhs_c), GenericArgument::Const(rhs_c)) => {
                    if unifier.unify_const(*lhs_c, *rhs_c).is_err() {
                        return false;
                    }
                }
                _ => return false,
            }
        }

        // If headers overlap, they only remain overlapping when the combined
        // obligations of both impls are jointly satisfiable.
        if !self.combined_constraints_potentially_satisfiable(
            &[
                (existing.extension, existing_extension_args),
                (new_extension_id, new_extension_args),
            ],
            icx,
        ) {
            return false;
        }

        true
    }

    fn conformance_self_ty(&self, extension_id: DefinitionID) -> Option<Ty<'ctx>> {
        match self.context.definition_kind(extension_id) {
            DefinitionKind::Impl => self.context.get_impl_self_ty(extension_id),
            DefinitionKind::Struct | DefinitionKind::Enum => {
                Some(self.context.get_type(extension_id))
            }
            _ => None,
        }
    }

    fn combined_constraints_potentially_satisfiable(
        &self,
        entries: &[(DefinitionID, crate::sema::models::GenericArguments<'ctx>)],
        icx: Rc<InferCtx<'ctx>>,
    ) -> bool {
        if entries.is_empty() {
            return true;
        }

        let mut instantiated = Vec::new();
        for (extension_id, extension_args) in entries {
            let constraints = self.context.canonical_constraints_of(*extension_id);
            instantiated.extend(constraints.into_iter().map(|constraint| {
                instantiate_constraint_with_args(self.context, constraint.value, *extension_args)
            }));
        }
        if instantiated.is_empty() {
            return true;
        }

        let env = ParamEnv::new(instantiated.clone());
        let unifier = TypeUnifier::new(icx.clone());

        let passes = instantiated.len().max(1) * 2;
        for _ in 0..passes {
            for constraint in &instantiated {
                let Constraint::TypeEquality(lhs, rhs) = *constraint else {
                    continue;
                };
                let lhs = normalize_ty(icx.clone(), lhs, &env);
                let rhs = normalize_ty(icx.clone(), rhs, &env);
                if unifier.unify(lhs, rhs).is_err() {
                    return false;
                }
            }
        }

        // Positive bounds may become satisfiable in another package or after
        // a dependency update. Only contradictory equalities prove disjointness;
        // absence of a current witness is never a negative conformance proof.

        true
    }

    fn emit_orphan_error(
        &self,
        span: Span,
        ty: Ty<'ctx>,
        interface: InterfaceReference<'ctx>,
        reason: crate::sema::tycheck::utils::coherence::OrphanError,
    ) {
        let interface_name = interface.format(self.context);
        let type_name = ty.format(self.context);
        use crate::sema::tycheck::utils::coherence::OrphanError;
        let reason = match reason {
            OrphanError::NoLocalInput => {
                "neither the interface nor a qualifying input type is defined in this package"
            }
            OrphanError::UncoveredParameter => {
                "an uncovered type parameter appears before the first local input type"
            }
        };
        self.context.dcx().emit_error(
            format!("cannot implement '{interface_name}' for '{type_name}': {reason}"),
            Some(span),
        );
    }

    fn emit_redundant(&self, span: Span, prev: &ConformanceRecord<'ctx>) {
        let name = prev.interface.format(self.context);
        self.context
            .dcx()
            .emit_error(format!("conflicting conformance to '{}'", name), Some(span));
        self.context.dcx().emit_info(
            "existing conformance is defined here".into(),
            Some(prev.location),
        );
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn inherited_class_conformances_keep_base_arguments_and_distinct_child_instantiations() {
        use crate::sema::models::{GenericArgument, SelectionMode, Ty, TyKind};
        crate::test_support::analyze_script(
            r#"
interface Compare[Other = Self] { func compare(_ other: &Other) -> bool; }
interface Marker[Other = Self] {
    func marker() -> int32 { 1 }
    func echo[Z](_ value: Z) -> Z { value }
}
struct Base[A, B] {}
conform[X, Y] Base[Y, X] to Compare {
    func compare(_ other: &Base[Y, X]) -> bool { true }
}
conform[X, Y] Base[Y, X] to Marker {}
struct Child[U, V] {}
conform[U, V] Child[U, V] to Compare[Child[U, V]] {
    func compare(_ other: &Child[U, V]) -> bool { true }
}
func main() {}
"#,
            |package, gcx| {
                let named = |name: &str| {
                    package
                        .root
                        .declarations
                        .iter()
                        .find(|decl| decl.identifier.symbol.as_str() == name)
                        .unwrap()
                        .id
                };
                let base_id = named("Base");
                let child_id = named("Child");
                let empty_info = crate::sema::models::ClassInfo {
                    initializers: &[],
                    base: None,
                    methods: &[],
                    payload: None,
                    is_final: false,
                };
                let mut base_definition = gcx.get_struct_definition(base_id).clone();
                base_definition.class_info = Some(empty_info);
                gcx.cache_struct_definition(base_id, base_definition);
                let TyKind::Adt(base_def, _) = gcx.get_type(base_id).kind() else {
                    unreachable!()
                };
                let TyKind::Adt(child_def, child_identity) = gcx.get_type(child_id).kind() else {
                    unreachable!()
                };
                let parent = Ty::new(
                    TyKind::Adt(
                        base_def,
                        gcx.store
                            .interners
                            .intern_generic_args(vec![child_identity[1], child_identity[0]]),
                    ),
                    gcx,
                );
                let mut child_definition = gcx.get_struct_definition(child_id).clone();
                child_definition.class_info = Some(crate::sema::models::ClassInfo {
                    base: Some(parent),
                    ..empty_info
                });
                gcx.cache_struct_definition(child_id, child_definition);
                gcx.with_session_type_database(|database| {
                    database.selection_cache.clear();
                    database.witness_cache.clear();
                });
                let args = |types: Vec<_>| {
                    gcx.store
                        .interners
                        .intern_generic_args(types.into_iter().map(GenericArgument::Type).collect())
                };
                let child = Ty::new(
                    TyKind::Adt(child_def, args(vec![gcx.types.int32, gcx.types.bool])),
                    gcx,
                );
                let base = gcx.class_base(child).unwrap();
                assert_eq!(
                    base,
                    Ty::new(
                        TyKind::Adt(base_def, args(vec![gcx.types.bool, gcx.types.int32])),
                        gcx
                    )
                );
                let goal = |interface, rhs| crate::sema::models::InterfaceGoal {
                    interface_id: interface,
                    self_ty: child,
                    interface_args: args(vec![rhs]),
                    bindings: &[],
                    param_env: &[],
                };
                let compare = named("Compare");
                for rhs in [base, child] {
                    let witness = gcx
                        .build_conformance_witness(goal(compare, rhs), SelectionMode::Codegen)
                        .unwrap();
                    let requirement =
                        gcx.get_interface_requirements(compare).unwrap().methods[0].id;
                    let instance = crate::specialize::resolve_instance(
                        gcx,
                        requirement,
                        args(vec![child, rhs]),
                    );
                    assert!(instance.is_item());
                    let declared_owner = gcx
                        .get_impl_target_ty(witness.extension_id.unwrap())
                        .unwrap();
                    let actual_owner =
                        crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args(
                            gcx,
                            declared_owner,
                            instance.args(),
                        );
                    assert_eq!(actual_owner, rhs);
                    if rhs == base {
                        assert_eq!(instance.args(), args(vec![gcx.types.int32, gcx.types.bool]));
                    }
                }
                let marker = named("Marker");
                assert!(
                    gcx.build_conformance_witness(goal(marker, base), SelectionMode::Codegen)
                        .is_ok()
                );
                assert!(
                    gcx.build_conformance_witness(goal(marker, child), SelectionMode::Codegen)
                        .is_err(),
                    "an inherited default argument is Base, never silently Child"
                );
                let echo = gcx
                    .get_interface_requirements(marker)
                    .unwrap()
                    .methods
                    .iter()
                    .find(|method| method.name.as_str() == "echo")
                    .unwrap()
                    .id;
                let inherited = crate::specialize::resolve_instance(
                    gcx,
                    echo,
                    args(vec![child, base, gcx.types.int64]),
                );
                assert_eq!(inherited.def_id(), echo);
                assert_eq!(inherited.args(), args(vec![base, base, gcx.types.int64]));
            },
        );
    }

    use super::*;
    use crate::{
        sema::{
            resolve::models::DefinitionIndex,
            std_items::{StdItemEntry, StdItemRegistry},
        },
        span::FileID,
        test_support::with_test_gcx,
    };

    #[test]
    fn compiler_only_capabilities_cannot_be_asserted_by_conformances() {
        with_test_gcx(|gcx| {
            let tuple = DefinitionID::new(gcx.package_index(), DefinitionIndex::from_raw(41));
            let ordinary = DefinitionID::new(gcx.package_index(), DefinitionIndex::from_raw(42));
            let registry =
                StdItemRegistry::from_entries([(StdItem::Tuple, tuple)].map(|(item, def_id)| {
                    (
                        item,
                        StdItemEntry {
                            def_id,
                            def_kind: DefinitionKind::Interface,
                            span: Span::empty(FileID::from_raw(0)),
                        },
                    )
                }));
            *gcx.store.std_items.borrow_mut() = Some((gcx.package_index(), registry));
            let actor = Actor { context: gcx };
            assert!(actor.is_compiler_only_interface(tuple));
            assert!(!actor.is_compiler_only_interface(ordinary));
        });
    }
}
