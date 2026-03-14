use crate::{
    PackageIndex,
    compile::context::Gcx,
    error::CompileResult,
    hir::{self, DefinitionID, DefinitionKind, HirVisitor, StdItem},
    sema::{
        models::{
            ConformanceRecord, ConstKind, Constraint, GenericArgument, GoalResult, InterfaceGoal,
            InterfaceReference, SelectionMode, Ty, TyKind,
        },
        resolve::models::TypeHead,
        tycheck::{
            infer::InferCtx,
            lower::{DefTyLoweringCtx, TypeLowerer},
            utils::{
                ParamEnv,
                instantiate::{
                    instantiate_constraint_with_args, instantiate_interface_ref_with_args,
                },
                normalize_ty,
                unify::TypeUnifier,
            },
        },
    },
    span::Span,
};
use std::rc::Rc;

pub fn run(package: &hir::Package, context: Gcx) -> CompileResult<()> {
    Actor::run(package, context)
}

struct Actor<'ctx> {
    context: Gcx<'ctx>,
}

impl<'ctx> Actor<'ctx> {
    fn new(context: Gcx<'ctx>) -> Actor<'ctx> {
        Actor { context }
    }

    fn run(package: &hir::Package, context: Gcx<'ctx>) -> CompileResult<()> {
        let mut actor = Actor::new(context);
        hir::walk_package(&mut actor, package);
        context.dcx().ok()
    }
}

fn generic_arg_has_inference(arg: GenericArgument<'_>) -> bool {
    match arg {
        GenericArgument::Type(ty) => ty.contains_inference(),
        GenericArgument::Const(c) => {
            matches!(c.kind, ConstKind::Infer(_)) || c.ty.contains_inference()
        }
    }
}

impl<'ctx> HirVisitor for Actor<'ctx> {
    fn visit_declaration(&mut self, declaration: &hir::Declaration) -> Self::Result {
        match &declaration.kind {
            hir::DeclarationKind::Impl(node) => {
                if let Some(interface) = &node.interface {
                    self.collect_impl_conformance(declaration.id, interface);
                }
            }
            hir::DeclarationKind::Struct(node) => {
                if let Some(conformances) = &node.conformances {
                    self.collect_inline_conformance(declaration.id, conformances);
                }
            }
            hir::DeclarationKind::Enum(node) => {
                if let Some(conformances) = &node.conformances {
                    self.collect_inline_conformance(declaration.id, conformances);
                }
            }
            _ => {}
        }
    }
}

impl<'ctx> Actor<'ctx> {
    /// Collect conformance from impl blocks (impl Interface for Type {}).
    /// For marker interfaces like Copy, impl-based conformances are NOT allowed
    /// (they require inline syntax on the struct/enum definition).
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

        // Check if this is a marker interface that requires inline syntax
        if self.is_marker_interface(reference.id) {
            self.emit_marker_requires_inline(interface_ty.span, reference);
            return;
        }

        // Orphan rule check: must own the type OR own the interface
        if !self.is_conformance_allowed(ty_key, self_ty, reference.id, impl_pkg) {
            self.emit_orphan_error(interface_ty.span, ty_key, reference);
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
    /// This allows auto-derivation of derivable interfaces like Copy, Clone, Hashable, PartialEq.
    fn collect_inline_conformance(
        &mut self,
        type_id: DefinitionID,
        conformances: &hir::Conformances,
    ) {
        let interfaces = &conformances.bounds;
        if interfaces.is_empty() {
            return;
        }

        let kind = self.context.definition_kind(type_id);
        let ty_key = TypeHead::Nominal(type_id);
        let self_ty = self.context.get_type(type_id);

        let icx = DefTyLoweringCtx::new(type_id, self.context);

        for interface in interfaces {
            let reference = icx.lowerer().lower_interface_reference(self_ty, interface);

            // Check for duplicate conformances
            if let Some(prev) = self.find_conflicting_conformance(ty_key, reference, type_id) {
                self.emit_redundant(interface.span, &prev);
                continue;
            }

            // Reject compiler-only interfaces (Tuple)
            if self.is_compiler_only_interface(reference.id) {
                self.emit_compiler_only_error(interface.span, reference);
                continue;
            }

            // Validate auto-derive for marker interfaces (Copy, etc.)
            if !self.validate_marker_derivation(ty_key, reference, interface.span, kind) {
                continue;
            }

            // Register the conformance
            let is_conditional = !self.context.canonical_constraints_of(type_id).is_empty();
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

    /// Check if the given interface is a derivable interface that requires inline syntax.
    /// Returns the StdItem variant if it's derivable, None otherwise.
    fn get_derivable_interface(&self, interface_id: DefinitionID) -> Option<StdItem> {
        for iface in StdItem::ALL_INTERFACES {
            if let Some(def_id) = self.context.std_item_def(iface) {
                if interface_id == def_id && iface.is_derivable() {
                    return Some(iface);
                }
            }
        }
        None
    }

    /// Check if the given interface is a marker interface that requires inline derivation.
    fn is_marker_interface(&self, interface_id: DefinitionID) -> bool {
        self.get_derivable_interface(interface_id)
            .map(|iface| iface.is_marker_only())
            .unwrap_or(false)
    }

    fn emit_marker_requires_inline(&self, span: Span, interface: InterfaceReference<'ctx>) {
        let interface_name = interface.format(self.context);
        self.context.dcx().emit_error(
            format!(
                "'{}' cannot be implemented via impl block; use inline syntax on the struct/enum definition instead (e.g., `struct Foo: {} {{ ... }}`)",
                interface_name, interface_name
            ),
            Some(span),
        );
    }

    /// Check if an interface is compiler-only (cannot be implemented by user code).
    fn is_compiler_only_interface(&self, interface_id: DefinitionID) -> bool {
        // Tuple is a compiler-only interface
        if let Some(tuple_def) = self.context.std_item_def(StdItem::Tuple) {
            if interface_id == tuple_def {
                return true;
            }
        }
        false
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

    /// Orphan rule: you can add a conformance only if you own the type OR own the interface.
    /// For reference/pointer types, localness propagates through the reference.
    fn is_conformance_allowed(
        &self,
        ty: TypeHead,
        self_ty: Ty<'ctx>,
        interface_id: DefinitionID,
        extension_pkg: PackageIndex,
    ) -> bool {
        // Check if we own the interface
        if interface_id.package() == extension_pkg {
            return true;
        }

        // Check if we own the type (propagating through references/pointers)
        self.is_type_local(ty, self_ty, extension_pkg)
    }

    /// Check if a type is "local" to the given package.
    /// For reference/pointer types, localness propagates to the inner type.
    fn is_type_local(&self, ty: TypeHead, self_ty: Ty<'ctx>, pkg: PackageIndex) -> bool {
        match ty {
            TypeHead::Nominal(id) => id.package() == pkg,
            TypeHead::Closure(id) => id.package() == pkg,
            // For references and pointers, check the inner type
            TypeHead::Reference(_) | TypeHead::Pointer(_) => self.is_inner_type_local(self_ty, pkg),
            // Built-in types are owned by std
            TypeHead::Primary(_) | TypeHead::Tuple(_) | TypeHead::Array => self.is_std_package(pkg),
        }
    }

    /// Check if the inner type of a reference/pointer is local.
    fn is_inner_type_local(&self, ty: Ty<'ctx>, pkg: PackageIndex) -> bool {
        match ty.kind() {
            TyKind::Reference(inner, _) | TyKind::Pointer(inner, _) => {
                // Recursively check the inner type
                self.is_inner_type_local(inner, pkg)
            }
            TyKind::Adt(def, _) => def.id.package() == pkg,
            // For other types, fall back to std ownership
            _ => self.is_std_package(pkg),
        }
    }

    /// Check if the given package is the standard library.
    fn is_std_package(&self, pkg: PackageIndex) -> bool {
        self.context.is_std_package(pkg)
    }

    /// Find a conflicting conformance across all visible packages.
    fn find_conflicting_conformance(
        &self,
        ty_key: TypeHead,
        interface: InterfaceReference<'ctx>,
        new_extension_id: DefinitionID,
    ) -> Option<ConformanceRecord<'ctx>> {
        // Get the package that owns the type (if nominal)
        let type_pkg = match ty_key {
            TypeHead::Nominal(id) => Some(id.package()),
            TypeHead::Closure(id) => Some(id.package()),
            _ => None,
        };

        // Check the type's home package first (if different from current)
        if let Some(pkg) = type_pkg {
            if let Some(prev) =
                self.find_conformance_in_package(pkg, ty_key, interface, new_extension_id)
            {
                return Some(prev);
            }
        }

        // Check the interface's home package
        let interface_pkg = interface.id.package();
        if Some(interface_pkg) != type_pkg {
            if let Some(prev) =
                self.find_conformance_in_package(interface_pkg, ty_key, interface, new_extension_id)
            {
                return Some(prev);
            }
        }

        // Check the current session package
        let current_pkg = self.context.package_index();
        if Some(current_pkg) != type_pkg && current_pkg != interface_pkg {
            if let Some(prev) =
                self.find_conformance_in_package(current_pkg, ty_key, interface, new_extension_id)
            {
                return Some(prev);
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
        let candidates =
            self.context
                .conformance_records_for_interface_head(package_id, interface.id, ty_key);

        for candidate in candidates {
            if candidate.interface == interface {
                return Some(candidate);
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

        let (existing_iface, existing_extension_args) =
            match self.instantiate_interface_for_overlap(existing, icx.clone(), span) {
                Some(args) => args,
                None => return false,
            };
        let (new_iface, new_extension_args) = match self.instantiate_interface_for_new_overlap(
            new_interface,
            new_extension_id,
            icx.clone(),
            span,
        ) {
            Some(args) => args,
            None => return false,
        };

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

    fn instantiate_interface_for_overlap(
        &self,
        record: ConformanceRecord<'ctx>,
        icx: Rc<InferCtx<'ctx>>,
        span: Span,
    ) -> Option<(
        InterfaceReference<'ctx>,
        crate::sema::models::GenericArguments<'ctx>,
    )> {
        let args = icx.fresh_args_for_def(record.extension, span);
        let instantiated =
            instantiate_interface_ref_with_args(self.context, record.interface, args);
        Some((instantiated, args))
    }

    fn instantiate_interface_for_new_overlap(
        &self,
        interface: InterfaceReference<'ctx>,
        extension_id: DefinitionID,
        icx: Rc<InferCtx<'ctx>>,
        span: Span,
    ) -> Option<(
        InterfaceReference<'ctx>,
        crate::sema::models::GenericArguments<'ctx>,
    )> {
        let args = icx.fresh_args_for_def(extension_id, span);
        let instantiated = instantiate_interface_ref_with_args(self.context, interface, args);
        Some((instantiated, args))
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

        let param_env = self
            .context
            .store
            .arenas
            .global
            .alloc_slice_clone(instantiated.as_slice());

        for constraint in instantiated {
            let Constraint::Bound { ty, interface } = constraint else {
                continue;
            };

            let ty = normalize_ty(icx.clone(), ty, &env);
            let mut interface = interface;
            interface.arguments = icx.resolve_args_if_possible(interface.arguments);

            if ty.contains_inference()
                || interface
                    .arguments
                    .iter()
                    .any(|arg| generic_arg_has_inference(*arg))
                || interface
                    .bindings
                    .iter()
                    .any(|binding| binding.ty.contains_inference())
            {
                // Conservatively treat unresolved obligations as potentially satisfiable.
                continue;
            }

            let self_ty = match interface.arguments.get(0).copied() {
                Some(GenericArgument::Type(self_ty)) => self_ty,
                _ => ty,
            };
            let interface_args = if interface.arguments.len() > 1 {
                self.context
                    .store
                    .interners
                    .intern_generic_args_slice(&interface.arguments[1..])
            } else {
                crate::sema::models::GenericArguments::empty()
            };

            let goal = InterfaceGoal {
                interface_id: interface.id,
                self_ty,
                interface_args,
                bindings: interface.bindings,
                param_env,
            };

            if matches!(
                self.context
                    .prove_interface_goal(goal, SelectionMode::Coherence),
                GoalResult::NoSolution
            ) {
                return false;
            }
        }

        true
    }

    fn emit_orphan_error(&self, span: Span, ty: TypeHead, interface: InterfaceReference<'ctx>) {
        let interface_name = interface.format(self.context);
        let type_name = ty.format(self.context);
        self.context.dcx().emit_error(
            format!(
                "cannot implement '{}' for '{}': neither the type nor the interface is defined in this package",
                interface_name, type_name
            ),
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

    /// Marker interfaces no longer require special field-level validation.
    fn validate_marker_derivation(
        &self,
        _ty_key: TypeHead,
        _interface: InterfaceReference<'ctx>,
        _span: Span,
        _kind: DefinitionKind,
    ) -> bool {
        true
    }
}
