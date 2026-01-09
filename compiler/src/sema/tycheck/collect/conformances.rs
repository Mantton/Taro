use crate::{
    PackageIndex,
    compile::context::Gcx,
    error::CompileResult,
    hir::{self, DefinitionID, DefinitionKind, HirVisitor, StdInterface},
    sema::{
        models::{ConformanceRecord, EnumVariantKind, InterfaceReference, Ty, TyKind},
        resolve::models::TypeHead,
        tycheck::lower::{DefTyLoweringCtx, TypeLowerer},
    },
    span::Span,
};

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
        if let Some(prev) = self.find_conflicting_conformance(ty_key, reference) {
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

        self.context.with_session_type_database(|db| {
            db.conformances.entry(ty_key).or_default().push(record)
        });
    }

    /// Collect conformances from inline syntax on struct/enum definitions.
    /// This allows auto-derivation of derivable interfaces like Copy, Clone, Hashable, Equatable.
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
            if let Some(prev) = self.find_conflicting_conformance(ty_key, reference) {
                self.emit_redundant(interface.span, &prev);
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

            self.context.with_session_type_database(|db| {
                db.conformances.entry(ty_key).or_default().push(record)
            });
        }
    }

    /// Check if the given interface is a derivable interface that requires inline syntax.
    /// Returns the StdInterface variant if it's derivable, None otherwise.
    fn get_derivable_interface(&self, interface_id: DefinitionID) -> Option<StdInterface> {
        for iface in StdInterface::ALL {
            if let Some(def_id) = self.context.std_interface_def(iface) {
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
        self.context
            .package_ident(pkg)
            .map(|ident| ident.as_str() == crate::constants::STD_PREFIX)
            .unwrap_or(false)
    }

    /// Find a conflicting conformance across all visible packages.
    fn find_conflicting_conformance(
        &self,
        ty_key: TypeHead,
        interface: InterfaceReference<'ctx>,
    ) -> Option<ConformanceRecord<'ctx>> {
        // Get the package that owns the type (if nominal)
        let type_pkg = match ty_key {
            TypeHead::Nominal(id) => Some(id.package()),
            _ => None,
        };

        // Check the type's home package first (if different from current)
        if let Some(pkg) = type_pkg {
            if let Some(prev) = self.find_conformance_in_package(pkg, ty_key, interface) {
                return Some(prev);
            }
        }

        // Check the interface's home package
        let interface_pkg = interface.id.package();
        if Some(interface_pkg) != type_pkg {
            if let Some(prev) = self.find_conformance_in_package(interface_pkg, ty_key, interface) {
                return Some(prev);
            }
        }

        // Check the current session package
        let current_pkg = self.context.package_index();
        if Some(current_pkg) != type_pkg && current_pkg != interface_pkg {
            if let Some(prev) = self.find_conformance_in_package(current_pkg, ty_key, interface) {
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
    ) -> Option<ConformanceRecord<'ctx>> {
        self.context.with_type_database(package_id, |db| {
            db.conformances
                .get(&ty_key)
                .into_iter()
                .flat_map(|v| v.iter())
                .find(|rec| rec.interface == interface)
                .cloned()
        })
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
            .emit_warning(format!("redundant conformance to '{}'", name), Some(span));
        self.context.dcx().emit_info(
            "initial conformance is defined here".into(),
            Some(prev.location),
        );
    }

    /// Validate marker interface derivation (e.g., Copy).
    /// Returns true if validation passes, false if there's an error.
    fn validate_marker_derivation(
        &self,
        ty_key: TypeHead,
        interface: InterfaceReference<'ctx>,
        span: Span,
        kind: DefinitionKind,
    ) -> bool {
        // Check if this is Copy
        let Some(copy_def) = self.context.std_interface_def(StdInterface::Copy) else {
            return true; // No Copy interface defined, skip validation
        };

        if interface.id != copy_def {
            return true; // Not Copy, no special validation needed
        }

        // Validate that all fields are Copy
        let TypeHead::Nominal(type_id) = ty_key else {
            // Non-nominal types (tuples, arrays, etc.) are handled by is_type_copyable
            return true;
        };

        match kind {
            DefinitionKind::Struct => self.validate_struct_copy(type_id, span),
            DefinitionKind::Enum => self.validate_enum_copy(type_id, span),
            _ => true, // Other types don't need field validation
        }
    }

    fn validate_struct_copy(&self, struct_id: DefinitionID, span: Span) -> bool {
        let def = self.context.get_struct_definition(struct_id);
        let mut all_copy = true;

        for field in def.fields.iter() {
            if !self.is_type_copyable_in_context(field.ty, struct_id) {
                let type_name = field.ty.format(self.context);
                self.context.dcx().emit_error(
                    format!(
                        "cannot derive Copy for '{}': field '{}' of type '{}' is not Copy",
                        def.adt_def.name.as_str(),
                        field.name.as_str(),
                        type_name
                    ),
                    Some(span),
                );
                all_copy = false;
            }
        }

        all_copy
    }

    fn validate_enum_copy(&self, enum_id: DefinitionID, span: Span) -> bool {
        let def = self.context.get_enum_definition(enum_id);
        let mut all_copy = true;

        for variant in def.variants.iter() {
            if let EnumVariantKind::Tuple(fields) = &variant.kind {
                for (idx, field) in fields.iter().enumerate() {
                    if !self.is_type_copyable_in_context(field.ty, enum_id) {
                        let type_name = field.ty.format(self.context);
                        let field_name = field
                            .label
                            .map(|s| s.as_str().to_string())
                            .unwrap_or_else(|| format!("{}", idx));
                        self.context.dcx().emit_error(
                            format!(
                                "cannot derive Copy for '{}': field '{}' in variant '{}' of type '{}' is not Copy",
                                def.adt_def.name.as_str(),
                                field_name,
                                variant.name.as_str(),
                                type_name
                            ),
                            Some(span),
                        );
                        all_copy = false;
                    }
                }
            }
        }

        all_copy
    }

    /// Check if a type is copyable within the context of a specific definition.
    /// This is needed for type parameters, which need to check if they have a Copy bound.
    fn is_type_copyable_in_context(
        &self,
        ty: crate::sema::models::Ty<'ctx>,
        context_def: DefinitionID,
    ) -> bool {
        use crate::sema::models::{Constraint, TyKind};

        match ty.kind() {
            TyKind::Parameter(param) => {
                // For type parameters, check if there's a Copy bound in the constraints
                let Some(copy_def) = self.context.std_interface_def(StdInterface::Copy) else {
                    return false;
                };

                // Use the function that computes constraints if not cached
                let constraints = crate::sema::tycheck::constraints::canonical_constraints_of(
                    self.context,
                    context_def,
                );
                constraints.iter().any(|c| {
                    if let Constraint::Bound {
                        ty: bound_ty,
                        interface,
                    } = &c.value
                    {
                        // Compare by parameter index since different Ty instances may represent the same parameter
                        let bound_matches = match bound_ty.kind() {
                            TyKind::Parameter(bound_param) => bound_param.index == param.index,
                            _ => false,
                        };
                        bound_matches && interface.id == copy_def
                    } else {
                        false
                    }
                })
            }
            // For other types, delegate to the regular is_type_copyable
            _ => self.context.is_type_copyable(ty),
        }
    }
}
