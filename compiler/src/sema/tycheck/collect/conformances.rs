use crate::{
    PackageIndex,
    compile::context::Gcx,
    error::CompileResult,
    hir::{self, DefinitionID, DefinitionKind, HirVisitor, StdInterface},
    sema::{
        models::{ConformanceRecord, EnumVariantKind, InterfaceReference},
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
            hir::DeclarationKind::Extension(node) => {
                if let Some(conformances) = &node.conformances {
                    self.collect_extension_conformance(declaration.id, conformances);
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
    /// Collect conformances from extension blocks (extend Foo: Interface {}).
    /// For marker interfaces like Copyable, extension-based conformances are NOT allowed
    /// (they require inline syntax on the struct/enum definition).
    fn collect_extension_conformance(
        &mut self,
        extend_id: DefinitionID,
        conformances: &hir::Conformances,
    ) {
        let interfaces = &conformances.bounds;
        if interfaces.is_empty() {
            return;
        }

        // Get type head and self type for the extension
        let Some(ty_key) = self.context.get_extension_type_head(extend_id) else {
            return;
        };

        let Some(self_ty) = self.context.get_extension_self_ty(extend_id) else {
            return;
        };

        let icx = DefTyLoweringCtx::new(extend_id, self.context);
        let extension_pkg = extend_id.package();

        for interface in interfaces {
            let reference = icx.lowerer().lower_interface_reference(self_ty, interface);

            // Check if this is a marker interface that requires inline syntax
            if self.is_marker_interface(reference.id) {
                self.emit_marker_requires_inline(interface.span, reference);
                continue;
            }

            // Orphan rule check: must own the type OR own the interface
            if !self.is_conformance_allowed(ty_key, reference.id, extension_pkg) {
                self.emit_orphan_error(interface.span, ty_key, reference);
                continue;
            }

            // Check for duplicate conformances
            if let Some(prev) = self.find_conflicting_conformance(ty_key, reference) {
                self.emit_redundant(interface.span, &prev);
                continue;
            }

            // Register the conformance
            let is_conditional = !self.context.canonical_constraints_of(extend_id).is_empty();
            let record = ConformanceRecord {
                target: ty_key,
                interface: reference,
                extension: extend_id,
                location: interface.span,
                is_conditional,
            };

            self.context.with_session_type_database(|db| {
                db.conformances.entry(ty_key).or_default().push(record)
            });
        }
    }

    /// Collect conformances from inline syntax on struct/enum definitions.
    /// This allows auto-derivation of marker interfaces like Copyable.
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
        let type_pkg = type_id.package();

        for interface in interfaces {
            let reference = icx.lowerer().lower_interface_reference(self_ty, interface);

            // Check for duplicate conformances
            if let Some(prev) = self.find_conflicting_conformance(ty_key, reference) {
                self.emit_redundant(interface.span, &prev);
                continue;
            }

            // Validate auto-derive for marker interfaces (Copyable, etc.)
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
            };

            self.context.with_session_type_database(|db| {
                db.conformances.entry(ty_key).or_default().push(record)
            });
        }
    }

    /// Check if the given interface is a marker interface that requires inline derivation.
    fn is_marker_interface(&self, interface_id: DefinitionID) -> bool {
        // Check Copyable
        if let Some(copyable_def) = self.context.std_interface_def(StdInterface::Copyable) {
            if interface_id == copyable_def {
                return true;
            }
        }
        // Add other marker interfaces here as needed (Clone, etc.)
        false
    }

    fn emit_marker_requires_inline(&self, span: Span, interface: InterfaceReference<'ctx>) {
        let interface_name = interface.format(self.context);
        self.context.dcx().emit_error(
            format!(
                "'{}' cannot be implemented via extension; use inline syntax on the struct/enum definition instead (e.g., `struct Foo: {} {{ ... }}`)",
                interface_name, interface_name
            ),
            Some(span),
        );
    }

    /// Orphan rule: you can add a conformance only if you own the type OR own the interface.
    fn is_conformance_allowed(
        &self,
        ty: TypeHead,
        interface_id: DefinitionID,
        extension_pkg: PackageIndex,
    ) -> bool {
        // Check if we own the interface
        if interface_id.package() == extension_pkg {
            return true;
        }

        // Check if we own the type
        match ty {
            TypeHead::Nominal(id) => id.package() == extension_pkg,
            // Built-in types are owned by std
            TypeHead::Primary(_)
            | TypeHead::GcPtr
            | TypeHead::Tuple(_)
            | TypeHead::Reference(_)
            | TypeHead::Pointer(_)
            | TypeHead::Array => self.is_std_package(extension_pkg),
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

    /// Validate marker interface derivation (e.g., Copyable).
    /// Returns true if validation passes, false if there's an error.
    fn validate_marker_derivation(
        &self,
        ty_key: TypeHead,
        interface: InterfaceReference<'ctx>,
        span: Span,
        kind: DefinitionKind,
    ) -> bool {
        // Check if this is Copyable
        let Some(copyable_def) = self.context.std_interface_def(StdInterface::Copyable) else {
            return true; // No Copyable interface defined, skip validation
        };

        if interface.id != copyable_def {
            return true; // Not Copyable, no special validation needed
        }

        // Validate that all fields are Copyable
        let TypeHead::Nominal(type_id) = ty_key else {
            // Non-nominal types (tuples, arrays, etc.) are handled by is_type_copyable
            return true;
        };

        match kind {
            DefinitionKind::Struct => self.validate_struct_copyable(type_id, span),
            DefinitionKind::Enum => self.validate_enum_copyable(type_id, span),
            _ => true, // Other types don't need field validation
        }
    }

    fn validate_struct_copyable(&self, struct_id: DefinitionID, span: Span) -> bool {
        let def = self.context.get_struct_definition(struct_id);
        let mut all_copyable = true;

        for field in def.fields.iter() {
            if !self.context.is_type_copyable(field.ty) {
                let type_name = field.ty.format(self.context);
                self.context.dcx().emit_error(
                    format!(
                        "cannot derive Copyable for '{}': field '{}' of type '{}' is not Copyable",
                        def.adt_def.name.as_str(),
                        field.name.as_str(),
                        type_name
                    ),
                    Some(span),
                );
                all_copyable = false;
            }
        }

        all_copyable
    }

    fn validate_enum_copyable(&self, enum_id: DefinitionID, span: Span) -> bool {
        let def = self.context.get_enum_definition(enum_id);
        let mut all_copyable = true;

        for variant in def.variants.iter() {
            if let EnumVariantKind::Tuple(fields) = &variant.kind {
                for (idx, field) in fields.iter().enumerate() {
                    if !self.context.is_type_copyable(field.ty) {
                        let type_name = field.ty.format(self.context);
                        let field_name = field
                            .label
                            .map(|s| s.as_str().to_string())
                            .unwrap_or_else(|| format!("{}", idx));
                        self.context.dcx().emit_error(
                            format!(
                                "cannot derive Copyable for '{}': field '{}' in variant '{}' of type '{}' is not Copyable",
                                def.adt_def.name.as_str(),
                                field_name,
                                variant.name.as_str(),
                                type_name
                            ),
                            Some(span),
                        );
                        all_copyable = false;
                    }
                }
            }
        }

        all_copyable
    }
}
