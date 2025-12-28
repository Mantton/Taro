use crate::{
    PackageIndex,
    compile::context::Gcx,
    error::CompileResult,
    hir::{self, DefinitionID, DefinitionKind, HirVisitor},
    sema::{
        models::{ConformanceRecord, InterfaceReference},
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
        let kind = self.context.definition_kind(declaration.id);
        if !matches!(kind, DefinitionKind::Extension) {
            return;
        }

        let node = match &declaration.kind {
            hir::DeclarationKind::Extension(node) => node,
            _ => unreachable!(),
        };

        if let Some(conformances) = &node.conformances {
            self.collect(declaration.id, conformances);
        }
    }
}

impl<'ctx> Actor<'ctx> {
    fn collect(&mut self, extend_id: DefinitionID, conformances: &hir::Conformances) {
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
            let record = ConformanceRecord {
                target: ty_key,
                interface: reference,
                extension: extend_id,
                location: interface.span,
                is_conditional: false, // TODO: check generics where clause
            };

            self.context.with_session_type_database(|db| {
                db.conformances.entry(ty_key).or_default().push(record)
            });
        }
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
                .find(|rec| rec.interface.id == interface.id)
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
}
