use crate::{
    compile::context::{ComputedPropertyEntry, GlobalContext, MemberSet, TypeMemberIndex},
    error::CompileResult,
    hir::{self, DefinitionID, HirVisitor},
    sema::tycheck::lower::{DefTyLoweringCtx, TypeLowerer},
};
use rustc_hash::{FxHashMap, FxHasher};
use std::hash::{Hash, Hasher};

pub fn run(package: &hir::Package, context: GlobalContext) -> CompileResult<()> {
    let mut actor = Actor {
        context,
        impl_interfaces: FxHashMap::default(),
    };
    hir::walk_package(&mut actor, package);
    context.dcx().ok()
}

struct Actor<'ctx> {
    context: GlobalContext<'ctx>,
    /// Maps impl_id -> Option<interface_id> for quick lookup during member collection
    impl_interfaces: FxHashMap<DefinitionID, Option<DefinitionID>>,
}

impl<'ctx> Actor<'ctx> {
    fn is_hidden_property_accessor_name(&self, name: crate::span::Symbol) -> bool {
        let name = self.context.symbol_text(name);
        name.starts_with("__prop_get_") || name.starts_with("__prop_set_")
    }

    fn collect_impl_member(&mut self, impl_id: DefinitionID, decl: &hir::AssociatedDeclaration) {
        let Some(head) = self.context.get_impl_type_head(impl_id) else {
            return;
        };

        // Check if this impl has an interface (trait impl vs inherent impl)
        let interface_id = self.impl_interfaces.get(&impl_id).cloned().flatten();
        let _ = interface_id.is_some();

        match &decl.kind {
            hir::AssociatedDeclarationKind::Function(function) => {
                if self.is_hidden_property_accessor_name(decl.identifier.symbol) {
                    return;
                }
                let has_self = function
                    .signature
                    .prototype
                    .inputs
                    .first()
                    .is_some_and(|param| self.context.symbol_eq(param.name.symbol, "self"));
                self.collect_function(
                    head,
                    impl_id,
                    decl.id,
                    decl.identifier,
                    has_self,
                    interface_id,
                );
            }
            hir::AssociatedDeclarationKind::Property(property) => {
                self.collect_property(head, impl_id, decl.id, decl.identifier, property);
            }
            _ => {}
        }
    }

    fn collect_function(
        &mut self,
        head: crate::sema::resolve::models::TypeHead,
        _: DefinitionID,
        def_id: DefinitionID,
        ident: crate::span::Identifier,
        has_self: bool,
        interface_id: Option<DefinitionID>,
    ) {
        if has_self
            && let Some(previous) = self.context.with_session_type_database(|db| {
                db.type_head_to_properties
                    .get(&head)
                    .and_then(|properties| properties.get(&ident.symbol))
                    .copied()
            })
        {
            let msg = format!(
                "invalid redeclaration of '{}' as both property and method",
                self.context.symbol_text(ident.symbol)
            );
            self.context.dcx().emit_error(msg, Some(ident.span));

            let prev_ident = self.context.definition_ident(previous.property_id);
            let msg = format!(
                "'{}' is initially defined here",
                self.context.symbol_text(ident.symbol)
            );
            self.context.dcx().emit_info(msg, Some(prev_ident.span));
            return;
        }

        let fingerprint = self.fingerprint_for(def_id);
        self.context.with_session_type_database(|db| {
            let index: &mut TypeMemberIndex = db.type_head_to_members.entry(head).or_default();
            let is_trait_method = interface_id.is_some();

            {
                let set: &mut MemberSet = if let Some(interface_id) = interface_id {
                    // Trait impl: store in trait_methods with (interface_id, name) key
                    let key = (interface_id, ident.symbol);
                    index.trait_methods.entry(key).or_default()
                } else {
                    // Inherent impl: store in inherent_static or inherent_instance
                    if has_self {
                        index.inherent_instance.entry(ident.symbol).or_default()
                    } else {
                        index.inherent_static.entry(ident.symbol).or_default()
                    }
                };

                if let Some(previous) = set.fingerprints.insert(fingerprint, def_id) {
                    let msg = format!(
                        "invalid redeclaration of '{}'",
                        self.context.symbol_text(ident.symbol)
                    );
                    self.context.dcx().emit_error(msg, Some(ident.span));

                    let prev_ident = self.context.definition_ident(previous);
                    let msg = format!(
                        "'{}' is initially defined here",
                        self.context.symbol_text(ident.symbol)
                    );
                    self.context.dcx().emit_info(msg, Some(prev_ident.span));
                    return;
                }

                set.members.push(def_id);
            }

            if is_trait_method {
                index
                    .trait_methods_by_name
                    .entry(ident.symbol)
                    .or_default()
                    .push(def_id);
            }
        });
    }

    fn collect_property(
        &mut self,
        head: crate::sema::resolve::models::TypeHead,
        _impl_id: DefinitionID,
        property_id: DefinitionID,
        ident: crate::span::Identifier,
        property: &hir::ComputedProperty,
    ) {
        if self
            .context
            .lookup_field_in_type_head(head, ident.symbol)
            .is_some()
        {
            let msg = format!(
                "invalid redeclaration of '{}' as both field and property",
                self.context.symbol_text(ident.symbol)
            );
            self.context.dcx().emit_error(msg, Some(ident.span));
            return;
        }

        let mut method_collision: Option<DefinitionID> = None;
        let mut property_collision: Option<ComputedPropertyEntry<'ctx>> = None;

        self.context.with_session_type_database(|db| {
            if let Some(index) = db.type_head_to_members.get(&head) {
                method_collision = index
                    .inherent_instance
                    .get(&ident.symbol)
                    .and_then(|set| set.members.first().copied())
                    .or_else(|| {
                        index
                            .trait_methods_by_name
                            .get(&ident.symbol)
                            .and_then(|ids| ids.first().copied())
                    });
            }

            if let Some(existing) = db
                .type_head_to_properties
                .get(&head)
                .and_then(|properties| properties.get(&ident.symbol))
                .copied()
            {
                property_collision = Some(existing);
            }
        });

        if let Some(previous) = method_collision {
            let msg = format!(
                "invalid redeclaration of '{}' as both method and property",
                self.context.symbol_text(ident.symbol)
            );
            self.context.dcx().emit_error(msg, Some(ident.span));
            let prev_ident = self.context.definition_ident(previous);
            let msg = format!(
                "'{}' is initially defined here",
                self.context.symbol_text(ident.symbol)
            );
            self.context.dcx().emit_info(msg, Some(prev_ident.span));
            return;
        }

        if let Some(previous) = property_collision {
            let msg = format!(
                "invalid redeclaration of '{}'",
                self.context.symbol_text(ident.symbol)
            );
            self.context.dcx().emit_error(msg, Some(ident.span));
            let prev_ident = self.context.definition_ident(previous.property_id);
            let msg = format!(
                "'{}' is initially defined here",
                self.context.symbol_text(ident.symbol)
            );
            self.context.dcx().emit_info(msg, Some(prev_ident.span));
            return;
        }

        let lowerer = DefTyLoweringCtx::new(property_id, self.context);
        let property_ty = lowerer.lowerer().lower_type(&property.ty);
        self.context.cache_type(property_id, property_ty);

        let getter_sig = self.context.get_signature(property.getter_id);
        if getter_sig.output != property_ty {
            self.context.dcx().emit_error(
                format!(
                    "getter for property '{}' must return {}",
                    self.context.symbol_text(ident.symbol),
                    property_ty.format(self.context)
                ),
                Some(ident.span),
            );
            return;
        }

        if let Some(setter_id) = property.setter_id {
            let setter_sig = self.context.get_signature(setter_id);
            if setter_sig.inputs.len() != 2 || setter_sig.inputs[1].ty != property_ty {
                self.context.dcx().emit_error(
                    format!(
                        "setter for property '{}' must accept a value of type {}",
                        self.context.symbol_text(ident.symbol),
                        property_ty.format(self.context)
                    ),
                    Some(ident.span),
                );
                return;
            }

            if self.context.definition_is_async(setter_id) {
                self.context.dcx().emit_error(
                    "async setters are not supported".into(),
                    Some(ident.span),
                );
                return;
            }
        }

        let entry = ComputedPropertyEntry {
            property_id,
            ty: property_ty,
            getter_id: property.getter_id,
            setter_id: property.setter_id,
            visibility: self.context.definition_visibility(property_id),
        };

        self.context.with_session_type_database(|db| {
            db.type_head_to_properties
                .entry(head)
                .or_default()
                .insert(ident.symbol, entry);
        });
    }

    fn fingerprint_for(&self, id: DefinitionID) -> u64 {
        let sig = self.context.get_signature(id);

        let mut hasher = FxHasher::default();
        self.context.definition_is_async(id).hash(&mut hasher);
        sig.abi.hash(&mut hasher);
        sig.is_variadic.hash(&mut hasher);
        sig.inputs.len().hash(&mut hasher);
        for param in &sig.inputs {
            param.label.hash(&mut hasher);
            param.ty.hash(&mut hasher);
        }
        sig.output.hash(&mut hasher);
        hasher.finish()
    }
}

impl HirVisitor for Actor<'_> {
    fn visit_declaration(&mut self, declaration: &hir::Declaration) -> Self::Result {
        // Cache interface information for impl blocks
        if let hir::DeclarationKind::Impl(impl_node) = &declaration.kind {
            let interface_id = impl_node.interface.as_ref().and_then(|interface_ty| {
                // Extract interface ID from the type
                if let hir::TypeKind::Nominal(path) = &interface_ty.kind {
                    if let hir::ResolvedPath::Resolved(resolved) = path {
                        if let hir::Resolution::Definition(id, _) = resolved.resolution {
                            return Some(id);
                        }
                    }
                }
                None
            });
            self.impl_interfaces.insert(declaration.id, interface_id);
        }

        // Continue walking to visit children (especially associated declarations in impl blocks)
        hir::walk_declaration(self, declaration)
    }

    fn visit_assoc_declaration(
        &mut self,
        node: &hir::AssociatedDeclaration,
        context: hir::AssocContext,
    ) -> Self::Result {
        match context {
            hir::AssocContext::Interface(..) => return,
            hir::AssocContext::Impl(impl_id) => {
                self.collect_impl_member(impl_id, node);
            }
        }
    }
}
