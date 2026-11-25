use crate::{
    compile::context::{ComputedPropertyEntry, GlobalContext, MemberSet, TypeMemberIndex},
    error::CompileResult,
    hir::{self, DefinitionID, HirVisitor},
    sema::tycheck::lower::{DefTyLoweringCtx, TypeLowerer},
};
use rustc_hash::{FxHashMap, FxHashSet};

pub fn run(package: &hir::Package, context: GlobalContext) -> CompileResult<()> {
    super::super::overloads::run(package, context)?;
    let mut actor = Actor {
        context,
        impl_interfaces: FxHashMap::default(),
        property_accessors: FxHashSet::default(),
    };
    hir::walk_package(&mut actor, package);
    context.dcx().ok()
}

struct Actor<'ctx> {
    context: GlobalContext<'ctx>,
    /// Full conformance identity, including interface arguments.
    impl_interfaces: FxHashMap<DefinitionID, Option<crate::sema::models::InterfaceReference<'ctx>>>,
    property_accessors: FxHashSet<DefinitionID>,
}

impl<'ctx> Actor<'ctx> {
    fn collect_impl_member(&mut self, impl_id: DefinitionID, decl: &hir::AssociatedDeclaration) {
        let Some(head) = self.context.get_impl_type_head(impl_id) else {
            return;
        };

        // Check if this impl has an interface (trait impl vs inherent impl)
        let interface_id = self
            .impl_interfaces
            .get(&impl_id)
            .copied()
            .flatten()
            .map(|interface| interface.id);

        if self.property_accessors.contains(&decl.id) {
            return;
        }
        if let Some(interface) = interface_id {
            let mut pending = vec![interface];
            let mut seen = rustc_hash::FxHashSet::default();
            let mut declared = false;
            while let Some(interface) = pending.pop() {
                if !seen.insert(interface) {
                    continue;
                }
                if let Some(requirements) = self.context.get_interface_requirements(interface) {
                    let name = decl.identifier.symbol;
                    declared |= match &decl.kind {
                        hir::AssociatedDeclarationKind::Function(_) => {
                            requirements.methods.iter().any(|item| item.name == name)
                                || self
                                    .context
                                    .native_subscript_for_accessor(decl.id)
                                    .is_some()
                                    && requirements.methods.iter().any(|item| {
                                        self.context
                                            .native_subscript_for_accessor(item.id)
                                            .is_some()
                                    })
                        }
                        hir::AssociatedDeclarationKind::Property(_) => {
                            requirements.properties.iter().any(|item| item.name == name)
                        }
                        hir::AssociatedDeclarationKind::Constant(_) => {
                            requirements.constants.iter().any(|item| item.name == name)
                        }
                        hir::AssociatedDeclarationKind::Type(_) => {
                            requirements.types.iter().any(|item| item.name == name)
                        }
                        hir::AssociatedDeclarationKind::Subscript(_) => {
                            requirements.methods.iter().any(|item| {
                                self.context
                                    .native_subscript_for_accessor(item.id)
                                    .is_some()
                            })
                        }
                        hir::AssociatedDeclarationKind::Initializer(_) => false,
                    };
                }
                if let Some(definition) = self.context.get_interface_definition(interface) {
                    pending.extend(definition.superfaces.iter().map(|item| item.value.id));
                }
            }
            if !declared {
                self.context.dcx().emit_error(format!("'{}' is not a requirement of this interface; declare unrelated members in an `extend` block", self.context.symbol_text(decl.identifier.symbol)), Some(decl.identifier.span));
                return;
            }
        }

        match &decl.kind {
            hir::AssociatedDeclarationKind::Function(function)
            | hir::AssociatedDeclarationKind::Initializer(function) => {
                let has_self = function
                    .signature
                    .prototype
                    .inputs
                    .first()
                    .is_some_and(|param| self.context.symbol_eq(param.name.symbol, "self"));
                if !has_self
                    && interface_id.is_none()
                    && self.conflicts_with_constant(head, impl_id, decl, false)
                {
                    return;
                }
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
                self.collect_property(
                    head,
                    impl_id,
                    decl.id,
                    decl.identifier,
                    property,
                    interface_id,
                );
            }
            hir::AssociatedDeclarationKind::Constant(_) if interface_id.is_none() => {
                self.conflicts_with_constant(head, impl_id, decl, true);
            }
            _ => {}
        }
    }

    fn conflicts_with_constant(
        &self,
        head: crate::sema::resolve::models::TypeHead,
        impl_id: DefinitionID,
        decl: &hir::AssociatedDeclaration,
        constant: bool,
    ) -> bool {
        let candidates = self.context.with_session_type_database(|db| {
            db.type_head_to_members
                .get(&head)?
                .inherent_constants
                .get(&decl.identifier.symbol)
                .cloned()
        });
        let Some(candidates) = candidates else {
            return false;
        };
        let target = super::super::overloads::declaration_target(self.context, impl_id);
        let Some(other) = candidates.into_iter().find(|id| {
            (!constant || *id < decl.id)
                && self.context.definition_parent(*id).and_then(|parent| {
                    super::super::overloads::declaration_target(self.context, parent)
                }) == target
        }) else {
            return false;
        };
        self.context.dcx().emit_error(
            format!("invalid redeclaration of '{}'", self.context.symbol_text(decl.identifier.symbol)),
            Some(decl.identifier.span),
        );
        self.context.dcx().emit_info(
            "associated constant declared here".into(),
            Some(self.context.definition_ident(other).span),
        );
        true
    }

    fn collect_function(
        &mut self,
        head: crate::sema::resolve::models::TypeHead,
        impl_id: DefinitionID,
        def_id: DefinitionID,
        ident: crate::span::Identifier,
        has_self: bool,
        interface_id: Option<DefinitionID>,
    ) {
        let colliding_property = self.context.with_session_type_database(|db| {
            if let Some(interface_id) = interface_id {
                db.type_head_to_interface_properties
                    .get(&head)
                    .and_then(|properties| properties.get(&(interface_id, ident.symbol)))
                    .and_then(|entries| {
                        entries.iter().copied().find(|entry| {
                            self.context.definition_parent(entry.property_id) == Some(impl_id)
                        })
                    })
            } else {
                db.type_head_to_properties
                    .get(&head)
                    .and_then(|properties| properties.get(&ident.symbol))
                    .copied()
            }
        });
        if has_self && let Some(previous) = colliding_property {
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

        let fingerprint = super::super::overloads::member_fingerprint(
            self.context,
            def_id,
            self.impl_interfaces.get(&impl_id).copied().flatten(),
        );
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
        impl_id: DefinitionID,
        property_id: DefinitionID,
        ident: crate::span::Identifier,
        property: &hir::ComputedProperty,
        interface_id: Option<DefinitionID>,
    ) {
        if interface_id.is_none()
            && self
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
                method_collision = if let Some(interface_id) = interface_id {
                    index
                        .trait_methods
                        .get(&(interface_id, ident.symbol))
                        .and_then(|set| {
                            set.members.iter().copied().find(|candidate| {
                                self.context.definition_parent(*candidate) == Some(impl_id)
                            })
                        })
                } else {
                    index
                        .inherent_instance
                        .get(&ident.symbol)
                        .and_then(|set| set.members.first().copied())
                };
            }

            property_collision = if let Some(interface_id) = interface_id {
                db.type_head_to_interface_properties
                    .get(&head)
                    .and_then(|properties| properties.get(&(interface_id, ident.symbol)))
                    .and_then(|entries| {
                        entries.iter().copied().find(|entry| {
                            self.context.definition_parent(entry.property_id) == Some(impl_id)
                        })
                    })
            } else {
                db.type_head_to_properties
                    .get(&head)
                    .and_then(|properties| properties.get(&ident.symbol))
                    .copied()
            };
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

        let entry = ComputedPropertyEntry {
            property_id,
            ty: property_ty,
            getter_id: property.getter_id,
            visibility: self.context.definition_visibility(property_id),
        };

        self.context.with_session_type_database(|db| {
            if let Some(interface_id) = interface_id {
                db.type_head_to_interface_properties
                    .entry(head)
                    .or_default()
                    .entry((interface_id, ident.symbol))
                    .or_default()
                    .push(entry);
            } else {
                db.type_head_to_properties
                    .entry(head)
                    .or_default()
                    .insert(ident.symbol, entry);
            }
        });
    }
}

impl HirVisitor for Actor<'_> {
    fn visit_declaration(&mut self, declaration: &hir::Declaration) -> Self::Result {
        // Cache interface information for impl blocks
        if let hir::DeclarationKind::Impl(impl_node) = &declaration.kind {
            let interface = impl_node.interface.as_ref().and_then(|interface| {
                let hir::TypeKind::Nominal(hir::ResolvedPath::Resolved(path)) = &interface.kind
                else {
                    return None;
                };
                if !matches!(
                    path.resolution,
                    hir::Resolution::Definition(_, hir::DefinitionKind::Interface)
                ) {
                    return None;
                }
                let path = hir::PathNode {
                    id: interface.id,
                    path: hir::ResolvedPath::Resolved(path.clone()),
                    span: interface.span,
                };
                let lowerer = DefTyLoweringCtx::new(declaration.id, self.context);
                let target = self
                    .context
                    .get_impl_target_ty(declaration.id)
                    .expect("collected extension target");
                Some(lowerer.lowerer().lower_interface_reference(target, &path))
            });
            self.impl_interfaces.insert(declaration.id, interface);
            for declaration in &impl_node.declarations {
                if let hir::AssociatedDeclarationKind::Property(property) = &declaration.kind {
                    self.property_accessors.insert(property.getter_id);
                }
            }
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

#[cfg(test)]
mod declaration_tests {
    #[test]
    fn g29_reference_clone_requires_an_explicit_reference() {
        let prefix = "interface Clone { func clone() -> Self; }; struct Plain { value: int32 }; ";
        for expression in ["value.clone()", "value.clone"] {
            let source = format!(
                "{prefix}func main() {{ value := Plain {{ value: 1 }}; copied := {expression}; }}"
            );
            let diagnostics = crate::test_support::analyze_language_item_script(
                &source,
                false,
                &[(crate::hir::StdItem::Clone, "Clone")],
            );
            assert!(!diagnostics.is_empty(), "{source}");
        }
        let source = format!(
            "{prefix}func main() {{ value := Plain {{ value: 1 }}; reference := (&value).clone(); copyReference := (&value).clone; copied := copyReference(); }}"
        );
        let diagnostics = crate::test_support::analyze_language_item_script(
            &source,
            true,
            &[(crate::hir::StdItem::Clone, "Clone")],
        );
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }

    #[test]
    fn g29_value_storage_and_class_receivers() {
        for source in [
            "struct Secret { private value: int32; private update: int32 }; extend &Secret { func update() { self.value = self.update }; }; func main() {}",
            "struct Kind { value: int32 }; enum Input { case value(int32); }; extend &Kind { func take(_ input: Input) {}; }; func main() { kind := Kind { value: 0 }; kind.take(.value(1)) }",
            "struct Counter { value: int32 }; extend Counter { func copyChange() -> int32 { self.value += 1; self.value }; }; extend &Counter { func change() { self.value += 1 }; }; func main() { counter := Counter { value: 1 }; copied := counter.copyChange(); counter.change(); update := counter.change; update() }",
            "final class Object { value: int32 }; extend &Object { func replace(_ other: Object) { *self = other }; }; func main() {}",
            "final class Counter { value: int32 }; extend Counter { init() { self.value = 0 }; func change() { self.value += 1 }; }; func main() { counter := Counter(); counter.change() }",
            "interface Read { func read[T](_ value: T) -> int32 { 7 }; }; final class Box[Item, const Size: usize] { value: Item }; conform[Item, const Size: usize] Box[Item, Size] to Read {}; func main() {}",
            "struct Secret { private value: int32 }; extend &Secret { func read() -> int32 { self.value }; }; func main() {}",
        ] {
            let diagnostics = if source.contains("Counter()") {
                crate::test_support::analyze_script_diagnostics(source)
            } else {
                crate::test_support::analyze_script_mir_diagnostics(source)
            };
            assert!(diagnostics.is_empty(), "{source}\n{diagnostics:#?}");
        }
    }

    #[test]
    fn g29_reference_subject_bounds_support_generic_assignment() {
        let source = "interface AddAssign[Rhs] { func addAssign(_ rhs: Rhs); }; func update[T](_ value: &T, _ rhs: &T) where &T: AddAssign[T] { *value += *rhs }; func main() {}";
        let diagnostics = crate::test_support::analyze_language_item_script(
            source,
            true,
            &[(crate::hir::StdItem::AddAssign, "AddAssign")],
        );
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
        let value_receiver = source.replace(" where &T: AddAssign[T]", " where T: AddAssign[T]");
        let diagnostics = crate::test_support::analyze_language_item_script(
            &value_receiver,
            true,
            &[(crate::hir::StdItem::AddAssign, "AddAssign")],
        );
        assert!(
            diagnostics.is_empty(),
            "value receivers may mutate shared state: {diagnostics:#?}"
        );
        for source in [
            source.replace(" where &T: AddAssign[T]", ""),
            format!("{source}\nfunc missing[T](_ value: &T, _ rhs: &T) {{ update(value, rhs) }}"),
        ] {
            let diagnostics = crate::test_support::analyze_language_item_script(
                &source,
                true,
                &[(crate::hir::StdItem::AddAssign, "AddAssign")],
            );
            assert!(!diagnostics.is_empty(), "{source}");
        }
    }

    #[test]
    fn g29_reference_targets_require_storage_and_explicit_conformance() {
        for source in [
            "struct Counter { value: int32 }; extend &Counter { func change() { self.value += 1 }; }; func use(_ pointer: *const Counter) { unsafe { pointer.change() } }; func main() {}",
            "final class Object {}; extend &Object { func replace(_ other: Object) { *self = other }; }; func use(_ pointer: *const Object, _ other: Object) { unsafe { pointer.replace(other) } }; func main() {}",
            "final class Object {}; func use(_ pointer: *const Object) { unsafe { reference := &*pointer; } }; func main() {}",
            "struct Counter { value: int32 }; extend Counter { var copy: Counter { get { self } }; }; extend &Counter { func change() { self.value += 1 }; }; func main() { value := Counter { value: 0 }; value.copy.change() }",
            "struct Counter { value: int32 }; extend &Counter { func change() { self.value += 1 }; }; func make() -> Counter { Counter { value: 0 } }; func main() { make().change() }",
            "interface Update { func change(); }; struct Counter { value: int32 }; conform &Counter to Update { func change() { self.value += 1 }; }; func use[T: Update](_ value: T) { value.change() }; func main() { value := Counter { value: 0 }; use(value) }",
        ] {
            let diagnostics = crate::test_support::analyze_script_diagnostics(source);
            assert!(!diagnostics.is_empty(), "{source}");
        }
    }

    #[test]
    fn g29_conformance_bodies_cannot_add_unrelated_methods() {
        let source = "interface Reader { func read() -> int32; }\nstruct Value {}\nconform Value to Reader { func read() -> int32 { 1 }; func unrelated() {}; }\nfunc main() {}";
        let diagnostics = crate::test_support::analyze_script_diagnostics(source);
        assert!(
            diagnostics
                .iter()
                .any(|item| item.message.contains("not a requirement")),
            "{diagnostics:#?}"
        );
    }
}
