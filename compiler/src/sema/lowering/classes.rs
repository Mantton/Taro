//! Nominal class values own a physical handle, not their logical payload fields.
//! Root source classes use the native construction/publication and object-field
//! permission protocol. Inheritance and interface witnesses remain separate.
use crate::{
    compile::context::GlobalContext,
    hir::StdItem,
    sema::{
        models::{AdtKind, ClassInfo, Ty, TyKind},
        tycheck::utils::normalize_aliases,
    },
};

impl<'ctx> GlobalContext<'ctx> {
    /// Constructor synthesis calls this std hook; GC codegen replaces its
    /// placeholder body, which must therefore never be inlined or summarized.
    pub fn is_class_payload_factory(self, definition: crate::hir::DefinitionID) -> bool {
        self.symbol_text(self.definition_symbol_or_fallback(definition))
            .as_str()
            == "__classAllocatePayload"
    }

    /// Recover the source class for its private, physically nested payload.
    /// Source lookup uses flattened fields; storage and cleanup keep the base
    /// prefix intact so each initialized inheritance level owns its cleanup.
    pub fn class_for_payload(self, ty: Ty<'ctx>) -> Option<Ty<'ctx>> {
        let TyKind::Adt(payload, args) = normalize_aliases(self, ty).kind() else {
            return None;
        };
        let kind = self
            .store
            .synthetic_definitions
            .borrow()
            .get(&payload.id)?
            .kind;
        let crate::sema::models::SyntheticDefinitionKind::ClassPayload { class } = kind else {
            return None;
        };
        let TyKind::Adt(class, _) = self.get_type(class).kind() else {
            return None;
        };
        Some(Ty::new(TyKind::Adt(class, args), self))
    }

    pub fn source_struct_definition(
        self,
        ty: Ty<'ctx>,
    ) -> Option<crate::sema::models::StructDefinition<'ctx>> {
        let ty = self.class_for_payload(ty).unwrap_or(ty);
        let TyKind::Adt(def, args) = ty.kind() else {
            return None;
        };
        if def.kind != AdtKind::Struct {
            return None;
        }
        Some(
            crate::sema::tycheck::utils::instantiate::instantiate_struct_definition_with_args(
                self,
                self.get_struct_definition(def.id),
                args,
            ),
        )
    }

    pub fn class_info(self, ty: Ty<'ctx>) -> Option<ClassInfo<'ctx>> {
        match normalize_aliases(self, ty).kind() {
            TyKind::Adt(definition, _) if definition.kind == AdtKind::Struct => self
                .try_get_struct_definition(definition.id)
                .and_then(|definition| definition.class_info),
            _ => None,
        }
    }

    pub fn class_base(self, ty: Ty<'ctx>) -> Option<Ty<'ctx>> {
        let TyKind::Adt(adt, args) = normalize_aliases(self, ty).kind() else {
            return None;
        };
        if self.store.collecting_constant_headers.get() {
            crate::sema::tycheck::ensure_class_base(self, adt.id);
        }
        self.class_info(ty)?.base.map(|base| {
            crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args(self, base, args)
        })
    }

    pub fn class_initializer(
        self,
        class: Ty<'ctx>,
        id: crate::hir::DefinitionID,
    ) -> Option<crate::sema::models::ClassInitializer<'ctx>> {
        let class = self.constructor_value(class);
        let TyKind::Adt(_, args) = normalize_aliases(self, class).kind() else {
            return None;
        };
        let mut entry = *self.class_info(class)?.initializers.iter().find(|entry| {
            entry.definition == id || entry.family == id || entry.implementation == id
        })?;
        entry.owner = crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args(
            self,
            entry.owner,
            args,
        );
        Some(entry)
    }

    pub fn class_ancestry(self, ty: Ty<'ctx>) -> Vec<Ty<'ctx>> {
        let mut result = vec![];
        let mut visited = rustc_hash::FxHashSet::default();
        let mut current = Some(normalize_aliases(self, ty));
        while let Some(ty) = current {
            let TyKind::Adt(adt, _) = ty.kind() else {
                break;
            };
            if !self.is_class_type(ty) || !visited.insert(adt.id) {
                break;
            }
            result.push(ty);
            current = self.class_base(ty);
        }
        result
    }

    pub fn is_class_subtype(self, derived: Ty<'ctx>, base: Ty<'ctx>) -> bool {
        self.is_class_type(base)
            && self
                .class_ancestry(derived)
                .contains(&normalize_aliases(self, base))
    }

    /// Translate the flattened source field index to nested base-prefix storage.
    /// Runtime access paths retain flattened identities, shared by every upcast.
    pub fn class_field_payload_path(self, class: Ty<'ctx>, mut index: usize) -> Option<Vec<u32>> {
        let mut class = class;
        let mut path = vec![];
        loop {
            let base = self.class_base(class);
            if let Some(base) = base {
                let TyKind::Adt(base_def, _) = base.kind() else {
                    return None;
                };
                let inherited = self.get_struct_definition(base_def.id).fields.len();
                if index < inherited {
                    path.push(0);
                    class = base;
                    continue;
                }
                index -= inherited;
                path.push(u32::try_from(index + 1).ok()?);
                return Some(path);
            }
            path.push(u32::try_from(index).ok()?);
            return Some(path);
        }
    }

    /// Construct an unnameable value layout for object bytes. Keeping this
    /// nominal layout separate lets ordinary initialized-field/drop analysis
    /// manage construction without ever treating a class handle as its fields.
    /// Source class activation must validate field retention before calling it.
    pub fn ensure_class_payload(self, class: Ty<'ctx>) -> Option<Ty<'ctx>> {
        use crate::sema::models::{
            AdtDef, LabeledFunctionSignature, StructDefinition, StructRepr, SyntheticDefinition,
            SyntheticDefinitionKind,
        };
        let TyKind::Adt(definition, arguments) = normalize_aliases(self, class).kind() else {
            return None;
        };
        let mut object = self.get_struct_definition(definition.id).clone();
        let mut info = object.class_info?;
        let payload = if let Some(payload) = info.payload {
            payload
        } else {
            let payload = self.allocate_synthetic_id(definition.id.package());
            let payload_def = AdtDef {
                id: payload,
                kind: AdtKind::Struct,
            };
            let generics = self.generics_of(definition.id);
            let identity =
                crate::sema::tycheck::utils::generics::GenericsBuilder::identity_for_item(
                    self,
                    definition.id,
                );
            let payload_ty = Ty::new(TyKind::Adt(payload_def, identity), self);
            let signature = self
                .store
                .arenas
                .function_signatures
                .alloc(LabeledFunctionSignature {
                    inputs: vec![],
                    output: payload_ty,
                    is_variadic: false,
                    abi: None,
                });
            self.register_synthetic_definition(
                payload,
                SyntheticDefinition {
                    kind: SyntheticDefinitionKind::ClassPayload {
                        class: definition.id,
                    },
                    name: self.intern_symbol(&format!(
                        "{}$payload",
                        self.symbol_text(self.definition_ident(definition.id).symbol)
                    )),
                    generics,
                    signature,
                    span: self.definition_ident(definition.id).span,
                },
            );
            self.cache_type(payload, payload_ty);
            self.update_constraints(payload, self.constraints_of(definition.id));
            let mut fields = object.fields.to_vec();
            let mut repr = StructRepr::Taro;
            if let Some(base) = info.base {
                let base_payload = self.ensure_class_payload(base)?;
                let TyKind::Adt(base_def, _) = base.kind() else {
                    return None;
                };
                fields.drain(..self.get_struct_definition(base_def.id).fields.len());
                fields.insert(
                    0,
                    crate::sema::models::StructField {
                        default_provider: None,
                        name: self.intern_symbol("$base"),
                        ty: base_payload,
                        mutability: crate::hir::Mutability::Mutable,
                        def_id: base_def.id,
                        visibility: self.definition_visibility(definition.id),
                        coding_key: None,
                        coding_skip: false,
                    },
                );
                repr = StructRepr::C;
            }
            self.cache_struct_definition(
                payload,
                StructDefinition {
                    adt_def: payload_def,
                    class_info: None,
                    positional: false,
                    has_initializer: false,
                    repr,
                    fields: self.store.arenas.global.alloc_slice_copy(&fields),
                },
            );
            info.payload = Some(payload);
            object.class_info = Some(info);
            self.cache_struct_definition(definition.id, object);
            payload
        };
        let TyKind::Adt(payload, _) = self.get_type(payload).kind() else {
            return None;
        };
        Some(Ty::new(TyKind::Adt(payload, arguments), self))
    }

    /// Virtual source calls cannot use a concrete base body's optimization or
    /// escape summary: a later package may provide a different override.
    pub fn is_virtual_class_method(self, method: crate::hir::DefinitionID) -> bool {
        self.try_get_signature(method)
            .and_then(|signature| signature.inputs.first())
            .filter(|input| self.symbol_text(input.name).as_str() == "self")
            .map(|input| match normalize_aliases(self, input.ty).kind() {
                TyKind::Reference(inner) => inner,
                _ => input.ty,
            })
            .is_some_and(|class| {
                self.class_method(class, method)
                    .is_some_and(|slot| !slot.is_final)
            })
    }

    /// Split class construction from publication. The source initializer keeps
    /// its public result; this unnameable body replaces only the success type
    /// with initialized payload bytes, preserving any Result error type.
    pub fn class_payload_initializer(
        self,
        initializer: crate::hir::DefinitionID,
    ) -> Option<crate::hir::DefinitionID> {
        use crate::sema::models::{SyntheticDefinition, SyntheticDefinitionKind};
        let class = self.initializer_target(initializer);
        self.class_info(class)?;
        if self
            .class_initializer(class, initializer)
            .is_some_and(|entry| entry.is_convenience)
        {
            return None;
        }
        if let Some(id) = self.store.synthetic_definitions.borrow().iter().find_map(|(id, definition)| {
            matches!(definition.kind, SyntheticDefinitionKind::ClassPayloadInitializer { initializer: source, .. } if source == initializer).then_some(*id)
        }) { return Some(id); }
        let mut signature = self.get_signature(initializer).clone();
        let payload = self.ensure_class_payload(class)?;
        signature.output = self.constructor_result(signature.output, payload);
        let signature = self.store.arenas.function_signatures.alloc(signature);
        let id = self.allocate_synthetic_id(initializer.package());
        let TyKind::Adt(class, _) = class.kind() else {
            return None;
        };
        self.register_synthetic_definition(
            id,
            SyntheticDefinition {
                kind: SyntheticDefinitionKind::ClassPayloadInitializer {
                    class: class.id,
                    initializer,
                },
                name: self.intern_symbol(&format!(
                    "{}$init_payload${}",
                    self.symbol_text(self.definition_ident(class.id).symbol),
                    initializer.index().raw()
                )),
                generics: self.generics_of(initializer),
                signature,
                span: self.definition_ident(initializer).span,
            },
        );
        self.cache_signature(id, signature.clone());
        self.cache_type(id, Ty::from_labeled_signature(self, signature));
        self.update_constraints(id, self.constraints_of(initializer));
        Some(id)
    }

    /// A private native stub forwards the exact constructor ABI after removing
    /// its process-long descriptor input. It owns no additional argument copies
    /// or cleanup state: the selected checked constructor receives all debts.
    pub fn class_initializer_dispatch(
        self,
        initializer: crate::hir::DefinitionID,
    ) -> Option<crate::hir::DefinitionID> {
        use crate::sema::models::{
            LabeledFunctionParameter, SyntheticDefinition, SyntheticDefinitionKind,
        };
        let class = self.initializer_target(initializer);
        self.class_initializer(class, initializer)?;
        if let Some(id) = self.store.synthetic_definitions.borrow().iter().find_map(|(id, definition)| {
            matches!(definition.kind, SyntheticDefinitionKind::ClassInitializerDispatch { initializer: source } if source == initializer).then_some(*id)
        }) { return Some(id); }
        let mut signature = self.get_signature(initializer).clone();
        signature.inputs.insert(
            0,
            LabeledFunctionParameter {
                label: None,
                name: self.intern_symbol("$class_context"),
                ty: Ty::new(
                    TyKind::Pointer(self.types.uint8, crate::hir::Mutability::Immutable),
                    self,
                ),
                is_lazy: false,
                default_provider: None,
            },
        );
        for parameter in &mut signature.inputs {
            parameter.default_provider = None;
        }
        let signature = self.store.arenas.function_signatures.alloc(signature);
        let id = self.allocate_synthetic_id(initializer.package());
        self.register_synthetic_definition(
            id,
            SyntheticDefinition {
                kind: SyntheticDefinitionKind::ClassInitializerDispatch { initializer },
                name: self.intern_symbol(&format!("$init_dispatch${}", initializer.index().raw())),
                generics: self.generics_of(initializer),
                signature,
                span: self.definition_ident(initializer).span,
            },
        );
        self.cache_signature(id, signature.clone());
        self.cache_type(id, Ty::from_labeled_signature(self, signature));
        self.update_constraints(id, self.constraints_of(initializer));
        Some(id)
    }

    pub fn class_convenience_initializer(
        self,
        initializer: crate::hir::DefinitionID,
    ) -> Option<crate::hir::DefinitionID> {
        use crate::sema::models::{
            LabeledFunctionParameter, SyntheticDefinition, SyntheticDefinitionKind,
        };
        let class = self.initializer_target(initializer);
        if !self.class_initializer(class, initializer)?.is_convenience {
            return None;
        }
        if let Some(id) = self.store.synthetic_definitions.borrow().iter().find_map(|(id, definition)| {
            matches!(definition.kind, SyntheticDefinitionKind::ClassConvenienceInitializer { initializer: source } if source == initializer).then_some(*id)
        }) { return Some(id); }
        let mut signature = self.get_signature(initializer).clone();
        signature.inputs.insert(
            0,
            LabeledFunctionParameter {
                label: None,
                name: self.intern_symbol("$class_context"),
                ty: Ty::new(
                    TyKind::Pointer(self.types.uint8, crate::hir::Mutability::Immutable),
                    self,
                ),
                is_lazy: false,
                default_provider: None,
            },
        );
        for parameter in &mut signature.inputs {
            parameter.default_provider = None;
        }
        let signature = self.store.arenas.function_signatures.alloc(signature);
        let id = self.allocate_synthetic_id(initializer.package());
        self.register_synthetic_definition(
            id,
            SyntheticDefinition {
                kind: SyntheticDefinitionKind::ClassConvenienceInitializer { initializer },
                name: self
                    .intern_symbol(&format!("$init_convenience${}", initializer.index().raw())),
                generics: self.generics_of(initializer),
                signature,
                span: self.definition_ident(initializer).span,
            },
        );
        self.cache_signature(id, signature.clone());
        self.cache_type(id, Ty::from_labeled_signature(self, signature));
        self.update_constraints(id, self.constraints_of(initializer));
        Some(id)
    }

    pub fn class_construction_descriptor(
        self,
        class: Ty<'ctx>,
    ) -> Option<crate::hir::DefinitionID> {
        use crate::sema::models::{
            LabeledFunctionSignature, SyntheticDefinition, SyntheticDefinitionKind,
        };
        let TyKind::Adt(class, _) = class.kind() else {
            return None;
        };
        self.class_info(self.get_type(class.id))?;
        if let Some(id) = self.store.synthetic_definitions.borrow().iter().find_map(|(id, definition)| {
            matches!(definition.kind, SyntheticDefinitionKind::ClassConstructionDescriptor { class: source } if source == class.id).then_some(*id)
        }) { return Some(id); }
        let signature = self
            .store
            .arenas
            .function_signatures
            .alloc(LabeledFunctionSignature {
                inputs: vec![],
                output: Ty::new(
                    TyKind::Pointer(self.types.uint8, crate::hir::Mutability::Immutable),
                    self,
                ),
                is_variadic: false,
                abi: None,
            });
        let id = self.allocate_synthetic_id(class.id.package());
        self.register_synthetic_definition(
            id,
            SyntheticDefinition {
                kind: SyntheticDefinitionKind::ClassConstructionDescriptor { class: class.id },
                name: self.intern_symbol(&format!("$class_context${}", class.id.index().raw())),
                generics: self.generics_of(class.id),
                signature,
                span: self.definition_ident(class.id).span,
            },
        );
        self.cache_signature(id, signature.clone());
        self.cache_type(id, Ty::from_labeled_signature(self, signature));
        Some(id)
    }

    /// Class handles are Copy. Callers supply an owned copy; the Native stub
    /// releases exactly that copy after reading immutable descriptor metadata.
    pub fn class_object_descriptor(self, class: Ty<'ctx>) -> Option<crate::hir::DefinitionID> {
        use crate::sema::models::{
            LabeledFunctionParameter, LabeledFunctionSignature, SyntheticDefinition,
            SyntheticDefinitionKind,
        };
        let TyKind::Adt(class, _) = class.kind() else {
            return None;
        };
        self.class_info(self.get_type(class.id))?;
        if let Some(id) = self.store.synthetic_definitions.borrow().iter().find_map(|(id, definition)| {
            matches!(definition.kind, SyntheticDefinitionKind::ClassObjectDescriptor { class: source } if source == class.id).then_some(*id)
        }) { return Some(id); }
        let signature = self
            .store
            .arenas
            .function_signatures
            .alloc(LabeledFunctionSignature {
                inputs: vec![LabeledFunctionParameter {
                    label: None,
                    name: self.intern_symbol("value"),
                    ty: self.get_type(class.id),
                    is_lazy: false,
                    default_provider: None,
                }],
                output: Ty::new(
                    TyKind::Pointer(self.types.uint8, crate::hir::Mutability::Immutable),
                    self,
                ),
                is_variadic: false,
                abi: None,
            });
        let id = self.allocate_synthetic_id(class.id.package());
        self.register_synthetic_definition(
            id,
            SyntheticDefinition {
                kind: SyntheticDefinitionKind::ClassObjectDescriptor { class: class.id },
                name: self.intern_symbol(&format!("$object_context${}", class.id.index().raw())),
                generics: self.generics_of(class.id),
                signature,
                span: self.definition_ident(class.id).span,
            },
        );
        self.cache_signature(id, signature.clone());
        self.cache_type(id, Ty::from_labeled_signature(self, signature));
        Some(id)
    }

    /// A nominal source class, rather than the compiler's private physical type.
    pub fn is_class_type(self, ty: Ty<'ctx>) -> bool {
        self.class_info(ty).is_some()
    }

    /// Both nominal classes and the private backend owner use the exact same
    /// retain/release ABI. This confers neither Clone nor Sendable.
    pub fn uses_native_class_handle(self, ty: Ty<'ctx>) -> bool {
        self.is_class_type(ty)
            || matches!(normalize_aliases(self, ty).kind(),
            TyKind::Adt(definition, _) if self.std_item_def(StdItem::ClassHandle) == Some(definition.id))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn class_payload_has_a_separate_noncopyable_nominal_layout() {
        crate::test_support::analyze_script(
            "struct Object[T] { value: T; count: int32 }\nfunc main() {}",
            |package, gcx| {
                let id = package.root.declarations[0].id;
                let class_ty = gcx.get_type(id);
                let mut definition = gcx.get_struct_definition(id).clone();
                definition.class_info = Some(ClassInfo {
                    initializers: &[],
                    base: None,
                    methods: &[],
                    payload: None,
                    is_final: false,
                });
                gcx.cache_struct_definition(id, definition);
                let payload = gcx.ensure_class_payload(class_ty).unwrap();
                assert_ne!(class_ty, payload);
                assert_eq!(payload.format(gcx), "Object$payload[T]");
                assert!(!gcx.is_class_type(payload));
                let TyKind::Adt(payload_def, arguments) = payload.kind() else {
                    panic!("payload ADT");
                };
                assert_eq!(
                    gcx.definition_kind(payload_def.id),
                    crate::hir::DefinitionKind::Struct
                );
                assert_eq!(gcx.definition_parent(payload_def.id), Some(id));
                assert_eq!(
                    gcx.get_struct_definition(payload_def.id).fields,
                    gcx.get_struct_definition(id).fields
                );
                assert_eq!(gcx.ensure_class_payload(class_ty), Some(payload));
                assert_eq!(
                    gcx.class_info(class_ty).unwrap().payload,
                    Some(payload_def.id)
                );
                assert_eq!(arguments.len(), 1);
                let TyKind::Adt(class_def, _) = class_ty.kind() else {
                    unreachable!()
                };
                let concrete = gcx.store.interners.intern_generic_args(vec![
                    crate::sema::models::GenericArgument::Type(gcx.types.int32),
                ]);
                let concrete_class = Ty::new(TyKind::Adt(class_def, concrete), gcx);
                assert_eq!(
                    gcx.ensure_class_payload(concrete_class),
                    Some(Ty::new(TyKind::Adt(payload_def, concrete), gcx))
                );
            },
        );
    }

    #[test]
    fn any_object_bounds_accept_handles_but_reject_values_and_handle_borrows() {
        let source = "interface AnyObject {}\nstruct Handle { owner: *const uint8 }\nfunc duplicate[T: AnyObject](_ value: T) -> (T, T) { (value, value) }\nfunc main() { var h: Handle = Handle { owner: unsafe { 0 as *const uint8 } }; pair := duplicate(h) }";
        let items = [
            (StdItem::AnyObject, "AnyObject"),
            (StdItem::ClassHandle, "Handle"),
        ];
        let diagnostics = crate::test_support::analyze_language_item_script(source, true, &items);
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
        for source in [
            "interface AnyObject {}\nstruct Value: AnyObject {}\nfunc main() {}",
            "interface AnyObject {}\nstruct Handle { owner: *const uint8 }\nfunc requireObject[T: AnyObject](_ value: T) {}\nfunc main() { var h: Handle = Handle { owner: unsafe { 0 as *const uint8 } }; requireObject(&h) }",
        ] {
            let selected = if source.contains("Handle") {
                &items[..]
            } else {
                &items[..1]
            };
            let diagnostics =
                crate::test_support::analyze_language_item_script(source, false, selected);
            assert!(
                diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.message.contains("AnyObject")),
                "{diagnostics:#?}"
            );
        }
    }
}

impl<'ctx> GlobalContext<'ctx> {
    /// Build an implementation's argument list without confusing inherited base
    /// parameters with the subclass's parameters or the method's own generics.
    pub fn class_method_arguments(
        self,
        owner: Ty<'ctx>,
        method: crate::hir::DefinitionID,
        method_arguments: crate::sema::models::GenericArguments<'ctx>,
    ) -> Option<crate::sema::models::GenericArguments<'ctx>> {
        if let Some(crate::sema::models::SyntheticDefinitionKind::InheritedClassInitializer {
            class,
            initializer,
        }) = self
            .store
            .synthetic_definitions
            .borrow()
            .get(&method)
            .map(|value| value.kind)
        {
            let TyKind::Adt(def, args) = owner.kind() else {
                return None;
            };
            if def.id != class {
                return None;
            }
            if self.generics_of(method).parent != Some(class) {
                let mut combined = args.to_vec();
                let source = self.class_method_arguments(
                    self.class_base(owner)?,
                    initializer,
                    method_arguments,
                )?;
                combined.extend_from_slice(source.as_slice());
                return Some(self.store.interners.intern_generic_args(combined));
            }
            let mut args = args.to_vec();
            args.extend_from_slice(method_arguments.as_slice());
            return Some(self.store.interners.intern_generic_args(args));
        }
        let parent = self.definition_parent(method)?;
        if self.try_definition_kind(parent) == Some(crate::hir::DefinitionKind::Struct)
            && self.is_class_type(self.get_type(parent))
        {
            let ancestor = self
                .class_ancestry(owner)
                .into_iter()
                .find(|ty| matches!(ty.kind(), TyKind::Adt(def, _) if def.id == parent))?;
            let TyKind::Adt(_, args) = ancestor.kind() else {
                unreachable!()
            };
            let mut arguments = args.to_vec();
            arguments.extend_from_slice(method_arguments.as_slice());
            return Some(self.store.interners.intern_generic_args(arguments));
        }
        let mut arguments = self
            .class_ancestry(owner)
            .into_iter()
            .find_map(|ancestor| {
                crate::sema::impl_engine::deduce_impl_subst(self, parent, ancestor, &[])
            })?
            .to_vec();
        arguments.extend_from_slice(method_arguments.as_slice());
        Some(self.store.interners.intern_generic_args(arguments))
    }

    /// Map a concrete inherited entry to its immediate base entry. Keeping
    /// this substitution explicit also supports reordered extension generics,
    /// nested base types, and generic/default argument forwarding.
    pub fn inherited_initializer_target(
        self,
        initializer: crate::hir::DefinitionID,
        arguments: crate::sema::models::GenericArguments<'ctx>,
    ) -> Option<(
        crate::hir::DefinitionID,
        crate::sema::models::GenericArguments<'ctx>,
    )> {
        let crate::sema::models::SyntheticDefinitionKind::InheritedClassInitializer {
            initializer: base,
            ..
        } = self
            .store
            .synthetic_definitions
            .borrow()
            .get(&initializer)?
            .kind
        else {
            return None;
        };
        let generics = self.generics_of(initializer);
        if let Some(parent) = generics.parent {
            let environment = self
                .store
                .synthetic_definitions
                .borrow()
                .get(&parent)
                .map(|value| value.kind);
            if matches!(
                environment,
                Some(crate::sema::models::SyntheticDefinitionKind::InitializerEnvironment { .. })
            ) {
                let nominal_count = self.generics_of(parent).parent_count;
                let source_arguments = arguments.get(nominal_count..)?;
                return Some((
                    base,
                    self.store
                        .interners
                        .intern_generic_args_slice(source_arguments),
                ));
            }
        }
        let class = crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args(
            self,
            self.initializer_target(initializer),
            arguments,
        );
        let base_class = self.class_base(class)?;
        let own = self.generics_of(initializer);
        let own_args = self
            .store
            .interners
            .intern_generic_args_slice(&arguments[own.parent_count..]);
        Some((
            base,
            self.class_method_arguments(base_class, base, own_args)?,
        ))
    }

    /// Refine only the direct owned Self result; nested/invariant occurrences
    /// are deliberately not rewritten. The method body proves its dynamic
    /// class promise before this compiler-only adaptation reaches codegen.
    pub fn class_self_result(
        self,
        receiver: Ty<'ctx>,
        method: crate::hir::DefinitionID,
    ) -> Option<Ty<'ctx>> {
        let class = match receiver.kind() {
            TyKind::Reference(class) => class,
            _ => receiver,
        };
        self.class_method(class, method)?
            .returns_self
            .then_some(class)
    }

    pub fn class_method(
        self,
        class: Ty<'ctx>,
        method: crate::hir::DefinitionID,
    ) -> Option<crate::sema::models::ClassMethod<'ctx>> {
        self.class_methods(class)
            .into_iter()
            .find(|slot| slot.family == method || slot.implementation == method)
    }

    /// Interface namespace of a virtual family in the receiver's coordinates.
    /// The first argument is Self, which deliberately does not participate in
    /// matching an inherited conformance's fixed interface instantiation.
    pub(crate) fn class_method_interface(
        self,
        class: Ty<'ctx>,
        method: crate::hir::DefinitionID,
    ) -> Option<crate::sema::models::InterfaceReference<'ctx>> {
        let parent = self.definition_parent(method);
        let mut records = self.collect_from_databases(|database| {
            database
                .conformance_records
                .values()
                .filter(|record| Some(record.extension) == parent)
                .copied()
                .collect::<Vec<_>>()
        });
        records.extend(self.collect_from_databases(|database| {
            database
                .class_adoptions
                .iter()
                .filter(|adoption| {
                    adoption.methods.iter().any(|entry| {
                        entry.slot.family == method || entry.slot.implementation == method
                    })
                })
                .filter_map(|adoption| {
                    database
                        .conformance_records
                        .get(&adoption.conformance)
                        .copied()
                })
                .collect::<Vec<_>>()
        }));
        records.into_iter().find_map(|record| {
            let substitution = self.class_ancestry(class).into_iter().find_map(|owner| {
                crate::sema::impl_engine::deduce_impl_subst(self, record.extension, owner, &[])
            })?;
            Some(
                crate::sema::tycheck::utils::instantiate::instantiate_interface_ref_with_args(
                    self,
                    record.interface,
                    substitution,
                ),
            )
        })
    }

    /// Effective families in this receiver's actual generic coordinates. Late
    /// conformances remain in their owning package; never mutate an imported
    /// ClassInfo or its already-published LinkOnceODR descriptor contents.
    pub(crate) fn class_methods(
        self,
        class: Ty<'ctx>,
    ) -> Vec<crate::sema::models::ClassMethod<'ctx>> {
        use crate::sema::tycheck::utils::{
            instantiate::instantiate_ty_with_args, type_head_from_value_ty,
        };
        let TyKind::Adt(_, arguments) = normalize_aliases(self, class).kind() else {
            return vec![];
        };
        let Some(info) = self.class_info(class) else {
            return vec![];
        };
        let mut methods: Vec<_> = info
            .methods
            .iter()
            .map(|slot| crate::sema::models::ClassMethod {
                owner: instantiate_ty_with_args(self, slot.owner, arguments),
                ..*slot
            })
            .collect();
        let adoptions: Vec<_> = self
            .store
            .type_databases
            .borrow()
            .values()
            .flat_map(|database| database.class_adoptions.iter().copied())
            .collect();
        let ancestry = self.class_ancestry(class);
        for adoption in adoptions {
            let Some(record) = self.conformance_record(adoption.conformance) else {
                continue;
            };
            let Some(owner) = ancestry
                .iter()
                .find(|owner| Some(record.target) == type_head_from_value_ty(**owner))
            else {
                continue;
            };
            let Some(substitution) =
                crate::sema::impl_engine::deduce_impl_subst(self, record.extension, *owner, &[])
            else {
                continue;
            };
            for method in adoption.methods {
                let candidate = crate::sema::models::ClassMethod {
                    owner: instantiate_ty_with_args(self, method.slot.owner, substitution),
                    ..method.slot
                };
                if let Some(slot) = methods
                    .iter_mut()
                    .find(|slot| slot.family == candidate.family)
                {
                    let depth = |owner| {
                        ancestry
                            .iter()
                            .position(|ancestor| *ancestor == owner)
                            .unwrap_or(usize::MAX)
                    };
                    if depth(candidate.owner) < depth(slot.owner) {
                        *slot = candidate;
                    }
                } else {
                    methods.push(candidate);
                }
            }
        }
        methods
    }

    pub(crate) fn class_family_is_registered(self, family: crate::hir::DefinitionID) -> bool {
        // New families belong to the conformance package. Consult that owner
        // even through a transitive dependency: rebuilding an imported class
        // descriptor must not depend on which packages happen to be in scope.
        self.with_type_database(family.package(), |database| {
            database
                .class_adoptions
                .iter()
                .flat_map(|adoption| adoption.methods.iter())
                .any(|method| method.slot.family == family && method.is_registered)
        })
    }
}

/// Class descriptors are published independently of an interface conformance.
/// Their targets must satisfy extension bounds as well as method-local bounds.
pub(crate) fn method_available<'ctx>(
    gcx: crate::compile::context::Gcx<'ctx>,
    method: crate::hir::DefinitionID,
    arguments: crate::sema::models::GenericArguments<'ctx>,
) -> bool {
    let generated = gcx
        .store
        .synthetic_definitions
        .borrow()
        .get(&method)
        .map(|definition| definition.kind);
    let capability = match generated {
        Some(crate::sema::models::SyntheticDefinitionKind::ClassEncoder { class }) => {
            Some((class, StdItem::Encodable))
        }
        Some(
            crate::sema::models::SyntheticDefinitionKind::ClassDecoder { class, .. }
            | crate::sema::models::SyntheticDefinitionKind::ClassDecodingInitializer { class },
        ) => Some((class, StdItem::Decodable)),
        _ => None,
    };
    if let Some((class, capability)) = capability
        && let Some(interface_id) = gcx.std_item_def(capability)
    {
        let class = crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args(
            gcx,
            gcx.get_type(class),
            arguments,
        );
        let goal = crate::sema::models::InterfaceGoal {
            self_ty: class,
            interface_id,
            interface_args: crate::sema::models::GenericArguments::empty(),
            bindings: &[],
            param_env: &[],
        };
        if gcx.prove_interface_goal(goal, crate::sema::models::SelectionMode::Codegen)
            != crate::sema::models::GoalResult::Proven
        {
            return false;
        }
    }
    use crate::sema::tycheck::{
        constraints::canonical_constraints_of, utils::instantiate::instantiate_constraint_with_args,
    };
    constraints_satisfied(
        gcx,
        canonical_constraints_of(gcx, method)
            .into_iter()
            .map(|constraint| instantiate_constraint_with_args(gcx, constraint.value, arguments)),
        &[],
    )
}

pub(super) fn constraints_satisfied<'ctx>(
    gcx: crate::compile::context::Gcx<'ctx>,
    constraints: impl IntoIterator<Item = crate::sema::models::Constraint<'ctx>>,
    assumptions: &[crate::sema::models::Constraint<'ctx>],
) -> bool {
    use crate::sema::{
        models::{Constraint, GoalResult, SelectionMode},
        tycheck::{
            infer::InferCtx,
            utils::{ParamEnv, normalize_ty},
        },
    };
    let env = ParamEnv::new(assumptions.to_vec());
    let icx = std::rc::Rc::new(InferCtx::new(gcx));
    let assumptions = gcx.store.arenas.global.alloc_slice_copy(assumptions);
    constraints.into_iter().all(|constraint| match constraint {
        Constraint::TypeEquality(left, right) => {
            normalize_ty(icx.clone(), left, &env) == normalize_ty(icx.clone(), right, &env)
        }
        Constraint::Bound { ty, interface } => {
            let ty = normalize_ty(icx.clone(), ty, &env);
            gcx.prove_interface_goal(
                interface.to_goal_with_self_ty(gcx, assumptions, ty),
                SelectionMode::Typecheck,
            ) == GoalResult::Proven
        }
    })
}

/// Run after conformance collection, so concrete local interface facts are
/// available. An override cannot silently narrow an inherited family's domain
/// by adding stronger conditions on its extension's class parameters.
pub(crate) fn validate_override_extensions<'ctx>(
    gcx: crate::compile::context::Gcx<'ctx>,
    class: Ty<'ctx>,
) {
    use crate::sema::tycheck::{
        constraints::canonical_constraints_of,
        utils::{generics::GenericsBuilder, instantiate::instantiate_constraint_with_args},
    };
    let TyKind::Adt(class_id, _) = class.kind() else {
        return;
    };
    let Some(base) = gcx.class_base(class) else {
        return;
    };
    let Some(info) = gcx.class_info(class) else {
        return;
    };
    let overrides = info
        .methods
        .iter()
        .filter(|method| method.owner == class && method.family != method.implementation)
        .map(|method| (method.family, method.implementation, false))
        .chain(
            info.initializers
                .iter()
                .filter(|entry| {
                    !entry.is_inherited
                        && entry.owner == class
                        && entry.family != entry.implementation
                })
                .map(|entry| (entry.family, entry.implementation, true)),
        );
    for (family, implementation, initializer) in overrides {
        let inherited = if initializer {
            gcx.class_initializer(base, family)
                .map(|entry| (entry.owner, entry.implementation))
        } else {
            gcx.class_method(base, family)
                .map(|entry| (entry.owner, entry.implementation))
        };
        let Some((inherited_owner, inherited_implementation)) = inherited else {
            continue;
        };
        let actual_parent = gcx.definition_parent(implementation).unwrap();
        let base_parent = gcx.definition_parent(inherited_implementation).unwrap();
        let identity = GenericsBuilder::identity_for_item(gcx, implementation);
        let own = gcx
            .store
            .interners
            .intern_generic_args_slice(&identity[gcx.generics_of(implementation).parent_count..]);
        let context_class = if gcx
            .class_method_arguments(class, implementation, own)
            .is_some()
        {
            class
        } else {
            gcx.get_impl_target_ty(actual_parent)
                .expect("override extension target")
        };
        let TyKind::Adt(_, context_arguments) = context_class.kind() else {
            unreachable!()
        };
        let inherited_owner = crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args(
            gcx,
            inherited_owner,
            context_arguments,
        );
        let Some(actual_args) = gcx.class_method_arguments(context_class, implementation, own)
        else {
            continue;
        };
        let Some(base_args) =
            gcx.class_method_arguments(inherited_owner, inherited_implementation, own)
        else {
            continue;
        };
        let assumptions: Vec<_> = canonical_constraints_of(gcx, class_id.id)
            .into_iter()
            .map(|constraint| {
                instantiate_constraint_with_args(gcx, constraint.value, context_arguments)
            })
            .chain(
                canonical_constraints_of(gcx, base_parent)
                    .into_iter()
                    .map(|constraint| {
                        instantiate_constraint_with_args(gcx, constraint.value, base_args)
                    }),
            )
            .collect();
        let required = canonical_constraints_of(gcx, actual_parent)
            .into_iter()
            .map(|constraint| instantiate_constraint_with_args(gcx, constraint.value, actual_args));
        if !constraints_satisfied(gcx, required, &assumptions) {
            gcx.dcx().emit_error(
                if initializer {
                    "override extension requires stronger conditions than the inherited initializer"
                } else {
                    "override extension requires stronger conditions than the inherited method"
                }
                .into(),
                Some(gcx.definition_ident(implementation).span),
            );
        }
    }
}
