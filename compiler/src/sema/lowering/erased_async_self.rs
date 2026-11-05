//! An async Self result must be erased after polling, never at cold construction.
//! Synthesize the ordinary generic async wrapper a programmer could write:
//! await the concrete method, then box that ready T into the caller's any P.
use crate::{
    compile::context::Gcx,
    hir::DefinitionID,
    sema::{
        models::*,
        tycheck::{
            constraints::canonical_constraints_of,
            utils::{
                generics::{GenericsBuilder, generic_parameter_marker},
                instantiate::instantiate_signature_with_args,
            },
        },
    },
    span::Spanned,
};

impl<'ctx> Gcx<'ctx> {
    pub(crate) fn erased_async_self_adapter(
        self,
        context: DefinitionID,
        method: DefinitionID,
        source_args: GenericArguments<'ctx>,
        erased: Ty<'ctx>,
    ) -> DefinitionID {
        let parent_count = GenericsBuilder::identity_for_item(self, context).len();
        let parameter = GenericParameterDefinition {
            id: self.allocate_synthetic_id(self.package_index()),
            name: self.intern_symbol("OpenedSelf"),
            index: parent_count,
            kind: GenericParameterDefinitionKind::Type { default: None },
        };
        let target = Ty::new(
            TyKind::Parameter(generic_parameter_marker(&parameter)),
            self,
        );
        let mut arguments = source_args.to_vec();
        // Interface arguments may contain relative Self (including beneath
        // another existential binder). Reconstruct those coordinates from the
        // raw receiver interface instead of substituting only argument zero:
        // Duplicate[Self] must become Duplicate[OpenedSelf], not
        // Duplicate[any Duplicate]. Method-owned generics are rejected by the
        // ordinary existential method checker before this lowering pass.
        let original_self = source_args[0].ty().expect("interface Self is a type");
        let TyKind::BoxedExistential { interfaces } = original_self.kind() else {
            panic!("async Self adapter requires an erased receiver");
        };
        let owner = self
            .definition_parent(method)
            .expect("interface method owner");
        let raw = interfaces
            .iter()
            .flat_map(|root| {
                crate::sema::impl_engine::ref_ops::collect_interface_with_superfaces(self, *root)
            })
            .find(|interface| {
                // Source method resolution installs the public receiver in
                // coordinate zero and preserves relative binders elsewhere.
                interface.id == owner
                    && source_args.get(1..interface.arguments.len())
                        == Some(&interface.arguments[1..])
            })
            .expect("checked async requirement belongs to its receiver interface");
        let concrete = super::super::tycheck::utils::erased_self::bind(self, raw, target);
        arguments[..concrete.arguments.len()].copy_from_slice(&concrete.arguments);
        let arguments = self.store.interners.intern_generic_args(arguments);
        let kind = SyntheticDefinitionKind::ErasedAsyncSelf { context, method };
        let existing =
            self.store
                .synthetic_definitions
                .borrow()
                .iter()
                .find_map(|(id, definition)| {
                    (definition.kind == kind
                        && definition.signature.output == erased
                        && self.with_type_database(id.package(), |db| {
                            db.erased_async_self_arguments.get(id).copied()
                        }) == Some(arguments))
                    .then_some(*id)
                });
        if let Some(id) = existing {
            return id;
        }
        let id = self.allocate_synthetic_id(self.package_index());
        let generics = self.store.arenas.generics.alloc(Generics {
            parent: Some(context),
            parent_count,
            parameters: vec![parameter],
            has_self: false,
        });
        let mut signature =
            instantiate_signature_with_args(self, self.get_signature(method), arguments);
        signature.output = erased;
        signature.inputs[0].name = self.intern_symbol("source");
        // Provider adapters translate helper coordinates back to declaration
        // coordinates. The outer call will use ordinary concrete opening for
        // their evaluation over its already prepared receiver.
        let defaults: Vec<_> = signature
            .inputs
            .iter()
            .enumerate()
            .filter_map(|(index, input)| input.default_provider.map(|provider| (index, provider)))
            .collect();
        let span = self.definition_ident(method).span;
        for (index, provider) in defaults {
            let default_id = self.allocate_synthetic_id(self.package_index());
            let output =
                instantiate_signature_with_args(self, self.get_signature(provider), arguments)
                    .output;
            let default_signature =
                self.store
                    .arenas
                    .function_signatures
                    .alloc(LabeledFunctionSignature {
                        inputs: vec![],
                        output,
                        is_variadic: false,
                        abi: None,
                    });
            self.register_synthetic_definition(
                default_id,
                SyntheticDefinition {
                    kind: SyntheticDefinitionKind::ErasedAsyncSelfDefault {
                        adapter: id,
                        provider,
                    },
                    name: self.intern_symbol("__asyncSelfDefault"),
                    generics,
                    signature: default_signature,
                    span,
                },
            );
            self.cache_signature(default_id, default_signature.clone());
            self.cache_type(
                default_id,
                Ty::from_labeled_signature(self, default_signature),
            );
            signature.inputs[index].default_provider = Some(default_id);
        }
        let signature = self.store.arenas.function_signatures.alloc(signature);
        self.register_synthetic_definition(
            id,
            SyntheticDefinition {
                kind,
                name: self.intern_symbol("__asyncSelfResult"),
                generics,
                signature,
                span,
            },
        );
        self.cache_signature(id, signature.clone());
        self.cache_type(id, Ty::from_labeled_signature(self, signature));
        self.cache_async_body_output(id, erased);
        self.with_session_type_database(|db| {
            db.erased_async_self_arguments.insert(id, arguments);
        });
        let mut constraints = canonical_constraints_of(self, context);
        if let TyKind::BoxedExistential { interfaces } = erased.kind() {
            for interface in interfaces {
                constraints.push(Spanned::new(
                    Constraint::Bound {
                        ty: target,
                        interface: super::super::tycheck::utils::erased_self::bind(
                            self, *interface, target,
                        ),
                    },
                    span,
                ));
            }
        } else {
            panic!("async Self adapter requires an erased result");
        }
        self.update_constraints(id, constraints.clone());
        for input in &signature.inputs {
            if let Some(provider) = input.default_provider {
                self.update_constraints(provider, constraints.clone());
            }
        }
        id
    }
}

/// Reborrow a receiver without copying its unique controller.
pub(crate) fn receiver_type(ty: Ty<'_>) -> Ty<'_> {
    match ty.kind() {
        TyKind::Reference(inner) => inner,
        _ => ty,
    }
}
