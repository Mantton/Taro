//! Compiler-provided operations on owning existential containers. These are
//! methods of the container, not additional conformances of its hidden value.
use crate::{
    compile::context::Gcx,
    hir::{DefinitionID, StdItem},
    sema::{
        models::*,
        tycheck::utils::{
            generics::{GenericsBuilder, generic_parameter_marker},
            instantiate::instantiate_ty_with_args,
        },
    },
    span::Symbol,
};

impl<'ctx> Gcx<'ctx> {
    pub(crate) fn erased_access_context(self, id: DefinitionID) -> Option<DefinitionID> {
        match self.store.synthetic_definitions.borrow().get(&id)?.kind {
            SyntheticDefinitionKind::ErasedTakeAs { context }
            | SyntheticDefinitionKind::ErasedAsRef { context, .. }
            | SyntheticDefinitionKind::ErasedPayloadReference { context, .. } => Some(context),
            _ => None,
        }
    }

    pub(crate) fn erased_take_as(
        self,
        context: DefinitionID,
        erased: Ty<'ctx>,
        name: Symbol,
    ) -> Option<DefinitionID> {
        let borrowed = match name.as_str() {
            "takeAs" => false,
            "asRef" => true,
            _ => return None,
        };
        // These operations have ordinary targets: takeAs on the container
        // value, asRef on its storage. Receiver lookup supplies auto-reference.
        let erased = match (borrowed, erased.kind()) {
            (false, TyKind::BoxedExistential { .. }) => erased,
            (true, TyKind::Reference(inner))
                if matches!(inner.kind(), TyKind::BoxedExistential { .. }) =>
            {
                inner
            }
            _ => return None,
        };
        let TyKind::BoxedExistential { interfaces } = erased.kind() else {
            unreachable!()
        };
        // A declared requirement wins over the convenience container operation.
        if interfaces.iter().any(|interface| {
            self.get_interface_requirements(interface.id)
                .is_some_and(|requirements| {
                    requirements
                        .methods
                        .iter()
                        .any(|method| method.name == name)
                })
        }) {
            return None;
        }
        let result = self.std_item_def(if borrowed {
            StdItem::Optional
        } else {
            StdItem::Result
        })?;
        let kind = if borrowed {
            SyntheticDefinitionKind::ErasedAsRef { context }
        } else {
            SyntheticDefinitionKind::ErasedTakeAs { context }
        };
        let receiver = if borrowed {
            Ty::new(TyKind::Reference(erased), self)
        } else {
            erased
        };
        if let Some(id) =
            self.store
                .synthetic_definitions
                .borrow()
                .iter()
                .find_map(|(id, definition)| {
                    (definition.kind == kind
                        && definition
                            .signature
                            .inputs
                            .first()
                            .is_some_and(|input| input.ty == receiver))
                    .then_some(*id)
                })
        {
            return Some(id);
        }
        let id = self.allocate_synthetic_id(self.package_index());
        let parent_count = GenericsBuilder::identity_for_item(self, context).len();
        let parameter = GenericParameterDefinition {
            is_anonymous: false,
            id: self.allocate_synthetic_id(self.package_index()),
            name: self.intern_symbol("T"),
            index: parent_count,
            kind: GenericParameterDefinitionKind::Type { default: None },
        };
        let target = Ty::new(
            TyKind::Parameter(generic_parameter_marker(&parameter)),
            self,
        );
        let generics = self.store.arenas.generics.alloc(Generics {
            parent: Some(context),
            parent_count,
            parameters: vec![parameter],
            has_self: false,
        });
        let result_arguments = if borrowed {
            vec![GenericArgument::Type(Ty::new(
                TyKind::Reference(target),
                self,
            ))]
        } else {
            vec![GenericArgument::Type(target), GenericArgument::Type(erased)]
        };
        let arguments = self.store.interners.intern_generic_args(result_arguments);
        let signature = self
            .store
            .arenas
            .function_signatures
            .alloc(LabeledFunctionSignature {
                inputs: vec![LabeledFunctionParameter {
                    label: None,
                    name: self.intern_symbol("self"),
                    ty: receiver,
                    is_lazy: false,
                    default_provider: None,
                }],
                output: instantiate_ty_with_args(self, self.get_type(result), arguments),
                is_variadic: false,
                abi: None,
            });
        self.register_synthetic_definition(
            id,
            SyntheticDefinition {
                kind,
                name,
                generics,
                signature,
                span: self.definition_ident(context).span,
            },
        );
        self.cache_signature(id, signature.clone());
        self.cache_type(id, Ty::from_labeled_signature(self, signature));
        self.update_constraints(id, Vec::new());
        Some(id)
    }
    /// Private exact-payload projection. It has a direct borrowed result so the
    /// ordinary wrapper can construct Optional from the checked payload address.
    pub(crate) fn erased_payload_reference(self, wrapper: DefinitionID) -> DefinitionID {
        let context = self
            .erased_access_context(wrapper)
            .expect("erased wrapper context");
        let signature = self.get_signature(wrapper);
        let TyKind::Reference(_) = signature.inputs[0].ty.kind() else {
            unreachable!()
        };
        let kind = SyntheticDefinitionKind::ErasedPayloadReference { context };
        let TyKind::Adt(_, args) = signature.output.kind() else {
            unreachable!()
        };
        let output = args[0].ty().expect("optional reference");
        if let Some(id) =
            self.store
                .synthetic_definitions
                .borrow()
                .iter()
                .find_map(|(id, definition)| {
                    (definition.kind == kind
                        && definition.signature.inputs[0].ty == signature.inputs[0].ty
                        && definition.signature.output == output)
                        .then_some(*id)
                })
        {
            return id;
        }
        let id = self.allocate_synthetic_id(self.package_index());
        let signature = self
            .store
            .arenas
            .function_signatures
            .alloc(LabeledFunctionSignature {
                inputs: signature.inputs.clone(),
                output,
                abi: None,
                is_variadic: false,
            });
        self.register_synthetic_definition(
            id,
            SyntheticDefinition {
                kind,
                name: self.intern_symbol("$erased_payload_reference"),
                generics: self.generics_of(wrapper),
                signature,
                span: self.definition_ident(wrapper).span,
            },
        );
        self.cache_signature(id, signature.clone());
        self.cache_type(id, Ty::from_labeled_signature(self, signature));
        self.update_constraints(id, self.constraints_of(wrapper));
        id
    }
}

/// Only the compiler-provided projection family earns a dependency proof. Neither
/// a familiar source name nor a reference-shaped arbitrary function is enough.
pub(crate) fn projection_signature(gcx: Gcx<'_>, id: DefinitionID) -> Option<()> {
    let definition = gcx.store.synthetic_definitions.borrow().get(&id)?.clone();
    let SyntheticDefinitionKind::ErasedPayloadReference { context } = definition.kind else {
        return None;
    };
    let signature = definition.signature;
    let [input] = signature.inputs.as_slice() else {
        return None;
    };
    let TyKind::Reference(source) = input.ty.kind() else {
        return None;
    };
    let TyKind::Reference(target) = signature.output.kind() else {
        return None;
    };
    let valid_target = matches!(target.kind(), TyKind::Parameter(parameter) if parameter.index == definition.generics.parent_count);
    (matches!(source.kind(), TyKind::BoxedExistential { .. })
        && valid_target
        && definition.generics.parent == Some(context)
        && signature.abi.is_none()
        && !signature.is_variadic)
        .then_some(())
}
