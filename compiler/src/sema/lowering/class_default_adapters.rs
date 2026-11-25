//! Keep adopted methods in their conformance's environment. In particular,
//! interface Self and method-own parameters need not have the same indices as
//! the class extension's parameters. Exact source bodies keep their old indices.
use crate::{
    compile::context::Gcx,
    hir::DefinitionID,
    sema::{
        models::*,
        tycheck::{
            constraints::canonical_constraints_of,
            utils::{
                generics::{GenericsBuilder, generic_parameter_marker},
                instantiate::{
                    instantiate_const_with_args, instantiate_constraint_with_args,
                    instantiate_signature_with_args, instantiate_ty_with_args,
                },
            },
        },
    },
    span::Spanned,
};

impl<'ctx> Gcx<'ctx> {
    /// Source arguments expressed in this adapter's coordinates. This mapping
    /// is also used for argument-default providers, constraints and async output.
    pub(crate) fn adapter_source_arguments(
        self,
        method: DefinitionID,
        arguments: GenericArguments<'ctx>,
    ) -> Option<(DefinitionID, GenericArguments<'ctx>)> {
        let (conformance, source) =
            match self.store.synthetic_definitions.borrow().get(&method)?.kind {
                SyntheticDefinitionKind::AdoptedClassDefault {
                    conformance,
                    source,
                }
                | SyntheticDefinitionKind::DelegatedMethod {
                    conformance,
                    source,
                    ..
                } => (conformance, source),
                _ => return None,
            };
        let record = self.conformance_record(conformance)?;
        let mut source_arguments = record
            .interface
            .arguments
            .iter()
            .map(|argument| match *argument {
                GenericArgument::Type(ty) => {
                    GenericArgument::Type(instantiate_ty_with_args(self, ty, arguments))
                }
                GenericArgument::Const(value) => {
                    GenericArgument::Const(instantiate_const_with_args(self, value, arguments))
                }
            })
            .collect::<Vec<_>>();
        source_arguments.extend_from_slice(arguments.get(self.generics_of(method).parent_count..)?);
        Some((
            source,
            self.store.interners.intern_generic_args(source_arguments),
        ))
    }

    pub(crate) fn adopted_class_default(
        self,
        conformance: ConformanceRecordId,
        source: DefinitionID,
    ) -> Option<DefinitionID> {
        self.conformance_adapter(conformance, source, None)
    }

    pub(crate) fn conformance_adapter(
        self,
        conformance: ConformanceRecordId,
        source: DefinitionID,
        delegate: Option<(u32, bool)>,
    ) -> Option<DefinitionID> {
        let kind = match delegate {
            Some((field, borrow_field)) => SyntheticDefinitionKind::DelegatedMethod {
                conformance,
                source,
                field,
                borrow_field,
            },
            None => SyntheticDefinitionKind::AdoptedClassDefault {
                conformance,
                source,
            },
        };
        if let Some(id) = self
            .store
            .synthetic_definitions
            .borrow()
            .iter()
            .find_map(|(id, definition)| (definition.kind == kind).then_some(*id))
        {
            return Some(id);
        }
        let record = self.conformance_record(conformance)?;
        if delegate.is_none() {
            self.class_default_body(source)?;
        }
        let id = self.allocate_synthetic_id(self.package_index());
        let old = self.generics_of(source);
        let parent_identity = GenericsBuilder::identity_for_item(self, record.extension);
        let parent_count = parent_identity.len();
        let mut parameters = old.parameters.clone();
        for (index, parameter) in parameters.iter_mut().enumerate() {
            parameter.id = self.allocate_synthetic_id(self.package_index());
            parameter.index = parent_count + index;
        }
        let generics = self.store.arenas.generics.alloc(Generics {
            parent: Some(record.extension),
            parent_count,
            parameters,
            has_self: false,
        });
        let mut source_arguments = record.interface.arguments.to_vec();
        for (new, prior) in generics.parameters.iter().zip(&old.parameters) {
            let marker = generic_parameter_marker(new);
            let source_prefix = self
                .store
                .interners
                .intern_generic_args_slice(&source_arguments);
            let value = match new.kind {
                GenericParameterDefinitionKind::Type { .. } => {
                    GenericArgument::Type(Ty::new(TyKind::Parameter(marker), self))
                }
                GenericParameterDefinitionKind::Const { .. } => {
                    let ty = instantiate_ty_with_args(
                        self,
                        self.try_generic_const_param_ty(prior.id)?,
                        source_prefix,
                    );
                    self.cache_generic_const_param_ty(new.id, ty);
                    GenericArgument::Const(Const {
                        ty,
                        kind: ConstKind::Param(marker),
                    })
                }
            };
            source_arguments.push(value);
        }
        let source_arguments = self.store.interners.intern_generic_args(source_arguments);
        for (new, prior) in generics.parameters.iter().zip(&old.parameters) {
            if let Some(default) = self.try_generic_type_default(prior.id) {
                self.cache_generic_type_default(
                    new.id,
                    instantiate_ty_with_args(self, default, source_arguments),
                );
            }
            if let Some(default) = self.try_generic_const_default(prior.id) {
                self.cache_generic_const_default(
                    new.id,
                    instantiate_const_with_args(self, default, source_arguments),
                );
            }
        }
        let mut signature =
            instantiate_signature_with_args(self, self.get_signature(source), source_arguments);
        let span = record.location;
        for input in &mut signature.inputs {
            if let Some(provider) = input.default_provider {
                let default = self.allocate_synthetic_id(self.package_index());
                let default_signature =
                    self.store
                        .arenas
                        .function_signatures
                        .alloc(LabeledFunctionSignature {
                            inputs: self.get_signature(provider).inputs.clone(),
                            output: input.ty,
                            is_variadic: false,
                            abi: None,
                        });
                self.register_synthetic_definition(
                    default,
                    SyntheticDefinition {
                        kind: SyntheticDefinitionKind::AdoptedClassDefaultArgument {
                            method: id,
                            provider,
                        },
                        name: self.intern_symbol("$adopted_default_argument"),
                        generics,
                        signature: default_signature,
                        span,
                    },
                );
                self.cache_signature(default, default_signature.clone());
                self.cache_type(default, Ty::from_labeled_signature(self, default_signature));
                input.default_provider = Some(default);
            }
        }
        let signature = self.store.arenas.function_signatures.alloc(signature);
        self.register_synthetic_definition(
            id,
            SyntheticDefinition {
                kind,
                name: self.definition_ident(source).symbol,
                generics,
                signature,
                span,
            },
        );
        self.cache_signature(id, signature.clone());
        self.cache_type(id, Ty::from_labeled_signature(self, signature));
        let parent_constraints: rustc_hash::FxHashSet<_> =
            canonical_constraints_of(self, record.extension)
                .into_iter()
                .map(|constraint| constraint.value)
                .collect();
        // Interface-level requirements are established by the conformance.
        // Only method-own bounds participate in override compatibility.
        self.update_constraints(
            id,
            self.constraints_of(source)
                .into_iter()
                .map(|constraint| {
                    Spanned::new(
                        instantiate_constraint_with_args(self, constraint.value, source_arguments),
                        constraint.span,
                    )
                })
                .filter(|constraint| !parent_constraints.contains(&constraint.value))
                .collect(),
        );
        if self.definition_is_async(source) {
            self.cache_async_body_output(
                id,
                instantiate_ty_with_args(self, self.function_body_output(source), source_arguments),
            );
        }
        if self.definition_is_unsafe(source) {
            self.with_session_type_database(|database| {
                database.def_to_unsafe.insert(id);
            });
        }
        Some(id)
    }
}
