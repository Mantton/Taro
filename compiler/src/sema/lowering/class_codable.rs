//! A class's Decodable witness constructs through its decoding initializer.
//! Required initializer families, not covariance of Result[Self, E], select
//! the actual subclass. No partially initialized public object is exposed.
use crate::{
    compile::context::Gcx,
    error::CompileResult,
    hir::{DefinitionID, StdItem},
    sema::{
        models::*,
        tycheck::{
            derive::SyntheticMethodInfo,
            utils::{
                generics::GenericsBuilder, instantiate::instantiate_signature_with_args,
                normalize_aliases,
            },
        },
    },
};

pub fn prepare(gcx: Gcx<'_>) -> CompileResult<()> {
    let Some(interface) = gcx.std_item_def(StdItem::Decodable) else {
        return Ok(());
    };
    let Some(requirements) = gcx.get_interface_requirements(interface) else {
        return Ok(());
    };
    let Some(method) = requirements
        .methods
        .iter()
        .find(|method| gcx.symbol_eq(method.name, "decode"))
    else {
        return Ok(());
    };
    let mut records = gcx.all_conformance_records(gcx.package_index());
    records.sort_by_key(|record| {
        record
            .interface
            .self_ty()
            .map_or(0, |ty| gcx.class_ancestry(ty).len())
    });
    for record in records {
        let Some(class) = record
            .interface
            .self_ty()
            .filter(|ty| gcx.is_class_type(*ty))
        else {
            continue;
        };
        if record.interface.id != interface || !record.is_inline {
            continue;
        }
        let has_decoder_shape = gcx.class_info(class).unwrap().initializers.iter().any(|entry| {
            let generics = gcx.generics_of(entry.definition);
            let signature = gcx.get_signature(entry.definition);
            generics.parameters.len() == 1 && signature.inputs.len() == 1
                && signature.inputs[0].label.is_some_and(|label| gcx.symbol_eq(label, "from"))
                && matches!(normalize_aliases(gcx, signature.inputs[0].ty).kind(), TyKind::Parameter(parameter) if parameter.index == generics.parent_count)
        });
        if has_decoder_shape && manual_initializer(gcx, class, method.id).is_none() {
            gcx.dcx().emit_error("decoding init(from:) must return Result[Self, D::Error] and accept every Decoder without extra constraints".into(), Some(record.location));
            continue;
        }
        // An existing superclass conformance is inherited, never synthesized
        // afresh to include the subclass's additional stored fields.
        if gcx.class_base(class).is_some_and(|base| {
            gcx.prove_interface_goal(
                InterfaceGoal {
                    interface_id: interface,
                    self_ty: base,
                    interface_args: GenericArguments::empty(),
                    bindings: &[],
                    param_env: &[],
                },
                SelectionMode::Typecheck,
            ) == GoalResult::Proven
        }) {
            continue;
        }
        crate::sema::tycheck::derive::try_synthesize_method(
            gcx,
            record.target,
            class,
            interface,
            record.interface.arguments,
            method.name,
            method.id,
            GenericsBuilder::identity_for_item(gcx, method.id),
        );
    }
    gcx.dcx().ok()
}

/// Match a user-written initializer in the codec's renamed method environment.
/// This compares its error projection as well as the decoder input, so a
/// similarly named initializer cannot silently satisfy a different contract.
pub fn matching_initializer<'ctx>(
    gcx: Gcx<'ctx>,
    class: Ty<'ctx>,
    expected: &LabeledFunctionSignature<'ctx>,
    own: GenericArguments<'ctx>,
) -> Option<DefinitionID> {
    let matches = |id, signature: &LabeledFunctionSignature<'ctx>| {
        if gcx.generics_of(id).parameters.len() != own.len() {
            return false;
        }
        let Some(args) = gcx.class_method_arguments(class, id, own) else {
            return false;
        };
        let actual = instantiate_signature_with_args(gcx, signature, args);
        actual.inputs.len() == expected.inputs.len()
            && actual.inputs.iter().zip(&expected.inputs).all(|(a, b)| {
                a.label == b.label && normalize_aliases(gcx, a.ty) == normalize_aliases(gcx, b.ty)
            })
            && normalize_aliases(gcx, actual.output) == normalize_aliases(gcx, expected.output)
    };
    gcx.class_info(class)?
        .initializers
        .iter()
        .map(|entry| entry.definition)
        .find(|id| matches(*id, gcx.get_signature(*id)))
        .or_else(|| {
            if gcx.store.collecting_constant_headers.get()
                && let TyKind::Adt(adt, _) = class.kind()
            {
                return crate::sema::tycheck::find_decoder_header(gcx, adt.id, matches);
            }
            None
        })
}

/// A handwritten decoding initializer replaces structural synthesis, including
/// its stored-field capability requirements. Its generic decoder contract must
/// be exactly as general as Decodable's requirement.
pub fn manual_initializer<'ctx>(
    gcx: Gcx<'ctx>,
    class: Ty<'ctx>,
    requirement: DefinitionID,
) -> Option<DefinitionID> {
    let TyKind::Adt(_, class_args) = class.kind() else {
        return None;
    };
    let parameter = gcx.generics_of(requirement).parameters.first()?.clone();
    let decoder = Ty::new(
        TyKind::Parameter(GenericParameter {
            index: class_args.len(),
            name: parameter.name,
        }),
        gcx,
    );
    let own = gcx
        .store
        .interners
        .intern_generic_args(vec![GenericArgument::Type(decoder)]);
    let interface_args = gcx.store.interners.intern_generic_args(vec![
        GenericArgument::Type(class),
        GenericArgument::Type(decoder),
    ]);
    let expected =
        instantiate_signature_with_args(gcx, gcx.get_signature(requirement), interface_args);
    let initializer = matching_initializer(gcx, class, &expected, own)?;
    if gcx
        .store
        .synthetic_definitions
        .borrow()
        .contains_key(&initializer)
    {
        return None;
    }
    let arguments = gcx.class_method_arguments(class, initializer, own)?;
    let permitted: rustc_hash::FxHashSet<_> = gcx
        .constraints_of(requirement)
        .into_iter()
        .map(|bound| {
            normalize_aliases(
                gcx,
                crate::sema::tycheck::utils::instantiate::instantiate_constraint_with_args(
                    gcx,
                    bound.value,
                    interface_args,
                ),
            )
        })
        .collect();
    gcx.constraints_of(initializer)
        .into_iter()
        .all(|bound| {
            permitted.contains(&normalize_aliases(
                gcx,
                crate::sema::tycheck::utils::instantiate::instantiate_constraint_with_args(
                    gcx,
                    bound.value,
                    arguments,
                ),
            ))
        })
        .then_some(initializer)
}

pub fn register<'ctx>(gcx: Gcx<'ctx>, info: SyntheticMethodInfo<'ctx>, factory: DefinitionID) {
    if matches!(
        gcx.store
            .synthetic_definitions
            .borrow()
            .get(&factory)
            .map(|value| value.kind),
        Some(SyntheticDefinitionKind::ClassDecoder { .. })
    ) {
        return;
    }
    let TyKind::Adt(class, _) = info.self_ty.kind() else {
        unreachable!()
    };
    let signature = gcx.get_signature(factory);
    let generics = gcx.generics_of(factory);
    let initializer = manual_initializer(gcx, info.self_ty, info.method_id).unwrap_or_else(|| {
        let id = gcx.allocate_synthetic_id(gcx.package_index());
        gcx.register_synthetic_definition(
            id,
            SyntheticDefinition {
                kind: SyntheticDefinitionKind::ClassDecodingInitializer { class: class.id },
                name: gcx.intern_symbol("init"),
                generics,
                signature,
                span: gcx.definition_ident(class.id).span,
            },
        );
        gcx.cache_type(id, Ty::from_labeled_signature(gcx, signature));
        gcx.cache_signature(id, signature.clone());
        gcx.update_constraints(id, gcx.constraints_of(factory));
        let mut definition = gcx.get_struct_definition(class.id).clone();
        let class_info = definition.class_info.as_mut().unwrap();
        let mut entries = class_info.initializers.to_vec();
        entries.push(ClassInitializer {
            definition: id,
            implementation: id,
            family: id,
            owner: info.self_ty,
            is_required: !class_info.is_final,
            is_convenience: false,
            is_inherited: false,
            delegations: &[],
        });
        class_info.initializers = gcx.store.arenas.global.alloc_slice_copy(&entries);
        definition.has_initializer = true;
        gcx.cache_struct_definition(class.id, definition);
        gcx.class_payload_initializer(id);
        id
    });
    if let Some(entry) = gcx.class_initializer(info.self_ty, initializer)
        && !gcx.class_info(info.self_ty).unwrap().is_final
        && !entry.is_required
    {
        gcx.dcx().emit_error(
            "an inheritable Decodable class needs a required init(from:)".into(),
            Some(gcx.definition_ident(initializer).span),
        );
    }
    if !gcx
        .definition_visibility(initializer)
        .supports_required_initializer(gcx.definition_visibility(class.id))
    {
        gcx.dcx().emit_error(
            "decoding init(from:) must be at least as visible as its class".into(),
            Some(gcx.definition_ident(initializer).span),
        );
    }
    gcx.store
        .synthetic_definitions
        .borrow_mut()
        .get_mut(&factory)
        .unwrap()
        .kind = SyntheticDefinitionKind::ClassDecoder {
        class: class.id,
        initializer,
    };
}

/// Swift permits synthesis over a non-Decodable superclass only when it has
/// an accessible designated, non-fallible init(). Taro keeps its existing
/// explicit class-initializer surface; no implicit default init is introduced.
pub fn base_initializer<'ctx>(
    gcx: Gcx<'ctx>,
    class: Ty<'ctx>,
) -> Option<(DefinitionID, GenericArguments<'ctx>)> {
    let base = gcx.class_base(class)?;
    let TyKind::Adt(owner, class_args) = class.kind() else {
        return None;
    };
    let entries = gcx.class_info(base)?.initializers;
    let mut candidates = entries.iter().filter_map(|entry| {
        let signature = gcx.get_signature(entry.definition);
        if entry.is_convenience
            || !signature.inputs.is_empty()
            || !gcx.generics_of(entry.definition).parameters.is_empty()
            || gcx.result_parts(signature.output).is_some()
            || !gcx.is_definition_visible(entry.definition, owner.id)
        {
            return None;
        }
        let args = gcx.class_method_arguments(base, entry.definition, GenericArguments::empty())?;
        let assumptions: Vec<_> =
            crate::sema::tycheck::constraints::canonical_constraints_of(gcx, owner.id)
                .into_iter()
                .map(|bound| {
                    crate::sema::tycheck::utils::instantiate::instantiate_constraint_with_args(
                        gcx,
                        bound.value,
                        class_args,
                    )
                })
                .collect();
        let obligations =
            crate::sema::tycheck::constraints::canonical_constraints_of(gcx, entry.definition)
                .into_iter()
                .map(|bound| {
                    crate::sema::tycheck::utils::instantiate::instantiate_constraint_with_args(
                        gcx,
                        bound.value,
                        args,
                    )
                });
        super::classes::constraints_satisfied(gcx, obligations, &assumptions)
            .then_some((entry.definition, args))
    });
    let first = candidates.next()?;
    candidates.next().is_none().then_some(first)
}

pub fn validate(gcx: Gcx<'_>) -> CompileResult<()> {
    let classes: Vec<_> = gcx
        .store
        .synthetic_definitions
        .borrow()
        .iter()
        .filter_map(|(id, value)| {
            if id.package() != gcx.package_index() {
                return None;
            }
            match value.kind {
                SyntheticDefinitionKind::ClassDecodingInitializer { class } => Some(class),
                _ => None,
            }
        })
        .collect();
    for id in classes {
        let class = gcx.get_type(id);
        if gcx.class_base(class).is_some() && base_initializer(gcx, class).is_none() {
            gcx.dcx().emit_error("derived class decoding requires an accessible designated non-fallible superclass init(); write init(from:) explicitly".into(), Some(gcx.definition_ident(id).span));
        }
    }
    gcx.dcx().ok()
}

impl<'ctx> Gcx<'ctx> {
    pub fn is_decoding_initializer(self, initializer: DefinitionID) -> bool {
        let Some(entry) = self.class_initializer(self.initializer_target(initializer), initializer)
        else {
            return false;
        };
        let decoders: Vec<_> = self
            .store
            .synthetic_definitions
            .borrow()
            .values()
            .filter_map(|value| match value.kind {
                SyntheticDefinitionKind::ClassDecoder { initializer, .. } => Some(initializer),
                _ => None,
            })
            .collect();
        decoders.into_iter().any(|initializer| {
            self.class_initializer(self.initializer_target(initializer), initializer)
                .is_some_and(|decoder| decoder.family == entry.family)
        })
    }
}
