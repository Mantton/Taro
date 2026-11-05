//! Validate imported class layouts, defaults, statics and erased-value adapters
//! before publishing the package. These shapes are part of GC code generation.
use super::wire::TypeDatabaseWire;
use crate::{
    compile::context::{Gcx, TypeDatabase},
    sema::{
        models::TyKind,
        resolve::models::{DefinitionKind, ResolutionOutput},
    },
};
use rustc_hash::FxHashSet;

pub(super) fn validate_wire_entries(wire: &TypeDatabaseWire) -> Result<(), String> {
    let mut defaults = FxHashSet::default();
    for (id, _) in &wire.def_to_class_default_contract {
        if !defaults.insert((id.package, id.index)) {
            return Err("metadata contains duplicate class default contracts".into());
        }
    }
    let mut async_self_arguments = FxHashSet::default();
    for (id, _) in &wire.erased_async_self_arguments {
        if !async_self_arguments.insert((id.package, id.index)) {
            return Err("metadata repeats async Self arguments".into());
        }
    }
    let mut adoptions = FxHashSet::default();
    for (id, methods) in &wire.class_adoptions {
        if !adoptions.insert((id.package, id.index)) {
            return Err("metadata repeats a class adoption".into());
        }
        let mut requirements = FxHashSet::default();
        for method in methods {
            if !requirements.insert((method.requirement.package, method.requirement.index)) {
                return Err("class adoption repeats an interface requirement".into());
            }
        }
    }
    Ok(())
}

/// Opening facts are discovery hints, never substitute for a checked Native
/// body. Validate declaration existence, argument coordinates and concrete
/// storage before publishing them; codegen rechecks eligibility and constraints.
pub(super) fn validate_opening_facts<'ctx>(
    gcx: Gcx<'ctx>,
    database: &TypeDatabase<'ctx>,
    synthetics: &[(
        crate::hir::DefinitionID,
        crate::sema::models::SyntheticDefinition<'ctx>,
    )],
    types: &FxHashSet<crate::sema::models::Ty<'ctx>>,
    calls: &FxHashSet<crate::specialize::Instance<'ctx>>,
) -> Result<(), String> {
    use crate::sema::{
        models::{GenericArgument, GenericParameterDefinitionKind},
        tycheck::utils::unresolved::contains_unresolved_generics,
    };
    if types
        .iter()
        .any(|ty| contains_unresolved_generics(*ty) || matches!(ty.kind(), TyKind::Error))
    {
        return Err("existential opening metadata contains unresolved concrete storage".into());
    }
    for call in calls {
        if !call.is_item() || contains_unresolved_generics(call.args()) {
            return Err("existential opening metadata contains an unresolved callable".into());
        }
        let id = call.def_id();
        let synthetic = synthetics
            .iter()
            .find(|(key, _)| *key == id)
            .map(|(_, value)| value);
        let external = gcx.store.type_databases.borrow();
        let imported = external.get(&id.package());
        let generics = synthetic
            .map(|value| value.generics)
            .or_else(|| database.def_to_generics.get(&id).copied())
            .or_else(|| imported.and_then(|db| db.def_to_generics.get(&id).copied()))
            .ok_or("existential opening metadata refers to an absent generic declaration")?;
        let signature = synthetic
            .map(|value| value.signature)
            .or_else(|| database.def_to_fn_sig.get(&id).copied())
            .or_else(|| imported.and_then(|db| db.def_to_fn_sig.get(&id).copied()))
            .ok_or("existential opening metadata refers to an absent signature")?;
        if call.args().len() != generics.parent_count + generics.parameters.len()
            || signature.abi.is_some()
            || !generics.parameters.iter().all(|parameter| {
                matches!(
                    (&parameter.kind, call.args().get(parameter.index)),
                    (
                        GenericParameterDefinitionKind::Type { .. },
                        Some(GenericArgument::Type(_))
                    ) | (
                        GenericParameterDefinitionKind::Const { .. },
                        Some(GenericArgument::Const(_))
                    )
                )
            })
        {
            return Err(
                "existential opening metadata changes generic coordinates or calling convention"
                    .into(),
            );
        }
    }
    Ok(())
}

/// Only compiler capabilities with exact static storage/signatures may bypass
/// ordinary returned-borrow inference. Imported zero-argument lookalikes cannot
/// manufacture a global permission or substitute an initializer body.
pub(super) fn validate_statics<'ctx>(
    gcx: Gcx<'ctx>,
    database: &TypeDatabase<'ctx>,
    synthetics: &[(
        crate::hir::DefinitionID,
        crate::sema::models::SyntheticDefinition<'ctx>,
    )],
) -> Result<(), String> {
    use crate::sema::models::SyntheticDefinitionKind;
    for (id, definition) in synthetics {
        let (storage, borrow) = match definition.kind {
            SyntheticDefinitionKind::StaticInitializer { storage } => (storage, false),
            SyntheticDefinitionKind::StaticReference { storage } => (storage, true),
            _ => continue,
        };
        let imported = gcx.store.type_databases.borrow();
        let source = if database.def_to_static_mutability.contains_key(&storage) {
            database
        } else {
            imported
                .get(&storage.package())
                .ok_or("static capability has no storage package")?
        };
        if !source.def_to_static_mutability.contains_key(&storage) {
            return Err("static capability names non-static storage".into());
        }
        let ty = *source
            .def_to_ty
            .get(&storage)
            .ok_or("static capability has no stored type")?;
        let signature = definition.signature;
        let valid_output = if borrow {
            signature.abi == Some(crate::hir::Abi::Intrinsic)
                && matches!(signature.output.kind(), TyKind::Reference(inner) if inner == ty)
        } else {
            storage.package() == id.package() && signature.output == ty && signature.abi.is_none()
        };
        if !valid_output
            || !signature.inputs.is_empty()
            || signature.is_variadic
            || definition.generics.total_count() != 0
            || database.def_to_async_body_output.contains_key(id)
        {
            return Err(
                "static capability changes storage, borrow mode or initializer signature".into(),
            );
        }
    }
    Ok(())
}

/// Async Self wrappers must retain their real generic target; the family tag
/// never grants an unchecked poll/result conversion or body-generated proof.
pub(super) fn validate_async_self<'ctx>(
    gcx: Gcx<'ctx>,
    database: &TypeDatabase<'ctx>,
    synthetics: &[(
        crate::hir::DefinitionID,
        crate::sema::models::SyntheticDefinition<'ctx>,
    )],
) -> Result<(), String> {
    use crate::sema::{
        models::{GenericParameterDefinitionKind, SyntheticDefinitionKind},
        tycheck::utils::instantiate::instantiate_signature_with_args,
    };
    for (id, definition) in synthetics {
        match definition.kind {
            SyntheticDefinitionKind::ErasedAsyncSelf { context, method } => {
                let arguments = *database
                    .erased_async_self_arguments
                    .get(id)
                    .ok_or("async Self wrapper loses its concrete target arguments")?;
                let external = gcx
                    .store
                    .type_databases
                    .borrow()
                    .get(&method.package())
                    .cloned();
                let source = if database.def_to_fn_sig.contains_key(&method) {
                    database
                } else {
                    external
                        .as_ref()
                        .ok_or("async Self wrapper has no method package")?
                };
                let method_signature = *source
                    .def_to_fn_sig
                    .get(&method)
                    .ok_or("async Self wrapper has no method")?;
                let output = *source
                    .def_to_async_body_output
                    .get(&method)
                    .ok_or("async Self target is not asynchronous")?;
                let output = staged_alias_type(gcx, source, method.package(), output)?;
                let generics = definition.generics;
                let [parameter] = generics.parameters.as_slice() else {
                    return Err("async Self wrapper needs one hidden type".into());
                };
                let target = crate::sema::models::Ty::new(
                    TyKind::Parameter(
                        crate::sema::tycheck::utils::generics::generic_parameter_marker(parameter),
                    ),
                    gcx,
                );
                let target_signature =
                    instantiate_signature_with_args(gcx, method_signature, arguments);
                if source
                    .def_to_generics
                    .get(&method)
                    .map(|generics| generics.parent_count + generics.parameters.len())
                    != Some(arguments.len())
                {
                    return Err("async Self target changes generic arity".into());
                }
                if let TyKind::BoxedExistential { interfaces } = definition.signature.output.kind()
                {
                    let constraints = database
                        .def_to_constraints
                        .get(id)
                        .ok_or("async Self wrapper loses its conformance assumptions")?;
                    for interface in interfaces {
                        let expected =
                            crate::sema::tycheck::utils::erased_self::bind(gcx, *interface, target);
                        if !constraints.iter().any(|constraint|matches!(constraint.value,crate::sema::models::Constraint::Bound {ty,interface} if ty==target && interface==expected)) {
                            return Err("async Self wrapper loses a result conformance".into());
                        }
                    }
                }

                if generics.parent != Some(context)
                    || parameter.index != generics.parent_count
                    || generics.has_self
                    || !matches!(
                        &parameter.kind,
                        GenericParameterDefinitionKind::Type { default: None }
                    )
                    || arguments.first().and_then(|argument| argument.ty()) != Some(target)
                    || !matches!(output.kind(),TyKind::Parameter(parameter) if parameter.index==0)
                    || !source.interface_requirements.values().any(|requirements| {
                        requirements.methods.iter().any(|entry| entry.id == method)
                    })
                    || definition.signature.abi.is_some()
                    || definition.signature.is_variadic
                    || !matches!(
                        definition.signature.output.kind(),
                        TyKind::BoxedExistential { .. }
                    )
                    || crate::sema::lowering::erased_opening::contains_parameter(
                        definition.signature.output,
                        parameter.index,
                    )
                    || database.def_to_async_body_output.get(id)
                        != Some(&definition.signature.output)
                    || target_signature.inputs.len() != definition.signature.inputs.len()
                    || !target_signature
                        .inputs
                        .iter()
                        .zip(&definition.signature.inputs)
                        .all(|(expected, actual)| {
                            expected.ty == actual.ty && expected.label == actual.label
                        })
                {
                    return Err(
                        "async Self wrapper changes its target, result or input signature".into(),
                    );
                }
            }
            SyntheticDefinitionKind::ErasedAsyncSelfDefault { adapter, provider } => {
                let owner = synthetics
                    .iter()
                    .find(|(id, _)| *id == adapter)
                    .map(|(_, definition)| definition)
                    .ok_or("async Self default has no wrapper")?;
                let SyntheticDefinitionKind::ErasedAsyncSelf { method, .. } = owner.kind else {
                    return Err("async Self default has wrong owner".into());
                };
                let arguments = *database
                    .erased_async_self_arguments
                    .get(&adapter)
                    .ok_or("async Self default loses target arguments")?;
                let external = gcx
                    .store
                    .type_databases
                    .borrow()
                    .get(&provider.package())
                    .cloned();
                let source = if database.def_to_fn_sig.contains_key(&provider) {
                    database
                } else {
                    external
                        .as_ref()
                        .ok_or("async Self default has no provider package")?
                };
                let signature = *source
                    .def_to_fn_sig
                    .get(&provider)
                    .ok_or("async Self default has no provider")?;
                let method_signature = *source
                    .def_to_fn_sig
                    .get(&method)
                    .ok_or("async Self default has no method")?;
                if !signature.inputs.is_empty()
                    || signature.abi.is_some()
                    || !method_signature
                        .inputs
                        .iter()
                        .any(|input| input.default_provider == Some(provider))
                    || definition.signature.output
                        != instantiate_signature_with_args(gcx, signature, arguments).output
                    || !definition.signature.inputs.is_empty()
                    || definition.signature.abi.is_some()
                    || definition.signature.is_variadic
                    || definition.generics.parent != owner.generics.parent
                    || definition.generics.parent_count != owner.generics.parent_count
                    || definition.generics.parameters.len() != owner.generics.parameters.len()
                    || !definition
                        .generics
                        .parameters
                        .iter()
                        .zip(&owner.generics.parameters)
                        .all(|(left, right)| left.id == right.id && left.index == right.index)
                    || database.def_to_async_body_output.contains_key(id)
                {
                    return Err("async Self default changes provider or generic coordinates".into());
                }
            }
            _ => {}
        }
    }
    if database.erased_async_self_arguments.keys().any(|id| {
        !synthetics.iter().any(|(key, definition)| {
            key == id
                && matches!(
                    definition.kind,
                    SyntheticDefinitionKind::ErasedAsyncSelf { .. }
                )
        })
    }) {
        return Err("orphan async Self target arguments".into());
    }
    Ok(())
}

/// These families determine a concrete payload address at code generation.
/// Reject stale signatures or forged generic-coordinate/borrow-mode adapters
/// before publishing their Native calling convention or dependency proof.
pub(super) fn validate_erased_access<'ctx>(
    gcx: Gcx<'ctx>,
    database: &TypeDatabase<'ctx>,
    synthetics: &[(
        crate::hir::DefinitionID,
        crate::sema::models::SyntheticDefinition<'ctx>,
    )],
    registry: Option<&crate::sema::std_items::StdItemRegistry>,
) -> Result<(), String> {
    use crate::{
        hir::StdItem,
        sema::models::{GenericParameterDefinitionKind, SyntheticDefinitionKind},
    };
    for (id, declaration) in synthetics {
        let (context, mode, raw) = match declaration.kind {
            SyntheticDefinitionKind::ErasedTakeAs { context } => (context, None, false),
            SyntheticDefinitionKind::ErasedAsRef { context } => (context, Some(()), false),
            SyntheticDefinitionKind::ErasedPayloadReference { context } => {
                (context, Some(()), true)
            }
            _ => continue,
        };
        let generics = declaration.generics;
        let parent = database
            .def_to_generics
            .get(&context)
            .copied()
            .ok_or("erased access has no generic context")?;
        let [parameter] = generics.parameters.as_slice() else {
            return Err("erased access requires exactly one target parameter".into());
        };
        if context.package() != id.package()
            || generics.parent != Some(context)
            || generics.parent_count != parent.parent_count + parent.parameters.len()
            || parameter.index != generics.parent_count
            || generics.has_self
            || !matches!(
                parameter.kind,
                GenericParameterDefinitionKind::Type { default: None }
            )
        {
            return Err("erased access changes its generic target or context".into());
        }
        let signature = declaration.signature;
        let [input] = signature.inputs.as_slice() else {
            return Err("erased access requires exactly one receiver".into());
        };
        if input.name.as_str() != "self"
            || input.label.is_some()
            || input.default_provider.is_some()
            || signature.abi.is_some()
            || signature.is_variadic
            || database.def_to_async_body_output.contains_key(id)
            || database.def_to_unsafe.contains(id)
        {
            return Err("erased access has an incompatible receiver or calling convention".into());
        }
        let erased = match (input.ty.kind(), mode) {
            (TyKind::Reference(erased), Some(_)) => erased,
            (_, None) => input.ty,
            _ => return Err("erased access changes its input borrow mode".into()),
        };
        if !matches!(erased.kind(), TyKind::BoxedExistential { .. }) {
            return Err("erased access receiver is not an existential".into());
        }
        let target = crate::sema::models::Ty::new(
            TyKind::Parameter(
                crate::sema::tycheck::utils::generics::generic_parameter_marker(parameter),
            ),
            gcx,
        );
        let output_payload = mode
            .map(|()| crate::sema::models::Ty::new(TyKind::Reference(target), gcx))
            .unwrap_or(target);
        if raw {
            if signature.output != output_payload {
                return Err("erased projection changes its target or result borrow mode".into());
            }
        } else {
            let item = if mode.is_some() {
                StdItem::Optional
            } else {
                StdItem::Result
            };
            let owner = registry
                .and_then(|registry| registry.get(item).map(|entry| entry.def_id))
                .or_else(|| gcx.std_item_def(item))
                .ok_or("erased access is missing its standard result type")?;
            let TyKind::Adt(output, args) = signature.output.kind() else {
                return Err("erased access result is not a standard container".into());
            };
            if output.id != owner
                || args.len() != if mode.is_some() { 1 } else { 2 }
                || args[0].ty() != Some(output_payload)
                || (mode.is_none() && args[1].ty() != Some(erased))
            {
                return Err("erased access changes its checked result container".into());
            }
        }
    }
    Ok(())
}

/// A default adapter may only rebind a declared zero-argument provider into
/// its source function's unchanged generic environment. It has no authority
/// to upgrade a borrow or change the provider's owned result representation.
pub(super) fn validate_opened_defaults<'ctx>(
    gcx: Gcx<'ctx>,
    database: &TypeDatabase<'ctx>,
    synthetics: &[(
        crate::hir::DefinitionID,
        crate::sema::models::SyntheticDefinition<'ctx>,
    )],
) -> Result<(), String> {
    use crate::sema::models::SyntheticDefinitionKind;
    let signature = |id| {
        database
            .def_to_fn_sig
            .get(&id)
            .copied()
            .or_else(|| {
                synthetics
                    .iter()
                    .find(|(key, _)| *key == id)
                    .map(|(_, declaration)| declaration.signature)
            })
            .or_else(|| gcx.try_get_signature(id))
    };
    let generics = |id| {
        database
            .def_to_generics
            .get(&id)
            .copied()
            .or_else(|| {
                synthetics
                    .iter()
                    .find(|(key, _)| *key == id)
                    .map(|(_, declaration)| declaration.generics)
            })
            .or_else(|| (id.package() != gcx.package_index()).then(|| gcx.generics_of(id)))
    };
    for (_, declaration) in synthetics {
        let SyntheticDefinitionKind::ErasedDefault {
            source,
            provider,
            parameter,
        } = declaration.kind
        else {
            continue;
        };
        let source_signature = signature(source).ok_or("opened default has no source signature")?;
        let provider_signature =
            signature(provider).ok_or("opened default has no provider signature")?;
        let source_generics = generics(source).ok_or("opened default has no generic source")?;
        let source_parameter = source_generics
            .parameters
            .iter()
            .find(|item| item.index == parameter)
            .ok_or("opened default parameter is not owned by its source")?;
        let actual = declaration.signature;
        let expected = declaration.generics;
        if source_signature.abi.is_some()
            || !provider_signature.inputs.is_empty()
            || !source_signature
                .inputs
                .iter()
                .any(|input| input.default_provider == Some(provider))
            || actual.abi.is_some()
            || actual.is_variadic
            || actual.inputs.len() != 1
            || actual.inputs[0].name.as_str() != "source"
            || actual.inputs[0].label.is_some()
            || actual.inputs[0].default_provider.is_some()
            || actual.output != provider_signature.output
            || !matches!(actual.inputs[0].ty.kind(), TyKind::Reference(inner)
                if matches!(inner.kind(), TyKind::Parameter(value)
                    if value.index == parameter && value.name == source_parameter.name))
            || expected.parent != source_generics.parent
            || expected.parent_count != source_generics.parent_count
            || expected.has_self != source_generics.has_self
            || expected.parameters.len() != source_generics.parameters.len()
            || expected
                .parameters
                .iter()
                .zip(&source_generics.parameters)
                .any(|(a, b)| {
                    a.id != b.id
                        || a.index != b.index
                        || a.name != b.name
                        || std::mem::discriminant(&a.kind) != std::mem::discriminant(&b.kind)
                })
        {
            return Err("opened default changes its declared provider, result or generic/borrow coordinates".into());
        }
    }
    Ok(())
}

/// Required constructor visibility is a promise to downstream subclasses, not
/// just a call-site check. Follow inherited entries to their source visibility
/// before making an imported class available.
pub(super) fn validate_required_initializers<'ctx>(
    gcx: Gcx<'ctx>,
    database: &TypeDatabase<'ctx>,
    resolution: &ResolutionOutput<'ctx>,
    synthetics: &[(
        crate::hir::DefinitionID,
        crate::sema::models::SyntheticDefinition<'ctx>,
    )],
) -> Result<(), String> {
    let visibility = |mut id| {
        let mut seen = FxHashSet::default();
        loop {
            if !seen.insert(id) {
                return Err(
                    "required initializer visibility contains an inheritance cycle".to_string(),
                );
            }
            let kind = synthetics
                .iter()
                .find(|(key, _)| *key == id)
                .map(|(_, definition)| definition.kind)
                .or_else(|| {
                    gcx.store
                        .synthetic_definitions
                        .borrow()
                        .get(&id)
                        .map(|definition| definition.kind)
                });
            if let Some(crate::sema::models::SyntheticDefinitionKind::ClassDecodingInitializer {
                class,
            }) = kind
            {
                id = class;
                continue;
            }
            if let Some(crate::sema::models::SyntheticDefinitionKind::InheritedClassInitializer {
                initializer,
                ..
            }) = kind
            {
                id = initializer;
                continue;
            }
            return resolution
                .definition_to_visibility
                .get(&id)
                .copied()
                .or_else(|| {
                    gcx.try_resolution_output(id.package())?
                        .definition_to_visibility
                        .get(&id)
                        .copied()
                })
                .ok_or_else(|| "required initializer visibility is missing".to_string());
        }
    };
    for (&class, definition) in &database.def_to_struct_def {
        let Some(info) = definition.class_info.filter(|info| !info.is_final) else {
            continue;
        };
        for entry in info.initializers.iter().filter(|entry| entry.is_required) {
            if !visibility(entry.definition)?.supports_required_initializer(visibility(class)?) {
                return Err("required initializer is less visible than its non-final class".into());
            }
        }
    }
    Ok(())
}

/// Class values and payloads have different physical layouts. Reject imported
/// aliases between them before publishing any of the package's type database.
#[cfg(test)]
pub(super) fn validate_class_payloads<'ctx>(
    gcx: crate::compile::context::Gcx<'ctx>,
    database: &TypeDatabase<'ctx>,
    synthetics: &[(
        crate::hir::DefinitionID,
        crate::sema::models::SyntheticDefinition<'ctx>,
    )],
) -> Result<(), String> {
    validate_class_payloads_with_result(
        gcx,
        database,
        synthetics,
        gcx.std_item_def(crate::hir::StdItem::Result),
    )
}

pub(super) fn validate_class_payloads_with_result<'ctx>(
    gcx: crate::compile::context::Gcx<'ctx>,
    database: &TypeDatabase<'ctx>,
    synthetics: &[(
        crate::hir::DefinitionID,
        crate::sema::models::SyntheticDefinition<'ctx>,
    )],
    result_id: Option<crate::hir::DefinitionID>,
) -> Result<(), String> {
    use crate::sema::models::{AdtKind, StructRepr, SyntheticDefinitionKind, Ty};
    use crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args;
    // Imported aliases and the incoming std registry are not published yet.
    // Inspect constructor shapes in that database rather than relying on a
    // previously installed package's language-item IDs.
    let package = database
        .def_to_struct_def
        .keys()
        .next()
        .map_or(gcx.package_index(), |id| id.package());
    let normalize = |ty| staged_alias_type(gcx, database, package, ty);
    let parts = |ty| -> Result<Option<(Ty<'ctx>, Ty<'ctx>)>, String> {
        let ty = normalize(ty)?;
        match ty.kind() {
            TyKind::Adt(definition, arguments)
                if Some(definition.id) == result_id && arguments.len() == 2 =>
            {
                let success = arguments[0]
                    .ty()
                    .ok_or("constructor Result has a non-type success argument")?;
                let error = arguments[1]
                    .ty()
                    .ok_or("constructor Result has a non-type error argument")?;
                Ok(Some((normalize(success)?, normalize(error)?)))
            }
            _ => Ok(None),
        }
    };
    let constructed = |ty| -> Result<Ty<'ctx>, String> {
        match parts(ty)? {
            Some((value, _)) => Ok(value),
            None => normalize(ty),
        }
    };
    let signature_shape = |signature: &crate::sema::models::LabeledFunctionSignature<'ctx>| -> Result<Ty<'ctx>, String> {
        let mut signature = signature.clone();
        signature.output = normalize(signature.output)?;
        if let Some((success, error)) = parts(signature.output)? {
            let TyKind::Adt(definition, _) = signature.output.kind() else { unreachable!() };
            signature.output = Ty::new(TyKind::Adt(definition, gcx.store.interners.intern_generic_args(vec![
                crate::sema::models::GenericArgument::Type(success), crate::sema::models::GenericArgument::Type(error)
            ])), gcx);
        }
        for input in &mut signature.inputs { input.ty = normalize(input.ty)?; }
        Ok(crate::sema::impl_engine::witness::SignatureFreshener::new(gcx).freshen(Ty::from_labeled_signature(gcx, &signature)))
    };
    let lookup = |id| {
        database
            .def_to_struct_def
            .get(&id)
            .copied()
            .or_else(|| gcx.try_get_struct_definition(id))
    };
    for (&id, definition) in &database.def_to_struct_def {
        let Some(info) = definition.class_info else {
            continue;
        };
        let payload = info
            .payload
            .ok_or("class metadata is missing its payload layout")?;
        if payload == id || payload.package() != id.package() {
            return Err("class metadata aliases handle storage with its payload".into());
        }
        let stored = database
            .def_to_struct_def
            .get(&payload)
            .ok_or("class payload definition is missing")?;
        if stored.adt_def.id != payload
            || stored.adt_def.kind != AdtKind::Struct
            || stored.class_info.is_some()
            || stored.has_initializer
        {
            return Err("class payload layout or cleanup disagrees with its class".into());
        }
        let mut ancestry = FxHashSet::default();
        ancestry.insert(id);
        let mut next = info.base;
        while let Some(base) = next {
            let TyKind::Adt(base_id, arguments) = base.kind() else {
                return Err("class base is not nominal".into());
            };
            if !ancestry.insert(base_id.id) {
                return Err("class metadata contains an inheritance cycle".into());
            }
            let base_info = lookup(base_id.id)
                .and_then(|base| base.class_info)
                .ok_or("class base metadata is missing")?;
            if base_info.is_final {
                return Err("class metadata inherits a final base".into());
            }
            next = base_info
                .base
                .map(|base| instantiate_ty_with_args(gcx, base, arguments));
        }
        if let Some(base) = info.base {
            let TyKind::Adt(base_id, arguments) = base.kind() else {
                unreachable!()
            };
            let base = lookup(base_id.id).ok_or("class base definition is missing")?;
            let base_payload = base
                .class_info
                .and_then(|info| info.payload)
                .ok_or("class base has no payload")?;
            let expected = Ty::new(
                TyKind::Adt(
                    crate::sema::models::AdtDef {
                        id: base_payload,
                        kind: AdtKind::Struct,
                    },
                    arguments,
                ),
                gcx,
            );
            let inherited = base.fields.len();
            if stored.repr != StructRepr::C
                || stored
                    .fields
                    .first()
                    .is_none_or(|field| field.ty != expected)
                || definition.fields.len() < inherited
                || stored.fields.len() != definition.fields.len() - inherited + 1
                || stored.fields[1..] != definition.fields[inherited..]
                || base
                    .fields
                    .iter()
                    .zip(definition.fields)
                    .any(|(base, field)| {
                        base.def_id != field.def_id
                            || base.name != field.name
                            || instantiate_ty_with_args(gcx, base.ty, arguments) != field.ty
                    })
            {
                return Err(
                    "class payload layout or cleanup disagrees with its class base prefix".into(),
                );
            }
        } else if stored.fields != definition.fields {
            return Err("class payload layout or cleanup disagrees with its class".into());
        }
        let mut families = FxHashSet::default();
        for method in info.methods {
            if !families.insert(method.family) {
                return Err("class metadata repeats a virtual method family".into());
            }
            let TyKind::Adt(owner, _) = method.owner.kind() else {
                return Err("class method owner is not nominal".into());
            };
            if !ancestry.contains(&owner.id) {
                return Err("class method implementation is outside its ancestry".into());
            }
            if method.returns_self {
                let signature = database
                    .def_to_fn_sig
                    .get(&method.implementation)
                    .copied()
                    .or_else(|| gcx.try_get_signature(method.implementation))
                    .ok_or("dynamic Self method signature is missing")?;
                let output = crate::sema::tycheck::utils::normalize_aliases(gcx, signature.output);
                let receiver_is_owner = signature.inputs.first().is_some_and(|input| {
                    let ty = crate::sema::tycheck::utils::normalize_aliases(gcx, input.ty);
                    let ty = match ty.kind() {
                        TyKind::Reference(class) => class,
                        _ => ty,
                    };
                    input.name.as_str() == "self"
                        && matches!(ty.kind(), TyKind::Adt(class, _) if class.id == owner.id)
                });
                if !receiver_is_owner
                    || !matches!(output.kind(), TyKind::Adt(class, _) if ancestry.contains(&class.id))
                {
                    return Err("dynamic Self method must return an owned class in its ancestry with its class receiver".into());
                }
            }
        }
        if let Some(base) = info.base
            && let TyKind::Adt(base, _) = base.kind()
            && let Some(base_info) = lookup(base.id).and_then(|definition| definition.class_info)
        {
            for inherited in base_info
                .methods
                .iter()
                .filter(|method| method.returns_self)
            {
                if !info
                    .methods
                    .iter()
                    .any(|method| method.family == inherited.family && method.returns_self)
                {
                    return Err(
                        "class metadata removes an inherited dynamic Self result contract".into(),
                    );
                }
            }
            // A late conformance can introduce the promise after the base's
            // nominal packet was compiled. An override must not erase that
            // promise merely because it is absent from the old descriptor.
            let base_ty = info.base.unwrap();
            if gcx.try_get_struct_definition(base.id).is_some() {
                for inherited in gcx
                    .class_methods(base_ty)
                    .into_iter()
                    .filter(|method| method.returns_self)
                {
                    if info
                        .methods
                        .iter()
                        .any(|method| method.family == inherited.family && !method.returns_self)
                    {
                        return Err("class metadata removes an inherited late-family dynamic Self result contract".into());
                    }
                }
            }
        }
        let mut initializers = FxHashSet::default();
        for initializer in info.initializers {
            if !initializers.insert(initializer.definition) {
                return Err("class metadata repeats an initializer entry point".into());
            }
            let TyKind::Adt(owner, _) = initializer.owner.kind() else {
                return Err("class initializer owner is not nominal".into());
            };
            if !ancestry.contains(&owner.id) || (!initializer.is_inherited && owner.id != id) {
                return Err("class initializer implementation is outside its ancestry".into());
            }
            let signature = database
                .def_to_fn_sig
                .get(&initializer.definition)
                .copied()
                .or_else(|| gcx.try_get_signature(initializer.definition))
                .ok_or("class initializer entry point signature is missing")?;
            if (!initializer.is_convenience || initializer.is_inherited)
                && !initializer.delegations.is_empty()
            {
                return Err("only source convenience initializers carry delegation facts".into());
            }
            for &target in initializer.delegations {
                let target_signature = database
                    .def_to_fn_sig
                    .get(&target)
                    .copied()
                    .or_else(|| gcx.try_get_signature(target))
                    .ok_or("initializer delegation target signature is missing")?;
                if !info
                    .initializers
                    .iter()
                    .any(|entry| entry.definition == target)
                    || !matches!(constructed(target_signature.output)?.kind(), TyKind::Adt(result, _) if result.id == id)
                {
                    return Err("initializer delegation target is outside its class".into());
                }
            }
            if signature.is_variadic
                || signature.abi.is_some()
                || !matches!(constructed(signature.output)?.kind(), TyKind::Adt(result, _) if result.id == id)
            {
                return Err(format!(
                    "class initializer entry point does not construct its class: {:?} expected {:?}",
                    signature.output.kind(),
                    id
                ));
            }
        }
        if let Some(base) = info.base {
            let TyKind::Adt(base, _) = base.kind() else {
                return Err("class base is not nominal".into());
            };
            let inherited = lookup(base.id)
                .and_then(|base| base.class_info)
                .ok_or("class base metadata is missing")?;
            for required in inherited
                .initializers
                .iter()
                .filter(|entry| entry.is_required)
            {
                if !info
                    .initializers
                    .iter()
                    .any(|entry| entry.family == required.family && entry.is_required)
                {
                    return Err("class metadata is missing a required initializer family".into());
                }
            }
        }
        if !synthetics.iter().any(|(key, synthetic)| {
            *key == payload && synthetic.kind == SyntheticDefinitionKind::ClassPayload { class: id }
        }) {
            return Err("class payload lacks its nominal compiler declaration".into());
        }
        let Some(TyKind::Adt(public, public_args)) =
            database.def_to_ty.get(&id).map(|ty| ty.kind())
        else {
            return Err("class nominal type is missing".into());
        };
        let Some(TyKind::Adt(private, private_args)) =
            database.def_to_ty.get(&payload).map(|ty| ty.kind())
        else {
            return Err("class payload nominal type is missing".into());
        };
        if public.id != id || private.id != payload || public_args != private_args {
            return Err("class payload generic arguments disagree with its class".into());
        }
    }
    for adoption in &database.class_adoptions {
        let record = database
            .conformance_records
            .get(&adoption.conformance)
            .ok_or("class adoption does not own its conformance record")?;
        let class = record
            .interface
            .self_ty()
            .ok_or("class adoption has no receiver")?;
        let TyKind::Adt(class_id, _) = class.kind() else {
            return Err("class adoption receiver is not nominal".into());
        };
        let info = lookup(class_id.id)
            .and_then(|definition| definition.class_info)
            .ok_or("class adoption receiver is not a class")?;
        let requirements = database
            .interface_requirements
            .get(&record.interface.id)
            .copied()
            .or_else(|| gcx.get_interface_requirements(record.interface.id))
            .ok_or("class adoption interface is missing")?;
        let mut ancestry = FxHashSet::default();
        let mut current = Some(class);
        let mut published_families = FxHashSet::default();
        while let Some(TyKind::Adt(class, arguments)) = current.map(|class| class.kind()) {
            if !ancestry.insert(class.id) {
                return Err("class adoption ancestry contains a cycle".into());
            }
            let level = lookup(class.id)
                .and_then(|definition| definition.class_info)
                .ok_or("class adoption ancestor is missing")?;
            published_families.extend(level.methods.iter().map(|method| method.family));
            current = level
                .base
                .map(|base| instantiate_ty_with_args(gcx, base, arguments));
        }
        for method in adoption.methods {
            let known_requirement = requirements
                .methods
                .iter()
                .any(|requirement| requirement.id == method.requirement)
                || requirements
                    .properties
                    .iter()
                    .any(|property| property.getter_id == method.requirement);
            let signature = database
                .def_to_fn_sig
                .get(&method.slot.implementation)
                .copied()
                .or_else(|| gcx.try_get_signature(method.slot.implementation))
                .ok_or("class adoption implementation signature is missing")?;
            let requirement_signature = database
                .def_to_fn_sig
                .get(&method.requirement)
                .copied()
                .or_else(|| gcx.try_get_signature(method.requirement))
                .ok_or("class adoption requirement signature is missing")?;
            let TyKind::Adt(owner, _) = method.slot.owner.kind() else {
                return Err("class adoption method owner is not nominal".into());
            };
            let receiver_matches = signature.inputs.first().is_some_and(|input| {
                let ty = match input.ty.kind() {
                    TyKind::Reference(class) => class,
                    _ => input.ty,
                };
                input.name.as_str() == "self"
                    && matches!(ty.kind(), TyKind::Adt(class, _) if class.id == owner.id)
            });
            if !known_requirement
                || !ancestry.contains(&owner.id)
                || !receiver_matches
                || (info.is_final && !method.slot.is_final)
                || (method.is_registered
                    && method.slot.family.package() != adoption.conformance.package
                    && !gcx.class_family_is_registered(method.slot.family))
                || (!method.is_registered && !published_families.contains(&method.slot.family))
            {
                return Err(
                    "class adoption has an incompatible requirement, receiver or dispatch family"
                        .into(),
                );
            }
            let requires_self =
                crate::sema::tycheck::utils::normalize_aliases(gcx, requirement_signature.output)
                    == gcx.types.self_type_parameter;
            if (!info.is_final
                && (!crate::sema::lowering::class_defaults::class_interface_signature_supported(
                    gcx,
                    requirement_signature,
                ) || (requires_self && !method.slot.returns_self)))
                || (method.slot.returns_self
                    && !matches!(signature.output.kind(), TyKind::Adt(class, _) if ancestry.contains(&class.id)))
            {
                return Err(
                    "class adoption loses its dynamic Self or invariant-storage contract".into(),
                );
            }
        }
    }
    for (id, synthetic) in synthetics {
        match synthetic.kind {
            SyntheticDefinitionKind::AdoptedClassDefault {
                conformance,
                source,
            } => {
                validate_adopted_default(
                    gcx,
                    database,
                    synthetics,
                    *id,
                    synthetic,
                    conformance,
                    source,
                )?;
            }
            SyntheticDefinitionKind::AdoptedClassDefaultArgument { method, provider } => {
                let owner = synthetics
                    .iter()
                    .find(|(key, _)| *key == method)
                    .map(|(_, value)| value)
                    .ok_or("adopted default argument has no method")?;
                let SyntheticDefinitionKind::AdoptedClassDefault { source, .. } = owner.kind else {
                    return Err("adopted default argument owner is not an adapter".into());
                };
                let source_signature = database
                    .def_to_fn_sig
                    .get(&source)
                    .copied()
                    .or_else(|| {
                        (source.package() != id.package())
                            .then(|| gcx.try_get_signature(source))
                            .flatten()
                    })
                    .ok_or("adopted default argument has no source signature")?;
                let input = source_signature
                    .inputs
                    .iter()
                    .zip(&owner.signature.inputs)
                    .find(|(original, _)| original.default_provider == Some(provider))
                    .map(|(_, input)| input)
                    .ok_or("adopted argument is not a source default")?;
                if input.default_provider != Some(*id)
                    || synthetic.signature.output != input.ty
                    || !synthetic.signature.inputs.is_empty()
                    || synthetic.signature.abi.is_some()
                    || synthetic.signature.is_variadic
                    || synthetic.generics.parent != owner.generics.parent
                    || synthetic.generics.parent_count != owner.generics.parent_count
                    || synthetic
                        .generics
                        .parameters
                        .iter()
                        .map(|parameter| parameter.id)
                        .ne(owner
                            .generics
                            .parameters
                            .iter()
                            .map(|parameter| parameter.id))
                {
                    return Err("adopted argument changes its method environment or result".into());
                }
            }
            SyntheticDefinitionKind::ClassDefaultBody { source } => {
                let generics = database
                    .def_to_generics
                    .get(&source)
                    .copied()
                    .or_else(|| (source.package() != id.package()).then(|| gcx.generics_of(source)))
                    .ok_or("exact default body has no source generics")?;
                let interface = generics
                    .parent
                    .ok_or("exact default body has no interface owner")?;
                let requirements = database
                    .interface_requirements
                    .get(&interface)
                    .copied()
                    .or_else(|| {
                        (interface.package() != id.package())
                            .then(|| gcx.get_interface_requirements(interface))
                            .flatten()
                    })
                    .ok_or("exact default body source is not an interface member")?;
                let is_default = requirements
                    .methods
                    .iter()
                    .any(|method| method.id == source && !method.is_required)
                    || requirements.properties.iter().any(|property| {
                        property.getter_id == source && !property.getter_is_required
                    });
                let signature = database
                    .def_to_fn_sig
                    .get(&source)
                    .copied()
                    .or_else(|| {
                        (source.package() != id.package())
                            .then(|| gcx.try_get_signature(source))
                            .flatten()
                    })
                    .ok_or("exact default body has no source signature")?;
                let source_async = database
                    .def_to_async_body_output
                    .get(&source)
                    .copied()
                    .or_else(|| {
                        (source.package() != id.package() && gcx.definition_is_async(source))
                            .then(|| gcx.function_body_output(source))
                    });
                let source_unsafe = database.def_to_unsafe.contains(&source)
                    || (source.package() != id.package() && gcx.definition_is_unsafe(source));
                if !is_default
                    || !synthetic.signature.same_shape(signature)
                    || synthetic.signature.output != signature.output
                    || synthetic.signature.abi != signature.abi
                    || synthetic
                        .signature
                        .inputs
                        .iter()
                        .zip(&signature.inputs)
                        .any(|(a, b)| {
                            a.ty != b.ty
                                || a.name != b.name
                                || a.label != b.label
                                || a.default_provider != b.default_provider
                        })
                    || synthetic.generics.parent != generics.parent
                    || synthetic.generics.has_self != generics.has_self
                    || synthetic.generics.parent_count != generics.parent_count
                    || synthetic.generics.parameters.len() != generics.parameters.len()
                    || synthetic
                        .generics
                        .parameters
                        .iter()
                        .zip(&generics.parameters)
                        .any(|(a, b)| a.id != b.id || a.index != b.index)
                    || database.def_to_async_body_output.get(id).copied() != source_async
                    || database.def_to_unsafe.contains(id) != source_unsafe
                {
                    return Err(
                        "exact default body changes its source signature or generic coordinates"
                            .into(),
                    );
                }
            }
            SyntheticDefinitionKind::ClassDecoder { class, initializer } => {
                let info = lookup(class)
                    .and_then(|definition| definition.class_info)
                    .ok_or("class decoder owner is not a class")?;
                let entry = info
                    .initializers
                    .iter()
                    .find(|entry| entry.definition == initializer)
                    .ok_or("class decoder has no checked initializer entry")?;
                let source = database
                    .def_to_fn_sig
                    .get(&initializer)
                    .copied()
                    .or_else(|| gcx.try_get_signature(initializer))
                    .ok_or("class decoder initializer signature is missing")?;
                if (!info.is_final && !entry.is_required)
                    || parts(synthetic.signature.output)?.is_none()
                    || !matches!(constructed(synthetic.signature.output)?.kind(), TyKind::Adt(owner, _) if owner.id == class)
                    || synthetic.signature.inputs.len() != 1
                    || !synthetic.signature.inputs[0]
                        .label
                        .is_some_and(|label| gcx.symbol_eq(label, "from"))
                    || source.inputs.iter().map(|input| input.label).ne(synthetic
                        .signature
                        .inputs
                        .iter()
                        .map(|input| input.label))
                    || signature_shape(source)? != signature_shape(synthetic.signature)?
                {
                    return Err(
                        "class decoder factory disagrees with its decoding initializer".into(),
                    );
                }
            }
            SyntheticDefinitionKind::ClassDecodingInitializer { class } => {
                let info = lookup(class)
                    .and_then(|definition| definition.class_info)
                    .ok_or("decoding initializer owner is not a class")?;
                let entry = info
                    .initializers
                    .iter()
                    .find(|entry| entry.definition == *id)
                    .ok_or("orphaned derived decoding initializer")?;
                if entry.is_inherited || entry.is_convenience || (!info.is_final && !entry.is_required)
                    || synthetic.generics.parent != Some(class) || synthetic.generics.parameters.len() != 1
                    || !synthetics.iter().any(|(_, factory)| matches!(factory.kind, SyntheticDefinitionKind::ClassDecoder { class: owner, initializer } if owner == class && initializer == *id)) {
                    return Err("derived decoding initializer has no matching class codec contract".into());
                }
            }
            SyntheticDefinitionKind::ClassPayload { class } => {
                if database
                    .def_to_struct_def
                    .get(&class)
                    .and_then(|value| value.class_info)
                    .and_then(|info| info.payload)
                    != Some(*id)
                {
                    return Err("orphaned class payload compiler declaration".into());
                }
            }
            SyntheticDefinitionKind::ClassPayloadInitializer { class, initializer } => {
                let payload = database
                    .def_to_struct_def
                    .get(&class)
                    .and_then(|value| value.class_info)
                    .and_then(|info| info.payload)
                    .ok_or("class initializer has no payload definition")?;
                let source = database
                    .def_to_fn_sig
                    .get(&initializer)
                    .ok_or("class initializer signature is missing")?;
                let TyKind::Adt(public, public_args) = constructed(source.output)?.kind() else {
                    return Err("class initializer has a nonclass result".into());
                };
                let TyKind::Adt(private, private_args) =
                    constructed(synthetic.signature.output)?.kind()
                else {
                    return Err("class payload initializer has no payload result".into());
                };
                if parts(source.output)?.map(|(_, error)| error)
                    != parts(synthetic.signature.output)?.map(|(_, error)| error)
                    || public.id != class
                    || private.id != payload
                    || public_args != private_args
                    || source.inputs.len() != synthetic.signature.inputs.len()
                    || !source
                        .inputs
                        .iter()
                        .zip(&synthetic.signature.inputs)
                        .all(|(left, right)| left.ty == right.ty && left.label == right.label)
                    || source.is_variadic
                    || synthetic.signature.is_variadic
                    || source.abi != synthetic.signature.abi
                {
                    return Err(
                        "class payload initializer disagrees with its public constructor".into(),
                    );
                }
            }
            SyntheticDefinitionKind::InheritedClassInitializer { class, initializer } => {
                let definition = lookup(class).ok_or("inherited initializer class is missing")?;
                let info = definition
                    .class_info
                    .ok_or("inherited initializer owner is not a class")?;
                let base = info
                    .base
                    .ok_or("root class cannot have an inherited initializer")?;
                let TyKind::Adt(base, _) = base.kind() else {
                    return Err("inherited initializer base is not nominal".into());
                };
                let base_info = lookup(base.id)
                    .and_then(|value| value.class_info)
                    .ok_or("inherited initializer base class is missing")?;
                let source = base_info
                    .initializers
                    .iter()
                    .find(|entry| entry.definition == initializer)
                    .ok_or("inherited initializer has no immediate base entry")?;
                let entry = info
                    .initializers
                    .iter()
                    .find(|entry| entry.definition == *id)
                    .ok_or("orphaned inherited initializer declaration")?;
                if !entry.is_inherited
                    || entry.implementation != *id
                    || entry.family != source.family
                    || entry.is_convenience != source.is_convenience
                    || entry.is_required != source.is_required
                    || !matches!(constructed(synthetic.signature.output)?.kind(), TyKind::Adt(result, _) if result.id == class)
                {
                    return Err("inherited initializer disagrees with its base contract".into());
                }
            }
            SyntheticDefinitionKind::ClassInitializerDispatch { initializer }
            | SyntheticDefinitionKind::ClassConvenienceInitializer { initializer } => {
                let source = database
                    .def_to_fn_sig
                    .get(&initializer)
                    .copied()
                    .or_else(|| gcx.try_get_signature(initializer))
                    .ok_or("constructor dispatch source signature is missing")?;
                let TyKind::Adt(class, _) = constructed(source.output)?.kind() else {
                    return Err("constructor dispatch source has no class result".into());
                };
                let info = lookup(class.id)
                    .and_then(|definition| definition.class_info)
                    .ok_or("constructor dispatch source is not a class")?;
                if !info.initializers.iter().any(|entry| {
                    entry.definition == initializer
                        && (!matches!(
                            synthetic.kind,
                            SyntheticDefinitionKind::ClassConvenienceInitializer { .. }
                        ) || entry.is_convenience)
                }) {
                    return Err("constructor dispatch source is not an initializer".into());
                }
                let generics = database
                    .def_to_generics
                    .get(&initializer)
                    .copied()
                    .or_else(|| {
                        synthetics
                            .iter()
                            .find(|(key, _)| *key == initializer)
                            .map(|(_, declaration)| declaration.generics)
                    })
                    .unwrap_or_else(|| gcx.generics_of(initializer));
                let signature = synthetic.signature;
                if signature.abi.is_some()
                    || signature.is_variadic
                    || signature.output != source.output
                    || signature.inputs.len() != source.inputs.len() + 1
                    || !matches!(signature.inputs[0].ty.kind(), TyKind::Pointer(element, crate::hir::Mutability::Immutable) if element == gcx.types.uint8)
                    || signature
                        .inputs
                        .iter()
                        .any(|parameter| parameter.default_provider.is_some())
                    || !signature.inputs[1..]
                        .iter()
                        .zip(&source.inputs)
                        .all(|(a, b)| a.ty == b.ty && a.label == b.label)
                    || synthetic.generics.parent != generics.parent
                    || synthetic.generics.parent_count != generics.parent_count
                    || synthetic.generics.has_self != generics.has_self
                    || synthetic.generics.parameters.len() != generics.parameters.len()
                    || !synthetic
                        .generics
                        .parameters
                        .iter()
                        .zip(&generics.parameters)
                        .all(|(a, b)| {
                            a.id == b.id
                                && a.index == b.index
                                && std::mem::discriminant(&a.kind)
                                    == std::mem::discriminant(&b.kind)
                        })
                {
                    return Err("constructor dispatch disagrees with its source ABI".into());
                }
            }
            SyntheticDefinitionKind::ClassConstructionDescriptor { class }
            | SyntheticDefinitionKind::ClassObjectDescriptor { class } => {
                let definition =
                    lookup(class).ok_or("class context descriptor owner is missing")?;
                let source = database
                    .def_to_generics
                    .get(&class)
                    .copied()
                    .unwrap_or_else(|| gcx.generics_of(class));
                if definition.class_info.is_none()
                    || match synthetic.kind {
                        SyntheticDefinitionKind::ClassObjectDescriptor { .. } => {
                            let class_ty = database
                                .def_to_ty
                                .get(&class)
                                .copied()
                                .or_else(|| gcx.try_get_type(class));
                            synthetic.signature.inputs.len() != 1
                                || class_ty != Some(synthetic.signature.inputs[0].ty)
                                || synthetic.signature.inputs[0].label.is_some()
                                || synthetic.signature.inputs[0].default_provider.is_some()
                        }
                        _ => !synthetic.signature.inputs.is_empty(),
                    }
                    || synthetic.signature.abi.is_some()
                    || synthetic.signature.is_variadic
                    || !matches!(synthetic.signature.output.kind(), TyKind::Pointer(element, crate::hir::Mutability::Immutable) if element == gcx.types.uint8)
                    || synthetic.generics.parent != source.parent
                    || synthetic.generics.parent_count != source.parent_count
                    || synthetic.generics.parameters.len() != source.parameters.len()
                    || !synthetic
                        .generics
                        .parameters
                        .iter()
                        .zip(&source.parameters)
                        .all(|(a, b)| a.id == b.id && a.index == b.index)
                {
                    return Err("class construction descriptor has an invalid signature".into());
                }
            }
            SyntheticDefinitionKind::InitializerEnvironment { class, initializer } => {
                let info = lookup(class)
                    .and_then(|value| value.class_info)
                    .ok_or("initializer environment owner is not a class")?;
                let base = info
                    .base
                    .ok_or("initializer environment has no base class")?;
                let TyKind::Adt(base, _) = base.kind() else {
                    return Err("initializer environment base is not nominal".into());
                };
                let base_info = lookup(base.id)
                    .and_then(|value| value.class_info)
                    .ok_or("initializer environment base is missing")?;
                if !base_info
                    .initializers
                    .iter()
                    .any(|entry| entry.definition == initializer)
                {
                    return Err("initializer environment has no immediate base entry".into());
                }
                let class_ty = database.def_to_ty.get(&class).copied();
                let Some(TyKind::Adt(_, args)) = class_ty.map(|ty| ty.kind()) else {
                    return Err("initializer environment class arguments are missing".into());
                };
                let source = synthetics
                    .iter()
                    .find(|(id, _)| *id == initializer)
                    .map(|(_, value)| value.generics)
                    .or_else(|| database.def_to_generics.get(&initializer).copied())
                    .unwrap_or_else(|| gcx.generics_of(initializer));
                if class.package() != id.package()
                    || synthetic.generics.parent != Some(class)
                    || synthetic.generics.parent_count != args.len()
                    || synthetic.generics.parameters.len() != source.parent_count
                    || synthetic
                        .generics
                        .parameters
                        .iter()
                        .enumerate()
                        .any(|(index, parameter)| {
                            parameter.index != args.len() + index
                                || parameter.id.package() != id.package()
                        })
                    || !synthetic.signature.inputs.is_empty()
                    || synthetic.signature.output != gcx.types.void
                    || synthetic.signature.abi.is_some()
                    || synthetic.signature.is_variadic
                {
                    return Err("initializer environment has invalid generic coordinates".into());
                }
            }
            SyntheticDefinitionKind::InheritedInitializerDefault { initializer, .. } => {
                if !synthetics.iter().any(|(key, value)| {
                    *key == initializer
                        && matches!(
                            value.kind,
                            SyntheticDefinitionKind::InheritedClassInitializer { .. }
                        )
                }) || !synthetic.signature.inputs.is_empty()
                    || synthetic.signature.is_variadic
                    || synthetic.signature.abi.is_some()
                {
                    return Err("invalid inherited initializer default provider".into());
                }
            }
            _ => {}
        }
    }
    Ok(())
}

/// Validate against the incoming database, before its IDs/synthetics are live.
/// Never reconstruct a purported adapter from a previously hydrated signature.
fn validate_adopted_default<'ctx>(
    gcx: Gcx<'ctx>,
    database: &TypeDatabase<'ctx>,
    synthetics: &[(
        crate::hir::DefinitionID,
        crate::sema::models::SyntheticDefinition<'ctx>,
    )],
    id: crate::hir::DefinitionID,
    synthetic: &crate::sema::models::SyntheticDefinition<'ctx>,
    conformance: crate::sema::models::ConformanceRecordId,
    source: crate::hir::DefinitionID,
) -> Result<(), String> {
    use crate::sema::{
        models::*,
        tycheck::utils::{
            generics::generic_parameter_marker,
            instantiate::{instantiate_signature_with_args, instantiate_ty_with_args},
        },
    };
    let record = database
        .conformance_records
        .get(&conformance)
        .ok_or("adopted default has no conformance")?;
    let source_generics = database
        .def_to_generics
        .get(&source)
        .copied()
        .or_else(|| (source.package() != id.package()).then(|| gcx.generics_of(source)))
        .ok_or("adopted default has no source environment")?;
    let requirements = database
        .interface_requirements
        .get(&record.interface.id)
        .copied()
        .or_else(|| {
            (record.interface.id.package() != id.package())
                .then(|| gcx.get_interface_requirements(record.interface.id))
                .flatten()
        })
        .ok_or("adopted default has no interface")?;
    let original = database
        .def_to_fn_sig
        .get(&source)
        .copied()
        .or_else(|| {
            (source.package() != id.package())
                .then(|| gcx.try_get_signature(source))
                .flatten()
        })
        .ok_or("adopted default has no source signature")?;
    let proof = database
        .def_to_class_default_contract
        .get(&source)
        .copied()
        .or_else(|| {
            (source.package() != id.package())
                .then(|| gcx.class_default_contract(source))
                .flatten()
        });
    let returns_self = staged_alias_type(gcx, database, id.package(), original.output)?
        == gcx.types.self_type_parameter;
    if returns_self && !proof.is_some_and(|proof| proof.preserves_dynamic_self == Some(true)) {
        return Err(
            "adopted default lacks its conditional class receiver or dynamic Self proof".into(),
        );
    }
    let parent_count = database
        .def_to_generics
        .get(&record.extension)
        .map(|generics| generics.parent_count + generics.parameters.len())
        .or_else(|| {
            (record.extension.package() != id.package()).then(|| {
                let generics = gcx.generics_of(record.extension);
                generics.parent_count + generics.parameters.len()
            })
        })
        .ok_or("adopted default has no extension environment")?;
    if conformance.package != id.package()
        || source_generics.parent != Some(record.interface.id)
        || !requirements
            .methods
            .iter()
            .any(|method| method.id == source && !method.is_required)
        || synthetic.generics.parent != Some(record.extension)
        || synthetic.generics.parent_count != parent_count
        || synthetic.generics.has_self
        || synthetic.generics.parameters.len() != source_generics.parameters.len()
    {
        return Err("adopted default changes its source or generic owner".into());
    }
    let mut arguments = record.interface.arguments.to_vec();
    for (index, (parameter, prior)) in synthetic
        .generics
        .parameters
        .iter()
        .zip(&source_generics.parameters)
        .enumerate()
    {
        if parameter.index != parent_count + index
            || parameter.id.package() != id.package()
            || std::mem::discriminant(&parameter.kind) != std::mem::discriminant(&prior.kind)
        {
            return Err("adopted default has invalid generic coordinates".into());
        }
        let marker = generic_parameter_marker(parameter);
        arguments.push(match parameter.kind {
            GenericParameterDefinitionKind::Type { .. } => {
                GenericArgument::Type(Ty::new(TyKind::Parameter(marker), gcx))
            }
            GenericParameterDefinitionKind::Const { .. } => {
                let ty = database
                    .generic_const_param_tys
                    .get(&parameter.id)
                    .copied()
                    .ok_or("adopted const parameter lacks a type")?;
                GenericArgument::Const(Const {
                    ty,
                    kind: ConstKind::Param(marker),
                })
            }
        });
    }
    let arguments = gcx.store.interners.intern_generic_args(arguments);
    let expected = instantiate_signature_with_args(gcx, original, arguments);
    let actual = synthetic.signature;
    if !actual.same_shape(&expected)
        || actual.output != expected.output
        || actual.abi != expected.abi
        || actual
            .inputs
            .iter()
            .zip(&expected.inputs)
            .any(|(input, expected)| {
                if input.ty != expected.ty
                    || input.name != expected.name
                    || input.label != expected.label
                {
                    return true;
                }
                match (input.default_provider, expected.default_provider) {
                    (None, None) => false,
                    (Some(adapter), Some(provider)) => !synthetics.iter().any(|(key, value)| {
                        *key == adapter
                            && value.kind
                                == SyntheticDefinitionKind::AdoptedClassDefaultArgument {
                                    method: id,
                                    provider,
                                }
                    }),
                    _ => true,
                }
            })
    {
        return Err("adopted default changes its source signature".into());
    }
    let source_async = database
        .def_to_async_body_output
        .get(&source)
        .copied()
        .or_else(|| {
            (source.package() != id.package() && gcx.definition_is_async(source))
                .then(|| gcx.function_body_output(source))
        });
    if database.def_to_async_body_output.get(&id).copied()
        != source_async.map(|ty| instantiate_ty_with_args(gcx, ty, arguments))
        || database.def_to_unsafe.contains(&id)
            != (database.def_to_unsafe.contains(&source)
                || (source.package() != id.package() && gcx.definition_is_unsafe(source)))
    {
        return Err("adopted default changes its async or unsafe contract".into());
    }
    Ok(())
}

pub(super) fn validate_class_defaults<'ctx>(
    gcx: crate::compile::context::Gcx<'ctx>,
    database: &TypeDatabase<'ctx>,
    resolution: &ResolutionOutput<'_>,
) -> Result<(), String> {
    for (&id, proof) in &database.def_to_class_default_contract {
        let interface = resolution
            .definition_to_parent
            .get(&id)
            .copied()
            .ok_or("class default contract has no interface owner")?;
        let signature = database
            .def_to_fn_sig
            .get(&id)
            .ok_or("class default contract has no method signature")?;
        let default = database
            .interface_requirements
            .get(&interface)
            .is_some_and(|requirements| {
                requirements
                    .methods
                    .iter()
                    .any(|method| method.id == id && !method.is_required)
                    || requirements
                        .properties
                        .iter()
                        .any(|property| property.getter_id == id && !property.getter_is_required)
            });
        let blanket = database
            .impl_to_target_ty
            .get(&interface)
            .is_some_and(|target| matches!(target.kind(), TyKind::Parameter(_)))
            && matches!(
                resolution.definition_to_kind.get(&id),
                Some(DefinitionKind::AssociatedFunction)
            );
        if (!default && !blanket)
            || !signature
                .inputs
                .first()
                .is_some_and(|input| input.name.as_str() == "self")
        {
            return Err("class default contract does not describe an instance default".into());
        }
        let self_output = staged_alias_type(gcx, database, id.package(), signature.output)?;
        let valid_self_output = (default && self_output == gcx.types.self_type_parameter)
            || (blanket && database.impl_to_target_ty.get(&interface) == Some(&self_output));
        if proof.preserves_dynamic_self.is_some() && !valid_self_output {
            return Err("class default Self proof has no direct owned Self result".into());
        }
    }

    Ok(())
}

/// Imported databases are validated before publication. Resolve their aliases
/// against that staged database rather than accidentally reading stale/live
/// state for the same package from the global context.
fn staged_alias_type<'ctx>(
    gcx: crate::compile::context::Gcx<'ctx>,
    database: &TypeDatabase<'ctx>,
    package: crate::PackageIndex,
    mut ty: crate::sema::models::Ty<'ctx>,
) -> Result<crate::sema::models::Ty<'ctx>, String> {
    let mut visited = FxHashSet::default();
    while let TyKind::Alias {
        kind: crate::sema::models::AliasKind::Weak | crate::sema::models::AliasKind::Inherent,
        def_id,
        args,
    } = ty.kind()
    {
        if !visited.insert(ty) || visited.len() > 256 {
            return Err("metadata has cyclic ownership signature aliases".into());
        }
        let template = if def_id.package() == package {
            database.resolved_aliases.get(&def_id).copied()
        } else {
            gcx.try_get_alias_type(def_id)
        }
        .ok_or_else(|| "metadata ownership signature alias is unresolved".to_owned())?;
        ty =
            crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args(gcx, template, args);
    }
    Ok(ty)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::analyze_script;

    #[test]
    fn g37_imported_required_visibility_follows_inherited_sources() {
        use crate::{metadata::wire, sema::resolve::models::Visibility};
        analyze_script(
            "public class Base {}\nextend Base { public required init() {}; }\npublic class Middle: Base {}\npublic class Child: Middle {}\nfunc main() {}",
            |package, gcx| {
                let base = package.root.declarations[0].id;
                let child = package.root.declarations[3].id;
                let source = gcx.class_info(gcx.get_type(base)).unwrap().initializers[0].definition;
                let inherited =
                    gcx.class_info(gcx.get_type(child)).unwrap().initializers[0].definition;
                let mut database = gcx.with_session_type_database(|database| database.clone());
                database.def_to_struct_def.retain(|id, _| *id == child);
                // Earlier inherited entries are already loaded dependencies,
                // rather than part of the new packet's synthetic declarations.
                let synthetics = vec![(
                    inherited,
                    gcx.store.synthetic_definitions.borrow()[&inherited].clone(),
                )];
                let mut symbols = wire::SymbolTableBuilder::default();
                let encoded = wire::resolution_output_to_wire(
                    gcx.resolution_output(gcx.package_index()),
                    &mut symbols,
                );
                let table = symbols.finish();
                let invalid = std::cell::Cell::new(None);
                let files = rustc_hash::FxHashMap::default();
                let mut resolution = wire::resolution_output_from_wire(
                    gcx,
                    &encoded,
                    wire::FileRemap { old_to_new: &files },
                    wire::SymbolTableRef::new(&table, &invalid),
                )
                .unwrap();
                validate_required_initializers(gcx, &database, &resolution, &synthetics).unwrap();
                resolution
                    .definition_to_visibility
                    .insert(source, Visibility::Private(base));
                assert!(
                    validate_required_initializers(gcx, &database, &resolution, &synthetics)
                        .unwrap_err()
                        .contains("less visible")
                );
            },
        );
    }

    #[test]
    fn class_object_descriptor_metadata_requires_one_owned_exact_class_input() {
        analyze_script(
            "class Record[T] { value: T }\nfunc main() {}",
            |package, gcx| {
                let class = gcx.get_type(package.root.declarations[0].id);
                let helper = gcx.class_object_descriptor(class).unwrap();
                assert_eq!(gcx.class_object_descriptor(class), Some(helper));
                let mut database = TypeDatabase::default();
                gcx.with_session_type_database(|live| {
                    database.def_to_ty = live.def_to_ty.clone();
                    database.def_to_fn_sig = live.def_to_fn_sig.clone();
                    database.def_to_struct_def = live.def_to_struct_def.clone();
                    database.def_to_generics = live.def_to_generics.clone();
                });
                let mut synthetics: Vec<_> = gcx
                    .store
                    .synthetic_definitions
                    .borrow()
                    .iter()
                    .map(|(id, definition)| (*id, definition.clone()))
                    .collect();
                validate_class_payloads(gcx, &database, &synthetics).unwrap();
                let original = synthetics
                    .iter()
                    .find(|(id, _)| *id == helper)
                    .unwrap()
                    .1
                    .clone();
                for inputs in [
                    vec![],
                    vec![crate::sema::models::LabeledFunctionParameter {
                        ty: crate::sema::models::Ty::new(TyKind::Reference(class), gcx),
                        ..original.signature.inputs[0]
                    }],
                    vec![crate::sema::models::LabeledFunctionParameter {
                        ty: gcx.types.int32,
                        ..original.signature.inputs[0]
                    }],
                ] {
                    let mut signature = original.signature.clone();
                    signature.inputs = inputs;
                    synthetics
                        .iter_mut()
                        .find(|(id, _)| *id == helper)
                        .unwrap()
                        .1
                        .signature = gcx.store.arenas.function_signatures.alloc(signature);
                    assert!(
                        validate_class_payloads(gcx, &database, &synthetics)
                            .unwrap_err()
                            .contains("descriptor has an invalid signature")
                    );
                }
            },
        );
    }

    #[test]
    fn conditional_default_contracts_roundtrip_and_reject_stale_or_duplicate_headers() {
        crate::test_support::analyze_script_built_mir(
            r#"
interface Factory {
    func keep() -> Self { self }
    func other(_ value: Self) -> Self { value }
    func step() {}
    func replace(_ value: Self) { self = value }
}
func main() {}
"#,
            |bodies, gcx| {
                assert!(crate::mir::class_defaults::collect(gcx, bodies.iter()).is_ok());
                let database = gcx.with_session_type_database(|database| database.clone());
                assert_eq!(database.def_to_class_default_contract.len(), 4);
                let id = bodies
                    .iter()
                    .find(|body| gcx.definition_ident(body.owner).symbol.as_str() == "keep")
                    .unwrap()
                    .owner;
                assert!(
                    database.def_to_class_default_contract[&id]
                        .preserves_dynamic_self
                        .unwrap()
                );
                let mut symbols = super::super::wire::SymbolTableBuilder::default();
                let mut wire = super::super::wire::type_database_to_wire(&database, &mut symbols);
                let table = symbols.finish();
                let invalid = std::cell::Cell::new(None);
                let files = gcx
                    .resolution_output(gcx.package_index())
                    .definition_to_ident
                    .values()
                    .map(|identifier| (identifier.span.file.index() as u32, identifier.span.file))
                    .collect();
                let mut decoded = super::super::wire::type_database_from_wire(
                    gcx,
                    &wire,
                    super::super::wire::FileRemap { old_to_new: &files },
                    super::super::wire::SymbolTableRef::new(&table, &invalid),
                );
                assert_eq!(
                    decoded.def_to_class_default_contract,
                    database.def_to_class_default_contract
                );
                validate_class_defaults(gcx, &decoded, gcx.resolution_output(gcx.package_index()))
                    .unwrap();
                wire.def_to_class_default_contract
                    .push(wire.def_to_class_default_contract[0].clone());
                assert!(
                    validate_wire_entries(&wire)
                        .unwrap_err()
                        .contains("duplicate class default")
                );
                let mut signature = decoded.def_to_fn_sig[&id].clone();
                signature.output = gcx.types.int32;
                decoded
                    .def_to_fn_sig
                    .insert(id, gcx.store.arenas.function_signatures.alloc(signature));
                assert!(
                    validate_class_defaults(
                        gcx,
                        &decoded,
                        gcx.resolution_output(gcx.package_index())
                    )
                    .unwrap_err()
                    .contains("direct owned Self")
                );
            },
        );
    }

    #[test]
    fn adopted_default_metadata_validates_rebased_generics_and_argument_providers() {
        crate::test_support::analyze_script_built_mir(
            r#"
interface Readable[A] {
    func choose[T](_ value: T, _ amount: int32 = 7) -> T { value }
    func read(_ input: &A) -> int32 { 7 }
}
class Box[U, V, W] {}
conform[W, V, U] Box[U, V, W] to Readable[int32] {}
func main() {}
"#,
            |bodies, gcx| {
                assert!(crate::mir::class_defaults::collect(gcx, bodies.iter()).is_ok());
                let database = gcx.with_session_type_database(|database| database.clone());
                let mut synthetics: Vec<_> = gcx
                    .store
                    .synthetic_definitions
                    .borrow()
                    .iter()
                    .map(|(id, value)| (*id, value.clone()))
                    .collect();
                validate_class_payloads(gcx, &database, &synthetics).unwrap();
                let index = synthetics
                    .iter()
                    .position(|(_, definition)| definition.name.as_str() == "choose")
                    .unwrap();
                let original = synthetics[index].1.clone();
                let mut invalid = original.signature.clone();
                invalid.inputs[1].ty = gcx.types.bool;
                synthetics[index].1.signature = gcx.store.arenas.function_signatures.alloc(invalid);
                assert!(
                    validate_class_payloads(gcx, &database, &synthetics)
                        .unwrap_err()
                        .contains("changes its source signature")
                );
                synthetics[index].1 = original.clone();
                let mut generics = original.generics.clone();
                generics.parent_count += 1;
                synthetics[index].1.generics = gcx.store.arenas.generics.alloc(generics);
                // Either the adapter or its argument provider can be visited first;
                // both must reject the now-inconsistent generic environment.
                assert!(validate_class_payloads(gcx, &database, &synthetics).is_err());
                synthetics[index].1 = original;
                let mut symbols = super::super::wire::SymbolTableBuilder::default();
                for (id, definition) in &synthetics {
                    let wire = super::super::wire::synthetic_definition_to_wire(*id, definition);
                    // Encoding all new kinds is independent of hydration order.
                    assert_eq!(wire.id.index, id.index().raw());
                }
                let _ = super::super::wire::type_database_to_wire(&database, &mut symbols);
            },
        );
    }

    #[test]
    fn blanket_self_proofs_allow_true_and_false_conditional_promises_in_metadata() {
        for result in ["self", "other"] {
            let source = format!(
                "interface Factory {{ func choose(_ other: Self) -> Self; }}\nconform[T] T to Factory {{ func choose(_ other: T) -> T {{ {result} }}; }}\nfunc main() {{}}"
            );
            crate::test_support::analyze_script_built_mir(&source, |bodies, gcx| {
                assert!(crate::mir::class_defaults::collect(gcx, bodies.iter()).is_ok());
                let database = gcx.with_session_type_database(|database| database.clone());
                assert_eq!(
                    database
                        .def_to_class_default_contract
                        .values()
                        .next()
                        .unwrap()
                        .preserves_dynamic_self,
                    Some(result == "self")
                );
                validate_class_defaults(gcx, &database, gcx.resolution_output(gcx.package_index()))
                    .unwrap();
            });
        }
    }

    #[test]
    fn exact_default_body_metadata_rejects_changed_types_and_required_sources() {
        analyze_script(
            r#"
interface Readable {
    func read[T](_ value: &T) -> &T { value }
    func delayed() async -> int32 { 7 }
    func required() -> int32
}
func main() {}
"#,
            |package, gcx| {
                let requirements = gcx
                    .get_interface_requirements(package.root.declarations[0].id)
                    .unwrap();
                let named = |name: &str| {
                    requirements
                        .methods
                        .iter()
                        .find(|method| method.name.as_str() == name)
                        .unwrap()
                        .id
                };
                let alias = gcx.class_default_body(named("read")).unwrap();
                gcx.class_default_body(named("delayed")).unwrap();
                let database = gcx.with_session_type_database(|database| database.clone());
                let mut synthetics: Vec<_> = gcx
                    .store
                    .synthetic_definitions
                    .borrow()
                    .iter()
                    .map(|(id, definition)| (*id, definition.clone()))
                    .collect();
                validate_class_payloads(gcx, &database, &synthetics).unwrap();
                let original = synthetics
                    .iter()
                    .find(|(id, _)| *id == alias)
                    .unwrap()
                    .1
                    .clone();
                let mut wrong = original.signature.clone();
                wrong.output = gcx.types.int32;
                synthetics
                    .iter_mut()
                    .find(|(id, _)| *id == alias)
                    .unwrap()
                    .1
                    .signature = gcx.store.arenas.function_signatures.alloc(wrong);
                assert!(
                    validate_class_payloads(gcx, &database, &synthetics)
                        .unwrap_err()
                        .contains("exact default body changes")
                );
                synthetics
                    .iter_mut()
                    .find(|(id, _)| *id == alias)
                    .unwrap()
                    .1 = original;
                synthetics
                    .iter_mut()
                    .find(|(id, _)| *id == alias)
                    .unwrap()
                    .1
                    .kind = crate::sema::models::SyntheticDefinitionKind::ClassDefaultBody {
                    source: named("required"),
                };
                assert!(validate_class_payloads(gcx, &database, &synthetics).is_err());
            },
        );
    }

    #[test]
    fn conformance_owned_class_families_roundtrip_without_changing_the_nominal_catalog() {
        analyze_script(
            r#"
interface Readable { func read() -> int32; }
final class Counter { value: int32 }
conform Counter to Readable { func read() -> int32 { self.value }; }
func main() {}
"#,
            |package, gcx| {
                use crate::sema::models::{ClassAdoption, ClassMethod, ClassWitnessMethod};
                let class = gcx.get_type(package.root.declarations[1].id);
                let requirement = gcx
                    .get_interface_requirements(package.root.declarations[0].id)
                    .unwrap()
                    .methods[0]
                    .id;
                let (conformance, record) = gcx
                    .with_session_type_database(|database| {
                        database
                            .conformance_records
                            .iter()
                            .next()
                            .map(|(id, record)| (*id, *record))
                    })
                    .unwrap();
                let implementation = gcx
                    .with_session_type_database(|database| {
                        database.def_to_fn_sig.keys().copied().find(|id| {
                            gcx.definition_parent(*id) == Some(record.extension)
                                && gcx.definition_ident(*id).symbol.as_str() == "read"
                        })
                    })
                    .unwrap();
                // Model A's earlier nominal packet, before B supplied this family.
                // Current source collection also catalogs explicit conform bodies.
                let TyKind::Adt(class_definition, _) = class.kind() else {
                    unreachable!()
                };
                let mut definition = gcx.get_struct_definition(class_definition.id).clone();
                definition.class_info.as_mut().unwrap().methods = &[];
                gcx.cache_struct_definition(class_definition.id, definition);
                let static_catalog = gcx.class_info(class).unwrap().methods;
                assert!(static_catalog.is_empty());
                let methods = gcx
                    .store
                    .arenas
                    .global
                    .alloc_slice_copy(&[ClassWitnessMethod {
                        requirement,
                        slot: ClassMethod {
                            returns_self: false,
                            family: implementation,
                            implementation,
                            owner: class,
                            is_final: true,
                        },
                        is_registered: true,
                    }]);
                gcx.with_session_type_database(|database| {
                    database.class_adoptions.push(ClassAdoption {
                        conformance,
                        methods,
                    })
                });
                assert_eq!(gcx.class_methods(class), vec![methods[0].slot]);
                assert_eq!(
                    gcx.class_method(class, implementation),
                    Some(methods[0].slot)
                );
                assert!(gcx.class_family_is_registered(implementation));
                assert!(
                    gcx.class_info(class).unwrap().methods.is_empty(),
                    "the imported nominal descriptor must stay immutable"
                );
                let database = gcx.with_session_type_database(|database| database.clone());
                let synthetics: Vec<_> = gcx
                    .store
                    .synthetic_definitions
                    .borrow()
                    .iter()
                    .map(|(id, value)| (*id, value.clone()))
                    .collect();
                validate_class_payloads(gcx, &database, &synthetics).unwrap();
                let mut symbols = super::super::wire::SymbolTableBuilder::default();
                let mut wire = super::super::wire::type_database_to_wire(&database, &mut symbols);
                let symbols = symbols.finish();
                let invalid = std::cell::Cell::new(None);
                let files = gcx
                    .resolution_output(gcx.package_index())
                    .definition_to_ident
                    .values()
                    .map(|identifier| (identifier.span.file.index() as u32, identifier.span.file))
                    .collect();
                let mut decoded = super::super::wire::type_database_from_wire(
                    gcx,
                    &wire,
                    super::super::wire::FileRemap { old_to_new: &files },
                    super::super::wire::SymbolTableRef::new(&symbols, &invalid),
                );
                assert_eq!(decoded.class_adoptions[0].conformance, conformance);
                assert_eq!(decoded.class_adoptions[0].methods, methods);
                validate_class_payloads(gcx, &decoded, &synthetics).unwrap();
                let mut wrong = methods[0];
                wrong.is_registered = false;
                decoded.class_adoptions[0].methods =
                    gcx.store.arenas.global.alloc_slice_copy(&[wrong]);
                assert!(
                    validate_class_payloads(gcx, &decoded, &synthetics)
                        .unwrap_err()
                        .contains("dispatch family")
                );
                wire.class_adoptions.push(wire.class_adoptions[0].clone());
                assert!(
                    validate_wire_entries(&wire)
                        .unwrap_err()
                        .contains("repeats a class adoption")
                );
            },
        );
    }

    #[test]
    fn subclass_metadata_cannot_drop_a_self_promise_introduced_by_a_late_conformance() {
        analyze_script(
            r#"
interface Identity { func identity() -> Self; }
class Base {}
conform Base to Identity { func identity() -> Self { self }; }
class Derived: Base {}
conform Derived to Identity { override func identity() -> Self { self }; }
func main() {}
"#,
            |package, gcx| {
                let base = package.root.declarations[1].id;
                let derived = package.root.declarations[3].id;
                // Model an earlier Base packet without the conformance-owned row.
                let mut old_base = gcx.get_struct_definition(base).clone();
                old_base.class_info.as_mut().unwrap().methods = &[];
                gcx.cache_struct_definition(base, old_base);
                let mut database = gcx.with_session_type_database(|database| database.clone());
                let synthetics: Vec<_> = gcx
                    .store
                    .synthetic_definitions
                    .borrow()
                    .iter()
                    .map(|(id, value)| (*id, value.clone()))
                    .collect();
                validate_class_payloads(gcx, &database, &synthetics).unwrap();
                let mut changed = database.def_to_struct_def[&derived].clone();
                let mut methods = changed.class_info.unwrap().methods.to_vec();
                assert_eq!(methods.len(), 1);
                methods[0].returns_self = false;
                changed.class_info.as_mut().unwrap().methods =
                    gcx.store.arenas.global.alloc_slice_copy(&methods);
                database
                    .def_to_struct_def
                    .insert(derived, gcx.store.arenas.struct_definitions.alloc(changed));
                assert!(
                    validate_class_payloads(gcx, &database, &synthetics)
                        .unwrap_err()
                        .contains("late-family dynamic Self")
                );
            },
        );
    }

    #[test]
    fn blanket_receiver_class_contract_metadata_roundtrips_without_claiming_dynamic_self() {
        crate::test_support::analyze_script_built_mir(
            r#"
interface Replace { func replace(_ other: Self); }
conform[T] T to Replace {
    func replace(_ other: T) { self = other }
}
func main() {}
"#,
            |bodies, gcx| {
                assert!(crate::mir::class_defaults::collect(gcx, bodies.iter()).is_ok());
                let mut database = gcx.with_session_type_database(|database| database.clone());
                let method = bodies
                    .iter()
                    .find(|body| gcx.definition_ident(body.owner).symbol.as_str() == "replace")
                    .unwrap()
                    .owner;
                assert_eq!(
                    database.def_to_class_default_contract[&method].preserves_dynamic_self,
                    None
                );
                let resolution = gcx.resolution_output(gcx.package_index());
                validate_class_defaults(gcx, &database, resolution).unwrap();
                database
                    .def_to_class_default_contract
                    .get_mut(&method)
                    .unwrap()
                    .preserves_dynamic_self = Some(true);
                assert!(
                    validate_class_defaults(gcx, &database, resolution)
                        .unwrap_err()
                        .contains("direct owned Self")
                );
            },
        );
    }

    #[test]
    fn class_metadata_preserves_and_validates_dynamic_self_contracts() {
        analyze_script(
            "class Base {}\nextend Base { func identity() -> Self { self }; func count() -> int32 { 1 }; }\nclass Child: Base {}\nfunc main() {}",
            |package, gcx| {
                let base = package.root.declarations[0].id;
                let child = package.root.declarations[2].id;
                let mut database = TypeDatabase::default();
                gcx.with_session_type_database(|live| {
                    database.def_to_ty = live.def_to_ty.clone();
                    database.def_to_fn_sig = live.def_to_fn_sig.clone();
                    database.def_to_struct_def = live.def_to_struct_def.clone();
                    database.def_to_generics = live.def_to_generics.clone();
                });
                let synthetics: Vec<_> = gcx
                    .store
                    .synthetic_definitions
                    .borrow()
                    .iter()
                    .map(|(id, declaration)| (*id, declaration.clone()))
                    .collect();
                validate_class_payloads(gcx, &database, &synthetics).unwrap();
                let original = database.def_to_struct_def[&child].clone();
                let mut symbols = super::super::wire::SymbolTableBuilder::default();
                let wire = super::super::wire::struct_definition_to_wire(&original, &mut symbols);
                let table = symbols.finish();
                let invalid = std::cell::Cell::new(None);
                let decoded = super::super::wire::struct_definition_from_wire(
                    gcx,
                    &wire,
                    super::super::wire::SymbolTableRef::new(&table, &invalid),
                );
                assert_eq!(
                    decoded.class_info.unwrap().methods,
                    original.class_info.unwrap().methods
                );
                let mut changed = original.clone();
                let mut methods = changed.class_info.unwrap().methods.to_vec();
                methods
                    .iter_mut()
                    .for_each(|method| method.returns_self = false);
                changed.class_info.as_mut().unwrap().methods =
                    gcx.store.arenas.global.alloc_slice_copy(&methods);
                database
                    .def_to_struct_def
                    .insert(child, gcx.store.arenas.struct_definitions.alloc(changed));
                assert!(
                    validate_class_payloads(gcx, &database, &synthetics)
                        .unwrap_err()
                        .contains("inherited dynamic Self")
                );
                database
                    .def_to_struct_def
                    .insert(child, gcx.store.arenas.struct_definitions.alloc(original));
                let method = database.def_to_struct_def[&base]
                    .class_info
                    .unwrap()
                    .methods
                    .iter()
                    .find(|method| method.returns_self)
                    .unwrap()
                    .implementation;
                let original_signature = database.def_to_fn_sig[&method];
                let mut invalid_signature = original_signature.clone();
                invalid_signature.inputs[0].ty = gcx.types.int32;
                database.def_to_fn_sig.insert(
                    method,
                    gcx.store
                        .arenas
                        .function_signatures
                        .alloc(invalid_signature),
                );
                assert!(
                    validate_class_payloads(gcx, &database, &synthetics)
                        .unwrap_err()
                        .contains("class receiver")
                );
                database.def_to_fn_sig.insert(method, original_signature);
                let mut changed = database.def_to_struct_def[&base].clone();
                let mut methods = changed.class_info.unwrap().methods.to_vec();
                methods
                    .iter_mut()
                    .for_each(|method| method.returns_self = true);
                changed.class_info.as_mut().unwrap().methods =
                    gcx.store.arenas.global.alloc_slice_copy(&methods);
                database
                    .def_to_struct_def
                    .insert(base, gcx.store.arenas.struct_definitions.alloc(changed));
                assert!(
                    validate_class_payloads(gcx, &database, &synthetics)
                        .unwrap_err()
                        .contains("owned class")
                );
            },
        );
    }

    #[test]
    fn class_metadata_cannot_remove_an_inherited_required_constructor() {
        analyze_script(
            "class Base { value: int32 }\nextend Base { public required init(_ value: int32) { self.value = value } }\nclass Child: Base {}\nfunc main() {}",
            |package, gcx| {
                let child = package.root.declarations[2].id;
                let mut database = TypeDatabase::default();
                gcx.with_session_type_database(|live| {
                    database.def_to_ty = live.def_to_ty.clone();
                    database.def_to_fn_sig = live.def_to_fn_sig.clone();
                    database.def_to_struct_def = live.def_to_struct_def.clone();
                    database.def_to_generics = live.def_to_generics.clone();
                });
                let synthetics: Vec<_> = gcx
                    .store
                    .synthetic_definitions
                    .borrow()
                    .iter()
                    .map(|(id, declaration)| (*id, declaration.clone()))
                    .collect();
                validate_class_payloads(gcx, &database, &synthetics).unwrap();
                let mut definition = database.def_to_struct_def[&child].clone();
                definition.class_info.as_mut().unwrap().initializers = &[];
                database
                    .def_to_struct_def
                    .insert(child, gcx.store.arenas.struct_definitions.alloc(definition));
                assert!(
                    validate_class_payloads(gcx, &database, &synthetics)
                        .unwrap_err()
                        .contains("missing a required initializer")
                );
            },
        );
    }

    #[test]
    fn fallible_initializer_metadata_preserves_success_storage_and_error_type() {
        use crate::sema::models::{AliasKind, GenericArgument, LabeledFunctionSignature, Ty};
        analyze_script(
            "enum Outcome[T, E] { case ok(T); case err(E) }\ntype Wire[T] = Outcome[T, int32]\nclass Record { value: int32 }\nextend Record { public init() { self.value = 7 } }\nfunc main() {}",
            |package, gcx| {
                let outcome = package.root.declarations[0].id;
                let alias = package.root.declarations[1].id;
                let class = package.root.declarations[2].id;
                let initializer =
                    gcx.class_info(gcx.get_type(class)).unwrap().initializers[0].definition;
                let helper = gcx.class_payload_initializer(initializer).unwrap();
                let mut database = gcx.with_session_type_database(|database| database.clone());
                let TyKind::Adt(result, _) = gcx.get_type(outcome).kind() else {
                    unreachable!()
                };
                let result_ty = |value, error| {
                    Ty::new(
                        TyKind::Adt(
                            result,
                            gcx.store.interners.intern_generic_args(vec![
                                GenericArgument::Type(value),
                                GenericArgument::Type(error),
                            ]),
                        ),
                        gcx,
                    )
                };
                let public = gcx.get_signature(initializer);
                let alias_result = Ty::new(
                    TyKind::Alias {
                        kind: AliasKind::Weak,
                        def_id: alias,
                        args: gcx
                            .store
                            .interners
                            .intern_generic_args(vec![GenericArgument::Type(gcx.get_type(class))]),
                    },
                    gcx,
                );
                database.def_to_fn_sig.insert(
                    initializer,
                    gcx.store
                        .arenas
                        .function_signatures
                        .alloc(LabeledFunctionSignature {
                            output: alias_result,
                            ..public.clone()
                        }),
                );
                let mut definitions: Vec<_> = gcx
                    .store
                    .synthetic_definitions
                    .borrow()
                    .iter()
                    .map(|(id, value)| (*id, value.clone()))
                    .collect();
                let (_, body) = definitions
                    .iter_mut()
                    .find(|(id, _)| *id == helper)
                    .unwrap();
                let payload = body.signature.output;
                body.signature =
                    gcx.store
                        .arenas
                        .function_signatures
                        .alloc(LabeledFunctionSignature {
                            output: result_ty(payload, gcx.types.int32),
                            ..body.signature.clone()
                        });
                validate_class_payloads_with_result(gcx, &database, &definitions, Some(outcome))
                    .unwrap();
                let (_, body) = definitions
                    .iter_mut()
                    .find(|(id, _)| *id == helper)
                    .unwrap();
                body.signature =
                    gcx.store
                        .arenas
                        .function_signatures
                        .alloc(LabeledFunctionSignature {
                            output: result_ty(payload, gcx.types.bool),
                            ..body.signature.clone()
                        });
                assert!(
                    validate_class_payloads_with_result(
                        gcx,
                        &database,
                        &definitions,
                        Some(outcome)
                    )
                    .unwrap_err()
                    .contains("disagrees with its public constructor")
                );
            },
        );
    }

    #[test]
    fn class_initializer_metadata_requires_unique_valid_entry_points() {
        analyze_script(
            "class Record[T] { value: T }\nextend[T] Record[T] { init(_ value: T) { self.value = value } }\nfunc main() {}",
            |package, gcx| {
                let class = package.root.declarations[0].id;
                let mut database = TypeDatabase::default();
                gcx.with_session_type_database(|live| {
                    database.def_to_ty = live.def_to_ty.clone();
                    database.def_to_fn_sig = live.def_to_fn_sig.clone();
                    database.def_to_struct_def = live.def_to_struct_def.clone();
                });
                let synthetics: Vec<_> = gcx
                    .store
                    .synthetic_definitions
                    .borrow()
                    .iter()
                    .map(|(id, definition)| (*id, definition.clone()))
                    .collect();
                validate_class_payloads(gcx, &database, &synthetics).unwrap();
                let original = database.def_to_struct_def[&class].clone();
                let initializer = original.class_info.unwrap().initializers[0];
                for (entries, expected) in [
                    (vec![initializer, initializer], "repeats an initializer"),
                    (
                        vec![crate::sema::models::ClassInitializer {
                            owner: gcx.types.int32,
                            ..initializer
                        }],
                        "owner is not nominal",
                    ),
                    (
                        vec![crate::sema::models::ClassInitializer {
                            definition: package.root.declarations[2].id,
                            ..initializer
                        }],
                        "does not construct its class",
                    ),
                ] {
                    let mut wrong = original.clone();
                    wrong.class_info.as_mut().unwrap().initializers =
                        gcx.store.arenas.global.alloc_slice_copy(&entries);
                    database
                        .def_to_struct_def
                        .insert(class, gcx.store.arenas.struct_definitions.alloc(wrong));
                    assert!(
                        validate_class_payloads(gcx, &database, &synthetics)
                            .unwrap_err()
                            .contains(expected),
                        "{expected}"
                    );
                }
            },
        );
    }

    #[test]
    fn inherited_initializer_metadata_requires_the_immediate_base_contract() {
        analyze_script(
            "class Base[T] { value: T }\nextend[T] Base[T] { init(_ value: T, flag: bool = true) { self.value = value } }\nclass Child[T]: Base[T] { count: int32 = 3 }\nfunc main() {}",
            |package, gcx| {
                let child = package.root.declarations[2].id;
                let mut database = TypeDatabase::default();
                gcx.with_session_type_database(|live| {
                    database.def_to_ty = live.def_to_ty.clone();
                    database.def_to_fn_sig = live.def_to_fn_sig.clone();
                    database.def_to_struct_def = live.def_to_struct_def.clone();
                });
                let synthetics: Vec<_> = gcx
                    .store
                    .synthetic_definitions
                    .borrow()
                    .iter()
                    .map(|(id, definition)| (*id, definition.clone()))
                    .collect();
                validate_class_payloads(gcx, &database, &synthetics).unwrap();
                let mut changed = database.def_to_struct_def[&child].clone();
                let info = changed.class_info.as_mut().unwrap();
                let mut entry = info.initializers[0];
                entry.family = package.root.declarations[3].id;
                info.initializers = gcx.store.arenas.global.alloc_slice_copy(&[entry]);
                database
                    .def_to_struct_def
                    .insert(child, gcx.store.arenas.struct_definitions.alloc(changed));
                assert!(
                    validate_class_payloads(gcx, &database, &synthetics)
                        .unwrap_err()
                        .contains("base contract")
                );
            },
        );
    }

    #[test]
    fn inherited_initializer_environment_metadata_checks_parameter_coordinates() {
        analyze_script(
            "struct Box[T] { value: T }\nclass Base[T] { value: T }\nextend[U] Base[Box[U]] { init(_ value: Box[U]) { self.value = value } }\nclass Child[T, V]: Base[T] { extra: [V; 0] = [] }\nfunc main() {}",
            |_, gcx| {
                let mut database = TypeDatabase::default();
                gcx.with_session_type_database(|live| {
                    database.def_to_ty = live.def_to_ty.clone();
                    database.def_to_fn_sig = live.def_to_fn_sig.clone();
                    database.def_to_struct_def = live.def_to_struct_def.clone();
                    database.def_to_generics = live.def_to_generics.clone();
                });
                let mut synthetics: Vec<_> = gcx
                    .store
                    .synthetic_definitions
                    .borrow()
                    .iter()
                    .map(|(id, declaration)| (*id, declaration.clone()))
                    .collect();
                validate_class_payloads(gcx, &database, &synthetics).unwrap();
                let (_, declaration) =
                    synthetics
                        .iter_mut()
                        .find(|(_, declaration)| {
                            matches!(declaration.kind,
                    crate::sema::models::SyntheticDefinitionKind::InitializerEnvironment { .. })
                        })
                        .unwrap();
                let mut incorrect = declaration.generics.clone();
                incorrect.parameters[0].index = 0;
                declaration.generics = gcx.store.arenas.generics.alloc(incorrect);
                assert!(
                    validate_class_payloads(gcx, &database, &synthetics)
                        .unwrap_err()
                        .contains("generic coordinates")
                );
            },
        );
    }

    #[test]
    fn constructor_dispatch_metadata_rejects_a_forged_private_context_abi() {
        analyze_script(
            "class Base {}\nextend Base { init() {} }\nfunc main() {}",
            |package, gcx| {
                let initializer = gcx
                    .class_info(gcx.get_type(package.root.declarations[0].id))
                    .unwrap()
                    .initializers[0]
                    .definition;
                let dispatch = gcx.class_initializer_dispatch(initializer).unwrap();
                let mut database = TypeDatabase::default();
                gcx.with_session_type_database(|live| {
                    database.def_to_ty = live.def_to_ty.clone();
                    database.def_to_fn_sig = live.def_to_fn_sig.clone();
                    database.def_to_struct_def = live.def_to_struct_def.clone();
                    database.def_to_generics = live.def_to_generics.clone();
                });
                let mut synthetics: Vec<_> = gcx
                    .store
                    .synthetic_definitions
                    .borrow()
                    .iter()
                    .map(|(id, declaration)| (*id, declaration.clone()))
                    .collect();
                validate_class_payloads(gcx, &database, &synthetics).unwrap();
                let declaration = &mut synthetics
                    .iter_mut()
                    .find(|(id, _)| *id == dispatch)
                    .unwrap()
                    .1;
                let mut signature = declaration.signature.clone();
                signature.inputs[0].ty = gcx.types.bool;
                declaration.signature = gcx.store.arenas.function_signatures.alloc(signature);
                assert!(
                    validate_class_payloads(gcx, &database, &synthetics)
                        .unwrap_err()
                        .contains("source ABI")
                );
            },
        );
    }

    #[test]
    fn inherited_payload_metadata_preserves_the_nested_base_prefix() {
        analyze_script(
            "class Base[T] { item: T }\nclass Derived[T]: Base[T] { other: int32 }\nfunc main() {}",
            |package, gcx| {
                let id = package.root.declarations[1].id;
                let payload = gcx.class_info(gcx.get_type(id)).unwrap().payload.unwrap();
                let mut database = TypeDatabase::default();
                gcx.with_session_type_database(|live| {
                    database.def_to_ty = live.def_to_ty.clone();
                    database.def_to_struct_def = live.def_to_struct_def.clone();
                });
                let synthetics: Vec<_> = gcx
                    .store
                    .synthetic_definitions
                    .borrow()
                    .iter()
                    .map(|(id, value)| (*id, value.clone()))
                    .collect();
                validate_class_payloads(gcx, &database, &synthetics).unwrap();
                let mut wrong = database.def_to_struct_def[&payload].clone();
                wrong.repr = crate::sema::models::StructRepr::Taro;
                database
                    .def_to_struct_def
                    .insert(payload, gcx.store.arenas.struct_definitions.alloc(wrong));
                assert!(
                    validate_class_payloads(gcx, &database, &synthetics)
                        .unwrap_err()
                        .contains("base prefix")
                );
            },
        );
    }
    #[test]
    fn imported_class_payloads_require_distinct_matching_nominal_layouts() {
        analyze_script(
            "struct Object[T] { value: T; count: int32 }\nfunc main() {}",
            |package, gcx| {
                use crate::sema::models::ClassInfo;
                let id = package.root.declarations[0].id;
                let ty = gcx.get_type(id);
                let mut class = gcx.get_struct_definition(id).clone();
                class.class_info = Some(ClassInfo {
                    initializers: &[],
                    base: None,
                    methods: &[],
                    payload: None,
                    is_final: false,
                });
                gcx.cache_struct_definition(id, class);
                let TyKind::Adt(payload, _) = gcx.ensure_class_payload(ty).unwrap().kind() else {
                    unreachable!()
                };
                let mut database = TypeDatabase::default();
                gcx.with_session_type_database(|live| {
                    database.def_to_ty = live.def_to_ty.clone();
                    database.def_to_struct_def = live.def_to_struct_def.clone();
                });
                let synthetics: Vec<_> = gcx
                    .store
                    .synthetic_definitions
                    .borrow()
                    .iter()
                    .map(|(id, definition)| (*id, definition.clone()))
                    .collect();
                validate_class_payloads(gcx, &database, &synthetics).unwrap();
                assert!(
                    validate_class_payloads(gcx, &database, &[])
                        .unwrap_err()
                        .contains("compiler declaration")
                );
                let original = database.def_to_struct_def[&payload.id];
                let mut wrong = original.clone();
                wrong.fields = &[];
                database
                    .def_to_struct_def
                    .insert(payload.id, gcx.store.arenas.struct_definitions.alloc(wrong));
                assert!(
                    validate_class_payloads(gcx, &database, &synthetics)
                        .unwrap_err()
                        .contains("layout or cleanup")
                );
                database.def_to_struct_def.insert(payload.id, original);
                let mut wrong = database.def_to_struct_def[&id].clone();
                wrong.class_info.as_mut().unwrap().payload = Some(id);
                database
                    .def_to_struct_def
                    .insert(id, gcx.store.arenas.struct_definitions.alloc(wrong));
                assert!(
                    validate_class_payloads(gcx, &database, &synthetics)
                        .unwrap_err()
                        .contains("aliases handle storage")
                );
            },
        );
    }
}

#[cfg(test)]
mod return_only_tests {
    use super::*;
    use crate::metadata::wire::{self, FileRemap, SymbolTableBuilder, SymbolTableRef};
    #[test]
    fn default_provider_signatures_roundtrip() {
        crate::test_support::check_script(
            "enum Maybe { case none; case some(&int32) }\nstruct View { value: Maybe = .none }\nfunc empty() -> View { View {} }\nfunc main() {}",
            |_, gcx| {
                let mut symbols = SymbolTableBuilder::default();
                let wire = gcx
                    .with_session_type_database(|db| wire::type_database_to_wire(db, &mut symbols));
                let symbols = symbols.finish();
                let resolution = gcx.resolution_output(gcx.package_index());
                let files = rustc_hash::FxHashMap::from_iter(
                    resolution
                        .definition_to_ident
                        .values()
                        .map(|ident| (ident.span.file.index() as u32, ident.span.file)),
                );
                let invalid = std::cell::Cell::new(None);
                let restored = wire::type_database_from_wire(
                    gcx,
                    &wire,
                    FileRemap { old_to_new: &files },
                    SymbolTableRef::new(&symbols, &invalid),
                );
                validate_class_defaults(gcx, &restored, resolution).unwrap();
                let provider = *gcx
                    .store
                    .default_value_exprs
                    .borrow()
                    .keys()
                    .next()
                    .unwrap();
                assert!(restored.def_to_fn_sig.contains_key(&provider));
            },
        );
    }
}

#[cfg(test)]
mod erased_access_tests {
    use crate::sema::{
        lowering::erased_access::projection_signature, models::*,
        tycheck::utils::generics::generic_parameter_marker,
    };

    #[test]
    fn private_projection_proof_rejects_receiver_authority_and_target_changes() {
        crate::test_support::analyze_script("func main() {}", |package, gcx| {
            let context = package.root.declarations[0].id;
            let span = gcx.definition_ident(context).span;
            let erased = Ty::new(TyKind::BoxedExistential { interfaces: &[] }, gcx);
            {
                let id = gcx.allocate_synthetic_id(gcx.package_index());
                let parameter = GenericParameterDefinition {
                    id: gcx.allocate_synthetic_id(gcx.package_index()),
                    name: gcx.intern_symbol("T"),
                    index: 0,
                    kind: GenericParameterDefinitionKind::Type { default: None },
                };
                let target = Ty::new(TyKind::Parameter(generic_parameter_marker(&parameter)), gcx);
                let generics = gcx.store.arenas.generics.alloc(Generics {
                    parent: Some(context),
                    parent_count: 0,
                    parameters: vec![parameter],
                    has_self: false,
                });
                let signature =
                    gcx.store
                        .arenas
                        .function_signatures
                        .alloc(LabeledFunctionSignature {
                            inputs: vec![LabeledFunctionParameter {
                                label: None,
                                name: gcx.intern_symbol("self"),
                                ty: Ty::new(TyKind::Reference(erased), gcx),
                                default_provider: None,
                            }],
                            output: Ty::new(TyKind::Reference(target), gcx),
                            abi: None,
                            is_variadic: false,
                        });
                let original = SyntheticDefinition {
                    kind: SyntheticDefinitionKind::ErasedPayloadReference { context },
                    name: gcx.intern_symbol("$erased_payload_reference"),
                    generics,
                    signature,
                    span,
                };
                gcx.register_synthetic_definition(id, original.clone());
                assert!(projection_signature(gcx, id).is_some());
                let database = gcx.with_session_type_database(|database| database.clone());
                crate::metadata::declarations::validate_erased_access(
                    gcx,
                    &database,
                    &[(id, original.clone())],
                    None,
                )
                .unwrap();
                for output in [
                    gcx.types.int,
                    Ty::new(TyKind::Reference(gcx.types.int), gcx),
                ] {
                    let signature =
                        gcx.store
                            .arenas
                            .function_signatures
                            .alloc(LabeledFunctionSignature {
                                output,
                                ..signature.clone()
                            });
                    let bad = SyntheticDefinition {
                        signature,
                        ..original.clone()
                    };
                    gcx.store
                        .synthetic_definitions
                        .borrow_mut()
                        .insert(id, bad.clone());
                    assert!(projection_signature(gcx, id).is_none());
                    assert!(
                        crate::metadata::declarations::validate_erased_access(
                            gcx,
                            &database,
                            &[(id, bad)],
                            None
                        )
                        .is_err()
                    );
                }
                gcx.store.synthetic_definitions.borrow_mut().insert(
                    id,
                    SyntheticDefinition {
                        kind: SyntheticDefinitionKind::Ordinary,
                        ..original
                    },
                );
                assert!(
                    projection_signature(gcx, id).is_none(),
                    "name and signature alone never grant authority"
                );
            }
        });
    }
}

#[cfg(test)]
mod opened_default_tests {
    use super::*;
    use crate::sema::models::{LabeledFunctionSignature, SyntheticDefinition};

    #[test]
    fn opened_default_metadata_preserves_provider_output_and_shared_input() {
        crate::test_support::analyze_script(
            r#"
interface P {}
type Width[T] = usize
func context[T: P](_ value: &T, _ size: Width[T] = 0) -> usize { size }
func main() {}
"#,
            |package, gcx| {
                let source = package
                    .root
                    .declarations
                    .iter()
                    .find(|item| item.identifier.symbol.as_str() == "context")
                    .unwrap()
                    .id;
                let provider = gcx.get_signature(source).inputs[1]
                    .default_provider
                    .unwrap();
                let helper = gcx.erased_default(source, provider, 0);
                let original = gcx.store.synthetic_definitions.borrow()[&helper].clone();
                let database = gcx.with_session_type_database(|database| database.clone());
                validate_opened_defaults(gcx, &database, &[(helper, original.clone())]).unwrap();
                let signature = original.signature;
                let TyKind::Reference(target) = signature.inputs[0].ty.kind() else {
                    unreachable!()
                };
                let mut inputs = signature.inputs.clone();
                inputs[0].ty = target;
                for changed in [
                    LabeledFunctionSignature {
                        inputs,
                        ..signature.clone()
                    },
                    LabeledFunctionSignature {
                        output: gcx.types.bool,
                        ..signature.clone()
                    },
                ] {
                    let signature = gcx.store.arenas.function_signatures.alloc(changed);
                    let bad = SyntheticDefinition {
                        signature,
                        ..original.clone()
                    };
                    assert!(validate_opened_defaults(gcx, &database, &[(helper, bad)]).is_err());
                }
            },
        );
    }
}

#[cfg(test)]
mod async_self_metadata_tests {
    #[test]
    fn async_self_metadata_keeps_target_arguments_and_boxed_ready_shape() {
        crate::test_support::analyze_native_class_fixture(
            r#"
interface Duplicate { func duplicate(_ count: int32 = 7) async -> Self; }
struct Counter { value: int32 }
conform Counter to Duplicate { func duplicate(_ count: int32 = 7) async -> Self { Counter { value: self.value } }; }
func main() async {
    var value: any Duplicate = Counter { value: 7 }
    var next: any Duplicate = await value.duplicate()
}
"#,
            &[],
            &[],
            |_, _, gcx| {
                let database = gcx
                    .store
                    .type_databases
                    .borrow()
                    .get(&gcx.package_index())
                    .unwrap()
                    .clone();
                let definitions: Vec<_> = gcx
                    .store
                    .synthetic_definitions
                    .borrow()
                    .iter()
                    .map(|(id, definition)| (*id, definition.clone()))
                    .collect();
                super::validate_async_self(gcx, &database, &definitions).unwrap();
                let mut missing = database.clone();
                missing.erased_async_self_arguments.clear();
                assert!(super::validate_async_self(gcx, &missing, &definitions).is_err());
                let mut wrong = definitions.clone();
                let (_, definition) = wrong
                    .iter_mut()
                    .find(|(_, definition)| {
                        matches!(
                            definition.kind,
                            crate::sema::models::SyntheticDefinitionKind::ErasedAsyncSelf { .. }
                        )
                    })
                    .unwrap();
                let mut signature = definition.signature.clone();
                signature.output = gcx.types.int32;
                definition.signature = gcx.store.arenas.function_signatures.alloc(signature);
                assert!(super::validate_async_self(gcx, &database, &wrong).is_err());
            },
        );
    }
}
