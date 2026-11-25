use crate::{
    compile::context::Gcx,
    sema::{
        models::{
            AliasKind, ConformanceRecord, ConformanceWitness, GenericArguments, GenericParameter,
            InferTy, InterfaceGoal, InterfaceMethodRequirement, InterfacePropertyRequirement,
            MethodImplementation, MethodWitness, SelectionError, SelectionMode,
            SyntheticMethodKind, Ty, TyKind,
        },
        resolve::models::TypeHead,
        tycheck::{
            fold::{TypeFoldable, TypeFolder, TypeSuperFoldable},
            infer::InferCtx,
            utils::{
                ParamEnv, generics::GenericsBuilder, instantiate::instantiate_ty_with_args,
                normalize_aliases, normalize_ty, type_head_from_value_ty, unify::TypeUnifier,
            },
        },
    },
};
use rustc_hash::{FxHashMap, FxHashSet};
use std::rc::Rc;

use super::{canonical::goal_key, select::select_interface_impl};

pub(super) fn build_conformance_witness<'ctx>(
    gcx: Gcx<'ctx>,
    goal: InterfaceGoal<'ctx>,
    mode: SelectionMode,
) -> Result<ConformanceWitness<'ctx>, SelectionError<'ctx>> {
    let key = goal_key(gcx, goal, mode);
    if let Some(cached) = gcx.get_witness_cache(gcx.package_index(), key) {
        return Ok(cached);
    }

    let selection = select_interface_impl(gcx, goal, mode);
    let witness = match selection {
        crate::sema::models::SelectionResult::Selected(selected) => match selected.source {
            crate::sema::models::CandidateSource::Impl(record_id) => {
                let Some(record) = gcx.conformance_record(record_id) else {
                    return Err(SelectionError::NoCandidates(goal));
                };
                let owner = record
                    .interface
                    .self_ty()
                    .map(|ty| instantiate_ty_with_args(gcx, ty, selected.subst))
                    .filter(|ty| gcx.is_class_type(*ty))
                    .unwrap_or(goal.self_ty);
                let Some(type_head) = type_head_from_value_ty(normalize_aliases(gcx, owner))
                    .or_else(|| record.target.is_blanket().then_some(record.target))
                else {
                    return Err(SelectionError::NoCandidates(goal));
                };
                build_witness_from_record(gcx, type_head, &record, selected.subst)?
            }
            crate::sema::models::CandidateSource::BuiltinTuple => ConformanceWitness::default(),
            crate::sema::models::CandidateSource::BuiltinTupleConformance => {
                build_builtin_tuple_conformance_witness(gcx, goal)?
            }
            crate::sema::models::CandidateSource::BuiltinCallable => {
                build_callable_witness(gcx, goal)?
            }
            crate::sema::models::CandidateSource::BuiltinClone => {
                build_builtin_clone_witness(gcx, goal)?
            }
            crate::sema::models::CandidateSource::BuiltinOperator => {
                let item = crate::mir::primitive_operators::item_for_goal(gcx, goal)
                    .ok_or(SelectionError::NoCandidates(goal))?;
                let helper = crate::mir::primitive_operators::declaration(
                    gcx,
                    item,
                    gcx.definition_ident(goal.interface_id).span,
                );
                let receiver = normalize_aliases(gcx, goal.self_ty);
                let operand = match receiver.kind() {
                    TyKind::Reference(inner) => inner,
                    _ => receiver,
                };
                let args = gcx
                    .store
                    .interners
                    .intern_generic_args(vec![crate::sema::models::GenericArgument::Type(operand)]);
                let mut witness = ConformanceWitness::default();
                if let Some(requirements) = gcx.get_interface_requirements(goal.interface_id) {
                    for output in &requirements.types {
                        if gcx.symbol_eq(output.name, "Output") {
                            witness.type_witnesses.insert(output.id, operand);
                        }
                    }
                    for method in &requirements.methods {
                        witness.method_witnesses.insert(
                            method.id,
                            MethodWitness {
                                implementation: MethodImplementation::Concrete(helper),
                                args_template: args,
                            },
                        );
                    }
                }
                witness
            }
            crate::sema::models::CandidateSource::BuiltinAnyObject
            | crate::sema::models::CandidateSource::ParamEnv => {
                let Some(reqs) = gcx.get_interface_requirements(goal.interface_id) else {
                    return Ok(ConformanceWitness::default());
                };
                if reqs.methods.is_empty() && reqs.types.is_empty() && reqs.constants.is_empty() {
                    ConformanceWitness::default()
                } else {
                    return Err(SelectionError::NoCandidates(goal));
                }
            }
        },
        crate::sema::models::SelectionResult::Ambiguous(_) => {
            return Err(SelectionError::Ambiguous(goal));
        }
        crate::sema::models::SelectionResult::NoSolution(errors) => {
            return Err(errors
                .into_iter()
                .next()
                .unwrap_or(SelectionError::NoCandidates(goal)));
        }
    };

    if !goal_bindings_satisfied(gcx, goal, &witness) {
        return Err(SelectionError::NoCandidates(goal));
    }

    gcx.put_witness_cache(gcx.package_index(), key, witness.clone());
    Ok(witness)
}

/// Resolve a strict ancestor using the already-fixed interface arguments.
/// Recursion always moves up the class chain; a distinct instantiation has no
/// inherited witness to customize. Blanket implementations are not adoptions.
pub(crate) fn inherited_class_witness<'ctx>(
    gcx: Gcx<'ctx>,
    record: &ConformanceRecord<'ctx>,
    subst: GenericArguments<'ctx>,
) -> Option<ConformanceWitness<'ctx>> {
    let goal = inherited_class_goal(gcx, record, subst)?;
    build_conformance_witness(gcx, goal, SelectionMode::Typecheck).ok()
}

pub(crate) fn inherited_class_goal<'ctx>(
    gcx: Gcx<'ctx>,
    record: &ConformanceRecord<'ctx>,
    subst: GenericArguments<'ctx>,
) -> Option<InterfaceGoal<'ctx>> {
    if record.target.is_blanket() {
        return None;
    }
    let interface = crate::sema::tycheck::utils::instantiate::instantiate_interface_ref_with_args(
        gcx,
        record.interface,
        subst,
    );
    let base = gcx.class_base(interface.self_ty()?)?;
    let assumptions: Vec<_> =
        crate::sema::tycheck::constraints::canonical_constraints_of(gcx, record.extension)
            .into_iter()
            .map(|constraint| {
                crate::sema::tycheck::utils::instantiate::instantiate_constraint_with_args(
                    gcx,
                    constraint.value,
                    subst,
                )
            })
            .collect();
    let goal = InterfaceGoal {
        interface_id: interface.id,
        self_ty: base,
        interface_args: gcx
            .store
            .interners
            .intern_generic_args_slice(&interface.arguments[1..]),
        bindings: &[],
        param_env: gcx.store.arenas.global.alloc_slice_copy(&assumptions),
    };
    let crate::sema::models::SelectionResult::Selected(selected) =
        select_interface_impl(gcx, goal, SelectionMode::Typecheck)
    else {
        return None;
    };
    let crate::sema::models::CandidateSource::Impl(id) = selected.source else {
        return None;
    };
    if gcx.conformance_record(id)?.target.is_blanket() {
        return None;
    }
    Some(goal)
}

/// Resolve associated bindings independently of method witnesses so forwarders
/// can check a projected parameter or result before publishing their bodies.
pub(crate) fn associated_type_witnesses<'ctx>(
    gcx: Gcx<'ctx>,
    type_head: TypeHead,
    record: &ConformanceRecord<'ctx>,
    subst: GenericArguments<'ctx>,
    requirements: &crate::sema::models::InterfaceRequirements<'ctx>,
) -> Result<FxHashMap<crate::hir::DefinitionID, Ty<'ctx>>, SelectionError<'ctx>> {
    let mut bindings = FxHashMap::default();
    let inherited = inherited_class_witness(gcx, record, subst);
    for assoc in &requirements.types {
        let explicit = find_explicit_type_witness(gcx, type_head, assoc.name, record)
            .map(|ty| instantiate_ty_with_args(gcx, ty, subst));
        let base = inherited
            .as_ref()
            .and_then(|witness| witness.type_witnesses.get(&assoc.id))
            .copied();
        if let (Some(actual), Some(expected)) = (explicit, base) {
            if normalize_aliases(gcx, actual) != normalize_aliases(gcx, expected) {
                gcx.dcx().emit_error("a subclass conformance override cannot change inherited associated type bindings".into(), Some(record.location));
                return Err(SelectionError::NoCandidates(interface_goal_from_record(
                    gcx, record,
                )));
            }
        }
        let Some(ty) = explicit.or(base).or_else(|| {
            // Defaults belong to the interface, not the implementing block.
            // Resolve Self and interface parameters at this declaration once;
            // descendants inherit the resulting binding unchanged.
            assoc.default_type.map(|ty| {
                let ty = instantiate_ty_with_args(gcx, ty, record.interface.arguments);
                instantiate_ty_with_args(gcx, ty, subst)
            })
        }) else {
            return Err(SelectionError::NoCandidates(interface_goal_from_record(
                gcx, record,
            )));
        };
        bindings.insert(assoc.id, ty);
    }

    // Resolve dependencies between associated defaults/bindings once, in the
    // selected conformance's coordinates. This also diagnoses unused cycles.
    let types = bindings.clone();
    for (id, ty) in &types {
        bindings.insert(
            *id,
            substitute_projection_witnesses(gcx, *ty, &types, record, subst),
        );
    }

    Ok(bindings)
}

fn build_witness_from_record<'ctx>(
    gcx: Gcx<'ctx>,
    type_head: TypeHead,
    record: &ConformanceRecord<'ctx>,
    subst: GenericArguments<'ctx>,
) -> Result<ConformanceWitness<'ctx>, SelectionError<'ctx>> {
    let interface_id = record.interface.id;
    let Some(requirements) = gcx.get_interface_requirements(interface_id) else {
        return Ok(ConformanceWitness::default());
    };

    let mut witness = ConformanceWitness::default();
    witness.extension_id = Some(record.extension);

    witness.type_witnesses =
        associated_type_witnesses(gcx, type_head, record, subst, requirements)?;

    for property in &requirements.properties {
        let Some(entries) = find_property_witnesses(
            gcx,
            type_head,
            property,
            record,
            subst,
            &witness.type_witnesses,
        ) else {
            return Err(SelectionError::NoCandidates(interface_goal_from_record(
                gcx, record,
            )));
        };
        witness.method_witnesses.extend(entries);
    }

    for method in &requirements.methods {
        if witness.method_witnesses.contains_key(&method.id) {
            continue;
        }
        let Some(entry) = find_method_witness(
            gcx,
            type_head,
            method,
            record,
            subst,
            &witness.type_witnesses,
        ) else {
            return Err(SelectionError::NoCandidates(interface_goal_from_record(
                gcx, record,
            )));
        };
        witness.method_witnesses.insert(method.id, entry);
    }

    for constant in &requirements.constants {
        let Some(id) = find_constant_witness(
            gcx,
            type_head,
            constant.id,
            constant.name,
            constant.ty,
            constant.has_default,
            record,
            subst,
            &witness.type_witnesses,
        ) else {
            return Err(SelectionError::NoCandidates(interface_goal_from_record(
                gcx, record,
            )));
        };
        witness.constant_witnesses.insert(constant.id, id);
    }

    // Extra capabilities are allowed on an implementation of a native
    // requirement. Unrelated index overloads still belong in `extend`.
    let native_declarations = gcx.with_type_database(record.extension.package(), |db| {
        db.native_subscripts
            .iter()
            .filter_map(|(&id, &entry)| {
                (gcx.definition_parent(id) == Some(record.extension)).then_some((id, entry))
            })
            .collect::<Vec<_>>()
    });
    for (id, mut entry) in native_declarations {
        if let Some(class) = record
            .interface
            .self_ty()
            .filter(|ty| gcx.is_class_type(*ty))
            && let Some((_, effective)) = gcx
                .class_subscripts(class)
                .into_iter()
                .find(|(declaration, _)| *declaration == id)
        {
            entry = effective;
        }
        if !witness.method_witnesses.values().any(|method| {
            method
                .implementation
                .impl_id()
                .is_some_and(|id| [entry.getter, entry.setter, entry.address].contains(&Some(id)))
        }) {
            return Err(SelectionError::NoCandidates(interface_goal_from_record(
                gcx, record,
            )));
        }
    }
    Ok(witness)
}

/// A class receives an object handle by value. Only directly Self-returning
/// defaults need a conditional promise: their result must retain the actual
/// dynamic class when the adopting class can have descendants.
pub(crate) fn validate_class_default_adoptions(gcx: Gcx<'_>) -> crate::error::CompileResult<()> {
    for record in gcx.all_conformance_records(gcx.package_index()) {
        let Some(class) = record.interface.self_ty() else {
            continue;
        };
        if !gcx.class_info(class).is_some_and(|info| !info.is_final) {
            continue;
        }
        let Ok(witness) =
            build_witness_from_record(gcx, record.target, &record, GenericArguments::empty())
        else {
            continue;
        };
        for (requirement, method) in witness.method_witnesses {
            if normalize_aliases(gcx, gcx.get_signature(requirement).output)
                != gcx.types.self_type_parameter
            {
                continue;
            }
            let source = match method.implementation {
                MethodImplementation::Default(source) => Some(source),
                MethodImplementation::Concrete(source) => {
                    gcx.class_default_source(source).or_else(|| {
                        crate::mir::analysis::class_self::conditional_receiver_owner(gcx, source)
                            .map(|_| source)
                    })
                }
                _ => None,
            };
            if let Some(source) = source
                && !gcx
                    .class_default_contract(source)
                    .is_some_and(|proof| proof.preserves_dynamic_self == Some(true))
            {
                gcx.dcx().emit_error("a non-final class Self witness requires a checked subclass-preserving implementation".into(), Some(record.location));
            }
        }
    }
    gcx.dcx().ok()
}

/// A universal implementation's result may happen to equal its receiver type
/// without promising dynamic Self (for example an explicit Rhs = T). Only a
/// body actually selected for a directly Self-returning requirement inherits
/// the subclass-preservation obligation.
pub(crate) fn class_receiver_requires_dynamic_self(
    gcx: Gcx<'_>,
    implementation: crate::hir::DefinitionID,
) -> bool {
    let Some(parent) = gcx.definition_parent(implementation) else {
        return false;
    };
    if gcx.try_definition_kind(parent) == Some(crate::hir::DefinitionKind::Interface) {
        return normalize_aliases(gcx, gcx.get_signature(implementation).output)
            == gcx.types.self_type_parameter;
    }
    gcx.conformance_records_for_extension(parent.package(), parent)
        .into_iter()
        .any(|record| {
            build_witness_from_record(gcx, record.target, &record, GenericArguments::empty())
                .is_ok_and(|witness| {
                    witness
                        .method_witnesses
                        .iter()
                        .any(|(requirement, method)| {
                            method.implementation.impl_id() == Some(implementation)
                                && normalize_aliases(gcx, gcx.get_signature(*requirement).output)
                                    == gcx.types.self_type_parameter
                        })
                })
        })
}

fn find_property_witnesses<'ctx>(
    gcx: Gcx<'ctx>,
    type_head: TypeHead,
    requirement: &InterfacePropertyRequirement<'ctx>,
    record: &ConformanceRecord<'ctx>,
    subst: GenericArguments<'ctx>,
    type_witnesses: &FxHashMap<crate::hir::DefinitionID, Ty<'ctx>>,
) -> Option<Vec<(crate::hir::DefinitionID, MethodWitness<'ctx>)>> {
    let explicit = gcx
        .lookup_interface_computed_properties(type_head, record.interface.id, requirement.name)
        .into_iter()
        .chain(gcx.lookup_interface_computed_properties(
            record.target,
            record.interface.id,
            requirement.name,
        ))
        .find(|entry| gcx.definition_parent(entry.property_id) == Some(record.extension));

    if explicit.is_none() {
        if let Some(witness) = inherited_class_witness(gcx, record, subst) {
            let entries = vec![(
                requirement.getter_id,
                *witness.method_witnesses.get(&requirement.getter_id)?,
            )];
            return Some(entries);
        }
    }

    let inherent = gcx
        .lookup_computed_property(type_head, requirement.name)
        .filter(|source| gcx.is_visibility_allowed(source.visibility, record.extension));

    let mut out = Vec::with_capacity(1);
    out.push((
        requirement.getter_id,
        find_property_accessor_witness(
            gcx,
            type_head,
            requirement,
            explicit,
            inherent,
            record,
            subst,
            type_witnesses,
        )?,
    ));
    Some(out)
}

pub(crate) fn property_requirement_satisfied<'ctx>(
    gcx: Gcx<'ctx>,
    type_head: TypeHead,
    requirement: &InterfacePropertyRequirement<'ctx>,
    record: &ConformanceRecord<'ctx>,
) -> bool {
    find_property_witnesses(
        gcx,
        type_head,
        requirement,
        record,
        GenericArguments::empty(),
        &FxHashMap::default(),
    )
    .is_some()
}

fn find_property_accessor_witness<'ctx>(
    gcx: Gcx<'ctx>,
    type_head: TypeHead,
    requirement: &InterfacePropertyRequirement<'ctx>,
    explicit: Option<crate::compile::context::ComputedPropertyEntry<'ctx>>,
    inherent: Option<crate::compile::context::ComputedPropertyEntry<'ctx>>,
    record: &ConformanceRecord<'ctx>,
    subst: GenericArguments<'ctx>,
    type_witnesses: &FxHashMap<crate::hir::DefinitionID, Ty<'ctx>>,
) -> Option<MethodWitness<'ctx>> {
    let requirement_id = requirement.getter_id;

    for source in [explicit, inherent].into_iter().flatten() {
        let implementation_id = source.getter_id;
        if let Some(witness) = direct_accessor_witness(
            gcx,
            requirement_id,
            implementation_id,
            record,
            subst,
            type_witnesses,
        ) {
            return Some(witness);
        }
    }

    stored_field_property_accessor_witness(
        gcx,
        type_head,
        requirement,
        record,
        subst,
        type_witnesses,
    )
    .or_else(|| default_accessor_witness(gcx, requirement_id, requirement.getter_is_required))
    .or_else(|| {
        if !record.is_inline
            || ![
                crate::hir::StdItem::RawValue,
                crate::hir::StdItem::CaseIterable,
            ]
            .iter()
            .any(|item| gcx.std_item_def(*item) == Some(record.interface.id))
        {
            return None;
        }
        crate::sema::tycheck::derive::try_synthesize_method(
            gcx,
            type_head,
            record.interface.self_ty()?,
            record.interface.id,
            record.interface.arguments,
            gcx.definition_ident(requirement_id).symbol,
            requirement_id,
            GenericsBuilder::identity_for_item(gcx, requirement_id),
        )
        .map(|synthesized| synthesized.witness)
    })
}

fn default_accessor_witness<'ctx>(
    gcx: Gcx<'ctx>,
    requirement_id: crate::hir::DefinitionID,
    is_required: bool,
) -> Option<MethodWitness<'ctx>> {
    (!is_required).then(|| MethodWitness {
        implementation: MethodImplementation::Default(requirement_id),
        args_template: GenericsBuilder::identity_for_item(gcx, requirement_id),
    })
}

fn direct_accessor_witness<'ctx>(
    gcx: Gcx<'ctx>,
    requirement_id: crate::hir::DefinitionID,
    implementation_id: crate::hir::DefinitionID,
    record: &ConformanceRecord<'ctx>,
    subst: GenericArguments<'ctx>,
    type_witnesses: &FxHashMap<crate::hir::DefinitionID, Ty<'ctx>>,
) -> Option<MethodWitness<'ctx>> {
    method_signature_matches(
        gcx,
        requirement_id,
        implementation_id,
        record,
        subst,
        type_witnesses,
    )
    .then(|| MethodWitness {
        implementation: MethodImplementation::Concrete(implementation_id),
        args_template: build_method_args_template(
            gcx,
            requirement_id,
            implementation_id,
            record,
            subst,
            type_witnesses,
        ),
    })
}

fn stored_field_property_accessor_witness<'ctx>(
    gcx: Gcx<'ctx>,
    type_head: TypeHead,
    requirement: &InterfacePropertyRequirement<'ctx>,
    record: &ConformanceRecord<'ctx>,
    subst: GenericArguments<'ctx>,
    type_witnesses: &FxHashMap<crate::hir::DefinitionID, Ty<'ctx>>,
) -> Option<MethodWitness<'ctx>> {
    let TypeHead::Nominal(type_id) = type_head else {
        return None;
    };
    let struct_def = gcx.try_get_struct_definition(type_id)?;
    let (field_index, field) = struct_def
        .fields
        .iter()
        .enumerate()
        .find(|(_, field)| field.name == requirement.name)?;
    if !gcx.is_definition_visible(field.def_id, record.extension) {
        return None;
    }

    let original_self_ty = record.interface.self_ty()?;
    let self_ty = if subst.is_empty() {
        original_self_ty
    } else {
        instantiate_ty_with_args(gcx, original_self_ty, subst)
    };
    let field_ty = match self_ty.kind() {
        TyKind::Adt(_, args) => instantiate_ty_with_args(gcx, field.ty, args),
        _ => field.ty,
    };
    let mut expected_ty = instantiate_ty_with_args(gcx, requirement.ty, record.interface.arguments);
    if !subst.is_empty() {
        expected_ty = instantiate_ty_with_args(gcx, expected_ty, subst);
    }
    expected_ty = substitute_projection_witnesses(gcx, expected_ty, type_witnesses, record, subst);
    if field_ty != expected_ty {
        return None;
    }

    let mut receiver = gcx.get_signature(requirement.getter_id).inputs.first()?.ty;
    receiver = instantiate_ty_with_args(gcx, receiver, record.interface.arguments);
    if !subst.is_empty() {
        receiver = instantiate_ty_with_args(gcx, receiver, subst);
    }
    receiver = substitute_projection_witnesses(gcx, receiver, type_witnesses, record, subst);
    if normalize_aliases(gcx, receiver) != normalize_aliases(gcx, self_ty) {
        return None;
    }
    let accessor_id = requirement.getter_id;
    let synthetic_kind = SyntheticMethodKind::PropertyFieldGetter(field_index);

    Some(
        crate::sema::tycheck::derive::synthesize_property_field_accessor(
            gcx,
            type_head,
            original_self_ty,
            record.interface,
            accessor_id,
            synthetic_kind,
        ),
    )
}

fn interface_goal_from_record<'ctx>(
    gcx: Gcx<'ctx>,
    record: &ConformanceRecord<'ctx>,
) -> InterfaceGoal<'ctx> {
    record.interface.to_goal(gcx, &[]).unwrap_or_else(|| {
        record
            .interface
            .to_goal_with_self_ty(gcx, &[], gcx.types.error)
    })
}

fn goal_bindings_satisfied<'ctx>(
    gcx: Gcx<'ctx>,
    goal: InterfaceGoal<'ctx>,
    witness: &ConformanceWitness<'ctx>,
) -> bool {
    if goal.bindings.is_empty() {
        return true;
    }

    let Some(requirements) = gcx.get_interface_requirements(goal.interface_id) else {
        return false;
    };

    for binding in goal.bindings {
        let Some(assoc) = requirements
            .types
            .iter()
            .find(|assoc| assoc.name == binding.name)
        else {
            return false;
        };
        let Some(actual) = witness.type_witnesses.get(&assoc.id).copied() else {
            return false;
        };
        let local_icx = Rc::new(InferCtx::new(gcx));
        let empty_env = ParamEnv::new(Vec::new());
        let actual = normalize_ty(local_icx.clone(), actual, &empty_env);
        let expected = normalize_ty(local_icx.clone(), binding.ty, &empty_env);
        if actual == expected {
            continue;
        }

        let unifier = TypeUnifier::new(local_icx);
        if unifier.unify(actual, expected).is_err() {
            return false;
        }
    }

    true
}

fn build_builtin_clone_witness<'ctx>(
    gcx: Gcx<'ctx>,
    goal: InterfaceGoal<'ctx>,
) -> Result<ConformanceWitness<'ctx>, SelectionError<'ctx>> {
    let self_ty = normalize_aliases(gcx, goal.self_ty);
    let Some(requirements) = gcx.get_interface_requirements(goal.interface_id) else {
        return Ok(ConformanceWitness::default());
    };
    let kind = if crate::sema::impl_engine::builtin_copy_clone(gcx, self_ty) {
        crate::sema::models::SyntheticDefinitionKind::BuiltinCopyClone
    } else if matches!(self_ty.kind(), TyKind::Array { .. }) {
        crate::sema::models::SyntheticDefinitionKind::ArrayClone
    } else if matches!(self_ty.kind(), TyKind::Closure { .. }) {
        crate::sema::models::SyntheticDefinitionKind::ClosureClone
    } else {
        crate::sema::models::SyntheticDefinitionKind::TupleClone
    };
    let helper = crate::mir::copy_clone::declaration_with_kind(
        gcx,
        gcx.definition_ident(goal.interface_id).span,
        kind,
    );
    let args = gcx
        .store
        .interners
        .intern_generic_args(vec![crate::sema::models::GenericArgument::Type(self_ty)]);
    let mut witness = ConformanceWitness::default();
    for method in &requirements.methods {
        if let Some(type_head) = type_head_from_value_ty(self_ty) {
            // Preserve ordinary method discovery; this entry is not a concrete
            // implementation and THIR synthesis must not overwrite the helper.
            gcx.register_synthetic_method(
                type_head,
                method.id,
                method.name,
                crate::sema::tycheck::derive::SyntheticMethodInfo {
                    kind: SyntheticMethodKind::CopyClone,
                    self_ty,
                    interface_id: goal.interface_id,
                    interface_args: goal.interface_args,
                    interface_bindings: &[],
                    method_id: method.id,
                    method_name: method.name,
                    syn_id: Some(helper),
                },
            );
        }
        witness.method_witnesses.insert(
            method.id,
            MethodWitness {
                implementation: MethodImplementation::Concrete(helper),
                args_template: args,
            },
        );
    }
    Ok(witness)
}

fn build_builtin_tuple_conformance_witness<'ctx>(
    gcx: Gcx<'ctx>,
    goal: InterfaceGoal<'ctx>,
) -> Result<ConformanceWitness<'ctx>, SelectionError<'ctx>> {
    let self_ty = normalize_aliases(gcx, goal.self_ty);
    let item = crate::mir::tuple_conformances::CONFORMANCE_ITEMS
        .iter()
        .copied()
        .find(|&item| gcx.std_item_def(item) == Some(goal.interface_id))
        .ok_or(SelectionError::NoCandidates(goal))?;
    if !crate::mir::tuple_conformances::has_synthetic_method(item) {
        return Ok(ConformanceWitness::default());
    }
    let Some(requirements) = gcx.get_interface_requirements(goal.interface_id) else {
        return Ok(ConformanceWitness::default());
    };
    let primary_name = crate::mir::tuple_conformances::primary_method_name(item)
        .ok_or(SelectionError::NoCandidates(goal))?;
    let helper = crate::mir::tuple_conformances::declaration(
        gcx,
        item,
        gcx.definition_ident(goal.interface_id).span,
    )
    .ok_or(SelectionError::NoCandidates(goal))?;

    let mut witness = ConformanceWitness::default();
    for method in &requirements.methods {
        if gcx.symbol_eq(method.name, primary_name) {
            let mut args = vec![crate::sema::models::GenericArgument::Type(self_ty)];
            let parent_count = gcx.generics_of(method.id).parent_count;
            let identity = GenericsBuilder::identity_for_item(gcx, method.id);
            if identity.len() > parent_count {
                args.extend_from_slice(&identity[parent_count..]);
            }
            let args_template = gcx.store.interners.intern_generic_args(args);
            witness.method_witnesses.insert(
                method.id,
                MethodWitness {
                    implementation: MethodImplementation::Concrete(helper),
                    args_template,
                },
            );
        } else if !method.is_required {
            let mut args = vec![crate::sema::models::GenericArgument::Type(self_ty)];
            if crate::mir::tuple_conformances::is_rhs_parameterized(item) {
                args.push(crate::sema::models::GenericArgument::Type(self_ty));
            }
            let parent_count = gcx.generics_of(method.id).parent_count;
            let identity = GenericsBuilder::identity_for_item(gcx, method.id);
            if identity.len() > parent_count {
                args.extend_from_slice(&identity[parent_count..]);
            }
            let args_template = gcx.store.interners.intern_generic_args(args);
            witness.method_witnesses.insert(
                method.id,
                MethodWitness {
                    implementation: MethodImplementation::Default(method.id),
                    args_template,
                },
            );
        }
    }
    Ok(witness)
}

fn build_callable_witness<'ctx>(
    gcx: Gcx<'ctx>,
    goal: InterfaceGoal<'ctx>,
) -> Result<ConformanceWitness<'ctx>, SelectionError<'ctx>> {
    if matches!(goal.self_ty.kind(), TyKind::FnPointer { .. }) {
        let (kind, inputs, output) = crate::sema::models::callable_signature(goal.self_ty)
            .ok_or(SelectionError::NoCandidates(goal))?;
        let helper = crate::mir::function_pointer_call::declaration(
            gcx,
            kind,
            gcx.definition_ident(goal.interface_id).span,
        );
        let args = gcx.store.interners.intern_generic_args(vec![
            crate::sema::models::GenericArgument::Type(goal.self_ty),
            crate::sema::models::GenericArgument::Type(crate::sema::models::callable_args_ty(
                gcx, inputs,
            )),
            crate::sema::models::GenericArgument::Type(output),
        ]);
        let mut witness = ConformanceWitness::default();
        if let Some(requirements) = gcx.get_interface_requirements(goal.interface_id) {
            for method in &requirements.methods {
                witness.method_witnesses.insert(
                    method.id,
                    MethodWitness {
                        implementation: MethodImplementation::Concrete(helper),
                        args_template: args,
                    },
                );
            }
        }
        return Ok(witness);
    }
    // The adapter is registered once per closure definition, and its stored
    // signature becomes the synthesized body. It must be the final one.
    assert!(
        !goal.self_ty.has_inference_variables(),
        "callable adapter demanded for unresolved type {}",
        goal.self_ty.format(gcx)
    );
    let TypeHead::Closure(closure_def_id) =
        type_head_from_value_ty(goal.self_ty).ok_or(SelectionError::NoCandidates(goal))?
    else {
        return Err(SelectionError::NoCandidates(goal));
    };
    let _captures = gcx
        .get_closure_captures(closure_def_id)
        .ok_or(SelectionError::NoCandidates(goal))?;

    if crate::sema::models::callable_kind(gcx, goal.interface_id).is_none() {
        return Err(SelectionError::NoCandidates(goal));
    }
    let kind = SyntheticMethodKind::ClosureCall;

    let Some(requirements) = gcx.get_interface_requirements(goal.interface_id) else {
        return Ok(ConformanceWitness::default());
    };

    let interface_args = goal.to_interface_ref(gcx).arguments;
    let mut witness = ConformanceWitness::default();
    for method in &requirements.methods {
        let args_template = GenericsBuilder::identity_for_item(gcx, method.id);
        let existing = gcx.find_synthetic_method(TypeHead::Closure(closure_def_id), method.id);
        let syn_id = existing.and_then(|info| info.syn_id);
        let info = crate::sema::tycheck::derive::SyntheticMethodInfo {
            kind,
            self_ty: goal.self_ty,
            interface_id: goal.interface_id,
            interface_args,
            interface_bindings: goal.bindings,
            method_id: method.id,
            method_name: method.name,
            syn_id,
        };
        if existing.is_none() {
            gcx.register_synthetic_method(
                TypeHead::Closure(closure_def_id),
                method.id,
                method.name,
                info,
            );
        }
        witness.method_witnesses.insert(
            method.id,
            MethodWitness {
                implementation: MethodImplementation::Synthetic(kind, syn_id),
                args_template,
            },
        );
    }
    witness.extension_id = None;
    Ok(witness)
}

/// The type a conformance record gives one associated type of its interface,
/// in the record's own generic parameters: its explicit binding, or the
/// interface's default. `None` when the binding would come from a class
/// ancestor's conformance instead, which only selection can find.
pub(crate) fn record_type_witness_template<'ctx>(
    gcx: Gcx<'ctx>,
    record: &ConformanceRecord<'ctx>,
    assoc_id: crate::hir::DefinitionID,
) -> Option<Ty<'ctx>> {
    let requirements = gcx.get_interface_requirements(record.interface.id)?;
    let assoc = requirements
        .types
        .iter()
        .find(|assoc| assoc.id == assoc_id)?;
    if let Some(explicit) = find_explicit_type_witness(gcx, record.target, assoc.name, record) {
        return Some(explicit);
    }
    let target = gcx.get_impl_target_ty(record.extension)?;
    if !record.target.is_blanket() && gcx.class_base(target).is_some() {
        return None;
    }
    assoc
        .default_type
        .map(|ty| instantiate_ty_with_args(gcx, ty, record.interface.arguments))
}

fn find_explicit_type_witness<'ctx>(
    gcx: Gcx<'ctx>,
    type_head: TypeHead,
    assoc_name: crate::span::Symbol,
    record: &ConformanceRecord<'ctx>,
) -> Option<Ty<'ctx>> {
    let extension_pkg = record.extension.package();
    let alias_id = gcx.with_type_database(extension_pkg, |db| {
        [type_head, record.target].into_iter().find_map(|head| {
            db.alias_table
                .by_type
                .get(&head)
                .and_then(|bucket| bucket.aliases.get(&assoc_name))
                .and_then(|vec| {
                    vec.iter().map(|(id, _)| *id).find(|&id| {
                        db.alias_table.aliases.get(&id).map(|def| def.extension_id)
                            == Some(Some(record.extension))
                    })
                })
        })
    });

    alias_id.map(|alias_id| gcx.get_alias_type(alias_id))
}

pub(crate) fn find_method_witness<'ctx>(
    gcx: Gcx<'ctx>,
    type_head: TypeHead,
    requirement: &InterfaceMethodRequirement<'ctx>,
    record: &ConformanceRecord<'ctx>,
    subst: GenericArguments<'ctx>,
    type_witnesses: &FxHashMap<crate::hir::DefinitionID, Ty<'ctx>>,
) -> Option<MethodWitness<'ctx>> {
    let impl_id = record.extension;
    let extension_pkg = impl_id.package();
    let interface_id = record.interface.id;

    let mut candidates: Vec<crate::hir::DefinitionID> = gcx
        .with_type_database(extension_pkg, |db| {
            db.type_head_to_members
                .get(&type_head)
                .and_then(|idx| {
                    let key = (interface_id, requirement.name);
                    idx.trait_methods.get(&key)
                })
                .map(|set| {
                    set.members
                        .iter()
                        .filter(|&&id| gcx.definition_parent(id) == Some(impl_id))
                        .copied()
                        .collect()
                })
        })
        .unwrap_or_default();
    if candidates.is_empty() {
        candidates = gcx.with_type_database(extension_pkg, |db| {
            db.def_to_fn_sig
                .keys()
                .copied()
                .filter(|candidate| {
                    gcx.definition_parent(*candidate) == Some(impl_id)
                        && gcx.definition_ident(*candidate).symbol == requirement.name
                        // An adopted default is not an explicit declaration
                        // resolving another interface's competing default.
                        && !gcx.store.synthetic_definitions.borrow().get(candidate).is_some_and(|definition|
                            matches!(definition.kind, crate::sema::models::SyntheticDefinitionKind::AdoptedClassDefault { .. }))
                })
                .collect()
        });
    }

    for candidate in candidates {
        if let Some((_, required)) = gcx.native_subscript_for_accessor(requirement.id) {
            let role = if required.getter == Some(requirement.id) {
                crate::compile::context::NativeSubscriptAccess::Get
            } else if required.setter == Some(requirement.id) {
                crate::compile::context::NativeSubscriptAccess::Set
            } else {
                crate::compile::context::NativeSubscriptAccess::Address
            };
            if gcx
                .native_subscript_for_accessor(candidate)
                .is_none_or(|(_, entry)| role.method(entry) != Some(candidate))
            {
                continue;
            }
            if let Some(class) = record
                .interface
                .self_ty()
                .filter(|ty| gcx.is_class_type(*ty))
                && let TyKind::Adt(definition, _) = class.kind()
                && gcx.with_type_database(definition.id.package(), |db| {
                    db.class_subscripts.contains_key(&definition.id)
                })
                && gcx
                    .native_subscript_for_receiver(candidate, class)
                    .is_none()
            {
                continue;
            }
        }
        if method_signature_matches(
            gcx,
            requirement.id,
            candidate,
            record,
            subst,
            type_witnesses,
        ) {
            let args_template = build_method_args_template(
                gcx,
                requirement.id,
                candidate,
                record,
                subst,
                type_witnesses,
            );

            // A witness may be reconstructed while compiling a downstream
            // package from dependency metadata. Synthetic derivations live in
            // the defining package's type database, not necessarily the
            // current session database.
            if let Some(info) = gcx.find_synthetic_method(type_head, candidate) {
                return Some(MethodWitness {
                    implementation: MethodImplementation::Synthetic(info.kind, info.syn_id),
                    args_template,
                });
            }

            return Some(MethodWitness {
                implementation: MethodImplementation::Concrete(candidate),
                args_template,
            });
        }
    }

    if let Some(witness) = inherited_class_witness(gcx, record, subst)
        .and_then(|witness| witness.method_witnesses.get(&requirement.id).copied())
    {
        return Some(witness);
    }

    if !requirement.is_required {
        let adapter = gcx.with_type_database(record.extension.package(), |database| {
            database.class_adoptions.iter().find_map(|adoption| {
                let adopted = database.conformance_records.get(&adoption.conformance)?;
                (adopted.extension == record.extension && adopted.interface == record.interface)
                    .then(|| {
                        adoption
                            .methods
                            .iter()
                            .find(|method| method.requirement == requirement.id)
                            .map(|method| method.slot.implementation)
                    })
                    .flatten()
            })
        });
        if let Some(adapter) = adapter {
            return Some(MethodWitness {
                implementation: MethodImplementation::Concrete(adapter),
                args_template: build_method_args_template(
                    gcx,
                    requirement.id,
                    adapter,
                    record,
                    subst,
                    type_witnesses,
                ),
            });
        }
        let args_template = default_method_arguments(gcx, requirement.id, record, subst);
        return Some(MethodWitness {
            implementation: MethodImplementation::Default(requirement.id),
            args_template,
        });
    }

    if record.is_inline {
        let self_ty = match type_head {
            TypeHead::Nominal(id) => gcx.get_type(id),
            _ => return None,
        };

        let args_template = GenericsBuilder::identity_for_item(gcx, requirement.id);
        if let Some(synthesized) = crate::sema::tycheck::derive::try_synthesize_method(
            gcx,
            type_head,
            self_ty,
            record.interface.id,
            record.interface.arguments,
            requirement.name,
            requirement.id,
            args_template,
        ) {
            return Some(synthesized.witness);
        }
    }

    None
}

fn default_method_arguments<'ctx>(
    gcx: Gcx<'ctx>,
    method: crate::hir::DefinitionID,
    record: &ConformanceRecord<'ctx>,
    subst: GenericArguments<'ctx>,
) -> GenericArguments<'ctx> {
    let interface = crate::sema::tycheck::utils::instantiate::instantiate_interface_ref_with_args(
        gcx,
        record.interface,
        subst,
    );
    let identity = GenericsBuilder::identity_for_item(gcx, method);
    let parent_count = gcx.generics_of(method).parent_count;
    let mut arguments = interface.arguments.to_vec();
    arguments.extend_from_slice(&identity[parent_count..]);
    gcx.store.interners.intern_generic_args(arguments)
}

fn find_constant_witness<'ctx>(
    gcx: Gcx<'ctx>,
    _type_head: TypeHead,
    requirement_id: crate::hir::DefinitionID,
    requirement_name: crate::span::Symbol,
    requirement_ty: Ty<'ctx>,
    has_default: bool,
    record: &ConformanceRecord<'ctx>,
    subst: GenericArguments<'ctx>,
    type_witnesses: &FxHashMap<crate::hir::DefinitionID, Ty<'ctx>>,
) -> Option<crate::hir::DefinitionID> {
    let impl_id = record.extension;
    let extension_pkg = impl_id.package();
    let mut expected_ty = instantiate_ty_with_args(gcx, requirement_ty, record.interface.arguments);
    if !subst.is_empty() {
        expected_ty = instantiate_ty_with_args(gcx, expected_ty, subst);
    }
    let expected_ty =
        substitute_projection_witnesses(gcx, expected_ty, type_witnesses, record, subst);

    let candidates: Vec<crate::hir::DefinitionID> = gcx.with_type_database(extension_pkg, |db| {
        db.def_to_ty
            .keys()
            .copied()
            .filter(|candidate| {
                gcx.definition_kind(*candidate)
                    == crate::sema::resolve::models::DefinitionKind::AssociatedConstant
                    && gcx.definition_parent(*candidate) == Some(impl_id)
                    && gcx.definition_ident(*candidate).symbol == requirement_name
            })
            .collect()
    });

    if !candidates.is_empty() {
        return candidates.into_iter().find(|candidate| {
            let declared = instantiate_ty_with_args(gcx, gcx.get_type(*candidate), subst);
            normalize_aliases(gcx, declared) == normalize_aliases(gcx, expected_ty)
        });
    }

    if let Some(id) = inherited_class_witness(gcx, record, subst)
        .and_then(|witness| witness.constant_witnesses.get(&requirement_id).copied())
    {
        return Some(id);
    }

    if has_default {
        let reqs = gcx.get_interface_requirements(record.interface.id)?;
        return reqs
            .constants
            .iter()
            .find(|c| c.name == requirement_name)
            .map(|c| c.id);
    }

    None
}

pub(crate) fn method_signature_matches<'ctx>(
    gcx: Gcx<'ctx>,
    interface_fn_id: crate::hir::DefinitionID,
    impl_fn_id: crate::hir::DefinitionID,
    record: &ConformanceRecord<'ctx>,
    subst: GenericArguments<'ctx>,
    type_witnesses: &FxHashMap<crate::hir::DefinitionID, Ty<'ctx>>,
) -> bool {
    let interface_sig = gcx.get_signature(interface_fn_id);
    let impl_sig = gcx.get_signature(impl_fn_id);
    if gcx.definition_is_async(interface_fn_id) != gcx.definition_is_async(impl_fn_id) {
        return false;
    }
    // Safety is part of a witness's contract even though bare function types
    // do not encode it. Erasure/generic dispatch must not turn an unsafe
    // implementation into a call permitted by a safe requirement.
    if gcx.definition_is_unsafe(interface_fn_id) != gcx.definition_is_unsafe(impl_fn_id) {
        return false;
    }
    if !interface_sig.same_shape(impl_sig) {
        return false;
    }

    let interface_generics = gcx.generics_of(interface_fn_id);
    let impl_generics = gcx.generics_of(impl_fn_id);
    if interface_generics.parameters.len() != impl_generics.parameters.len() {
        return false;
    }

    let mut expected = Ty::from_labeled_signature(gcx, interface_sig);
    expected = instantiate_ty_with_args(
        gcx,
        expected,
        default_method_arguments(gcx, interface_fn_id, record, subst),
    );
    expected = normalize_aliases(gcx, expected);
    expected = substitute_projection_witnesses(gcx, expected, type_witnesses, record, subst);
    expected = normalize_aliases(gcx, expected);

    let mut actual = Ty::from_labeled_signature(gcx, impl_sig);
    if !subst.is_empty() {
        actual = instantiate_ty_with_args(gcx, actual, subst);
    }
    actual = normalize_aliases(gcx, actual);
    actual = substitute_projection_witnesses(gcx, actual, type_witnesses, record, subst);
    actual = normalize_aliases(gcx, actual);

    let mut expected_freshener = SignatureFreshener::new(gcx);
    let expected = expected_freshener.freshen(expected);

    let mut actual_freshener = SignatureFreshener::new(gcx);
    let actual = actual_freshener.freshen(actual);

    if expected != actual {
        return false;
    }
    // A witness must accept every argument allowed by the requirement. Compare
    // declared bounds in the same renamed method-parameter coordinates used
    // for the signature; a conformance may supply its own ambient bounds.
    let source_arguments = default_method_arguments(gcx, interface_fn_id, record, subst);
    let impl_arguments = build_method_args_template(
        gcx,
        interface_fn_id,
        impl_fn_id,
        record,
        subst,
        type_witnesses,
    );
    let mut permitted: FxHashSet<_> =
        crate::sema::tycheck::constraints::canonical_constraints_of(gcx, interface_fn_id)
            .into_iter()
            .map(|constraint| {
                substitute_projection_witnesses(
                    gcx,
                    normalize_aliases(
                        gcx,
                        crate::sema::tycheck::utils::instantiate::instantiate_constraint_with_args(
                            gcx,
                            constraint.value,
                            source_arguments,
                        ),
                    ),
                    type_witnesses,
                    record,
                    subst,
                )
                .fold_with(&mut expected_freshener)
            })
            .collect();
    permitted.extend(
        crate::sema::tycheck::constraints::canonical_constraints_of(gcx, record.extension)
            .into_iter()
            .map(|constraint| {
                normalize_aliases(
                    gcx,
                    crate::sema::tycheck::utils::instantiate::instantiate_constraint_with_args(
                        gcx,
                        constraint.value,
                        subst,
                    ),
                )
                .fold_with(&mut actual_freshener)
            }),
    );
    crate::sema::tycheck::constraints::canonical_constraints_of(gcx, impl_fn_id)
        .into_iter()
        .all(|constraint| {
            permitted.contains(
                &substitute_projection_witnesses(
                    gcx,
                    normalize_aliases(
                        gcx,
                        crate::sema::tycheck::utils::instantiate::instantiate_constraint_with_args(
                            gcx,
                            constraint.value,
                            impl_arguments,
                        ),
                    ),
                    type_witnesses,
                    record,
                    subst,
                )
                .fold_with(&mut actual_freshener),
            )
        })
}

fn build_method_args_template<'ctx>(
    gcx: Gcx<'ctx>,
    interface_method_id: crate::hir::DefinitionID,
    impl_method_id: crate::hir::DefinitionID,
    record: &ConformanceRecord<'ctx>,
    subst: GenericArguments<'ctx>,
    type_witnesses: &FxHashMap<crate::hir::DefinitionID, Ty<'ctx>>,
) -> GenericArguments<'ctx> {
    let _ = (interface_method_id, type_witnesses);
    let impl_generics = gcx.generics_of(impl_method_id);
    if impl_generics.is_empty() {
        return gcx.store.interners.intern_generic_args(Vec::new());
    }
    let identity = GenericsBuilder::identity_for_item(gcx, impl_method_id);
    if subst.is_empty() {
        return identity;
    }

    // Method generic args include parent impl params first. Substitute those
    // with the selected impl substitution so post-mono normalization sees only
    // concrete impl arguments.
    let mut args: Vec<_> = identity.iter().copied().collect();
    let owner_generics = gcx.generics_of(record.extension);
    for param in &owner_generics.parameters {
        let index = param.index as usize;
        if let Some(arg) = subst.get(index).copied() {
            if index < args.len() {
                args[index] = arg;
            }
        }
    }

    gcx.store.interners.intern_generic_args(args)
}

pub(crate) fn substitute_projection_witnesses<'ctx, T: TypeFoldable<'ctx>>(
    gcx: Gcx<'ctx>,
    ty: T,
    type_witnesses: &FxHashMap<crate::hir::DefinitionID, Ty<'ctx>>,
    record: &ConformanceRecord<'ctx>,
    subst: GenericArguments<'ctx>,
) -> T {
    let Some(self_ty) = record.interface.self_ty() else {
        return ty;
    };
    let self_ty = normalize_aliases(gcx, instantiate_ty_with_args(gcx, self_ty, subst));
    let mut substitutor = ProjectionSubstitutor {
        gcx,
        type_witnesses,
        self_ty,
        record,
        subst,
        active: FxHashSet::default(),
    };
    ty.fold_with(&mut substitutor)
}

struct ProjectionSubstitutor<'ctx, 'w> {
    gcx: Gcx<'ctx>,
    type_witnesses: &'w FxHashMap<crate::hir::DefinitionID, Ty<'ctx>>,
    self_ty: Ty<'ctx>,
    record: &'w ConformanceRecord<'ctx>,
    subst: GenericArguments<'ctx>,
    active: FxHashSet<Ty<'ctx>>,
}

impl<'ctx> TypeFolder<'ctx> for ProjectionSubstitutor<'ctx, '_> {
    fn gcx(&self) -> Gcx<'ctx> {
        self.gcx
    }

    fn fold_ty(&mut self, ty: Ty<'ctx>) -> Ty<'ctx> {
        match ty.kind() {
            TyKind::Alias {
                kind: AliasKind::Projection,
                def_id,
                args,
            } => {
                // Witnesses apply to this conformance's Self, not another
                // generic value conforming to the same interface. In particular
                // Value = Source::Value must not substitute itself forever.
                let is_self_projection = matches!(args.first(), Some(crate::sema::models::GenericArgument::Type(source)) if normalize_aliases(self.gcx, *source) == self.self_ty);
                if is_self_projection {
                    if !self.active.insert(ty) {
                        self.gcx.dcx().emit_error(
                            "cyclic associated type bindings have no concrete witness".into(),
                            Some(self.record.location),
                        );
                        return Ty::error(self.gcx);
                    }
                    let witness_ty = self.type_witnesses.get(&def_id).copied().or_else(|| {
                        // A requirement on a subinterface can mention a type
                        // declared by its superinterface.
                        // Its witness belongs to that exact super-conformance,
                        // not this record's local associated-type declarations.
                        // Normalize the full projection arguments instead of
                        // merging maps keyed only by the associated type's ID:
                        // Read[int] and Read[bool] may resolve different Outputs.
                        if self.gcx.definition_parent(def_id) == Some(self.record.interface.id)
                            || crate::sema::tycheck::utils::unresolved::ty_contains_unresolved_inference(ty)
                        {
                            return None;
                        }
                        let constraints = crate::sema::tycheck::constraints::canonical_constraints_of(self.gcx, self.record.extension)
                            .into_iter()
                            .map(|constraint| crate::sema::tycheck::utils::instantiate::instantiate_constraint_with_args(self.gcx, constraint.value, self.subst))
                            .collect();
                        let env = ParamEnv::new(constraints);
                        let resolved = normalize_ty(Rc::new(InferCtx::new(self.gcx)), ty, &env);
                        (resolved != ty).then_some(resolved)
                    });
                    let result = witness_ty.map(|witness_ty| witness_ty.fold_with(self));
                    self.active.remove(&ty);
                    if let Some(result) = result {
                        return result;
                    }
                }
                ty.super_fold_with(self)
            }
            _ => ty.super_fold_with(self),
        }
    }
}

pub(crate) struct SignatureFreshener<'ctx> {
    next_var_id: u32,
    substitutions: FxHashMap<GenericParameter, u32>,
    const_substitutions: FxHashMap<GenericParameter, u32>,
    gcx: Gcx<'ctx>,
}

impl<'ctx> SignatureFreshener<'ctx> {
    pub(crate) fn new(gcx: Gcx<'ctx>) -> Self {
        Self {
            next_var_id: 0,
            substitutions: FxHashMap::default(),
            const_substitutions: FxHashMap::default(),
            gcx,
        }
    }

    fn fresh_var(&mut self) -> u32 {
        let var = self.next_var_id;
        self.next_var_id += 1;
        var
    }

    pub(crate) fn freshen(&mut self, ty: Ty<'ctx>) -> Ty<'ctx> {
        ty.fold_with(self)
    }
}

impl<'ctx> TypeFolder<'ctx> for SignatureFreshener<'ctx> {
    fn gcx(&self) -> Gcx<'ctx> {
        self.gcx
    }

    fn fold_const(
        &mut self,
        value: crate::sema::models::Const<'ctx>,
    ) -> crate::sema::models::Const<'ctx> {
        use crate::sema::models::{Const, ConstKind};
        let ConstKind::Param(parameter) = value.kind else {
            return Const {
                ty: value.ty.fold_with(self),
                kind: value.kind,
            };
        };
        let fresh = if let Some(&fresh) = self.const_substitutions.get(&parameter) {
            fresh
        } else {
            let fresh = self.fresh_var();
            self.const_substitutions.insert(parameter, fresh);
            fresh
        };
        Const {
            ty: value.ty.fold_with(self),
            // A reserved marker cannot alias a real inference variable or
            // literal value while comparing two declaration signatures.
            kind: ConstKind::Param(GenericParameter {
                index: fresh as usize,
                name: self.gcx.intern_symbol("$canonical_const"),
            }),
        }
    }

    fn fold_ty(&mut self, ty: Ty<'ctx>) -> Ty<'ctx> {
        match ty.kind() {
            TyKind::Parameter(param) => {
                let fresh = if let Some(&fresh) = self.substitutions.get(&param) {
                    fresh
                } else {
                    let fresh = self.fresh_var();
                    self.substitutions.insert(param, fresh);
                    fresh
                };
                Ty::new(TyKind::Infer(InferTy::FreshTy(fresh)), self.gcx)
            }
            _ => ty.super_fold_with(self),
        }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn signature_freshening_renames_const_parameters_without_losing_relationships() {
        crate::test_support::analyze_script(
            "struct Shape[const N: usize, const M: usize] { first: [int32; N]; second: [int32; M] }\nfunc main() {}",
            |package, gcx| {
                let fields = gcx
                    .get_struct_definition(package.root.declarations[0].id)
                    .fields;
                let function = |input, output| {
                    crate::sema::models::Ty::new(
                        crate::sema::models::TyKind::FnPointer {
                            inputs: gcx.store.interners.intern_ty_list(vec![input]),
                            output,
                            effects: Default::default(),
                        },
                        gcx,
                    )
                };
                let canonical = |ty| super::SignatureFreshener::new(gcx).freshen(ty);
                let left = canonical(function(fields[0].ty, fields[0].ty));
                assert_eq!(left, canonical(function(fields[1].ty, fields[1].ty)));
                assert_ne!(left, canonical(function(fields[0].ty, fields[1].ty)));
            },
        );
    }

    #[test]
    fn inherited_associated_outputs_match_the_selected_superinterface_instantiation() {
        let diagnostics = crate::test_support::analyze_script_mir_diagnostics(
            "interface Read[I] { type Output; func read(_ index: I) -> &Self::Output; }\ninterface Write[I]: Read[I] { func write(_ index: I) -> &Self::Output; }\nstruct Counter { value: int32 }\nconform Counter to Read[int32] { type Output = int32; func read(_ index: int32) -> &int32 { &self.value }\n}\nconform Counter to Write[int32] { func write(_ index: int32) -> &int32 { &self.value }\n}\nfunc main() { var counter = Counter { value: 7 }; *counter.write(0_i32) = 9_i32 }",
        );
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }

    #[test]
    fn inherited_outputs_keep_generic_superinterface_arguments_distinct() {
        let prefix = "interface Read[I] { type Output; func read(_ index: I) -> &Self::Output; }\ninterface Write[I]: Read[I] { func write(_ index: I) -> &Self::Output; }\nstruct Counter { number: int32; flag: bool }\nconform Counter to Read[int32] { type Output = int32; func read(_ index: int32) -> &int32 { &self.number }\n}\nconform Counter to Read[bool] { type Output = bool; func read(_ index: bool) -> &bool { &self.flag }\n}\nconform Counter to Write[int32] { func write(_ index: int32) -> &int32 { &self.number }\n}\n";
        let valid = format!(
            "{prefix}conform Counter to Write[bool] {{ func write(_ index: bool) -> &bool {{ &self.flag }}\n}}\nfunc main() {{ var counter = Counter {{ number: 1, flag: false }}; *counter.write(true) = true; *counter.write(0_i32) = 7_i32 }}"
        );
        let diagnostics = crate::test_support::analyze_script_mir_diagnostics(&valid);
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
        let invalid = format!(
            "{prefix}conform Counter to Write[bool] {{ func write(_ index: bool) -> &int32 {{ &self.number }}\n}}\nfunc main() {{}}"
        );
        let diagnostics = crate::test_support::analyze_script_diagnostics(&invalid);
        assert!(
            diagnostics.iter().any(|diagnostic| diagnostic
                .message
                .contains("missing required method 'write'")),
            "{diagnostics:#?}"
        );
    }

    #[test]
    fn inherited_output_resolution_preserves_conditional_impl_bounds() {
        let diagnostics = crate::test_support::analyze_script_mir_diagnostics(
            "interface Tagged {}\ninterface Read[I] { type Output; func read(_ index: I) -> &Self::Output; }\ninterface Write[I]: Read[I] { func write(_ index: I) -> &Self::Output; }\nstruct Container[T] { value: T }\nconform[T: Tagged] Container[T] to Read[int32] { type Output = T; func read(_ index: int32) -> &T { &self.value }\n}\nconform[T: Tagged] Container[T] to Write[int32] { func write(_ index: int32) -> &T { &self.value }\n}\nfunc edit[T: Tagged](_ value: &Container[T]) -> &T { value.write(0_i32) }\nfunc main() {}",
        );
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }

    #[test]
    fn shared_implementation_can_satisfy_an_exclusive_receiver_requirement() {
        let diagnostics = crate::test_support::analyze_script_mir_diagnostics(
            "interface Inspect { func inspect() -> int32; }\nstruct Counter { value: int32 }\nconform Counter to Inspect { func inspect() -> int32 { self.value }\n}\nfunc inspect[T: Inspect](_ value: &T) -> int32 { value.inspect() }\nfunc main() { direct := Counter { value: 5 }; shared := direct.inspect(); var value = Counter { value: 7 }; observed := inspect(&value); var erased: any Inspect = value; other := erased.inspect() }",
        );
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }

    #[test]
    fn witnesses_require_matching_explicit_parameters() {
        for (requirement, implementation) in [
            (
                "func inspect(other: &int32)",
                "func inspect(other: int32) {}",
            ),
            (
                "static func inspect(_ value: &Self)",
                "static func inspect(_ value: Self) {}",
            ),
        ] {
            let source = format!(
                "interface Inspect {{ {requirement}; }}\nstruct Counter {{ value: int32 }}\nconform Counter to Inspect {{ {implementation}\n}}\nfunc main() {{}}"
            );
            let diagnostics = crate::test_support::analyze_script_diagnostics(&source);
            assert!(
                diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.message.contains("missing required method")),
                "{source}\n{diagnostics:#?}"
            );
        }
    }

    #[test]
    fn conformance_substitutes_interface_const_parameters() {
        let diagnostics = crate::test_support::analyze_script_diagnostics(
            r#"
interface Fixed[const N: usize] {
    func consume(_ values: [int32; N])
}
struct Consumer {}
conform Consumer to Fixed[2] {
    func consume(_ values: [int32; 2]) {}
}
func main() {}
"#,
        );
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
    }
    #[test]
    fn mismatched_method_reports_missing_requirement_without_panicking() {
        let diagnostics = crate::test_support::analyze_script_diagnostics(
            r#"
interface Value {
    func consume(_ value: int32)
}
struct Consumer {}
conform Consumer to Value {
    func consume(_ value: bool) {}
}
func main() {}
"#,
        );
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message.contains("does not satisfy requirements")),
            "{diagnostics:?}"
        );
        assert!(
            diagnostics.iter().any(|diagnostic| diagnostic
                .message
                .contains("missing required method 'consume'")),
            "{diagnostics:?}"
        );
    }
}
