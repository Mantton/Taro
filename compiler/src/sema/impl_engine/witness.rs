use crate::{
    compile::context::Gcx,
    sema::{
        models::{
            AliasKind, ConformanceRecord, ConformanceWitness, GenericArgument, GenericArguments,
            GenericParameter, InferTy, InterfaceGoal, InterfaceMethodRequirement,
            InterfacePropertyRequirement, MethodImplementation, MethodWitness, SelectionError,
            SelectionMode, SyntheticMethodKind, Ty, TyKind,
        },
        resolve::models::TypeHead,
        tycheck::{
            fold::{TypeFoldable, TypeFolder, TypeSuperFoldable},
            infer::InferCtx,
            utils::{
                ParamEnv, generics::GenericsBuilder, instantiate::instantiate_ty_with_args,
                normalize_ty, type_head_from_value_ty, unify::TypeUnifier,
            },
        },
    },
};
use rustc_hash::FxHashMap;
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
                let Some(type_head) = type_head_from_value_ty(goal.self_ty)
                    .or_else(|| record.target.is_blanket().then_some(record.target))
                else {
                    return Err(SelectionError::NoCandidates(goal));
                };
                build_witness_from_record(gcx, type_head, &record, selected.subst)?
            }
            crate::sema::models::CandidateSource::BuiltinTuple => ConformanceWitness::default(),
            crate::sema::models::CandidateSource::BuiltinClosure => {
                build_closure_witness(gcx, goal)?
            }
            crate::sema::models::CandidateSource::BuiltinClone => {
                build_builtin_clone_witness(gcx, goal)?
            }
            crate::sema::models::CandidateSource::BuiltinCopy
            | crate::sema::models::CandidateSource::BuiltinSendable
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

    for assoc in &requirements.types {
        let Some(ty) = find_type_witness(gcx, type_head, assoc.id, assoc.name, record) else {
            return Err(SelectionError::NoCandidates(interface_goal_from_record(
                gcx, record,
            )));
        };
        let ty = if subst.is_empty() {
            ty
        } else {
            instantiate_ty_with_args(gcx, ty, subst)
        };
        witness.type_witnesses.insert(assoc.id, ty);
    }

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
            constant.default.is_some(),
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

    Ok(witness)
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

    let inherent = gcx
        .lookup_computed_property(type_head, requirement.name)
        .filter(|source| gcx.is_visibility_allowed(source.visibility, record.extension));

    let mut out = Vec::with_capacity(2);
    out.push((
        requirement.getter_id,
        find_property_accessor_witness(
            gcx,
            type_head,
            requirement,
            PropertyAccessorKind::Getter,
            explicit,
            inherent,
            record,
            subst,
            type_witnesses,
        )?,
    ));
    if let Some(setter_id) = requirement.setter_id {
        out.push((
            setter_id,
            find_property_accessor_witness(
                gcx,
                type_head,
                requirement,
                PropertyAccessorKind::Setter,
                explicit,
                inherent,
                record,
                subst,
                type_witnesses,
            )?,
        ));
    }
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

#[derive(Clone, Copy)]
enum PropertyAccessorKind {
    Getter,
    Setter,
}

fn find_property_accessor_witness<'ctx>(
    gcx: Gcx<'ctx>,
    type_head: TypeHead,
    requirement: &InterfacePropertyRequirement<'ctx>,
    kind: PropertyAccessorKind,
    explicit: Option<crate::compile::context::ComputedPropertyEntry<'ctx>>,
    inherent: Option<crate::compile::context::ComputedPropertyEntry<'ctx>>,
    record: &ConformanceRecord<'ctx>,
    subst: GenericArguments<'ctx>,
    type_witnesses: &FxHashMap<crate::hir::DefinitionID, Ty<'ctx>>,
) -> Option<MethodWitness<'ctx>> {
    let requirement_id = match kind {
        PropertyAccessorKind::Getter => requirement.getter_id,
        PropertyAccessorKind::Setter => requirement.setter_id?,
    };

    for source in [explicit, inherent].into_iter().flatten() {
        let implementation_id = match kind {
            PropertyAccessorKind::Getter => Some(source.getter_id),
            PropertyAccessorKind::Setter => source.setter_id,
        };
        let Some(implementation_id) = implementation_id else {
            continue;
        };
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
        kind,
        record,
        subst,
        type_witnesses,
    )
    .or_else(|| {
        let is_required = match kind {
            PropertyAccessorKind::Getter => requirement.getter_is_required,
            PropertyAccessorKind::Setter => requirement.setter_is_required?,
        };
        default_accessor_witness(gcx, requirement_id, is_required)
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
    kind: PropertyAccessorKind,
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
    let mut expected_ty = substitute_with_args(gcx, requirement.ty, record.interface.arguments);
    if !subst.is_empty() {
        expected_ty = instantiate_ty_with_args(gcx, expected_ty, subst);
    }
    expected_ty = substitute_projection_witnesses(gcx, expected_ty, type_witnesses);
    if field_ty != expected_ty {
        return None;
    }

    let (accessor_id, synthetic_kind) = match kind {
        PropertyAccessorKind::Getter => {
            if gcx.definition_is_async(requirement.getter_id) {
                return None;
            }
            let mut receiver = gcx.get_signature(requirement.getter_id).inputs.first()?.ty;
            receiver = substitute_with_args(gcx, receiver, record.interface.arguments);
            if !subst.is_empty() {
                receiver = instantiate_ty_with_args(gcx, receiver, subst);
            }
            receiver = substitute_projection_witnesses(gcx, receiver, type_witnesses);
            match receiver.kind() {
                TyKind::Reference(inner, _) if inner == self_ty => {
                    if !gcx.is_type_copyable(field_ty) {
                        return None;
                    }
                }
                _ if receiver == self_ty => {}
                _ => return None,
            }
            (
                requirement.getter_id,
                SyntheticMethodKind::PropertyFieldGetter(field_index),
            )
        }
        PropertyAccessorKind::Setter => {
            if field.mutability != crate::hir::Mutability::Mutable {
                return None;
            }
            (
                requirement.setter_id?,
                SyntheticMethodKind::PropertyFieldSetter(field_index),
            )
        }
    };

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
    let Some(type_head) = type_head_from_value_ty(goal.self_ty) else {
        return Err(SelectionError::NoCandidates(goal));
    };
    let Some(requirements) = gcx.get_interface_requirements(goal.interface_id) else {
        return Ok(ConformanceWitness::default());
    };

    let mut witness = ConformanceWitness::default();
    for method in &requirements.methods {
        let args_template = GenericsBuilder::identity_for_item(gcx, method.id);
        let Some(synthesized) = crate::sema::tycheck::derive::try_synthesize_method(
            gcx,
            type_head,
            goal.self_ty,
            goal.interface_id,
            goal.interface_args,
            method.name,
            method.id,
            args_template,
        ) else {
            return Err(SelectionError::NoCandidates(goal));
        };
        witness
            .method_witnesses
            .insert(method.id, synthesized.witness);
    }
    witness.extension_id = None;
    Ok(witness)
}

fn build_closure_witness<'ctx>(
    gcx: Gcx<'ctx>,
    goal: InterfaceGoal<'ctx>,
) -> Result<ConformanceWitness<'ctx>, SelectionError<'ctx>> {
    let TypeHead::Closure(closure_def_id) =
        type_head_from_value_ty(goal.self_ty).ok_or(SelectionError::NoCandidates(goal))?
    else {
        return Err(SelectionError::NoCandidates(goal));
    };
    let _captures = gcx
        .get_closure_captures(closure_def_id)
        .ok_or(SelectionError::NoCandidates(goal))?;

    let kind = if gcx.std_item_def(crate::hir::StdItem::Fn) == Some(goal.interface_id)
        || gcx.std_item_def(crate::hir::StdItem::AsyncFn) == Some(goal.interface_id)
    {
        SyntheticMethodKind::ClosureCall
    } else if gcx.std_item_def(crate::hir::StdItem::FnMut) == Some(goal.interface_id)
        || gcx.std_item_def(crate::hir::StdItem::AsyncFnMut) == Some(goal.interface_id)
    {
        SyntheticMethodKind::ClosureCallMut
    } else if gcx.std_item_def(crate::hir::StdItem::FnOnce) == Some(goal.interface_id)
        || gcx.std_item_def(crate::hir::StdItem::AsyncFnOnce) == Some(goal.interface_id)
    {
        SyntheticMethodKind::ClosureCallOnce
    } else {
        return Err(SelectionError::NoCandidates(goal));
    };

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

fn find_type_witness<'ctx>(
    gcx: Gcx<'ctx>,
    type_head: TypeHead,
    assoc_id: crate::hir::DefinitionID,
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

    if let Some(alias_id) = alias_id {
        return Some(gcx.get_alias_type(alias_id));
    }

    let reqs = gcx.get_interface_requirements(record.interface.id)?;
    let assoc = reqs.types.iter().find(|ty| ty.id == assoc_id)?;
    assoc.default_type
}

fn find_method_witness<'ctx>(
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
                })
                .collect()
        });
    }

    for candidate in candidates {
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

    if !requirement.is_required {
        let args_template = GenericsBuilder::identity_for_item(gcx, requirement.id);
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

fn find_constant_witness<'ctx>(
    gcx: Gcx<'ctx>,
    _type_head: TypeHead,
    _requirement_id: crate::hir::DefinitionID,
    requirement_name: crate::span::Symbol,
    requirement_ty: Ty<'ctx>,
    has_default: bool,
    record: &ConformanceRecord<'ctx>,
    subst: GenericArguments<'ctx>,
    type_witnesses: &FxHashMap<crate::hir::DefinitionID, Ty<'ctx>>,
) -> Option<crate::hir::DefinitionID> {
    let impl_id = record.extension;
    let extension_pkg = impl_id.package();
    let mut expected_ty = substitute_with_args(gcx, requirement_ty, record.interface.arguments);
    if !subst.is_empty() {
        expected_ty = instantiate_ty_with_args(gcx, expected_ty, subst);
    }
    let expected_ty = substitute_projection_witnesses(gcx, expected_ty, type_witnesses);

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

    for candidate in &candidates {
        if gcx.get_type(*candidate) == expected_ty {
            return Some(*candidate);
        }
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
    if !interface_sig.same_shape(impl_sig) {
        return false;
    }

    let interface_generics = gcx.generics_of(interface_fn_id);
    let impl_generics = gcx.generics_of(impl_fn_id);
    if interface_generics.parameters.len() != impl_generics.parameters.len() {
        return false;
    }

    let mut expected = Ty::from_labeled_signature(gcx, interface_sig);
    expected = substitute_with_args(gcx, expected, record.interface.arguments);
    if !subst.is_empty() {
        expected = instantiate_ty_with_args(gcx, expected, subst);
    }
    expected = substitute_projection_witnesses(gcx, expected, type_witnesses);

    let mut actual = Ty::from_labeled_signature(gcx, impl_sig);
    if !subst.is_empty() {
        actual = instantiate_ty_with_args(gcx, actual, subst);
    }
    actual = substitute_projection_witnesses(gcx, actual, type_witnesses);

    let mut expected_freshener = SignatureFreshener::new(gcx);
    let expected = expected_freshener.freshen(expected);

    let mut actual_freshener = SignatureFreshener::new(gcx);
    let actual = actual_freshener.freshen(actual);

    expected == actual
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

fn substitute_with_args<'ctx>(
    gcx: Gcx<'ctx>,
    ty: Ty<'ctx>,
    args: GenericArguments<'ctx>,
) -> Ty<'ctx> {
    if args.is_empty() {
        return ty;
    }
    let mut substitutor = ArgSubstitutor { gcx, args };
    ty.fold_with(&mut substitutor)
}

fn substitute_projection_witnesses<'ctx>(
    gcx: Gcx<'ctx>,
    ty: Ty<'ctx>,
    type_witnesses: &FxHashMap<crate::hir::DefinitionID, Ty<'ctx>>,
) -> Ty<'ctx> {
    if type_witnesses.is_empty() {
        return ty;
    }
    let mut substitutor = ProjectionSubstitutor {
        gcx,
        type_witnesses,
    };
    ty.fold_with(&mut substitutor)
}

struct ArgSubstitutor<'ctx> {
    gcx: Gcx<'ctx>,
    args: GenericArguments<'ctx>,
}

impl<'ctx> TypeFolder<'ctx> for ArgSubstitutor<'ctx> {
    fn gcx(&self) -> Gcx<'ctx> {
        self.gcx
    }

    fn fold_ty(&mut self, ty: Ty<'ctx>) -> Ty<'ctx> {
        match ty.kind() {
            TyKind::Parameter(param) => {
                if let Some(arg) = self.args.get(param.index as usize) {
                    if let GenericArgument::Type(sub_ty) = arg {
                        return *sub_ty;
                    }
                }
                ty
            }
            _ => ty.super_fold_with(self),
        }
    }
}

struct ProjectionSubstitutor<'ctx, 'w> {
    gcx: Gcx<'ctx>,
    type_witnesses: &'w FxHashMap<crate::hir::DefinitionID, Ty<'ctx>>,
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
                ..
            } => {
                if let Some(witness_ty) = self.type_witnesses.get(&def_id) {
                    return witness_ty.fold_with(self);
                }
                ty.super_fold_with(self)
            }
            _ => ty.super_fold_with(self),
        }
    }
}

struct SignatureFreshener<'ctx> {
    next_var_id: u32,
    substitutions: FxHashMap<GenericParameter, u32>,
    gcx: Gcx<'ctx>,
}

impl<'ctx> SignatureFreshener<'ctx> {
    fn new(gcx: Gcx<'ctx>) -> Self {
        Self {
            next_var_id: 0,
            substitutions: FxHashMap::default(),
            gcx,
        }
    }

    fn fresh_var(&mut self) -> u32 {
        let var = self.next_var_id;
        self.next_var_id += 1;
        var
    }

    fn freshen(&mut self, ty: Ty<'ctx>) -> Ty<'ctx> {
        ty.fold_with(self)
    }
}

impl<'ctx> TypeFolder<'ctx> for SignatureFreshener<'ctx> {
    fn gcx(&self) -> Gcx<'ctx> {
        self.gcx
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
