//! Shared associated-member discovery for checked and inferred type paths.
use crate::{
    compile::context::Gcx,
    hir::{DefinitionID, DefinitionKind},
    sema::{
        error::TypeError,
        models::{Constraint, GenericArgument, GenericArguments, InterfaceReference, Ty, TyKind},
        resolve::models::TypeHead,
        tycheck::{
            infer::InferCtx,
            overloads::dispatch_fingerprint,
            utils::{
                generics::GenericsBuilder, instantiate::instantiate_ty_with_args,
                normalize_aliases, type_head_from_value_ty,
            },
        },
    },
    span::{Span, Symbol},
};
use rustc_hash::FxHashSet;
use std::rc::Rc;

pub(crate) fn static_candidates<'ctx>(
    gcx: Gcx<'ctx>,
    base: Ty<'ctx>,
    name: Symbol,
    current: DefinitionID,
) -> Vec<DefinitionID> {
    if gcx.symbol_text(name).as_str() == "init"
        && let Some(info) = gcx.class_info(base)
    {
        return info
            .initializers
            .iter()
            .map(|entry| entry.definition)
            .collect();
    }
    let ancestry = gcx.class_ancestry(base);
    let owners = if ancestry.is_empty() {
        vec![base]
    } else {
        ancestry
    };
    let mut members = Vec::new();
    let mut seen = FxHashSet::default();
    let mut inherited_shapes = FxHashSet::default();
    for owner in owners {
        let Some(head) = type_head_from_value_ty(owner) else {
            continue;
        };
        let mut declarations = Vec::new();
        let mut collect = |db: &crate::compile::context::TypeDatabase<'ctx>| {
            if let Some(set) = db
                .type_head_to_members
                .get(&head)
                .and_then(|index| index.inherent_static.get(&name))
            {
                declarations.extend(set.members.iter().copied().filter(|id| seen.insert(*id)));
            }
        };
        gcx.with_session_type_database(|db| collect(db));
        for package in gcx.visible_packages() {
            gcx.with_type_database(package, |db| collect(db));
        }
        let mut shapes = Vec::new();
        for id in declarations {
            let parent = gcx.definition_parent(id);
            let target = parent.and_then(|parent| gcx.get_impl_target_ty(parent));
            let arguments = if gcx.is_class_type(owner)
                && !owner.contains_inference()
                && let (Some(parent), Some(target)) = (parent, target)
            {
                let Some(mut arguments) =
                    crate::sema::impl_engine::deduce_impl_subst(gcx, parent, owner, &[])
                        .map(|arguments| arguments.to_vec())
                else {
                    continue;
                };
                let target_arguments = gcx.store.interners.intern_generic_args(arguments.clone());
                if normalize_aliases(gcx, instantiate_ty_with_args(gcx, target, target_arguments))
                    != normalize_aliases(gcx, owner)
                {
                    continue;
                }
                let generics = gcx.generics_of(id);
                let identity = GenericsBuilder::identity_for_item(gcx, id);
                arguments.extend(identity.iter().skip(generics.parent_count).copied());
                Some(gcx.store.interners.intern_generic_args(arguments))
            } else {
                None
            };
            let shape = dispatch_fingerprint(gcx, id, arguments);
            if !inherited_shapes.contains(&shape) {
                members.push(id);
            }
            // An inaccessible subclass declaration cannot hide an accessible base overload.
            if gcx.is_definition_visible(id, current) {
                shapes.push(shape);
            }
        }
        inherited_shapes.extend(shapes);
        if let TypeHead::Nominal(interface) = head
            && gcx.definition_kind(interface) == DefinitionKind::Interface
            && let Some(requirements) = gcx.get_interface_requirements(interface)
            && let Some(property) = requirements
                .properties
                .iter()
                .find(|property| property.name == name)
        {
            members.push(property.getter_id);
        }
    }
    if members.is_empty() {
        members = conformance_static_requirements(gcx, base, name);
    }
    members
}

/// Static requirements of the interfaces a concrete type declares, so
/// `Type::member()` reaches a witness that has no inherent declaration: one
/// in a conformance block, or one the compiler synthesizes (`Default`). The
/// call names the requirement with `Self` fixed to the type, the same form as
/// a bounded `T::member()`; selection proves the conformance and picks the
/// witness. Inherent statics take precedence and are found first.
fn conformance_static_requirements<'ctx>(
    gcx: Gcx<'ctx>,
    base: Ty<'ctx>,
    name: Symbol,
) -> Vec<DefinitionID> {
    let Some(head) = type_head_from_value_ty(normalize_aliases(gcx, base)) else {
        return Vec::new();
    };
    if let TypeHead::Nominal(id) = head
        && gcx.definition_kind(id) == DefinitionKind::Interface
    {
        return Vec::new();
    }
    let records = gcx.collect_from_databases(|db| {
        db.conformance_by_head
            .get(&head)
            .into_iter()
            .flat_map(|ids| ids.iter())
            .filter_map(|id| db.conformance_records.get(id))
            .map(|record| record.interface)
            .collect::<Vec<_>>()
    });
    let mut seen = FxHashSet::default();
    let mut members = Vec::new();
    for interface in records {
        for interface in
            crate::sema::impl_engine::ref_ops::collect_interface_with_superfaces(gcx, interface)
        {
            let Some(requirements) = gcx.get_interface_requirements(interface.id) else {
                continue;
            };
            for method in &requirements.methods {
                if method.name == name && !method.has_self && seen.insert(method.id) {
                    members.push(method.id);
                }
            }
        }
    }
    if matches!(head, TypeHead::Tuple(_))
        && let Some(default_id) = gcx.std_item_def(crate::hir::StdItem::Default)
        && let Some(requirements) = gcx.get_interface_requirements(default_id)
    {
        for method in &requirements.methods {
            if method.name == name && !method.has_self && seen.insert(method.id) {
                members.push(method.id);
            }
        }
    }
    members
}

/// Identify the instantiated ancestor without moving inference variables into
/// another context. The caller unifies the target using its own InferCtx.
pub(crate) fn static_target<'ctx>(
    gcx: Gcx<'ctx>,
    owner: Ty<'ctx>,
    source: DefinitionID,
) -> Option<(Ty<'ctx>, Ty<'ctx>)> {
    let parent = gcx.definition_parent(source)?;
    if gcx.definition_kind(parent) == DefinitionKind::Interface {
        // A bounded T::method fixes the interface's Self even when its result
        // contains projections. Waiting for result coercion can leave Self
        // unresolved behind an associated type such as TryFrom::Error.
        return Some((gcx.types.self_type_parameter, owner));
    }
    let target = gcx.get_impl_target_ty(parent)?;
    let head = type_head_from_value_ty(normalize_aliases(gcx, target))?;
    let ancestor = gcx
        .class_ancestry(owner)
        .into_iter()
        .find(|ancestor| type_head_from_value_ty(*ancestor) == Some(head))?;
    Some((target, ancestor))
}

/// A constant in an extension can be read while an alias or array header is
/// being collected. Lower that extension's target on first use. Taking the
/// source prevents a circular target from recursing indefinitely.
fn constant_target<'ctx>(gcx: Gcx<'ctx>, extension: DefinitionID) -> Option<Ty<'ctx>> {
    use crate::sema::tycheck::lower::{DefTyLoweringCtx, TypeLowerer};
    if let Some(target) = gcx.get_impl_target_ty(extension) {
        return Some(target);
    }
    let source = gcx
        .store
        .constant_extension_targets
        .borrow_mut()
        .remove(&extension)?;
    let target = DefTyLoweringCtx::new(extension, gcx)
        .lowerer()
        .lower_type(source);
    gcx.cache_impl_target_ty(extension, target);
    Some(target)
}

/// Retain the declaring interface's arguments so two specializations of the
/// same requirement count as different candidates. A generic body can use
/// its declared bounds without committing to one implementation.
pub(crate) fn interface_constant<'ctx>(
    gcx: Gcx<'ctx>,
    receiver: Ty<'ctx>,
    name: Symbol,
    current: DefinitionID,
) -> Result<Option<(DefinitionID, InterfaceReference<'ctx>)>, TypeError<'ctx>> {
    use crate::sema::impl_engine::{deduce_conformance_interface, ref_ops};
    let receiver = normalize_aliases(gcx, receiver);
    if receiver.contains_inference() || matches!(receiver.kind(), TyKind::BoxedExistential { .. }) {
        return Ok(None);
    }
    let mut requirements = gcx.collect_from_databases(|db| {
        db.interface_requirements
            .iter()
            .flat_map(|(&interface, requirements)| {
                requirements
                    .constants
                    .iter()
                    .filter(move |req| req.name == name)
                    .map(move |req| (interface, req.id))
            })
            .collect()
    });
    let early = gcx.store.collecting_constant_headers.get();
    if early {
        requirements.extend(
            gcx.named_constant_headers(name)
                .into_iter()
                .filter(|(owner, _)| gcx.definition_kind(*owner) == DefinitionKind::Interface),
        );
        requirements.sort_unstable();
        requirements.dedup();
    }
    if requirements.is_empty() {
        return Ok(None);
    }
    let constraints: Vec<_> = super::super::constraints::canonical_constraints_of(gcx, current)
        .into_iter()
        .map(|constraint| constraint.value)
        .collect();
    let constraints: &[_] = gcx.store.arenas.global.alloc_slice_clone(&constraints);
    let mut roots = Vec::new();
    for constraint in constraints {
        if let Constraint::Bound { ty, interface } = constraint
            && *ty == receiver
        {
            roots.extend(ref_ops::collect_interface_with_superfaces(gcx, *interface));
        }
    }
    let ancestry = gcx.class_ancestry(receiver);
    let mut matches = Vec::new();
    let mut rejected_header = false;
    for (interface_id, requirement) in requirements {
        if early {
            super::super::collect::conformances::ensure_candidates(gcx, receiver, interface_id);
        }
        for bound in roots.iter().filter(|bound| bound.id == interface_id) {
            matches.push((requirement, *bound));
        }
        let records = gcx.collect_from_databases(|db| {
            db.conformance_by_interface
                .get(&interface_id)
                .into_iter()
                .flatten()
                .filter_map(|id| db.conformance_records.get(id).copied())
                .collect()
        });
        for owner in
            std::iter::once(receiver).chain(ancestry.iter().copied().filter(|ty| *ty != receiver))
        {
            for record in &records {
                if !record.target.is_blanket()
                    && Some(record.target) != type_head_from_value_ty(owner)
                {
                    continue;
                }
                let Some(reference) = deduce_conformance_interface(gcx, record, owner) else {
                    continue;
                };
                if !matches!(reference.arguments.first(), Some(GenericArgument::Type(ty)) if normalize_aliases(gcx,*ty) == owner)
                {
                    continue;
                }
                let reference = ref_ops::interface_ref_with_self(gcx, receiver, reference);
                let Some(goal) = reference.to_goal(gcx, constraints) else {
                    continue;
                };
                let mode = crate::sema::models::SelectionMode::Typecheck;
                let applicable = if early {
                    matches!(
                        gcx.select_interface_impl(goal, mode),
                        crate::sema::models::SelectionResult::Selected(_)
                    )
                } else {
                    gcx.build_conformance_witness(goal, mode).is_ok()
                };
                if applicable {
                    matches.push((requirement, reference));
                } else if early {
                    rejected_header = true;
                }
            }
        }
    }
    let mut seen = FxHashSet::default();
    let had_candidate = !matches.is_empty();
    matches.retain(|(id, interface)| {
        gcx.is_definition_visible(*id, current) && seen.insert((*id, interface.arguments))
    });
    match matches.as_slice() {
        [] if had_candidate => Err(TypeError::ConstantNotVisible { name, on: receiver }),
        [] if rejected_header => Err(TypeError::NoApplicableConstant { name, on: receiver }),
        [] => Ok(None),
        [found] => Ok(Some(*found)),
        _ => Err(TypeError::AmbiguousConstant { name, on: receiver }),
    }
}

pub(crate) fn associated_constant<'ctx>(
    gcx: Gcx<'ctx>,
    base: Ty<'ctx>,
    name: Symbol,
    current: DefinitionID,
    inference: Option<&Rc<InferCtx<'ctx>>>,
    span: Span,
) -> Result<Option<DefinitionID>, TypeError<'ctx>> {
    if let Some(id) = inherent_constant(gcx, base, name, current, inference, span)? {
        return Ok(Some(id));
    }
    Ok(interface_constant(gcx, base, name, current)?.map(|(id, _)| id))
}

/// Bind in the extension's coordinates: Pair[B, A] can reorder the arguments.
pub(crate) fn constant_arguments<'ctx>(
    icx: &Rc<InferCtx<'ctx>>,
    id: DefinitionID,
    base: Ty<'ctx>,
    current: DefinitionID,
    span: Span,
) -> Result<GenericArguments<'ctx>, TypeError<'ctx>> {
    let gcx = icx.gcx;
    let extension = gcx
        .definition_parent(id)
        .expect("associated constant owner");
    if gcx.definition_kind(extension) == DefinitionKind::Interface {
        let name = gcx.definition_ident(id).symbol;
        return interface_constant(gcx, base, name, current)?
            .filter(|(requirement, _)| *requirement == id)
            .map(|(_, interface)| interface.arguments)
            .ok_or(TypeError::NoSuchMember { name, on: base });
    }
    let target = constant_target(gcx, extension).ok_or(TypeError::NoSuchMember {
        name: gcx.definition_ident(id).symbol,
        on: base,
    })?;
    let arguments = icx.fresh_args_for_def(extension, span);
    let target = normalize_aliases(gcx, instantiate_ty_with_args(gcx, target, arguments));
    let owner = gcx
        .class_ancestry(base)
        .into_iter()
        .find(|ty| type_head_from_value_ty(*ty) == type_head_from_value_ty(target))
        .unwrap_or(base);
    super::unify::TypeUnifier::new(icx.clone()).unify(target, normalize_aliases(gcx, owner))?;
    Ok(icx.resolve_args_if_possible(arguments))
}

pub(crate) fn inherent_constant<'ctx>(
    gcx: Gcx<'ctx>,
    base: Ty<'ctx>,
    name: Symbol,
    current: DefinitionID,
    inference: Option<&Rc<InferCtx<'ctx>>>,
    span: Span,
) -> Result<Option<DefinitionID>, TypeError<'ctx>> {
    let base = normalize_aliases(gcx, base);
    let mut invisible = false;
    let ancestors = gcx.class_ancestry(base);
    for owner in std::iter::once(base).chain(ancestors.into_iter().filter(|ty| *ty != base)) {
        let Some(head) = type_head_from_value_ty(owner) else {
            continue;
        };
        let mut ids = gcx.collect_from_databases(|db| {
            db.type_head_to_members
                .get(&head)
                .and_then(|index| index.inherent_constants.get(&name))
                .cloned()
                .unwrap_or_default()
        });
        if ids.is_empty() {
            continue;
        }
        ids.sort_unstable();
        ids.dedup();
        let local;
        let icx = match inference {
            Some(icx) => icx,
            None if owner.contains_inference() => continue,
            None => {
                local = Rc::new(InferCtx::new(gcx));
                &local
            }
        };
        let mut found = None;
        for id in ids {
            if !icx.probe(|_| constant_arguments(icx, id, owner, current, span).is_ok()) {
                continue;
            }
            if !gcx.is_definition_visible(id, current) {
                invisible = true;
                continue;
            }
            if found.replace(id).is_some() {
                return Err(TypeError::AmbiguousConstant { name, on: base });
            }
        }
        if found.is_some() {
            return Ok(found);
        }
    }
    if invisible {
        return Err(TypeError::ConstantNotVisible { name, on: base });
    }
    Ok(None)
}
