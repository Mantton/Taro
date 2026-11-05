//! Shared associated-member discovery for checked and inferred type paths.
use crate::{
    compile::context::Gcx,
    hir::{DefinitionID, DefinitionKind},
    sema::{
        models::Ty,
        resolve::models::TypeHead,
        tycheck::{
            overloads::dispatch_fingerprint,
            utils::{
                generics::GenericsBuilder, instantiate::instantiate_ty_with_args,
                normalize_aliases, type_head_from_value_ty,
            },
        },
    },
    span::Symbol,
};
use rustc_hash::FxHashSet;

pub(crate) fn static_candidates<'ctx>(
    gcx: Gcx<'ctx>,
    base: Ty<'ctx>,
    name: Symbol,
    current: DefinitionID,
) -> Vec<DefinitionID> {
    if name.as_str() == "init"
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
