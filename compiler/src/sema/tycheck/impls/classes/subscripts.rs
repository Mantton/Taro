//! Merge logical capabilities before ordinary method-family validation. An
//! omitted accessor inherits its family; an address-derived default must not
//! replace an explicitly declared base getter or setter.
use super::*;
use crate::compile::context::NativeSubscriptEntry;

pub(super) struct Subscripts {
    pub entries: Vec<(hir::DefinitionID, NativeSubscriptEntry)>,
    pub suppressed: FxHashSet<hir::DefinitionID>,
    pub overrides: FxHashMap<hir::DefinitionID, bool>,
}

/// The pre-body conformance pass provisionally sees generated defaults as
/// explicit functions. Once partial inheritance is known, its witness rows
/// must retain the inherited families as well as ordinary member lookup does.
pub(super) fn retain_inherited_defaults<'ctx>(
    gcx: Gcx<'ctx>,
    class: Ty<'ctx>,
    subscripts: &Subscripts,
    inherited: &[ClassMethod<'ctx>],
) {
    if subscripts.suppressed.is_empty() {
        return;
    }
    let adoptions = gcx.with_session_type_database(|db| db.class_adoptions.clone());
    let adoptions = adoptions
        .into_iter()
        .map(|adoption| {
            let Some(record) = gcx.conformance_record(adoption.conformance) else {
                return adoption;
            };
            if record.interface.self_ty() != Some(class) {
                return adoption;
            }
            let methods = adoption
                .methods
                .iter()
                .map(|method| {
                    if !subscripts.suppressed.contains(&method.slot.implementation) {
                        return *method;
                    }
                    let (declaration, raw) = gcx
                        .native_subscript_for_accessor(method.slot.implementation)
                        .unwrap();
                    let entry = subscripts
                        .entries
                        .iter()
                        .find(|(id, _)| *id == declaration)
                        .unwrap()
                        .1;
                    let source = if raw.getter == Some(method.slot.implementation) {
                        entry.getter
                    } else {
                        entry.setter
                    }
                    .unwrap();
                    let slot = *inherited
                        .iter()
                        .find(|slot| slot.implementation == source || slot.family == source)
                        .expect("inherited native default family");
                    crate::sema::models::ClassWitnessMethod {
                        slot,
                        is_registered: gcx.class_family_is_registered(slot.family),
                        ..*method
                    }
                })
                .collect::<Vec<_>>();
            crate::sema::models::ClassAdoption {
                methods: gcx.store.arenas.global.alloc_slice_copy(&methods),
                ..adoption
            }
        })
        .collect();
    gcx.with_session_type_database(|db| {
        db.class_adoptions = adoptions;
        db.witness_cache.clear();
        db.selection_cache.clear();
    });
}

pub(super) fn prepare<'ctx>(
    gcx: Gcx<'ctx>,
    class: Ty<'ctx>,
    declarations: &[hir::DefinitionID],
) -> Subscripts {
    let mut result = Subscripts {
        entries: gcx
            .class_base(class)
            .map(|base| gcx.class_subscripts(base))
            .unwrap_or_default(),
        suppressed: FxHashSet::default(),
        overrides: FxHashMap::default(),
    };
    for &declaration in declarations {
        let own = gcx.with_type_database(declaration.package(), |db| {
            db.native_subscripts[&declaration]
        });
        let anchor = own.getter.or(own.setter).or(own.address).unwrap();
        let context = if gcx
            .class_method_arguments(class, anchor, Default::default())
            .is_some()
        {
            class
        } else {
            gcx.get_impl_target_ty(gcx.definition_parent(declaration).unwrap())
                .unwrap()
        };
        let shape = signature(gcx, context, own);
        let candidates: Vec<_> = result
            .entries
            .iter()
            .enumerate()
            .filter_map(|(index, (_, base))| {
                let base_anchor = base.getter.or(base.setter).or(base.address).unwrap();
                if !gcx.is_definition_visible(base_anchor, anchor) {
                    return None;
                }
                let same_interface = match (
                    gcx.class_method_interface(context, anchor),
                    gcx.class_method_interface(context, base_anchor),
                ) {
                    (None, None) => true,
                    (Some(actual), Some(base)) => {
                        actual.id == base.id && actual.arguments.get(1..) == base.arguments.get(1..)
                    }
                    _ => false,
                };
                let expected = signature(gcx, context, *base)?;
                (same_interface
                    && shape
                        .as_ref()
                        .is_some_and(|actual| actual.0 == expected.0 && actual.1 == expected.1))
                .then_some((index, expected.2))
            })
            .collect();
        let error = |message: &str| {
            gcx.dcx()
                .emit_error(message.into(), Some(gcx.definition_ident(declaration).span))
        };
        if candidates.len() > 1 {
            error("subscript override is ambiguous between inherited declarations");
            continue;
        }
        let mut effective = own;
        if let Some(&(index, element)) = candidates.first() {
            let base = result.entries[index].1;
            if !own.is_override {
                error("overriding an inherited subscript requires override");
            }
            if base.is_final {
                error("cannot override a final subscript");
            }
            if shape.as_ref().is_some_and(|actual| actual.2 != element) {
                error("subscript override must preserve the element type exactly");
            }
            for (actual, inherited, derived) in [
                (own.getter, base.getter, own.getter_is_default),
                (own.setter, base.setter, own.setter_is_default),
                (own.address, base.address, false),
            ] {
                if let Some(actual) = actual {
                    if derived && inherited.is_some() {
                        result.suppressed.insert(actual);
                    } else {
                        // Adding a capability introduces a new method family.
                        result.overrides.insert(actual, inherited.is_some());
                    }
                }
            }
            if own.getter.is_none() || own.getter_is_default && base.getter.is_some() {
                effective.getter = base.getter;
                effective.getter_is_default = base.getter_is_default;
            }
            if own.setter.is_none() || own.setter_is_default && base.setter.is_some() {
                effective.setter = base.setter;
                effective.setter_is_default = base.setter_is_default;
            }
            effective.address = own.address.or(base.address);
            effective.is_final |= base.is_final;
            result.entries[index] = (declaration, effective);
        } else {
            if own.is_override {
                error("override has no inherited subscript with matching indices and labels");
            }
            if own.getter.is_none() {
                error("a subscript requires an inherited or declared get accessor");
            }
            result.entries.push((declaration, effective));
        }
    }
    result
}

fn signature<'ctx>(
    gcx: Gcx<'ctx>,
    class: Ty<'ctx>,
    entry: NativeSubscriptEntry,
) -> Option<(Vec<Ty<'ctx>>, Vec<Option<crate::span::Symbol>>, Ty<'ctx>)> {
    let source = entry.getter.or(entry.setter).or(entry.address)?;
    let args = gcx.class_method_arguments(class, source, Default::default())?;
    let ty = method_type(gcx, source, args);
    let TyKind::FnPointer { inputs, output, .. } = ty.kind() else {
        return None;
    };
    let setter = Some(source) == entry.setter;
    let end = inputs.len() - usize::from(setter);
    let element = if setter {
        *inputs.last()?
    } else if Some(source) == entry.address {
        let TyKind::Reference(inner) = output.kind() else {
            return None;
        };
        inner
    } else {
        output
    };
    let labels = gcx.get_signature(source).inputs[1..end]
        .iter()
        .map(|p| p.label)
        .collect();
    Some((inputs[1..end].to_vec(), labels, element))
}

/// Native element types are invariant, including fixed associated bindings on
/// adopted defaults. Compare their normalized types rather than projection
/// spelling such as `Storage[Base]::Element` versus `int32`.
pub(super) fn method_type<'ctx>(
    gcx: Gcx<'ctx>,
    source: hir::DefinitionID,
    args: crate::sema::models::GenericArguments<'ctx>,
) -> Ty<'ctx> {
    let ty = instantiate_ty_with_args(gcx, gcx.get_type(source), args);
    if gcx.native_subscript_for_accessor(source).is_none() {
        return crate::sema::tycheck::utils::normalize_aliases(gcx, ty);
    }
    let constraints = crate::sema::tycheck::constraints::canonical_constraints_of(gcx, source)
        .into_iter()
        .map(|constraint| {
            crate::sema::tycheck::utils::instantiate::instantiate_constraint_with_args(
                gcx,
                constraint.value,
                args,
            )
        })
        .collect();
    crate::sema::tycheck::utils::normalize_ty(
        std::rc::Rc::new(crate::sema::tycheck::infer::InferCtx::new(gcx)),
        ty,
        &crate::sema::tycheck::utils::ParamEnv::new(constraints),
    )
}
